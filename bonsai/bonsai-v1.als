module bonsai
open prefixpath -- paths which can be prefixes of other paths

sig File {}

sig Manifest {
    files: Path -> lone File
}
{ all p1, p2: paths[files] | not ordered[p1, p2] } -- paths within a manifest can't be prefixes of each other

-- Return paths from a path -> X relation
let paths[pf] = pf.univ

-- Return subset of manifests mentioning the given paths
fun withPaths[manifests: set Manifest, p: set Path]: set Manifest {
	{ pm: manifests | p in paths[pm.files] }
}

fact identity {
	all m, m': Manifest | m.files = m'.files => m = m'
	all b,b': BonsaiCS | {
			b.del = b'.del
			b.add = b'.add
			b.mod = b'.mod
		} => b = b'
}

sig BonsaiCS {
	del: set Path,
	add: Path -> File,
	mod: Path -> File,

	-- not needed, but useful for assertions / diagrams
	manifest: Manifest,
	parents: set Manifest,
}
-- { #parents <= 2 }

fun pathConflict[manifests: set Manifest]: Path {
	let paths = paths[manifests.files] |
		{ p: paths | some p': paths | ordered[p, p'] }
}

-- Set of conflicts among manifests - files whose paths match but their contents don't
fun contentConflict[manifests: set Manifest]: set Path {
	{ p: paths[manifests.files] | some m1, m2: withPaths[manifests, p] | m1.files[p] != m2.files[p] }
}

fun conflict[manifests: set Manifest]: set Path {
	pathConflict[manifests] + contentConflict[manifests]
}

-- Set of paths which differ between a manifest and one of its parents which also contains that path
fun diffFiles[m: Manifest, parents: set Manifest]: set Path {
	-- paths is common paths between manifest and parents
	let commonpaths = paths[m.files] & paths[parents.files] |
		{ cp: commonpaths |
			-- only consider parents which contain the path
			some pf: withPaths[parents, cp] | m.files[cp] != pf.files[cp]
		}
}

fun parentPathConflicts[parent: set Path, manifest: set Path]: set Path {
	{ p: parent | some m: manifest | prefix[m, p] }
}

-- Generate a bonsai cs as a diff between a manifest and an arbitrary number of parents
pred bonsaiDiff[b: BonsaiCS, m: one Manifest, p: set Manifest ] {
	m not in p -- precond

	-- XXX FIXME - deal with path conflicts
	-- anything in parents which is prefixed by something in add/mod/del has to be in del
	-- (seems v brute force)
	-- also doesn't seem sufficient

	b.add = (paths[m.files] - paths[p.files]) <: m.files -- add files in manifest not in parents
	b.mod = diffFiles[m, p] <: m.files -- same paths, different contents
	 let dels = paths[p.files] - paths[m.files] | -- anything in parents not in manifest
		b.del = dels + parentPathConflicts[paths[p.files], paths[b.add] + paths[b.mod] + dels]

	-- helpers
	b.manifest = m
	b.parents = p
}

-- Apply a BonsaiCS to its parents to reconstruct the manifest
pred bonsaiApply[m: Manifest, b: BonsaiCS, parents: set Manifest] {
	-- new manifest is union of all the parents minus all the modified paths,
	-- with new changes applied
	let modded = b.del + paths[b.add] + paths[b.mod] |
		m.files = ((paths[parents.files] - modded) <: parents.files) + b.add + b.mod
}

fact traceDiff {
	all b: BonsaiCS |
		some m: Manifest | let p = Manifest - m | bonsaiDiff[b, m, p]
}

run show {
	some b: BonsaiCS | {
		-- something of everything
		some conflict[b.parents]
		some b.del
		some b.add
		some b.mod
	}
} for 10 but exactly 1 BonsaiCS

-- modified files are actually different from parents
assert modDifferent {
	all b: BonsaiCS | let mpaths = paths[b.mod] {
		-- all file paths in b.mod come from parents
		mpaths in paths[b.parents.files]

		-- at least one parent file with a path in b.mod must be different from b.mod
		all n: mpaths | some pf: b.parents.files[n] | pf != b.mod[n]
	}
}
check modDifferent for 5 but exactly 1 BonsaiCS

-- No file is both modified and deleted
assert noModDel {
	all b: BonsaiCS | no paths[b.mod] & b.del
}
check noModDel for 5

-- No file is both modified and added
assert noModAdd {
	all b: BonsaiCS| no paths[b.mod] & paths[b.add]
}
check noModAdd for 5

-- No file is both added and deleted
assert noAddDel {
	all b: BonsaiCS | no paths[b.add] & b.del
}
check noAddDel for 5

-- All conflicts are resolved
assert allResolved {
	all b: BonsaiCS | {
		conflict[b.parents] in (b.del + paths[b.mod]) -- conflicts either deleted or modified
		no conflict[b.parents] & paths[b.add] -- adding is not a conflict resolution
	}
}
check allResolved for 3 but exactly 1 BonsaiCS

-- Manifest paths are unique
assert manifestUnique {
	all m: Manifest | all p, p':paths[ m.files] | p = p' => m.files[p] = m.files[p']
}
check manifestUnique for 5

-- We can apply a BonsaiCS to its parent manifests to reconstruct the manifest
assert applyInvert {
	all b: BonsaiCS |
		let m = { m: Manifest | bonsaiApply[m, b, b.parents] } |
			 m = b.manifest
}
check applyInvert for 10 but exactly 1 BonsaiCS
