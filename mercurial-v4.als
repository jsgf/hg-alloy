// Mercurial repo model which allows changes
// This extends v3 by adding paths and files
module mercurial

open util/ordering [Repo] -- there's a (time) ordering between Repo instances

sig Repo {
	changesets: set Changeset,
}

-- Mercurial nodes are versioned with an ancestor graph
abstract sig Node {
	parents: set Node,
}
{
	#parents <= 2 -- mercurial bounds parents to 2
	all n: this | n not in n.^@parents -- axiomatically acyclic for now
}
let children = ~parents


fun ancestors [n: Node]: set Node {
	n.^parents
}
fun decendents [n: Node]: set Node {
	n.^children
}

sig Path {}
{ this in Manifest.files.path }

sig Manifest extends Node {
	files: set File,
}
{
	parents in Manifest -- all Manifest parents are Manifest
	this in Changeset.manifest -- All Manifests are referenced by Changesets (may be shared)
	one f: files, p: files.path | f.path = p -- filenames are unique
}

fact UniqueManifest {
	one fs: Manifest.files, ps: Manifest.parents, m: Manifest | m.files = fs and m.parents = ps
}

sig File extends Node {
	path: Path
}
{
	parents in File
	this in Manifest.files
}

sig Changeset extends Node {
	manifest: Manifest -- each cs has a manifest
}
{
	parents in Changeset -- all Changeset parents are Changeset
	this in Repo.changesets -- all Changesets are part ot at least one Repo (may be shared by Repos)
}

// Initial repo is empty
pred init[r: Repo] {
	no r.changesets
}

// commit adds a new changeset to a repo
pred commit [r, r': Repo, cs: Changeset] {
	-- preconditions

	-- changeset
	cs not in r.changesets -- new cs not already in repo
	cs.parents in r.changesets -- cs's parents are in repo

	-- manifest
	cs.manifest in ((Manifest - ancestors[cs].manifest) + cs.parents.manifest) -- manifest can't be reused from ancestors except parents
	cs.manifest.parents = cs.parents.manifest -- manifest has cs's parents manifests
	-- if we have parents, at least one of them has to have a different file set
	some cs.manifest.parents => some mp: cs.manifest.parents | mp.files != cs.manifest.files

	-- files
	-- a file's parents must be: 1. in the parent manifest, 2. have the same path
	all f: cs.manifest.files, fp: File |
		fp in f.parents iff (fp in cs.manifest.parents.files and fp.path = f.path)
	-- At least one of the parents has to be different from f
	all f: cs.manifest.files |
		some f.parents => some fp: f.parents | fp != f
	-- Can't resurrect a deleted file - so file must be either new (WRT ancestors) or in a parent
	all f: cs.manifest.files | f in ((File - ancestors[cs.manifest].files) + cs.manifest.parents.files)

	r'.changesets = r.changesets + cs -- add cs to r'
}

// All sequences of repos constructable by committing new changesets
fact Commits {
	init[first[]] -- start empty
	-- for all repos except the last one, the difference between it and the next is the commit of a Changeset
	all r: Repo - last[] | let r' = r.next |
		one cs: Changeset | commit[r, r', cs]
}

pred show {
	-- make things a bit interesting
	some f: File | #f.parents > 1 -- at least one file has a merge (implies manifest, changeset merge)
	-- some m: Manifest | #m.files > 1 -- at least one manifest has more than one file XXX FIXME not consistent
}
run show  for 8 but 24 Node

assert nodeAcyclic {
	all n: Node | n not in n.^parents -- check nodes are acyclic
}
check nodeAcyclic for 8

assert csConnected {
	all r: Repo | r.changesets = r.changesets.*parents
}
check csConnected for 7

assert manifestParents {
	all cs: Changeset | cs.manifest.parents = cs.parents.manifest
}
check manifestParents for 6 but 10 Node

assert noManifestReuse {
	all cs: Changeset | cs.manifest in (Manifest - (cs::ancestors[].manifest) + cs.parents.manifest)
}
check noManifestReuse for 8 but 14 Node
