// Mercurial repo model which allows changes
// This extends v2 by adding generic versioned nodes, and constructing changesets as part of them. Adds manifests.
//
// Manifests are complicated because:
// - not every changeset necessarily introduces a new manifest
// - manifest ancestor graph follows the changeset graph
//   - manifest parent set is the same as cs parent's manifests
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
}

fun ancestors [n: Node]: set Node {
	n.^parents
}

sig Manifest extends Node {}
{
	parents in Manifest -- all Manifest parents are Manifest
	this in Changeset.manifest -- All Manifests are referenced by Changesets (may be shared)
}

sig Changeset extends Node {
	manifest: Manifest -- each cs has a manifest
}
{
	parents in Changeset -- all Changeset parents are Changeset
	this in Repo.changesets -- all Changesets are part ot at least one Repo (may be shared by Repos)
}

fact identities {
	-- If two changesets have the same parents and the same manifest, they're the same changeset
	all cs, cs': Changeset | cs.parents = cs'.parents and cs.manifest = cs'.manifest => cs = cs'
}

// Initial repo is empty
pred init[r: Repo] {
	no r.changesets
}

pred changesetPrecond[r: Repo, cs: Changeset] {
    -- (we don't need to assert that cs isn't in the repo - committing a cs that already
	-- exists isn't a problem, and we've got an identity for changesets to make sure that
	-- we're de-duping identical changesets)
	cs.parents in r.changesets -- cs's parents are in repo
}

pred manifestPrecond[cs: Changeset] {
	cs.manifest in ((Manifest - ancestors[cs].manifest) + cs.parents.manifest) -- manifest can't be reused from ancestors except parents
	cs.manifest.parents = cs.parents.manifest -- manifest has cs's parents manifests
}

// commit adds a new changeset to a repo
pred commit [r, r': Repo, cs: Changeset] {
	-- preconditions
	changesetPrecond[r, cs]
	manifestPrecond[cs]

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
	some m: Manifest | #m.parents > 1 -- at least one manifest has more than one parent
}
run show  for 4 but 8 Node

assert nodeAcyclic {
	all n: Node | n not in n.^parents -- check nodes are acyclic
}
check nodeAcyclic for 8

assert csConnected {
	all r: Repo | r.changesets = r.changesets.*parents
}
check csConnected for 8 but 12 Node

assert manifestParents {
	all cs: Changeset | cs.manifest.parents = cs.parents.manifest
}
check manifestParents for 8 but 12 Node

assert noManifestReuse {
	all cs: Changeset | cs.manifest in (Manifest - (cs::ancestors[].manifest) + cs.parents.manifest)
}
check noManifestReuse for 8 but 12 Node
