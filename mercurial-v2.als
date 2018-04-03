// Mercurial repo model which allows changes
// This extends v1 by adding an initial state (empty repo) and a commit operation. What were previously
// facts about the structure become invariants which should be maintained by commit.
module mercurial

open util/ordering [Repo] -- there's a (time) ordering between Repo instances

sig Repo {
	changesets: set Changeset,
}

// A Changeset has a set of parents, up to 2
sig Changeset {
	parents: set Changeset,
}
{
	#parents <= 2 -- hg bounds parents to max 2
	all cs: this | cs in Repo.changesets -- all cs must be part of some repo
}

// Initial repo is empty
pred init[r: Repo] {
	no r.changesets
}

pred changesetPrecond[r: Repo, cs: Changeset] {
	cs not in r.changesets -- new cs not already in repo
	cs.parents in r.changesets -- cs's parents are in repo
}

// commit adds a new changeset to a repo
pred commit [r, r': Repo, cs: Changeset] {
	-- preconditions
	changesetPrecond[r, cs]

	r'.changesets = r.changesets + cs -- add cs to r'
}

// All sequences of repos constructable by committing new changesets
fact commits {
	init[first[]] -- start empty
	-- for all repos except the last one, the difference between it and the next is the commit of a Changeset
	all r: Repo - last[] | let r' = r.next |
		one cs: Changeset | commit[r, r', cs]
}

pred show {}
run show  for 4

assert csAcyclic {
	all cs: Changeset | cs not in cs.^parents -- check cs are acyclic
}
check csAcyclic for 5

assert csConnected {
	all r: Repo | r.changesets = r.changesets.*parents
}
check csConnected for 5
