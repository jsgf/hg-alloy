// Mercurial repo model which allows changes
// This extends v0 by adding Repo, which means that more than one can exist.
module mercurial

sig Repo {
	changesets: set Changeset,
}
{ changesets = changesets.*parents }


// A Changeset has a set of parents, up to 2
sig Changeset {
	parents: set Changeset,
}
{ #parents <= 2 }

// Repo <-> Changeset relationship
fact {
	// All changesets are part of a repo
	all c: Changeset | c in Repo.changesets
	// All changesets reachable from a repo are part of that repo
	all r: Repo | r.changesets.*parents in r.changesets
}

// A Changeset is acyclic WRT its ancestors
fact {
	no cs: Changeset | cs in cs.^parents -- ^parents = ancestors (all cs transitively reachable via parents)
}

pred show {
}

run show for exactly 5 Repo, 20 Changeset
