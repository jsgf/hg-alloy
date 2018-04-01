// Simplest possible model of Mercurial.
// This models a single repo containing changesets, which can have 0,1,2 parents
// This can't represent any kind of operation, because that requires more than one repo instance
// (before and after)
module mercurial

// A Changeset has a set of parents, up to 2
sig Changeset {
	parents: set Changeset,
}
{ #parents <= 2 }

// A Changeset is acyclic WRT its ancestors
fact {
	no cs: Changeset | cs in cs.^parents -- ^parents = ancestors (all cs transitively reachable via parents)
}

pred show[cs: set Changeset] {
	#cs > 5 -- at least 6
}

run show for 10 -- up to 10
