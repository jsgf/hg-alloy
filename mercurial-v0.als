// Simplest possible model of Mercurial.
// This models a single repo containing changesets, which can have 0,1,2 parents
// This can't represent any kind of operation, because that requires more than one repo instance
// (before and after)
module mercurial

// A Changeset has a set of parents, up to 2
sig Changeset {
	parents: set Changeset,
}
fact { -- axioms about Changeset
	all cs: Changeset | #cs.parents <= 2	-- mercurial allows up to 2 parents
	all cs: Changeset | cs not in cs.^parents	-- can't have cyclic history
}

pred show {
	#Changeset > 5 -- at least 6
}

run show for 10 -- up to 10
