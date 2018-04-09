module prefixpath

sig Name {}
{ this in Path.elems }

sig Path {
	elems: set Name,
	prefixes: set Path,
}
{ prefixes = { p: Path | p != this and p.@elems in elems } }

fact identity {
	all p1, p2: Path | p1.elems = p2.elems => p1 = p2
}

pred prefix[p1, p2: Path] {
	p1 in p2.prefixes
}

-- Paths have an ordering relationship if one is a prefix of the other
pred ordered[p1, p2: Path] {
	prefix[p1, p2] or prefix[p2, p1]
}

pred show {
	-- some p1, p2: Path | ordered[p1, p2]
}
run show for 5
