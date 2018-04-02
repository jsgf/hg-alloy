# Modelling Mercurial with Alloy

## Introduction

This is a chronicle of my voyage to build a model of Mercurial in Alloy. The goal is to build
a fairly rigorous model which we can experiment on, and likely find a few surprising things.
Later, we can use it as the basis for evaluating changes to the model.

[Alloy](http://alloytools.org/) is a declarative language for modeling data structures, using 
relations between sets. Operations and invariants are all expressed via constraints on the 
structure; Alloy allows these constraints to be expressed very concisely.

Alloy encourages a very iterative experimental approach. Here, I'm primarily interested in
constructing a model and looking at its output (ie, things that it generates that meet all the
stated constraints) to see if they meet my expectation. If there's something odd in there, it
either means that there's something missing from the model, or perhaps it means that there's are
implications of the model which I didn't anticipate.

This is not intended to be an Alloy tutorial, but I'm learning it myself. This is my writeup
of my learning process, so it should be fairly easy to follow along. You can download Alloy from
[here](https://github.com/AlloyTools/org.alloytools.alloy/releases) and load up the
[sources](https://github.com/jsgf/hg-alloy) to try them out.

### Sidenote - Understanding the Diagrams

I'm using Alloy's built-in tool for visualizing graphs. It doesn't do a great job of laying things out,
but it isn't too bad at this scale (it also supports exporting to dot for somewhat better layout).

Here's a more complex example which has a couple of everything:

![Example](images/example.png)

We'll get into more detail about what all these mean in detail later on, but broadly:

- `RepoN` is represents an instance of a repository, and is represented by a green parallelogram. Unlike
   everything else, the N is generally meaningful, as Repos have an ordered relationship - increasing N
   represents evolution over time.
- `ChangesetN` represents an instance of a changeset, and is a yellow ellipse
- `ManifestN` is a manifest, represented by a reddish rhombus
- `FileN` is a specific version of a file, in a blue box

(Not shown here are Paths, which every file has. They're omitted here for clarity, but can be shown
with a toggle in the style. Also Repo may not explicitly appear because the display is "projected over Repo" - this
allows diagrams to show progressive change as Repos change.)

Edges between these show how they're related:
- `changesets` shows the relation between a repo and all the changesets it contains. Note that a single changeset
   can be (and often is) part of multiple repos
- `parents` shows an arrow from a child to its parent(s). 
- `manifest` shows the relation between a changeset and its manifest. Every changeset has a manifest, but manifests
  can be shared between changesets
- `files` shows all the files that are part of a manifest

## Getting Started - The simplest thing that can possibly work

My first step is to model something that's extremely simple - so simple that I hope there are no questions or unknowns:
- a single repo
- only changesets which can have up to 2 parents

This model has a single (implicit) repo which contains `Changeset`s, each of which can have up to 2 parents.

Here's our initial model:
```
// comments are either like C++
-- or haskell
module mercurial -- declare the module name

-- Define a Changeset
sig Changeset {
    parents: set Changeset -- changeset can have 0 or more parents
}

-- axioms about Changesets
fact {
    all cs: Changeset | #cs.parents <= 2	    -- mercurial allows up to 2 parents
}

-- A helper predicate. This doesn't constrain anything except to keep things interesting
pred show {
    #Changeset >= 5 -- an interesting number of changesets
}

-- Show a random selection of repo configurations which meet the constraints
run show for 10 -- up to 10
```
Let's see some sample outputs:

This looks OK:

![Seems OK](images/v0-0.png)

Uh, but this isn't what we expect - Mercurial doesn't allow cycles in history, so parents should never point back to themselves:

![Unexpected cycles](images/v0-1.png)

The problem is that Alloy assumes nothing about our model, so any constraint we want we need to specify. Furthermore, this model is very simple, and just defines a single state of the Repo without any way to modify it - so we can't rely on construction to get the properties we want.

To fix this, we need to extend the axioms to say that its acyclic:
```
fact {
    all cs: Changeset | #cs.parents <= 2	    -- mercurial allows up to 2 parents
    all cs: Changeset | cs not in cs.^parents   -- non-cyclic structure
}
```

The `cs.^parents` means the transitive closure over `parents` - ie, everything we can reach via `parents`. If `cs not in ` everything reachable via parents, then the graph has no cycles.

![OK now](images/v0-2.png) ![Still OK](images/v0-3.png)

Note that this model still allows multiple disconnected DAGs of changesets. This is fine - so does Mercurial, though it's a little unusual.

## Multiple Repos

OK, we can make reasonable looking repos appear out of thin air, but how do we change them?

Alloy, being declarative, doesn't allow anything to change. Instead what we need to do is instantiate different Repos which represent change over time.

To start, we'll explicitly define a `Repo` which owns `Changeset`s:

```
module mercurial

-- define a Repo which owns a set of Changesets
sig Repo {
    changesets: set Changeset
}

sig Changeset {
    parents: set Changeset
}
{ #parents <=2 } -- shorthand to attach fact about Changeset

fact {
    all cs: Changeset | cs not in cs.^parents -- acyclic
}
```

This produces immediate problems:

![Missing connections](images/v1-0.png)

We've specified connections between `Repo` and `Changeset`, but we haven't said that *all* `Changeset`s
are connected to some `Repo`.

Let's add another constraint: all Changesets are part of a repo:
```
fact {
    all cs: Changeset | cs in Repo.changesets
}
```
This looks almost OK:

![Almost OK](images/v1-1.png)

Let's add an assertion to check another assertion: every Changeset reachable from a Repo
is part of that Repo.

```
assert allConnected {
    -- for all Repos, the repo's set of changesets should equal the set of reachable
    -- changesets. `*` is like `^` for transitive closure, but it includes the starting points.
    all r: Repo | r.changesets = r.changesets.*parents
}

check allConnected for 5
```
This defines an assertion of an invariant, and checks its true for all constructions up to 5 elements large. This quickly shows the problem:

![problem](images/v1-2.png)

Changesets{0,1} have a parent/child relationship, and Repo0 is connected to Changesets{0,1}, But Repo1 only has Changeset1, not 0.

Let's fix that for now by just making it an axiom:
```
fact {
    -- for every existing Repo, the changesets set must be the same as a all the changesets reachable from that set
    all r: Repo | r.changesets = r.changesets.*parents
}
```

## Making Changes

Now that we have multiple Repos, we can use them to represent changes - ie, before and after states.
We can build up a Repo's state inductively: starting from an initial empty Repo, we can keep
adding new Changesets via commit operations. This implies that Repos have an ordering relationship,
which we can use Alloy's built-in `util/ordering` module to implement.

```
module mercurial

open util/ordering [Repo] -- define an ordering relationship between Repo instances

sig Repo {
    changesets: set Changeset
}

sig Changeset {
    parents: set Changeset
}
{ #parents <= 2 }

-- initial state - an empty Repo
pred init[r: Repo] {
    no r.changesets
}

-- add a commit to repo
pred commit [r, r': Repo, cs: Changeset] {
    r'.changesets = r.changesets + cs -- add cs to next repo
}

-- All sequences of Repos constructable by adding new changesets
fact commits {
    init[first[]] -- initial Repo is empty
    -- for all Repos except for the last one, the difference between it and the next is a commit
    let r: Repo - last [] | let r' = r.next |
        one cs: Changeset | commit[r, r', cs]
}

-- All changesets reachable from a Repo are owned by that Repo
assert csOwned {
    all r: Repo | r.changesets = r.*changesets
}
check csOwned for 5

-- All changesets have an acyclic relationship with their parents
assert csAcyclic {
    all cs: Changeset | cs not in cs.^parents
}
check csAcyclic for 5
```

Now that we're constructing the Repo state incrementally via `commit`, we should be getting
the properties we want by construction rather than making them axioms...

Um, no:

![Loop / not new](images/v2-0.png)

We're still getting loops, and we're not adding new changesets on each `commit`.

We need to add some more preconditions to `commit`.
Firstly, we need to ensure that the `Changeset` we're adding to the Repo isn't already part of the
Repo. And secondly, its parents must be part of the Repo:

```
pred commit [r, r': Repo, cs: Changeset] {
    cs not in r.changesets      -- new cs not part of r
    cs.parents in r.changesets  -- but its parents (if any) must be part of r

    r'.changeset = r.changeset + cs
}
```

(Note that the lines in the predicate are treated as logically-ANDed together. The final line isn't an
assignment or imperative - it's just a constraint on the relationship between `r` and `r'`.)

Unfortunately, these preconditions are not quite enough - we still need to constrain all Changesets to
being part of a repo:

![Floating](images/v2-1.png)

That can be a `fact`.
```
fact {
    all cs: Changeset | cs in Repo.changesets
}
```

## Generalizing History

Mercurial uses a common structure for all parts of a repo with history - ie, things with parents such as
Changesets, Manifests and Files - these are all forms of a Node.

We can model this in Alloy:

```
module mercurial
open util/ordering [Repo]

-- A Node is anything with parents. Mercurial allows up to 2.
-- `abstract` means that `Node` can't exist on its own; all instances of Nodes are things
-- that extend it.
abstract sig Node {
    parents: set Node
}
{ #parents <= 2 }

sig Changeset extends Node {
    manifest: Manifest
}
{
    parents in Changeset        -- Changeset parents can only be other Changeset
    this in Repo.changesets     -- all Changesets part of a Repo
}

sig Manifest extends Node {}
{
    parents in Manifest         -- Manifest parents are only other parents
    this in Changeset.manifest  -- all Manifests are referenced by a Changeset
}
```

So now each Changeset has a Manifest, which is also a versioned object with parents. It's also
completely unconstrained, so let's see how that works out:

![Manifestly messy](images/v3-0.png)

Ew, the Manifests have parents, but they're completely uncoupled from their corresponding Changsets.
(Not to mention Manifest0's self parenthood, and Manifest1 and 2's mutual parenthood.)

Let's add some more preconditions for `commit`:

```
-- Helper function to return the set of ancestors for a particular Node.
fun ancestors [n: Node]: set Node {
    n.^parents
}

pred commit [r, r': Repo, cs: Changeset] {
    // Changeset preconditions
    cs not in r.changesets
    cs.parents in r.changesets

    // Manifest preconditions
    -- Manifest's parents must be changeset's parent's manifests 
    cs.manifest.parents = cs.parents.manifest
    -- Manifest must either be new (ie, not exist in ancestors) except for the parents
    cs.manifest in (Manifest - ancestors[cs].manifest + cs.parents.manifest)

    r'.changesets = r.changesets + cs
}
```

OK, so now we constrain Manifests to either being new, or from the parents. And the Manifest's parents must
be the Changeset's parents' Manifests.

Looks good:

![Looks good](images/v3-1.png)

Interesting Question: This allows no-op Changesets - ie, the metadata can change with no corresponding
file change. This means that the Manifest is unchanged across Changesets. If this is allowed, then it
means that two changesets can share the same parent, and a changeset that merges them would also have the
same Manifest.  OK, I guess?

Now that we're incrementally constructing the Repo state, and each commit has a set of local constraints
for Changesets as they're being added, we can check some assertions for global invariants that we expect
to hold over multiple commits:

```
-- All Nodes are acyclic with respect to their parents (covers Changesets, Manifests, Files)
assert nodeAcyclic {
    all n: Node | n not in n.^parents
}
check nodeAcyclic for 8 -- up to 8 of any top level thing

-- Manifest's parents are their Changeset's parents' Manifests
assert manifestParents {
	all cs: Changeset | cs.manifest.parents = cs.parents.manifest
}
check manifestParents for 8 but 12 Node -- allow more Nodes because each cs uses at least 2

-- Manifests aren't suddenly reused with respect to their history
-- (Disjoint history is allowed to reuse manifests?)
assert noManifestReuse {
	all cs: Changeset | cs.manifest in (Manifest - (cs::ancestors[].manifest) + cs.parents.manifest)
}
check noManifestReuse for 8 but 12 Node
```

Yep, all good.

## Files

TBD