# Singular homology

Singular homology and its properties (towards the Brouwer fixed point
theorem) was first formalized in Lean 3 by Brendan Seamas Murphy in 2022
https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Completed.20proof.20of.20the.20Brouwer.20Fixed.20Point.20Theorem/near/297494528

This roadmap describes an ongoing effort towards the addition in mathlib of
proofs of essential properties of singular homology. For the application
to the Brouwer fixed point theorem, the main is the computation of the
homology of spheres.

## Degree of generality

The definition of singular homology was added by Andrew Yang #21559
following a suggestion of definition by Adam Topaz. When reviewing this,
it appeared to Joël Riou that the right generality for the definition
of singular homology was the following.

Let `C` be a preadditive category with coproducts (e.g. the category of
abelian groups, or the category of modules over a ring `A`).
Let `R` be an object of `C` (e.g. an abelian group, or an `A`-module),
the singular chain complex of a topological space `X` with coefficients in `R`
is `((singularChainComplexFunctor C).obj R).obj X : ChainComplex C ℕ` (a more
convenient abbreviation `TopCat.singularChainComplex` shall be added soon),
and in degree `n : ℕ` (i.e. the `n`-chains), it is given by the categorical
coproduct of copies of `R` indexed by the singular `n`-simplices of `X`,
i.e. the continuous maps from the topological standard `n`-simplex to `X`.
(For example, when `R` is the abelian group `ℤ`, this identifies to a
finsupp `"n-simplices to X" →₀ ℤ`.)
(The definition of the singular chain
complex is actually a particular case of the chain complex of a
simplicial set. When it is applicable (e.g. relative homology #41285),
general definitions should be made first for simplicial sets.)

Note: when `C` has products, we may apply this construction to an object
in the opposite category `Cᵒᵖ`, and this would give a candidate definition
of the complex which computes singular **co**homology.

Most of the definitions or proofs involving singular homology should be
stated first in terms of these singular chain complexes (morphisms,
homotopies, homotopy equivalences), and only at the very end,
consequences in terms of the actual homology of these complexes
should be derived (this is the only place where we actually need that
`C` is an abelian category).

## Tasks

### Definition of singular homology (completed by Andrew Yang, #21559)

### Homotopy invariance (completed by Fabian Odermatt and Joël Riou, #37091, #32881, #33683)

If `f` and `g` are homotopic maps `X → Y`, they induce homotopic morphisms
between singular chain complexes. This was obtained by obtaining a similar
result for homotopic morphisms of simplicial sets. It follows that an homotopy equivalence
of topological spaces induces an homotopy equivalence on the singular chain complexes
(and thus isomorphisms in singular homology). (A long term goal will be to show
that this also hold for weak homotopy equivalences (maps which induces bijections on
homotopy groups). Joël's plan will be to show the similar result for simplicial sets
and to use Quillen's model category structure that he was formalized.)

### Small simplices lemma, excision's theorem (in the process of being upstreamed
from https://github.com/joelriou/excision by Joël Riou, #43524, #43528, ...)

If `X` is a topological space, and `U i` is a family of subsets of `X` such that
the interiors of the `U i` cover `X`, then we introduce a subcomplex of
the singular chain complex of `X` which consists of simplices that are contained
in some of the `U i`, and we show that the inclusion in the singular chain complex
of `X` is a homotopy equivalence. The standard phrasing of the excision theorem
follows (and it is also stated a a homotopy equivalence). The Mayer-Vietoris exact
sequence should also follow very easily: the best phrasing before passing to homology
could be using a distinguished triangle in the homotopy category of complexes.

### Reduced singular chain complex

If `X` is a (nonempty) topological space (or an augmented simplicial set),
one may consider the chain complex `C_*(X)` of `X`, and introduce the reduced
complex $\tilde C_*(X)$ obtained by replacing `C_0(X)` by the kernel of
the augmentation map `C_0(X) → C_0(PUnit)`. This chain complex is homotopically
equivalent to the relative singular chain complex of the pointed space `(X, x)`
for any `x : X`, but in order to handle the homology of spheres cleanly,
it may be easier to work with a definition that is independent of the base-point.

### Homology of spheres

The best phrasing is probably to define an homotopy equivalence between the
reduced chain complex $\tilde C_*(S^n)$ with the single chain complex
where `R` lies in degree `n`.
If `U` is the complement of the north pole in `S^{n+1}` and `V` the complement
of the south pole, the intersection `U ∩ V` is homotopy equivalent to `S^n`,
and the reduced version of the Mayer-Vietoris sequence (as a distinguished
triangle) gives an homotopy equivalence between $\tilde C_*(S^{n+1})$ and
the shift of $\tilde C_*(S^n)$. The "symmetry" properties of the Mayer-Vietoris
sequence/triangle should allow to show that the reflection which swaps the poles 
acts as `(-1) • ·`, which should be the key in understanding the action
of the orthogonal group on the chain complex (up to homotopy, or in homology).
[Sign shenanigans are certainly involved in the definition of the generator
of homology of `S^n` in degree `n`. It is probably ok, as a first implementation,
not to care to much about the precise convention we want to set, but in the
future, it would be great to check at least that for `n = 1`, the generator
we get is homologous to the obvious path with winding number `1`.]

### Brouwer fixed point theorem

If a continuous map from the ball to itself has no fixed point, one constructs a
continuous retraction from the ball to the sphere, which is not possible because
the homology of the sphere is nonzero.

## References
* [Allen Hatcher, *Algebraic topology*][hatcher02]


