# The Full Cyclic Vacuum State Commutant

## Abstract

The literal norm-four generator annihilator equals the commutant of every actual state in the existing cyclic vacuum span.

Let D be the production finite-rank even integral lattice data, a any charge and s any complex scalar. The ambient space is the full production Carrier(D), with its actual vacuum and actual state-field map Y. Put e=NormFourVirasoroVector.vector(D,a,s) and L_m=Y(e)_(m+1). Use exactly NormFourVacuumIrreducible.vacuumDescendants(D,a,s), denoted W: the complex linear span of all finite words L_(-(k+1)) on the actual vacuum, where each k is a natural number. The empty word is the vacuum; words may vanish or be linearly dependent. A span element is a finite linear combination, while the collection of word lengths and indices is unrestricted.

**Definition 1.1 (Every nonnegative coefficient of every actual cyclic state).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourFullCommutant.fullStateCommutant`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/NormFourFullCommutant.fullStateCommutant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

fullStateCommutant(D,a,s) is the submodule of all v in the full ambient carrier such that, for every u in this exact W and every integer j with j at least zero, Y(u)_j v=0. The coefficient convention is the Laurent exponent -j-1. The definition quantifies over all states of the existing span, all nonnegative integer coefficients and the whole ambient carrier.

**Theorem 1.2 (The literal generator annihilator is exactly the full cyclic state commutant).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourFullCommutant.space_eq_full_state_commutant`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/NormFourFullCommutant.space_eq_full_state_commutant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every production D, every charge a and every complex s, NormFourCommutant.space(D,a,s)=fullStateCommutant(D,a,s). Thus Y(e)_j v=0 for all integers j at least zero holds if and only if Y(u)_j v=0 for every u in the supplied cyclic span and every integer j at least zero. No norm-four equation, sign equation, positivity, inverse Gram matrix or Virasoro relation is needed for this equality.

Fix v and let B_v be the submodule of states u whose nonnegative Y(u) coefficients annihilate v. Linearity of the actual state-field map makes B_v a submodule. The actual vacuum field is the identity field, whose only nonzero coefficient is at -1, so vacuum belongs to B_v. For e,b in B_v, the actual all-state iterate formula, for every integer r and every integer n at least zero, expresses Y(e_r b)_n v as the first finite family minus (-1)^r times the second finite family. For each natural i, the first term is (-1)^i binomial(r,i)e_(r-i)(b_(n+i)v), and the second is (-1)^i binomial(r,i)b_(r+n-i)(e_i v). The first is zero because n+i is nonnegative; the second is zero because i is nonnegative. Every term in both complete families vanishes, including all tails; no finite cutoff is substituted.

The existing recursive word k::w is L_(-(k+1))word(w)=e_(-k)word(w). Induction on that exact word, using the iterate result with r=-k, places every word in B_v whenever v is in the generator annihilator. Its submodule property then places the entire supplied span W in B_v. Conversely, actual creation gives e=Y(e)_(-1)vacuum=L_(-2)vacuum=word([1]), so e belongs to W and the full-state condition includes the original generator condition.

The existing negative-word span and its definition are owned by NormFourVacuumIrreducible; its irreducibility theorem is not reproved or needed for this equality. The two finite iterate families are supplied by LatticeAllStateReconstruction.stateField_iterate in LatticeAllStateLocality, using the actual lattice fields and the StateFieldResidueReconstruction calculus. The lattice realization follows Bakalov-Kac, math/0402315, section 4.1. The norm-four state retains the Shimakura, arXiv:1202.6107, (1.3), and Dong-Mason-Zhu, Theorem 6.3 attribution. Imported residue and normal-product sources retain their Carnahan, Matsuo-Nagatomo and Kytola attribution and license notices. This is a repository derivation for these actual objects, with no novelty claim for the classical generator criterion for commutants. It identifies the commutant of the exact cyclic vacuum state span; it does not identify that carrier with an independently constructed Ising VOA. No simplicity, rationality, fusion, Baby Monster, Monster or full physical programme completion is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourFullCommutant.fullStateCommutant`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourFullCommutant.space_eq_full_state_commutant`
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourCommutant](NormFourCommutant.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourVacuumIrreducible](NormFourVacuumIrreducible.md)
