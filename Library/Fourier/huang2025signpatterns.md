---
bibkey: huang2025signpatterns
authors: "Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye"
year: 2025
title: "Sign-patterns of Certain Infinite Products"
doi: 10.48550/arXiv.2507.16644
url: https://arxiv.org/abs/2507.16644v1
claim: "Classical cubic theta definitions, Euler product identities, and the three-core lattice exponent used in the study of infinite-product signs."
strata_touched:
  - D5/S3/Arith/ModularForms/CubicThetaLattice
  - D5/S3/Arith/ModularForms/CubicThetaShifted
  - D5/S3/Arith/ModularForms/CubicThetaJacobi
  - D5/S3/Arith/ModularForms/CubicThetaRootProduct
  - D5/S3/Arith/ModularForms/CubicThetaJacobiCube
  - D5/S3/Arith/ModularForms/CubicThetaJacobiColumns
  - D5/S3/Arith/ModularForms/CubicThetaCubeDissection
  - D5/S3/Arith/ModularForms/CubicThetaResidueSums
  - D5/S3/Arith/ModularForms/CubicThetaRootEvaluation
  - D5/S3/Arith/ModularForms/CubicThetaCoreProduct
  - D5/S3/Arith/ModularForms/CubicThetaProductTwist
  - D5/S3/Arith/ModularForms/CubicThetaWeightedNorm
  - D5/S3/Arith/ModularForms/CubicThetaTwistedColumns
  - D5/S3/Arith/ModularForms/CubicThetaWeightedProduct
  - D5/S3/Arith/ModularForms/CubicThetaIdentities
  - D5/S3/Arith/ModularForms/EtaSignK6
license: citation-only
triage: anchor
---

# Cubic theta lattices and their product interpretation

## Verified locator

DOI: 10.48550/arXiv.2507.16644

URL: https://arxiv.org/abs/2507.16644v1

The inspected v1 source is `signpatternsaoc.tex`, extracted text SHA256
`e870441977cf9615a6e7a32daba63a7843bf668e7196c42087e4355a4cd780b6`.
The subsection titled “The Borwein cubic theta functions” defines the
norm theta series with exponent `x^2+x*y+y^2` and records the classical
identities in the display labelled `abc1`. The proof of the lemma labelled
`lem9` quotes Cooper, *Ramanujan's Theta Functions* (2017), Theorem 3.15,
for the three-core product and the sum over integer triples of sum zero.
The substitution `(m1,m2,m3)=(x,y,-x-y)` gives the exponent
`3*(x^2+x*y+y^2)-2*x-y`. Cooper's book was not independently inspected
for this note; its theorem is attributed as quoted by the inspected source.

## Formal anchors and scope

`D5/S3/Arith/ModularForms/CubicThetaLattice.norm_theta_dissection` proves
the all-index lattice identity `A(X)=A(X^3)+6*X*T_lattice(X^3)`.
The proof constructs a norm-tripling equivalence on the residue-zero
fibres and six disjoint rotated copies of the shifted lattice on the
residue-one fibres. Residue-two fibres are empty. The construction and
the finite-fibre bounds are repository proofs of classical lattice
mathematics, with no mathematical novelty claim.

`D5/S3/Arith/ModularForms/CubicThetaLattice.hasSum_lattice_theta` identifies
the coefficient-cardinality series with the full integer lattice sums.
The positivity and constant terms refer to these lattice series.

`D5/S3/Arith/ModularForms/CubicThetaShifted.shiftedCoreEquiv` gives three
disjoint exhaustive affine copies of each core fibre in the shifted
norm fibre `Q(x,y)-x-y=n`. Its series identity is
`shifted_theta_eq_three_core`.

`D5/S3/Arith/ModularForms/CubicThetaJacobi` reuses the repository's
`InversionSeq207TripleProduct.formal_triple_product` and
`InversionSeq207Euler.euler_coefficient_construction`. Its
`tendsto_finite_jacobi` proves that the actual finite Jacobi products
converge coefficientwise to the normalized supplier, while
`jacobiSeries_column` identifies every integer Laurent column. The
supplier, including its Durfee normalization, is attributed repository
mathematics, not a new cubic identity.

`D5/S3/Arith/ModularForms/CubicThetaRootProduct.jacobi_cubic_root_product`
proves the specialization `J(w;X)=(1-w)E(X^3)` under `w^2+w+1=0`, by
exact finite factorization followed by a coefficientwise limit. It does
not by itself identify the Euler quotient with the core lattice.

`D5/S3/Arith/ModularForms/CubicThetaJacobiCube.hasSum_jacobi_cube` proves
local finiteness and the full integer-triple sum for the cube of the
actual Jacobi product. The complete pair sums for each fixed Laurent
index are recorded by
`D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.hasSum_cube_column`.
The anchors `cube_column_zero` and `cube_column_one` identify its first
two columns with `A` and `-3*T_lattice`, respectively. The three anchors in
`D5/S3/Arith/ModularForms/CubicThetaCubeDissection`,
`cube_column_three_mul`, `cube_column_three_mul_add_one`, and
`cube_column_three_mul_add_two`, evaluate every integer Laurent column,
including all negative indices, by full affine lattice reindexing.

`D5/S3/Arith/ModularForms/CubicThetaResidueSums.hasSum_residue_zero`
uses a complete sign-reversing involution. Its `hasSum_residue_one` and
`hasSum_residue_two` are the two forms of Euler's pentagonal series.
`D5/S3/Arith/ModularForms/CubicThetaRootEvaluation.evaluated_jacobi_cube`
combines all columns, with finite Laurent support justifying evaluation.

`D5/S3/Arith/ModularForms/CubicThetaCoreProduct.core_product_eq_theta`
proves the actual identity `E(X^3)^3/E(X)=T_lattice` using unit inverses.
Its `coeff_core_product` counts the full finite fibre
`3*(x^2+x*y+y^2)-2*x-y=n` for every natural index, including zero.
The proof compares the complete cube evaluation with the actual Jacobi
finite-product limit in the rational quadratic algebra `w^2+w+1=0`,
then cancels a proven unit. This is a formal proof of the attributed
classical three-core identity, not an assumed theta identity or a
finite coefficient test.

`D5/S3/Arith/ModularForms/CubicThetaProductTwist.three_jacobi_product`
proves the product of three root-twisted Jacobi factors by finite
factorization and coefficientwise limits, without division.
`D5/S3/Arith/ModularForms/CubicThetaWeightedNorm.weighted_norm_dissection`
counts the full phase-weighted norm fibres using the same six core
cosets. The complete Laurent constant column is identified by
`D5/S3/Arith/ModularForms/CubicThetaTwistedColumns.twisted_column_zero`.
Together these prove
`D5/S3/Arith/ModularForms/CubicThetaWeightedProduct.norm_dissection_mul_euler`.

`D5/S3/Arith/ModularForms/CubicThetaIdentities.B_dissection` proves
`B=A(X^3)-3*X*T(X^3)` for the actual quotient `B=E(X)^3/E(X^3)`.
Its `cubic_identity` proves `A^3=B^3+27*X*T^3`. The cubic defect satisfies
a homogeneous recurrence; the generic coefficient-induction theorem
`D5/S3/Combinatorics/PowerSeries/ExpandingRecurrence.eq_zero_of_mul_eq_X_expand`
closes every degree. Thus all three classical identities are derived
from product and lattice mathematics, with no theta identity assumed.

`D5/S3/Arith/ModularForms/EtaSignK6.first_dissection` and
`D5/S3/Arith/ModularForms/EtaSignK6.second_dissection` prove the two
finite polynomial expansions for the actual normalized k6 quotient.
The all-index strict signs are in
`D5/S3/Arith/ModularForms/EtaSignK6.all_index_signs`. The nonzero-modulo-three
argument and general reduction are reused mathematics from `lem9`;
the second dissection completes the selected k6 table entry. No claim
of literature priority, worldwide absence, unique status, independent
formal acceptance, CI or publication follows from these formal anchors.

The printed progressions in the proof of `lem9` omit a factor `-9` in
residue one and retain an undilated denominator after extraction. They
are not used as stated. The formal first dissection retains the correct
factors `-9` and `27` and uses the rescaled reciprocal `1/E(X)^3`.

Citation and implementation scope only; no source text or PDF is vendored.
