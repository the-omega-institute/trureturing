# Four-dimensional spinor helicity and the tree double copy

## Abstract

Complex spinor factorizations and momentum conservation give the four-particle consistency laws and the four-point tree double copy.

Write the null momentum as the outer product of two independent complex spinors, and use the negative two-by-two determinant for the Mandelstam invariant. Real null rays use conjugate spinors in the stereographic chart.

**Theorem 1.1 (Antisymmetry of the spinor bracket).**

Lean statement: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.bracket_antisymm`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.bracket_antisymm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Swapping the two spinors exchanges the two terms of their determinant.

**Theorem 1.2 (A spinor brackets to zero with itself).**

Lean statement: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.bracket_self`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.bracket_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two scalar products in the bracket coincide by commutativity.

**Theorem 1.3 (Vanishing bracket and dependence).**

Lean statement: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.bracket_zero_iff_dependent`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.bracket_zero_iff_dependent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bracket of u and v vanishes exactly when u is zero or v is a scalar multiple of u. A nonzero coordinate of u determines that scalar, and the determinant equation gives the remaining coordinate.

**Theorem 1.4 (A spinor outer product is null).**

Lean statement: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.spinor_det_null`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.spinor_det_null` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant of the two-by-two outer product vanishes by direct expansion.

**Theorem 1.5 (Null momenta admit spinor factors).**

Lean statement: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.null_iff_rankOne`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.null_iff_rankOne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A matrix has zero determinant exactly when it is an outer product. A nonzero first column determines one factor and a nonzero entry of that column normalizes the other. If the first column vanishes, the second column alone gives the factorization.

**Theorem 1.6 (Schouten identity).**

Lean statement: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.schouten`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.schouten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For spinors a, b, c and d, the sum of the products of brackets in pairings (ab)(cd), (ac)(db) and (ad)(bc) vanishes by expansion.

**Theorem 1.7 (Mandelstam invariants from brackets).**

Lean statement: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.mandelstam_brackets`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.mandelstam_brackets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The negative determinant of two summed null momenta equals their left bracket times their reversed right bracket.

**Theorem 1.8 (Minkowski norm from the spinor matrix).**

Lean statement: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.det_sigma`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.det_sigma` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The negative determinant of the Hermitian matrix with diagonal entries x₀ ± x₃ and off-diagonal entries x₁ ∓ ix₂ is the Minkowski square in signature (−+++).

**Theorem 1.9 (Spinor factors of the finite-chart generator).**

Lean statement: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.nullGenerator_spinor_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.nullGenerator_spinor_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At z the Hermitian momentum matrix is twice the outer product of (1,z) with (1,conjugate z).

**Theorem 1.10 (Spinor factors at the south pole).**

Lean statement: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.nullGenerator_south_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.nullGenerator_south_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At infinity the Hermitian momentum matrix is twice the outer product of (0,1) with itself.

**Theorem 1.11 (Three-point momentum conservation has two branches).**

Lean statement: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.three_point_branches`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.three_point_branches` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If all left brackets vanish there is a left branch. If some left pair is independent, its two contractions with conservation express both corresponding right spinors as multiples of the remaining right spinor. All right brackets then vanish, including in degenerate configurations.

**Theorem 1.12 (Clearing the two shifted amplitudes).**

Lean statement: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.bcfw_iff_cleared`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.bcfw_iff_cleared` (`✓ std3`). ∎

*Citation.* Paolo Benincasa and Freddy Cachazo (2007). *Consistency Conditions on the S-Matrix of Massless Particles*. DOI: [10.48550/arXiv.0705.4305](https://doi.org/10.48550/arXiv.0705.4305). URL: <https://arxiv.org/abs/0705.4305>.

*Commentary.*

For nonzero x, y, x+y and nonzero prefactors P and K, equality of the two rational shifts is equivalent to zero of the channel polynomial. Their difference is that polynomial times P K^(s−1) divided by x^(s−1) y^(s−1) (x+y).

**Theorem 1.13 (Conserved channel coordinates).**

Lean statement: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.generic_channel_chart`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.generic_channel_chart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An explicit four-spinor chart realizes x, y and x+y as the three bracket products. Whenever x+y is nonzero, the spinor prefactor K is nonzero.

**Theorem 1.14 (Spin-one shift consistency is Jacobi).**

Lean statement: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.spin_one_consistency_iff_jacobi`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.spin_one_consistency_iff_jacobi` (`✓ std3`). ∎

*Citation.* Paolo Benincasa and Freddy Cachazo (2007). *Consistency Conditions on the S-Matrix of Massless Particles*. DOI: [10.48550/arXiv.0705.4305](https://doi.org/10.48550/arXiv.0705.4305). URL: <https://arxiv.org/abs/0705.4305>.

*Commentary.*

For alternating couplings the channel polynomial factors as −(x+y) times the component Jacobi sum. Evaluating at x=y=1 recovers Jacobi, and the factorization gives the converse at each generic pair.

**Theorem 1.15 (Spin-two shift consistency is associativity).**

Lean statement: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.spin_two_consistency_iff_associative`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.spin_two_consistency_iff_associative` (`✓ std3`). ∎

*Citation.* Paolo Benincasa and Freddy Cachazo (2007). *Consistency Conditions on the S-Matrix of Massless Particles*. DOI: [10.48550/arXiv.0705.4305](https://doi.org/10.48550/arXiv.0705.4305). URL: <https://arxiv.org/abs/0705.4305>.

*Commentary.*

For symmetric couplings the channel polynomial factors as (x+y)(y(U−V)−x(W−V)). The equation at x=y=1 gives W=U, the associativity equation on basis components. Permuting the species gives V=U, which makes both terms vanish throughout the chart.

**Theorem 1.16 (A single species of spin at least three has zero coupling).**

Lean statement: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.higher_spin_single_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.higher_spin_single_zero` (`✓ std3`). ∎

*Citation.* Paolo Benincasa and Freddy Cachazo (2007). *Consistency Conditions on the S-Matrix of Massless Particles*. DOI: [10.48550/arXiv.0705.4305](https://doi.org/10.48550/arXiv.0705.4305). URL: <https://arxiv.org/abs/0705.4305>.

*Commentary.*

At x=y=1 the shift equation identifies the crossed and uncrossed contractions. At x=1 and y=2 the equation becomes (2^(s−1)−2)g²=0. The coefficient is strictly positive for every integer s at least three.

**Theorem 1.17 (Orthogonal one-dimensional spin-two sectors).**

Lean statement: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.spin_two_orthogonal_split`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.spin_two_orthogonal_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a finite-dimensional real inner-product space, associative and commutative multiplication gives commuting multiplication maps. Symmetry makes them jointly orthogonally diagonalizable. In a common orthonormal basis, a product of distinct vectors lies in both corresponding lines, hence vanishes. Every basis vector's square lies in its own line.

**Theorem 1.18 (Complementary momentum channels agree).**

Lean statement: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.mandelstam_complement`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.mandelstam_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conservation identifies each pair sum with minus its complement. Their two-by-two determinants agree.

**Theorem 1.19 (Mixed four-point consistency forces equal couplings).**

Lean statement: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.nonzero_graviton_matter_universal`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.nonzero_graviton_matter_universal` (`✓ std3`). ∎

*Citation.* Paolo Benincasa and Freddy Cachazo (2007). *Consistency Conditions on the S-Matrix of Massless Particles*. DOI: [10.48550/arXiv.0705.4305](https://doi.org/10.48550/arXiv.0705.4305). URL: <https://arxiv.org/abs/0705.4305>.

*Commentary.*

Conservation gives s+t+u=0 and turns the ratio of the two dotted bracket products into t/s. This reduces the two shifts to expressions differing by the common nonzero spinor factor times κa(κ−κa)/s. A nonzero matter coupling therefore equals the graviton coupling. The Laurent exponents are algebraic. The scattering interpretation requires constructibility and the stated mixed vertices.

**Theorem 1.20 (Soft gauge invariance forces equal couplings).**

Lean statement: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.soft_ward_universal`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.soft_ward_universal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The leading soft polarization variation cancels each nonzero soft denominator. Conservation reduces the resulting equation to the coupling difference times the total matter momentum tested by any covector. The dual separates points, so nonzero total matter momentum forces equality.

**Theorem 1.21 (The gravity amplitude from the spin-two shift).**

Lean statement: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.gravityMHV4_bcfw`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.gravityMHV4_bcfw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Schouten gives z=x+y for the permuted helicity labels, so the shift factor 1−y/z is x/z. Substitution into the independent spin-two shift value gives the rational gravity amplitude.

**Theorem 1.22 (Exact four-point KLT relation).**

Lean statement: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.klt_four_point`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.klt_four_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For conserved four-spinor momenta with nonzero angle brackets, minus the Mandelstam invariant of the first pair times the two Parke–Taylor amplitudes in orders 1234 and 1243 equals the stripped MHV graviton amplitude. Antisymmetry and the complementary-channel identity align the numerators after clearing denominators.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.bcfw_iff_cleared`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.bracket_antisymm`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.bracket_self`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.bracket_zero_iff_dependent`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.det_sigma`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.generic_channel_chart`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.gravityMHV4_bcfw`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.higher_spin_single_zero`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.klt_four_point`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.mandelstam_brackets`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.mandelstam_complement`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.nonzero_graviton_matter_universal`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.nullGenerator_south_factor`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.nullGenerator_spinor_factor`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.null_iff_rankOne`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.schouten`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.soft_ward_universal`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.spin_one_consistency_iff_jacobi`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.spin_two_consistency_iff_associative`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.spin_two_orthogonal_split`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.spinor_det_null`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.three_point_branches`
- Dependency: [D5/S3/Geometry/Lorentz/WeylNullScreen](WeylNullScreen.md)
