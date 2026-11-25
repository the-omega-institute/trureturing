# A cubic criterion for three distinguishable pure states on four coordinates

## Abstract

A guarded cubic decides whether a nonnegative four-point law occurs as the common squared moduli of three orthonormal columns.

**Theorem 1.1 (The guarded cubic criterion).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.weighted_phase_columns_iff_cubic_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.weighted_phase_columns_iff_cubic_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Korzekwa, Kamil; Czachórski, Stanisław; Puchała, Zbigniew; Życzkowski, Karol (2019). *Distinguishing classically indistinguishable states and channels*. DOI: [10.1088/1751-8121/ab30f7](https://doi.org/10.1088/1751-8121/ab30f7). URL: <https://arxiv.org/abs/1812.09083v3>.

*Acknowledgement.* Grzegorz Rajchel; Adam Gąsiorowski; Karol Życzkowski (2018). *Robust Hadamard Matrices, Unistochastic Rays in Birkhoff Polytope and Equi-Entangled Bases in Composite Spaces*. DOI: [10.1007/s11786-018-0384-y](https://doi.org/10.1007/s11786-018-0384-y). URL: <https://arxiv.org/abs/1804.10715v2>.

*Commentary.*

Let p be a nonnegative law on four coordinates with sum one. A complex 4 × 3 matrix W with WᴴW = I and |Wᵢⱼ|² = pᵢ exists exactly when each pᵢ ≤ 1/3 and some 0 < t ≤ 1 satisfies qᵢ²t − dᵢ² ≥ 0 for every i and phaseCubic(p,t) = 0, where qᵢ = 1 − 2pᵢ and dᵢ = 4pᵢ − 1. The statement includes repeated weights, the uniform law, zero weights and admissible zero radicands.

Korzekwa, Czachórski, Puchała and Życzkowski give the pure-state column formulation in arXiv:1812.09083v3, PDF p. 5, Lemma 5 and Eq. (19). Completing W gives a unitary whose squared-modulus matrix is B = [p,p,p,1−3p]. Section III.B and Appendix C study the dimension-four region. Appendix C.3 already applies Haagerup’s order-four procedure to the repeated-column slice. Rajchel, Gąsiorowski and Życzkowski describe that procedure in arXiv:1804.10715v2, Appendix A. It completes two quadrilaterals at a common phase and tests a remaining block-entry modulus.

From W, the diagonal of the projection WWᴴ gives 3pᵢ ≤ 1. Unit row phases make the first two columns conjugates, using the identity phase where both entries vanish. Their scaled real and imaginary parts form a real orthonormal pair. The third column lies in the complexification of its real two-dimensional orthogonal complement. Its real and imaginary parts give a real positive semidefinite Gram operator on that plane with trace one and diagonal p. In an orthonormal eigenbasis c,e with eigenvalues (1+s)/2 and (1−s)/2, one has cᵢ²+eᵢ² = qᵢ and s(cᵢ²−eᵢ²) = dᵢ. For s ≠ 0, take t = s². The terms yᵢ = 2s cᵢeᵢ satisfy yᵢ² = qᵢ²t−dᵢ² and sum to zero. For s = 0, p is uniform and t = 1 works with alternating signed half-units.

For xᵢ = qᵢ²t−dᵢ², put A = x₀+x₁−x₂−x₃. The quartic is (A²−4x₀x₁−4x₂x₃)²−64x₀x₁x₂x₃. On nonnegative x it factors into eight linear forms in the square roots, with the first sign fixed. Thus a quartic zero is equivalent to a signed sum of the roots vanishing, including when one or more roots are zero. On substitution, the constant is the same quartic evaluated at (dᵢ²) and vanishes because Σᵢ dᵢ = 0. For the coefficient calculation, write x₀x₁ = f−gt+ht², x₂x₃ = j−kt+rt² and A²−4x₀x₁−4x₂x₃ = l+mt+nt². Expand (l+mt+nt²)²−64(f−gt+ht²)(j−kt+rt²) and shift the coefficients of t⁴,t³,t²,t down one degree. This gives the explicit polynomial of degree at most three. Its root test uses t > 0.

Conversely an admissible cubic root gives signed roots yᵢ with zero sum. Set s = √t, cᵢ = √((qᵢ+dᵢ/s)/2), and choose eᵢ with magnitude √((qᵢ−dᵢ/s)/2) and the sign of yᵢ, taking the positive sign at zero. The identities Σᵢ qᵢ = 2 and Σᵢ dᵢ = 0 give unit norms. The signed sum gives c·e = 0. Complete c,e by a real orthonormal pair a,b. Use the columns (a−ib)/√2, (a+ib)/√2 and √((1+s)/2)c + i√((1−s)/2)e. Their Gram matrix is the identity and their squared moduli are p.

**Theorem 1.2 (A strictly sub-cap law with no three columns).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.infeasible_weighted_phase_columns`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.infeasible_weighted_phase_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized law (19999, 15001, 12000, 13000)/60000 has four distinct positive weights, all strictly below 1/3. The cubic is (187047147977039896t³ + 345304640904270873t² + 158219836231921608t + 14368342729440656)/11390625000000000000. Every numerator coefficient is positive, so it has no positive root. The forward implication excludes an isometry for this law and shows that the row cap alone is insufficient for the three-column pure-state condition.

**Theorem 1.3 (A strictly sub-cap law with three columns).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.feasible_weighted_phase_columns`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.feasible_weighted_phase_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the normalized law (29, 27, 25, 19)/100, whose four positive weights are distinct and below 1/3. Its cubic is −32(44631t³−55970t²+15072t−1152)/244140625. It is positive at t = 1/2 and negative at t = 1. The intermediate value theorem gives a root strictly between these endpoints. Each radicand is already nonnegative at 1/2, and it increases weakly with t. The reverse implication supplies the prescribed three orthonormal columns.

**Theorem 1.4 (Strictly positive weights).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.weighted_phase_columns_iff_cubic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.weighted_phase_columns_iff_cubic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A strictly positive normalized law satisfies the same criterion. The positive entry supplies the fixed-bath specialization at positive Gibbs weights.

**Theorem 1.5 (Gauging two equal-modulus entries).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.conjugate_pair_gauge_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.conjugate_pair_gauge_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For equal positive squared moduli a unit phase makes the two entries conjugate. At squared modulus zero both entries vanish and the unit phase can be one.

**Theorem 1.6 (Real column Gram entries).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.real_gram_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.real_gram_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding the transpose product of a real isometry gives the column inner products as the Kronecker delta.

**Theorem 1.7 (Real orthogonal completion).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.complete_real_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.complete_real_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An orthonormal pair on four real coordinates extends to an orthogonal matrix whose first two columns are the given pair.

**Theorem 1.8 (Real part of the complex Gram matrix).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.complex_gram_re`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.complex_gram_re` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real part adds the dot products of the real parts and of the imaginary parts of the two columns.

**Theorem 1.9 (Imaginary part of the complex Gram matrix).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.complex_gram_im`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.complex_gram_im` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imaginary part subtracts the second mixed dot product from the first, as required by conjugation of the first column.

**Definition 1.10 (The coefficient calculation).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.cubicAfterConstant`

*Formalization.* `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.cubicAfterConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For generic affine radicands uᵢt−vᵢ, the coefficient formula drops the constant and shifts degrees down by one. The boundary certificate evaluates this formula at the exact vertex.

**Definition 1.11 (The polynomial for the guarded test).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.phaseCubic`

*Formalization.* `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.phaseCubic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit coefficient formula is the expansion of the quartic at xᵢ = qᵢ²t−dᵢ² with the constant term removed and the powers shifted down. Normalization makes the removed term zero.

**Definition 1.12 (The complementary projection diagonal).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.q`

*Formalization.* `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate qᵢ = 1 − 2pᵢ is the diagonal of the real projection orthogonal to the real pair obtained from the first two columns.

**Definition 1.13 (The diagonal difference).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.d`

*Formalization.* `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.d` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate dᵢ = 4pᵢ − 1 is the spectral gap times the difference of the two squared real eigenbasis coordinates.

**Definition 1.14 (The infeasible law).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.infeasibleWeights`

*Formalization.* `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.infeasibleWeights` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four coordinates are (19999, 15001, 12000, 13000)/60000.

**Definition 1.15 (The feasible law).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.feasibleWeights`

*Formalization.* `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.feasibleWeights` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four coordinates are (29, 27, 25, 19)/100.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.complete_real_pair`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.complex_gram_im`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.complex_gram_re`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.conjugate_pair_gauge_nonneg`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.cubicAfterConstant`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.d`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.feasibleWeights`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.feasible_weighted_phase_columns`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.infeasibleWeights`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.infeasible_weighted_phase_columns`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.phaseCubic`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.q`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.real_gram_entry`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.weighted_phase_columns_iff_cubic`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.weighted_phase_columns_iff_cubic_nonneg`
