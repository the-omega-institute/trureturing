# Original-D positivity, unit rows, and finite label relations

## Abstract

Directed positivity and finite phase balance on the original spin factor

The complete original carrier is E = R x (Fin 3 -> R), with unit (1,0), Jordan product (s,x) o (t,y) = (st + x dot y, s y + t x), cone s >= sqrt(x dot x), and norm |s| + sqrt(x dot x). Evaluations retain every mass m >= sqrt(v dot v), including zero, unequal, and subnormalized masses.

The map D is an arbitrary total function on this same E. The results below derive their stated relations from the actual P2 and PB predicates. Additivity, homogeneity, continuity, unit rows, translation neutrality, three-label positivity, and the associator relation are not premises.

**Definition 1.1 (Directed two-label positivity).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalDContract.P2`

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalDContract.P2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every mass m and vector v with m >= sqrt(v dot v), and every two original elements a,b, the directed complex matrix with entries alpha(a_i o a_j) - i alpha(D(a_i,a_j)) is positive semidefinite. Both directed off-diagonal entries come from the same total D.

**Definition 1.2 (Original plus and minus phase balance).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalDContract.PB`

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalDContract.PB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every positive evaluation and every original triple a,b,c, the square readouts at r = b + D(a,b) - a o c, s = c + a o b + D(a,c), and at the corresponding opposite signs, agree. Every inner and outer occurrence uses the same original D.

**Theorem 1.3 (The original directed relation is antisymmetric).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalDContract.p2_skew`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalDContract.p2_skew` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every total D satisfying P2 and all original a,b, D(b,a) = -D(a,b). Hermitian symmetry of the actual two-label table gives the equality in every positive readout; scalar and coordinate evaluations separate original elements.

**Theorem 1.4 (The real off-diagonal entry remains in the determinant bound).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalDContract.p2_determinant_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalDContract.p2_determinant_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D satisfying P2, every positive evaluation alpha, and all a,b, alpha(D(a,b)) squared is at most alpha(a squared) alpha(b squared) minus alpha(a o b) squared. This includes zero mass and all degenerate labels. The known real Jordan term is retained.

**Theorem 1.5 (All real proportional inputs have zero output).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalDContract.p2_proportional`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalDContract.p2_proportional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D satisfying P2, every real r and every original a, both D(r a,a) and D(a,r a) are zero. The known Jordan determinant is zero on such a pair; the separating positive evaluations give the element equality, including r = 0 and negative r.

**Theorem 1.6 (Both original zero rows vanish).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalDContract.p2_zero_rows`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalDContract.p2_zero_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D satisfying P2, D(0,b) = 0 and D(a,0) = 0 for every original a,b. These equalities are used in the degenerate unit-row cases.

**Theorem 1.7 (Phase balance is the element-valued finite-difference law).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalDContract.pb_iff_finite_difference`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalDContract.pb_iff_finite_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every total D, PB is equivalent to finiteDifference(D,a,b,c) = 0 for all original triples. Writing d = D(a,b) - a o c and e = a o b + D(a,c), this is D(b+d,c+e) - D(b-d,c-e) = -2 b o d - 2 c o e. Expanding only the known Jordan squares makes the readout difference twice the evaluation of this residual. No input sum is expanded through D.

**Theorem 1.8 (Nonzero scalar labels eliminate the unit row).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalDContract.unit_row_nonzero_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalDContract.unit_row_nonzero_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every total D satisfying P2 and PB, all real l,t and every vector y with t nonzero, D((l,0),(t,y)) = 0. P2 first puts the output on the scalar zero face, perpendicular to y. If z is its vector part and Z its length, take the actual evaluation (Z,z) and the finite scalar k = l Z / (1+l squared). Both outer Jordan determinants vanish. The element-valued balance then forces t Z squared = 0.

**Theorem 1.9 (All original unit rows vanish).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalDContract.unit_rows`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalDContract.unit_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every total D satisfying P2 and PB, every real q and every original b, D((q,0),b) = 0. This includes pure-vector b, q = 0, and zero vectors. The pure-vector case uses proportional inner labels and equal b,c to obtain a zero outer pair; a finite Cayley label substitution with parameter sqrt(2)-1 connects it to the desired scalar/vector pair. Its two inner scalar parts are nonzero, so the preceding unit-row result applies. No limit or homogeneity of D is used.

**Theorem 1.10 (Every exact SO(2) label rotation preserves the original relation).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalDContract.label_rotation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalDContract.label_rotation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D satisfying P2 and PB, every two real numbers C,S with C squared plus S squared equal to one, and all original b,c, D(b,c) = D(C b + S c, C c - S b). Thus C = cos(phi), S = sin(phi) covers every real angle. Cayley substitution gives every circle point except the half-turn; two exact quarter-turns give that last case. The unknown D is never differentiated or taken to a limit.

**Theorem 1.11 (Collinear vector parts give zero for every scalar part).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalDContract.collinear_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalDContract.collinear_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D satisfying P2 and PB and all original a,b whose vector parts have zero cross product, D(a,b) = 0. A zero first vector part is an original unit row. Otherwise the vector parts are proportional; an explicit unit-circle label rotation removes the first vector part, so the same unit-row result applies. All zero vectors, proportionality signs, and scalar values remain included.

## References

- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalDContract.P2`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalDContract.PB`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalDContract.collinear_zero`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalDContract.label_rotation`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalDContract.p2_determinant_bound`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalDContract.p2_proportional`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalDContract.p2_skew`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalDContract.p2_zero_rows`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalDContract.pb_iff_finite_difference`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalDContract.unit_row_nonzero_scalar`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalDContract.unit_rows`
