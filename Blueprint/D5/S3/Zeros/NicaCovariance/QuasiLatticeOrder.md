# Quasi-Lattice Order and Nica Covariance

## Abstract

The arithmetic shift realizes the full divisibility quasi-lattice: lcm joins multiply range projections, while gcd meets control quotients and cross-commutation.

**Theorem 1.1 (Range projections multiply at the lcm join).**

$$\forall u, v\in \operatorname{PrimeAxisTable},\ \operatorname{shiftRangeProjection}(u) \circ \operatorname{shiftRangeProjection}(v) = \operatorname{shiftRangeProjection}(\operatorname{tableSup}(u, v))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder.shift_range_projection_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The encoding of tableSup u v is the least common multiple of the two address encodings. A coefficient survives both range projections exactly when its address is divisible by this lcm, so their product is the single projection at the join. Symmetry of lcm also makes the family commute.

**Theorem 1.2 (A coprime join recovers normalized table addition).**

$$\forall u, v\in \operatorname{PrimeAxisTable},\ \operatorname{Coprime}(\operatorname{primeAxisEncoding}(u), \operatorname{primeAxisEncoding}(v)) \Rightarrow \operatorname{tableSup}(u, v) = \operatorname{normalizedTableAdd}(u, v)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder.tableSup_eq_normalizedTableAdd_of_coprime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coprimality identifies the lcm with the product, while normalized table addition encodes that same product. This theorem is the in-module bridge showing that the frozen coprime projection and double-commutation results are specializations of the full quasi-lattice relations.

**Theorem 1.3 (Divisible subspaces meet at the lcm join).**

$$\forall u, v\in \operatorname{PrimeAxisTable},\ \operatorname{divisibleSubspace}(u) \operatorname{inf} \operatorname{divisibleSubspace}(v) = \operatorname{divisibleSubspace}(\operatorname{tableSup}(u, v))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder.divisibleSubspace_inf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership in the submodule meet requires support on multiples of both addresses. Divisibility by tableSup u v is equivalent to those two conditions simultaneously, so the meet of the support subspaces is the support subspace at the lcm join.

**Theorem 1.4 (Subspace inclusion is reverse address divisibility).**

$$\forall u, v\in \operatorname{PrimeAxisTable},\ \operatorname{divisibleSubspace}(u) \le \operatorname{divisibleSubspace}(v) \Leftrightarrow \operatorname{primeAxisEncoding}(v) \mid \operatorname{primeAxisEncoding}(u)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder.divisibleSubspace_le_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If v divides u, every multiple of u is a multiple of v, giving the reverse inclusion of divisible support subspaces. Conversely, the unit vector at u lies in divisibleSubspace u; applying an assumed inclusion forces u to pass the v-divisibility filter.

**Theorem 1.5 (Quotients by the gcd meet are coprime).**

$$\forall u, v\in \operatorname{PrimeAxisTable},\ \operatorname{Coprime}(\operatorname{primeAxisEncoding}(\operatorname{normalizedTableSub}(u, \operatorname{tableInf}(u, v))), \operatorname{primeAxisEncoding}(\operatorname{normalizedTableSub}(v, \operatorname{tableInf}(u, v))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder.coprime_quotients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The encoding of tableInf u v is the gcd of the two address encodings. Factoring this common divisor from both addresses and cancelling its positive natural value leaves quotient encodings whose gcd is one.

**Theorem 1.6 (Backward and forward shifts cross-commute through the meet).**

$$\forall u, v\in \operatorname{PrimeAxisTable},\ \operatorname{backwardShiftCLM}(u) \circ \operatorname{forwardTranslationCLM}(v) = \operatorname{forwardTranslationCLM}(\operatorname{normalizedTableSub}(v, \operatorname{tableInf}(u, v))) \circ \operatorname{backwardShiftCLM}(\operatorname{normalizedTableSub}(u, \operatorname{tableInf}(u, v)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder.backward_shift_comp_forward_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write d for the gcd meet and factor u and v as quotient addresses times d. The quotient encodings are coprime, so the coordinate calculation reduces to coprime cross-commutation after cancelling d. Thus B_u V_v equals V_{v/d} B_{u/d} without a coprimality hypothesis.

**Theorem 1.7 (Nica cross-commutation in adjoint form).**

$$\forall u, v\in \operatorname{PrimeAxisTable},\ \operatorname{adjoint}(\operatorname{forwardTranslationCLM}(u)) \circ \operatorname{forwardTranslationCLM}(v) = \operatorname{forwardTranslationCLM}(\operatorname{normalizedTableSub}(v, \operatorname{tableInf}(u, v))) \circ \operatorname{adjoint}(\operatorname{forwardTranslationCLM}(\operatorname{normalizedTableSub}(u, \operatorname{tableInf}(u, v))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder.adjoint_forward_translation_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Hilbert adjoint of forward translation is the corresponding backward shift. Rewriting both backward shifts in the general cross-commutation identity therefore gives the standard adjoint presentation of Nica covariance through the gcd meet.

## References

- Truth anchor: `D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder.adjoint_forward_translation_comp`
- Truth anchor: `D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder.backward_shift_comp_forward_translation`
- Truth anchor: `D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder.coprime_quotients`
- Truth anchor: `D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder.divisibleSubspace_inf`
- Truth anchor: `D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder.divisibleSubspace_le_iff`
- Truth anchor: `D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder.shift_range_projection_comp`
- Truth anchor: `D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder.tableSup_eq_normalizedTableAdd_of_coprime`
- Dependency: [D5/S3/Zeros/NicaCovariance/DoubleCommutation](DoubleCommutation.md)
- Dependency: [D5/S3/Zeros/NicaCovariance/SemigroupRelations](SemigroupRelations.md)
- Dependency: [D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint](../ShiftOperators/BackwardShiftAdjoint.md)
- Dependency: [D5/S3/Zeros/ShiftOperators/ShiftRangeProjection](../ShiftOperators/ShiftRangeProjection.md)
