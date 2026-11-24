# Formal composition, Cayley trigonometry and concrete witnesses

## Abstract

Formal power-series substitution and exact algebraic, geometric and arithmetic identities.

**Theorem 1.1 (Formal chain rule).**

$$\forall N \in OmegaNat, f \in JetSeq, g \in JetSeq,\; \left(\left(\operatorname{Finite}\left(f\right) \land \operatorname{Finite}\left(g\right)\right) \land \operatorname{g}\left(0\right) \equiv 0\right) \Rightarrow \operatorname{EquivalentAt}\left(N, \operatorname{deriv}\left(\operatorname{compose}\left(f, g\right)\right), \operatorname{compose}\left(\operatorname{deriv}\left(f\right), g\right) \cdot \operatorname{deriv}\left(g\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaComposeAndWitnesses.deriv_compose_equivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every coefficient is a finite rational. With zero inner constant coefficient, powers of the inner stream vanish below their exponent. Leibniz's rule differentiates each finite substitution and the discarded terms contribute zero through the stated degree.

**Theorem 1.2 (Cosine of twice the formal arctangent).**

$$\forall N \in OmegaNat,\; \operatorname{EquivalentAt}\left(N, \operatorname{compose}\left(Cos, \operatorname{scale}\left(2, Atan\right)\right), CayleyCos\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaComposeAndWitnesses.cos_two_atan_eq_cayley` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formal chain rule and the arctangent equation give the cosine equation of the coupled Cayley system. The constant coefficient is one.

**Theorem 1.3 (Sine of twice the formal arctangent).**

$$\forall N \in OmegaNat,\; \operatorname{EquivalentAt}\left(N, \operatorname{compose}\left(Sin, \operatorname{scale}\left(2, Atan\right)\right), CayleySin\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaComposeAndWitnesses.sin_two_atan_eq_cayley` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the differentiated sine composition by one plus the square of the indeterminate gives twice the cosine composition. The zero sine constant and the unit cosine constant determine both streams at each truncation.

**Theorem 1.4 (Multiplicativity of the integer determinant).**

$$\forall A \in MatTwo, B \in MatTwo,\; \operatorname{det}\left(A \cdot B\right) = \operatorname{det}\left(A\right) \cdot \operatorname{det}\left(B\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaComposeAndWitnesses.mat2_det_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity holds for all two by two integer matrices, including singular matrices.

**Theorem 1.5 (Noncommuting ternion rays).**

$$\neg \operatorname{RayEquiv}\left(\operatorname{triad}\left(pHalf, o, qHalf\right), \operatorname{triad}\left(qHalf, o, pHalf\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaComposeAndWitnesses.phalf_qhalf_noncommutative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The middle point is the identity quaternion. The two products have the same nonzero real coordinate and opposite last coordinates, so they cannot represent the same ray.

**Theorem 1.6 (The signed six-beat orbit).**

$$\operatorname{SignedEq}\left(\operatorname{pow}\left(gSpin, 1\right), gSpin\right) \land \left(\operatorname{SignedEq}\left(\operatorname{pow}\left(gSpin, 2\right), second\right) \land \left(\operatorname{SignedEq}\left(\operatorname{pow}\left(gSpin, 3\right), antipode\right) \land \left(\operatorname{SignedEq}\left(\operatorname{pow}\left(gSpin, 4\right), fourth\right) \land \left(\operatorname{SignedEq}\left(\operatorname{pow}\left(gSpin, 5\right), fifth\right) \land \left(\operatorname{SignedEq}\left(\operatorname{pow}\left(gSpin, 6\right), identity\right) \land \left(\operatorname{kappaSpin}\left(identity, \operatorname{pow}\left(gSpin, 3\right)\right) \equiv 0 \land \operatorname{kappaSpin}\left(identity, \operatorname{pow}\left(gSpin, 6\right)\right) \equiv 1\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaComposeAndWitnesses.g120_spin_six_beat_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generator has homogeneous coordinates (1, 1, 1, 1) with denominator two. The second, fourth and fifth beats have numerators (-1, 1, 1, 1), (-1, -1, -1, -1) and (1, -1, -1, -1), each with denominator two. Beat three is the radius-one antipode and beat six is the radius-one identity. The corresponding accumulated rotation angles are 360 and 720 degrees.

**Theorem 1.7 (Quarter Gram determinant).**

$$\operatorname{detGram}\left(o, pHalf, qHalf\right) \equiv \frac{1}{4}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaComposeAndWitnesses.orthogonal_triad_excess_quarter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three vectors are the identity coordinate vector and the sums of that vector with the first and second imaginary coordinate vectors. Their normalized Gram determinant is one quarter.

**Theorem 1.8 (Exact first halt of the four-rule FRACTRAN program).**

$$\operatorname{Follows}\left(pOmega, trace, 131072\right) \land \left(\operatorname{run}\left(pOmega, 15, 131072\right) = 22 \land \left(\operatorname{Halts}\left(pOmega, 22\right) \land \left(\forall k \in OmegaNat,\; k < 15 \Rightarrow \neg \operatorname{Halts}\left(pOmega, \operatorname{run}\left(pOmega, k, 131072\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaComposeAndWitnesses.p_omega_halts_at_22` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rules in priority order are 11/49, 7/25, 5/9 and 3/4. After 131072 the states are 98304, 73728, 40960, 30720, 23040, 12800, 3584, 2688, 2016, 1120, 840, 630, 350, 98 and 22. Every listed transition fires the first enabled rule. All four guards fail at 22.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaComposeAndWitnesses.cos_two_atan_eq_cayley`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaComposeAndWitnesses.deriv_compose_equivAt`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaComposeAndWitnesses.g120_spin_six_beat_orbit`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaComposeAndWitnesses.mat2_det_mul`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaComposeAndWitnesses.orthogonal_triad_excess_quarter`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaComposeAndWitnesses.p_omega_halts_at_22`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaComposeAndWitnesses.phalf_qhalf_noncommutative`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaComposeAndWitnesses.sin_two_atan_eq_cayley`
