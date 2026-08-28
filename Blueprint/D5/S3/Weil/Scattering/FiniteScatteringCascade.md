# Finite Scattering Cascade

## Abstract

Half-integer shifted-xi scattering is a finite cascade of modular completed-zeta quotients.

**Definition 1.1 (Shifted-xi scattering reading).**

Lean statement: `D5/S3/Weil/Scattering/FiniteScatteringCascade.shiftedXiScattering`

*Formalization.* `D5/S3/Weil/Scattering/FiniteScatteringCascade.shiftedXiScattering` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reading is constructed from the frozen entire xi function by taking the quotient at the two opposite shifts around one half.

**Definition 1.2 (Modular scattering coefficient).**

Lean statement: `D5/S3/Weil/Scattering/FiniteScatteringCascade.modularScatteringCoefficient`

*Formalization.* `D5/S3/Weil/Scattering/FiniteScatteringCascade.modularScatteringCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient is the consecutive quotient of the frozen classical completed-zeta reading at twice the supplied parameter.

**Theorem 1.3 (Half-integer shifted-xi scattering is a finite cascade).**

$$\begin{aligned}\forall N\in \mathbb{N},\\{}\operatorname{toMeromorphicNFOn}((z \mapsto \frac{\operatorname{xiReading}(s_{z}(z) - \frac{N}{2})}{\operatorname{xiReading}(s_{z}(z) + \frac{N}{2})}), \mathbb{C}) = \operatorname{toMeromorphicNFOn}((z \mapsto \frac{\operatorname{a}(z) \cdot \left(\operatorname{a}(z) - 1\right)}{\left(\operatorname{a}(z) + N\right) \cdot \left(\operatorname{a}(z) + N - 1\right)} \cdot \prod_{0 \leq j < N} \operatorname{modularScatteringCoefficient}(\frac{\operatorname{a}(z) + j + 1}{2})), \mathbb{C}),\\{}\text{where}\quad s_{z}(z) := \frac{1}{2} - i \cdot z,\\{}\operatorname{a}(z) := s_{z}(z) - \frac{N}{2}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Scattering/FiniteScatteringCascade.finite_scattering_cascade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural cascade length N, set the shift to N/2, set s_z to one half minus i times z, and set a to s_z minus N/2. The left denominator s_z plus N/2 is therefore the right endpoint a plus N used by the finite cascade.

Both sides are converted to Mathlib's canonical meromorphic normal form on the complex plane. This states the unconditional meromorphic identity, including canonical pole values, rather than weakening it with pointwise nonvanishing hypotheses.

The proof establishes the telescoping quotient on a nonempty open right half-plane, where completed zeta is nonzero, and then applies the frozen uniqueness theorem for meromorphic normal forms.

## References

- Truth anchor: `D5/S3/Weil/Scattering/FiniteScatteringCascade.finite_scattering_cascade`
- Truth anchor: `D5/S3/Weil/Scattering/FiniteScatteringCascade.modularScatteringCoefficient`
- Truth anchor: `D5/S3/Weil/Scattering/FiniteScatteringCascade.shiftedXiScattering`
- Dependency: [D5/S3/Analytic/Isolation/MeromorphicContinuationUniqueness](../../Analytic/Isolation/MeromorphicContinuationUniqueness.md)
- Dependency: [D5/S3/Zeros/CompletedZeta](../../Zeros/CompletedZeta.md)
