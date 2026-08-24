# One-Step Repair Universal Property

## Abstract

The one-step interface is the coarsest interface deciding two successive readouts.

**Theorem 1.1 (One-step factorization).**

$$\forall X, B, C: \operatorname{Type}, q: X \to B, F: X \to X, r: X \to C, a, b: C \to B,\\{}q = a \circ r \land q \circ F = b \circ r \Rightarrow \operatorname{oneStepInterface}\left(q, F\right) = (a, b) \circ r.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Dialectics/OneStepRepairUniversalProperty.one_step_repair_universal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If q and q after F both factor through r, pairing the two supplied factors gives a factorization of the one-step interface through r. The proof needs no inhabitedness, finiteness, or type-class data.

**Theorem 1.2 (Factor uniqueness on the realized image).**

$$\operatorname{oneStepInterface}\left(q, F\right) = (a1, b1) \circ r \land \operatorname{oneStepInterface}\left(q, F\right) = (a2, b2) \circ r \Rightarrow \operatorname{EqOn}\left((a1, b1), (a2, b2), \operatorname{range}\left(r\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Dialectics/OneStepRepairUniversalProperty.one_step_repair_factor_unique_on_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any two paired factors inducing the same one-step interface agree on the realized range of r. Values outside that range remain unconstrained unless r is surjective.

**Theorem 1.3 (Reverse kernel containment).**

$$\forall x, y, r(x) = r(y) \Rightarrow \operatorname{oneStepInterface}\left(q, F\right)(x) = \operatorname{oneStepInterface}\left(q, F\right)(y).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Dialectics/OneStepRepairUniversalProperty.one_step_repair_kernel_contains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every equality in the kernel of r forces equality of both the current and next readouts. Thus the kernel of the one-step interface contains the kernel of every interface deciding both values.

**Theorem 1.4 (Current factorization is necessary).**

$$\exists q, F, r, a, b,\\{}q \circ F = b \circ r \land \operatorname{oneStepInterface}\left(q, F\right) \neq (a, b) \circ r.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Dialectics/OneStepRepairUniversalProperty.current_factorization_hypothesis_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Boolean identity readout with a constant update has a next readout factoring through Unit, while its current readout does not. The claimed paired factorization therefore fails.

**Theorem 1.5 (Next factorization is necessary).**

$$\exists q, F, r, a, b,\\{}q = a \circ r \land \operatorname{oneStepInterface}\left(q, F\right) \neq (a, b) \circ r.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Dialectics/OneStepRepairUniversalProperty.next_factorization_hypothesis_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a pair of Booleans, the first projection factors through itself, but swapping coordinates makes the next readout depend on the hidden second coordinate. The paired factorization then fails.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Dialectics/OneStepRepairUniversalProperty.current_factorization_hypothesis_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/Dialectics/OneStepRepairUniversalProperty.next_factorization_hypothesis_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/Dialectics/OneStepRepairUniversalProperty.one_step_repair_factor_unique_on_range`
- Truth anchor: `D5/S3/ConceptDynamics/Dialectics/OneStepRepairUniversalProperty.one_step_repair_kernel_contains`
- Truth anchor: `D5/S3/ConceptDynamics/Dialectics/OneStepRepairUniversalProperty.one_step_repair_universal`
- Dependency: [D5/S3/ConceptDynamics/Dialectics/DeterministicInterfaceEquivalence](DeterministicInterfaceEquivalence.md)
