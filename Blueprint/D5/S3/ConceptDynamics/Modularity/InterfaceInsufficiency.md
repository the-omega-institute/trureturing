# When Modular Interfaces Are Insufficient

## Abstract

Componentwise-equal public interfaces cannot verify a differing global target, while an explicit factorization through their joint readout supplies a verifier.

**Theorem 1.1 (Componentwise agreement cannot reveal a global difference).**

$$\forall X1 \in Type, X2 \in Type, I1 \in Type, I2 \in Type, Y \in Type, C1 \in X1 \to I1, C2 \in X2 \to I2, T \in X1 \times X2 \to Y, x1 \in X1, y1 \in X1, x2 \in X2, y2 \in X2,\; \left(C1\left(x1\right) = C1\left(y1\right) \land \left(C2\left(x2\right) = C2\left(y2\right) \land T\left(\operatorname{pair}\left(x1, x2\right)\right) \ne T\left(\operatorname{pair}\left(y1, y2\right)\right)\right)\right) \Rightarrow \left(\neg \left(\exists verify \in X1 \times X2 \to Y,\; \operatorname{InterfaceBlind}\left(C1, C2, verify\right) \land \left(\forall state \in X1 \times X2,\; verify\left(state\right) = T\left(state\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Modularity/InterfaceInsufficiency.modular_interfaces_cannot_verify_global_target` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose two composite states have the same first-component interface and the same second-component interface, while the global target assigns them different values. Their paired public readouts are therefore identical.

Interface blindness forces any verifier to return the same value on those states. A verifier that were correct everywhere would instead return their distinct target values, so no interface-blind verifier can be universally correct.

**Proposition 1.2 (A target factoring through the joint interface is verifiable).**

$$\forall X1 \in Type, X2 \in Type, I1 \in Type, I2 \in Type, Y \in Type, C1 \in X1 \to I1, C2 \in X2 \to I2, T \in X1 \times X2 \to Y,\; \left(\exists f \in I1 \times I2 \to Y,\; T = f \circ \operatorname{jointInterface}\left(C1, C2\right)\right) \Rightarrow \left(\exists verify \in X1 \times X2 \to Y,\; \operatorname{InterfaceBlind}\left(C1, C2, verify\right) \land \left(\forall state \in X1 \times X2,\; verify\left(state\right) = T\left(state\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Modularity/InterfaceInsufficiency.factorized_target_has_interface_blind_verifier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the target is a function of the paired component interfaces, compose that factor map with the joint interface and use the composite as the verifier.

Equal joint readouts remain equal after applying the factor map, which makes the verifier interface-blind. The factorization identity also makes its output agree with the target on every composite state.

**Lemma 1.3 (Constant Boolean interfaces cannot verify conjunction).**

$$\neg \left(\exists verify \in Bool \times Bool \to Bool,\; \operatorname{InterfaceBlind}\left(\operatorname{constant}\left(Bool, Unit\right), \operatorname{constant}\left(Bool, Unit\right), verify\right) \land \left(\forall state \in Bool \times Bool,\; verify\left(state\right) = \operatorname{boolAnd}\left(\operatorname{fst}\left(state\right), \operatorname{snd}\left(state\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Modularity/InterfaceInsufficiency.constant_bool_interfaces_cannot_verify_conjunction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two constant Unit-valued component interfaces expose the same public pair for every Boolean composite state. In particular, they cannot distinguish (true, true) from (false, false).

Boolean conjunction is true on the first state and false on the second. The general componentwise obstruction therefore rules out an interface-blind verifier that computes conjunction everywhere.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Modularity/InterfaceInsufficiency.constant_bool_interfaces_cannot_verify_conjunction`
- Truth anchor: `D5/S3/ConceptDynamics/Modularity/InterfaceInsufficiency.factorized_target_has_interface_blind_verifier`
- Truth anchor: `D5/S3/ConceptDynamics/Modularity/InterfaceInsufficiency.modular_interfaces_cannot_verify_global_target`
- Dependency: [D5/S3/ConceptDynamics/Contestability/InvisibleDefectUnrepairable](../Contestability/InvisibleDefectUnrepairable.md)
