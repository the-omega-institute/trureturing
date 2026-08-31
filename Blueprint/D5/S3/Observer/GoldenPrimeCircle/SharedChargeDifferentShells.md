# Shared Charge, Different Shells

## Abstract

Distinct observer shells may factor through the same charge readout while retaining different residual information.

**Theorem 1.1 (Common Charge Projections Agree).**

$$\forall X: \operatorname{Type}_{u} , Y_{1}: \operatorname{Type}_{v} , Y_{2}: \operatorname{Type}_{w} , C: \operatorname{Type}_{z} , shell_{1}: X \to Y_{1} , shell_{2}: X \to Y_{2} , charge_{1}: Y_{1} \to C , charge_{2}: Y_{2} \to C , charge: X \to C , x: X,\\{}(\operatorname{CarriesCharge}\left(shell_{1}, charge_{1}, charge\right)) \land (\operatorname{CarriesCharge}\left(shell_{2}, charge_{2}, charge\right)) \Rightarrow\\{}(charge_{1}(shell_{1}(x)) = charge_{2}(shell_{2}(x))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/SharedChargeDifferentShells.common_charge_agreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two shell maps both factor the same charge observation, their projected readings agree at every source point.

The equality is only after applying the respective charge projections; it does not identify the shell outputs themselves.

**Theorem 1.2 (The Concrete Shells Carry the Same Charge).**

$$((\operatorname{CarriesCharge}\left(coarseShell, id, fst\right)) \land (\operatorname{CarriesCharge}\left(fineShell, fineCharge, fst\right))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/SharedChargeDifferentShells.concrete_shells_carry_same_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coarse Boolean shell reads the first coordinate, while the fine shell retains the full pair and projects its first coordinate as charge.

Both factorizations recover the same source charge, but the conjunction alone does not assert equal information content.

**Theorem 1.3 (One Coarse Collision Is Separated by the Fine Shell).**

$$((\operatorname{coarseShell}\left((true, false)\right) = \operatorname{coarseShell}\left((true, true)\right)) \land (\operatorname{fineShell}\left((true, false)\right) \neq \operatorname{fineShell}\left((true, true)\right))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/SharedChargeDifferentShells.same_charge_different_observer_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inputs (true,false) and (true,true) have the same coarse first-coordinate reading.

Their fine-shell values remain distinct, giving a concrete residual distinction beyond the shared charge.

**Theorem 1.4 (Shared Charge Does Not Force Equal Resolution).**

$$(\exists x: \operatorname{Bool} \times \operatorname{Bool}, y: \operatorname{Bool} \times \operatorname{Bool}, ((\operatorname{coarseShell}\left(x\right) = \operatorname{coarseShell}\left(y\right)) \land (\operatorname{fineShell}\left(x\right) \neq \operatorname{fineShell}\left(y\right)))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/SharedChargeDifferentShells.shared_charge_does_not_force_same_resolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exist two Boolean-pair inputs that collide under the coarse shell and are separated by the fine shell.

This existential counterexample refutes only equality of observer resolution from shared charge; it does not compare arbitrary shell orders.

## References

- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/SharedChargeDifferentShells.common_charge_agreement`
- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/SharedChargeDifferentShells.concrete_shells_carry_same_charge`
- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/SharedChargeDifferentShells.same_charge_different_observer_witness`
- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/SharedChargeDifferentShells.shared_charge_does_not_force_same_resolution`
