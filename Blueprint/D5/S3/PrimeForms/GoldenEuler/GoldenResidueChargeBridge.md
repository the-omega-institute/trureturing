# Golden Residue Charge Bridge

## Abstract

Residues modulo five select the split, inert, and ramified charge values used by the golden local Euler factor.

**Theorem 1.1 (Split Residues Have Positive Charge).**

$$\forall p: \mathbb{N},\\{}((\operatorname{mod}\left(p, 5\right) = 1) \lor (\operatorname{mod}\left(p, 5\right) = 4)) \Rightarrow\\{}(\operatorname{goldenResidueCharge}\left(p\right) = 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenEuler/GoldenResidueChargeBridge.golden_residue_charge_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A natural number congruent to one or four modulo five is assigned golden residue charge plus one.

The theorem translates the stated residue premise only; primality and splitting are not inferred here.

**Theorem 1.2 (Inert Residues Have Negative Charge).**

$$\forall p: \mathbb{N},\\{}((\operatorname{mod}\left(p, 5\right) = 2) \lor (\operatorname{mod}\left(p, 5\right) = 3)) \Rightarrow\\{}(\operatorname{goldenResidueCharge}\left(p\right) = -1).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenEuler/GoldenResidueChargeBridge.golden_residue_charge_inert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A natural number congruent to two or three modulo five is assigned golden residue charge minus one.

The disjunctive residue hypothesis remains explicit, and no converse classification is asserted.

**Theorem 1.3 (Five Has Zero Golden Residue Charge).**

$$(\operatorname{goldenResidueCharge}\left(5\right) = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenEuler/GoldenResidueChargeBridge.golden_residue_charge_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The natural number five falls outside the split and inert residue branches and therefore receives charge zero.

This evaluates the distinguished ramified input without generalizing to every multiple of five.

**Theorem 1.4 (Split Residues Select the Squared Denominator).**

$$\forall p: \mathbb{N} , X: \mathbb{R},\\{}((\operatorname{mod}\left(p, 5\right) = 1) \lor (\operatorname{mod}\left(p, 5\right) = 4)) \Rightarrow\\{}(\operatorname{goldenLocalDenominator}\left(\operatorname{goldenResidueCharge}\left(p\right), X\right) = {1 - X}^{2}).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenEuler/GoldenResidueChargeBridge.split_residue_local_denominator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the split residue premise, the charge bridge feeds plus one into the local denominator and yields the squared linear form.

The conclusion is algebraic in the real variable X and does not assert convergence of a local or global Euler product.

**Theorem 1.5 (Inert Residues Select the Quadratic Denominator).**

$$\forall p: \mathbb{N} , X: \mathbb{R},\\{}((\operatorname{mod}\left(p, 5\right) = 2) \lor (\operatorname{mod}\left(p, 5\right) = 3)) \Rightarrow\\{}(\operatorname{goldenLocalDenominator}\left(\operatorname{goldenResidueCharge}\left(p\right), X\right) = 1 - {X}^{2}).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenEuler/GoldenResidueChargeBridge.inert_residue_local_denominator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the inert residue premise, the bridge feeds minus one into the local denominator and yields one minus X squared.

Only the supplied residue class is used; the statement adds no independent prime-splitting theorem.

**Theorem 1.6 (Five Selects the Ramified Linear Denominator).**

$$\forall X: \mathbb{R},\\{}(\operatorname{goldenLocalDenominator}\left(\operatorname{goldenResidueCharge}\left(5\right), X\right) = 1 - X).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenEuler/GoldenResidueChargeBridge.ramified_five_local_denominator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero charge assigned to five removes the nontrivial charge factor and leaves one minus X.

This is the single ramified specialization at five and remains a totalized real polynomial identity.

## References

- Truth anchor: `D5/S3/PrimeForms/GoldenEuler/GoldenResidueChargeBridge.golden_residue_charge_five`
- Truth anchor: `D5/S3/PrimeForms/GoldenEuler/GoldenResidueChargeBridge.golden_residue_charge_inert`
- Truth anchor: `D5/S3/PrimeForms/GoldenEuler/GoldenResidueChargeBridge.golden_residue_charge_split`
- Truth anchor: `D5/S3/PrimeForms/GoldenEuler/GoldenResidueChargeBridge.inert_residue_local_denominator`
- Truth anchor: `D5/S3/PrimeForms/GoldenEuler/GoldenResidueChargeBridge.ramified_five_local_denominator`
- Truth anchor: `D5/S3/PrimeForms/GoldenEuler/GoldenResidueChargeBridge.split_residue_local_denominator`
- Dependency: [D5/S3/PrimeForms/GoldenEuler/GoldenLocalEulerTrichotomy](GoldenLocalEulerTrichotomy.md)
- Dependency: [D5/S3/PrimeForms/GoldenPrimeClassification](../GoldenPrimeClassification.md)
