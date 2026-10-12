# Golden units for Kimberling row intersections

## Abstract

Golden integer units have signed integral powers and an oriented small-unit description.

**Definition 1.1 (Golden power rows).**

$$\forall i \in \mathrm{Nat},\; \forall N \in \mathrm{Nat},\; N \in \operatorname{row}\left(i\right) \Leftrightarrow \left(\exists k \in \mathrm{Nat},\; 1 \le k \land N = \left\lfloor\mathrm{goldenRatio}^{i} \cdot k\right\rfloor\right)$$

*Formalization.* `D5/S1/Recurrence/KimberlingArrayRowPairs.row` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Row i consists of the natural floors of positive integral multiples of the ith golden power.

**Definition 1.2 (Lucas trace).**

$$\forall n \in \mathrm{Nat},\; \operatorname{lucas}\left(n\right) = \operatorname{toNat}\left(\operatorname{goldenLucas}\left(n\right)\right)$$

*Formalization.* `D5/S1/Recurrence/KimberlingArrayRowPairs.lucas` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural Lucas number is the nonnegative integral trace of the nth golden power. Its initial values are two and one.

**Theorem 1.3 (Integral unit powers).**

$$\forall s \in \mathrm{Int},\; \operatorname{embedding}\left(\operatorname{coe}\left(\mathrm{phiUnit}^{s}\right)\right) = \mathrm{goldenRatio}^{s}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KimberlingArrayRowPairs.embedding_phiUnit_zpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The distinguished unit evaluates to the golden ratio for all integral exponents.

**Theorem 1.4 (Inverse powers).**

$$\forall r \in \mathrm{Nat},\; \operatorname{coe}\left(\mathrm{phiUnit}^{0 - r}\right) = \left(0 - 1\right)^{r} \cdot \operatorname{conj}\left(\mathrm{phi}^{r}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KimberlingArrayRowPairs.phiUnit_neg_nat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inverse powers have the signed conjugate coordinates.

**Theorem 1.5 (Orientation of small units).**

$$\forall z \in \mathrm{GoldenInt},\; \forall i \in \mathrm{Nat},\; \left(\operatorname{norm}\left(z\right) = 1 \lor \operatorname{norm}\left(z\right) = 0 - 1\right) \Rightarrow \left(\operatorname{b}\left(z\right) < 0 \Rightarrow \left(\operatorname{abs}\left(\operatorname{embedding}\left(z\right)\right) < \operatorname{inv}\left(\mathrm{goldenRatio}^{i}\right) \Rightarrow \left(\exists r \in \mathrm{Nat},\; i + 1 \le r \land \left(z = \operatorname{conj}\left(\mathrm{phi}^{r}\right) \land \operatorname{embedding}\left(z\right) = \left(0 - 1\right)^{r} \cdot \operatorname{inv}\left(\mathrm{goldenRatio}^{r}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KimberlingArrayRowPairs.golden_small_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A negative golden coefficient fixes the orientation of a sufficiently small unit to the conjugate of a positive power.

## References

- Truth anchor: `D5/S1/Recurrence/KimberlingArrayRowPairs.embedding_phiUnit_zpow`
- Truth anchor: `D5/S1/Recurrence/KimberlingArrayRowPairs.golden_small_unit`
- Truth anchor: `D5/S1/Recurrence/KimberlingArrayRowPairs.lucas`
- Truth anchor: `D5/S1/Recurrence/KimberlingArrayRowPairs.phiUnit_neg_nat`
- Truth anchor: `D5/S1/Recurrence/KimberlingArrayRowPairs.row`
- Dependency: [D5/S1/Scale/Embedding](../Scale/Embedding.md)
