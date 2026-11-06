# Three-Way Eighteen-Slot Recovery Identity

## Abstract

The explicit eighteen-slot three-way encoder has an exact positive recovery readout.

**Definition 1.1 (Positive slot weights).**

Lean statement: `D5/S3/Fourier/ThreeWaySlotIdentity.slotWeight`

*Formalization.* `D5/S3/Fourier/ThreeWaySlotIdentity.slotWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two slot colors have weights 2/3 and 1/3, selected by the value of s in Fin 2.

**Definition 1.2 (The eighteen-slot encoder).**

Lean statement: `D5/S3/Fourier/ThreeWaySlotIdentity.slotEncode`

*Formalization.* `D5/S3/Fourier/ThreeWaySlotIdentity.slotEncode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For k and j in Fin 3 and s in Fin 2, the slot indexed by (k,j,s) is slotWeight(s) times u^(k*j+s) times x(j).

**Definition 1.3 (The positive recovery readout).**

Lean statement: `D5/S3/Fourier/ThreeWaySlotIdentity.slotRecover`

*Formalization.* `D5/S3/Fourier/ThreeWaySlotIdentity.slotRecover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The j-th recovered coordinate is one third of the sum over k and s of u^(-(k*j+s)) times the corresponding fine slot.

**Theorem 1.4 (Exact recovery of every input coordinate).**

$$\forall (u: \mathbb{C}), (\forall (x: (\operatorname{Fin}(3) \to \mathbb{C})), ((u \ne (0: \mathbb{C})) \Rightarrow (\forall (j: \operatorname{Fin}(3)), (\operatorname{slotRecover}(u, \operatorname{slotEncode}(u, x), j) = x(j)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThreeWaySlotIdentity.slot_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero complex u and every vector x from Fin 3 to the complex numbers, the stated recovery readout applied to the stated encoder returns x at every coordinate.

The proof cancels each inverse-power factor against its matching power, then sums the three copies of the two positive weights. This is the finite recovery identity from equations (16.11)-(16.12); it does not assert either slot-count lower bound or the aggregation identity CD=L.

## References

- Truth anchor: `D5/S3/Fourier/ThreeWaySlotIdentity.slotEncode`
- Truth anchor: `D5/S3/Fourier/ThreeWaySlotIdentity.slotRecover`
- Truth anchor: `D5/S3/Fourier/ThreeWaySlotIdentity.slotWeight`
- Truth anchor: `D5/S3/Fourier/ThreeWaySlotIdentity.slot_recovery`
