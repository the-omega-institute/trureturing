# Six-Pole Strip Kernel Comparison

## Abstract

Six-Pole Strip Kernel Comparison

**Theorem 1.1 (Six-Pole Strip Kernel Comparison).**

$$\forall rho \in \mathbb{C},\; 0 < \operatorname{re}\left(\mathit{rho}\right) \Rightarrow \left(\operatorname{re}\left(\mathit{rho}\right) < 1 \Rightarrow \left(100 < \operatorname{im}\left(\mathit{rho}\right)^{2} \Rightarrow \left(0 < \operatorname{h14Weight}\left(\mathit{rho}\right) \land \left(\operatorname{im}\left(\mathit{rho}\right)^{2} \le 196 \Rightarrow \frac{345650537}{72636 \cdot 10^{18} + 763553532703907200} \le 2 \cdot \operatorname{h14Weight}\left(\mathit{rho}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/ActualHeightFourteenSector.h14_kernel_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here q=rho*(1-rho) and h14Weight(rho)=Re(1/(q*(q+30)*(q+56)*(q+90)*(q+132)*(q+182))). For every complex rho in the open strip with imaginary square above 100, the six-pole reciprocal kernel is positive. If the imaginary square is at most 196, twice its weight is at least 345650537/72636763553532703907200. The generic polar-angle and derivative proofs compare u and p on the closed auxiliary strip. The actual strip and height-ten premises are paid by the original exhaustive zero family at the final application; both signs and all multiplicities remain present.

## References

- Truth anchor: `D5/S3/Weil/ZeroData/ActualHeightFourteenSector.h14_kernel_bounds`
- Dependency: [D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds](ActualReciprocalSquareBounds.md)
