# White Floor and Sampling Duality

## Abstract

A spectral quadratic identity identifies the local white floor with the least unit-norm sampling energy.

**Theorem 1.1 (White floor equals the least sampling bound).**

$$\forall H \in Type, K \in Type, quadratic \in H \to \operatorname{Real}\left(\right), sampling \in \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), H, K\right),\; \left(\operatorname{NormedAddCommGroup}\left(H\right) \land \left(\operatorname{NormedSpace}\left(\operatorname{Real}\left(\right), H\right) \land \left(\operatorname{Nontrivial}\left(H\right) \land \left(\operatorname{NormedAddCommGroup}\left(K\right) \land \left(\operatorname{NormedSpace}\left(\operatorname{Real}\left(\right), K\right) \land \left(\forall f \in H,\; \operatorname{apply}\left(quadratic, f\right) = \left\lVert \operatorname{apply}\left(sampling, f\right) \right\rVert^{2}\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{let} whiteFloors = \left\{\forall f \in H,\; 0 \le \operatorname{sub}\left(\operatorname{apply}\left(quadratic, f\right), \operatorname{mul}\left(lambda, \left\lVert f \right\rVert^{2}\right)\right) \mid lambda \in \operatorname{Real}\left(\right)\right\}, \operatorname{let} samplingBounds = \left\{\exists f \in H,\; \left\lVert f \right\rVert = 1 \land r = \left\lVert \operatorname{apply}\left(sampling, f\right) \right\rVert^{2} \mid r \in \operatorname{Real}\left(\right)\right\}, \operatorname{sSup}\left(whiteFloors\right) = \operatorname{sInf}\left(samplingBounds\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaAnalytic/WhiteFloorSamplingDuality.white_floor_sampling_frame_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cone-margin theorem first expresses the floor as a nonzero Rayleigh infimum. Normalizing each nonzero test vector proves that this value set is exactly the unit-sphere sampling set.

## References

- Truth anchor: `D5/S3/Weil/ZetaAnalytic/WhiteFloorSamplingDuality.white_floor_sampling_frame_duality`
- Dependency: [D5/S3/Weil/ZetaAnalytic/LocalSpectralFloor](LocalSpectralFloor.md)
