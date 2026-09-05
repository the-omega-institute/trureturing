# Frame Non-Cancellation

## Abstract

A positive frame floor excludes blind modes, while complete tests without a uniform floor can still lose control along the infinite tail.

**Theorem 1.1 (Complete attenuated coordinates have no uniform lower bound).**

$$\left(\forall d \in OfflineModeSpace,\; \left(\forall n \in \mathbb{N},\; \operatorname{attenuatedCoordinateReadout}\left(n, d\right) = 0\right) \Rightarrow d = 0\right) \land \left(\left(\forall d \in OfflineModeSpace,\; \operatorname{Summable}\left(n: \mathbb{N} \mapsto \operatorname{attenuatedCoordinateReadout}\left(n, d\right)^{2}\right)\right) \land \left(\left(\forall d \in OfflineModeSpace,\; 0 \le \operatorname{attenuatedAnalysisEnergy}\left(d\right)\right) \land \left(\operatorname{Tendsto}\left(n: \mathbb{N} \mapsto \operatorname{attenuatedAnalysisEnergy}\left(\operatorname{single}\left(2, n, 1\right)\right), atTop, \operatorname{nhds}\left(0\right)\right) \land \left(\forall alpha \in \mathbb{R},\; 0 < \alpha \Rightarrow \left(\exists d \in OfflineModeSpace,\; \left\lVert d \right\rVert = 1 \land \operatorname{attenuatedAnalysisEnergy}\left(d\right) < \alpha\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/FrameNonCancellation.attenuated_coordinate_family_tail_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The offline carrier is the real square-summable sequence space. Coordinate n is read with weight one over n plus one, and the analysis energy is the sum of the squared weighted readouts.

Every weight is nonzero, so the full coordinate family separates all modes. Its energy is summable and nonnegative. The unit coordinate modes have energy one over n plus one squared, which tends to zero and excludes every positive uniform floor.

**Theorem 1.2 (A positive frame coefficient prevents cancellation).**

$$\forall H \in \operatorname{Type}, K \in \operatorname{Type}, analysis \in \operatorname{LinearMap}\left(\mathbb{R}, H, K\right),\; \left(\left(\operatorname{NormedAddCommGroup}\left(H\right) \land \left(\operatorname{NormedSpace}\left(\mathbb{R}, H\right) \land \left(\operatorname{NormedAddCommGroup}\left(K\right) \land \operatorname{NormedSpace}\left(\mathbb{R}, K\right)\right)\right)\right) \land 0 < \operatorname{frameLowerCoefficient}\left(analysis\right)\right) \Rightarrow \left(\left(\forall d \in H,\; analysis\left(d\right) = 0 \Rightarrow d = 0\right) \land \left(\left(\exists channel \in \operatorname{LinearMap}\left(\mathbb{R}, \operatorname{Prod}\left(\mathbb{R}, \mathbb{R}\right), \mathbb{R}\right), blind \in \operatorname{Prod}\left(\mathbb{R}, \mathbb{R}\right),\; blind \ne 0 \land \left(\left(\forall x \in \operatorname{Prod}\left(\mathbb{R}, \mathbb{R}\right),\; 0 \le channel\left(x\right)^{2}\right) \land channel\left(blind\right) = 0\right)\right) \land \left(\left(\forall d \in OfflineModeSpace,\; \left(\forall n \in \mathbb{N},\; \operatorname{attenuatedCoordinateReadout}\left(n, d\right) = 0\right) \Rightarrow d = 0\right) \land \left(\left(\forall d \in OfflineModeSpace,\; \operatorname{Summable}\left(n: \mathbb{N} \mapsto \operatorname{attenuatedCoordinateReadout}\left(n, d\right)^{2}\right)\right) \land \left(\left(\forall d \in OfflineModeSpace,\; 0 \le \operatorname{attenuatedAnalysisEnergy}\left(d\right)\right) \land \left(\operatorname{Tendsto}\left(n: \mathbb{N} \mapsto \operatorname{attenuatedAnalysisEnergy}\left(\operatorname{single}\left(2, n, 1\right)\right), atTop, \operatorname{nhds}\left(0\right)\right) \land \left(\forall alpha \in \mathbb{R},\; 0 < \alpha \Rightarrow \left(\exists d \in OfflineModeSpace,\; \left\lVert d \right\rVert = 1 \land \operatorname{attenuatedAnalysisEnergy}\left(d\right) < \alpha\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/FrameNonCancellation.frame_non_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frame coefficient is definitionally the infimum of the squared analysis-norm ratio over nonzero modes. If this coefficient is positive, an analysis-zero mode cannot be nonzero.

The first contrast uses one scalar channel on a real two-coordinate space. Every channel square is nonnegative, but the second coordinate is a nonzero blind mode.

The second contrast is the complete attenuated coordinate family. It has infinitely many separating tests and positive square energies, but its unit tail probes force the uniform lower frame coefficient to vanish.

## References

- Truth anchor: `D5/S3/Observer/Linear/FrameNonCancellation.attenuated_coordinate_family_tail_escape`
- Truth anchor: `D5/S3/Observer/Linear/FrameNonCancellation.frame_non_cancellation`
