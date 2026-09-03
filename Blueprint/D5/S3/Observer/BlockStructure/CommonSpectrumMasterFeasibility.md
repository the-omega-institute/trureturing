# Common-Spectrum Master Feasibility

## Abstract

Finite common-spectrum feasibility is exactly one positive Hermitian Toeplitz moment system, with a real-coordinate reduction on the even branch.

**Theorem 1.1 (One Toeplitz system carries every finite observation).**

$$\forall N \in \mathbb{N}, S \in Type, O \in Type, L \in S \to \operatorname{LinearMap}(\mathbb{R}, \operatorname{Matrix}(\operatorname{Fin}(N + 1), \operatorname{Fin}(N + 1), \mathbb{C}), O), I \in S \to \operatorname{Set}(O),\; \left(\operatorname{AddCommMonoid}(O) \land \operatorname{Module}(\mathbb{R}, O)\right) \Rightarrow \left(\left(\left(\exists mu \in \operatorname{FiniteMeasure}(Circle),\; \forall s \in S,\; L(s)(\operatorname{toeplitzMatrix}(\operatorname{circleMoment}(mu), N)) \in I(s)\right) \Leftrightarrow \left(\exists y \in \mathbb{Z} \to \mathbb{C},\; \left(\left(\operatorname{PosSemidef}(\operatorname{toeplitzMatrix}(y, N)) \land \left(\forall k \in \mathbb{Z},\; \operatorname{natAbs}(k) \le N \Rightarrow y({-k}) = {y(k)}^{*}\right)\right) \land \left(\forall s \in S,\; L(s)(\operatorname{toeplitzMatrix}(y, N)) \in I(s)\right)\right) \land \exists! x: \operatorname{Fin}(2 \cdot (N + 1) - 1) \to \mathbb{R}, \forall k \in \mathbb{Z},\; \operatorname{natAbs}(k) \le N \Rightarrow \operatorname{hermitianMomentCoordinates}(N, x, k) = y(k)\right)\right) \land \left(\left(\exists mu \in \operatorname{FiniteMeasure}(Circle),\; \operatorname{map}(mu, inv) = mu \land \left(\forall s \in S,\; L(s)(\operatorname{toeplitzMatrix}(\operatorname{circleMoment}(mu), N)) \in I(s)\right)\right) \Leftrightarrow \left(\exists y \in \mathbb{Z} \to \mathbb{C},\; \left(\left(\left(\operatorname{PosSemidef}(\operatorname{toeplitzMatrix}(y, N)) \land \left(\forall k \in \mathbb{Z},\; \operatorname{natAbs}(k) \le N \Rightarrow y({-k}) = {y(k)}^{*}\right)\right) \land \left(\forall k \in \mathbb{Z},\; \operatorname{natAbs}(k) \le N \Rightarrow y({-k}) = y(k)\right)\right) \land \left(\forall s \in S,\; L(s)(\operatorname{toeplitzMatrix}(y, N)) \in I(s)\right)\right) \land \exists! x: \operatorname{Fin}(N + 1) \to \mathbb{R}, \forall k \in \mathbb{Z},\; \operatorname{natAbs}(k) \le N \Rightarrow \operatorname{realEvenMomentCoordinates}(N, x, k) = y(k)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BlockStructure/CommonSpectrumMasterFeasibility.common_spectrum_master_feasibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive-spectrum side is carried by an actual finite positive measure on the circle. Each supplied linear observation acts on the same truncated Toeplitz moment matrix.

The reverse implication applies the frozen finite Toeplitz moment representation theorem after extending the supplied Hermitian window by zero outside its stated depth.

A Hermitian window is uniquely encoded by one real center and its positive complex moments, giving 2(N+1)-1 real coordinates. The real even branch is uniquely encoded by N+1 real values.

## References

- Truth anchor: `D5/S3/Observer/BlockStructure/CommonSpectrumMasterFeasibility.common_spectrum_master_feasibility`
- Dependency: [D5/S3/Weil/CayleyLaguerre/TruncatedCircleMomentBridge](../../Weil/CayleyLaguerre/TruncatedCircleMomentBridge.md)
- Dependency: [D5/S3/Weil/TestFunctions/LiCurvatureCriterion](../../Weil/TestFunctions/LiCurvatureCriterion.md)
