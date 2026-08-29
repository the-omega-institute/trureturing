# Finite Window and Global Boundary

## Abstract

Finite-window sampling floors are positive, while gap approximants force the global floor to vanish.

**Theorem 1.1 (Finite windows are interior and the global limit is boundary).**

$$\forall H \in Type, K \in Type, sampling \in \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), H, K\right), windowAdmissible \in \operatorname{Real}\left(\right) \to \left(H \to Prop\right), probe \in \operatorname{Nat}\left(\right) \to H, probeWindow \in \operatorname{Nat}\left(\right) \to \operatorname{Real}\left(\right),\; \left(\operatorname{NormedAddCommGroup}\left(H\right) \land \left(\operatorname{NormedSpace}\left(\operatorname{Real}\left(\right), H\right) \land \left(\operatorname{NormedAddCommGroup}\left(K\right) \land \left(\operatorname{NormedSpace}\left(\operatorname{Real}\left(\right), K\right) \land \left(\left(\forall L1 \in \operatorname{Real}\left(\right), L2 \in \operatorname{Real}\left(\right),\; L1 \le L2 \Rightarrow \left(\forall f \in H,\; \operatorname{applyTwo}\left(windowAdmissible, L1, f\right) \Rightarrow \operatorname{applyTwo}\left(windowAdmissible, L2, f\right)\right)\right) \land \left(\left(\forall L \in \operatorname{Real}\left(\right),\; L > 0 \Rightarrow \left(\exists f \in H,\; \operatorname{applyTwo}\left(windowAdmissible, L, f\right) \land \left\lVert f \right\rVert = 1\right)\right) \land \left(\left(\forall L \in \operatorname{Real}\left(\right),\; L > 0 \Rightarrow \left(\exists c \in \operatorname{Real}\left(\right),\; c > 0 \land \left(\forall f \in H,\; \operatorname{applyTwo}\left(windowAdmissible, L, f\right) \Rightarrow \operatorname{mul}\left(c, \left\lVert f \right\rVert^{2}\right) \le \left\lVert \operatorname{apply}\left(sampling, f\right) \right\rVert^{2}\right)\right)\right) \land \left(\left(\forall n \in \operatorname{Nat}\left(\right),\; \left\lVert \operatorname{apply}\left(probe, n\right) \right\rVert = 1\right) \land \left(\left(\forall n \in \operatorname{Nat}\left(\right),\; \operatorname{applyTwo}\left(windowAdmissible, \operatorname{apply}\left(probeWindow, n\right), \operatorname{apply}\left(probe, n\right)\right)\right) \land \operatorname{Tendsto}\left((n: \operatorname{Nat}\left(\right) \mapsto \left\lVert \operatorname{apply}\left(sampling, \operatorname{apply}\left(probe, n\right)\right) \right\rVert^{2}), atTop, \operatorname{nhds}\left(0\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{let} floor = L: \operatorname{Real}\left(\right) \mapsto \operatorname{sInf}\left(\left\{\exists f \in H,\; \operatorname{applyTwo}\left(windowAdmissible, L, f\right) \land \left(\left\lVert f \right\rVert = 1 \land r = \left\lVert \operatorname{apply}\left(sampling, f\right) \right\rVert^{2}\right) \mid r \in \operatorname{Real}\left(\right)\right\}\right), \left(\forall L \in \operatorname{Real}\left(\right),\; L > 0 \Rightarrow \operatorname{apply}\left(floor, L\right) > 0\right) \land \operatorname{Tendsto}\left(floor, atTop, \operatorname{nhds}\left(0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaAnalytic/FiniteWindowGlobalBoundary.finite_window_positive_global_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conditional completeness turns each positive frame witness into a strictly positive unit-sphere infimum. Nested admissibility carries each vanishing-energy gap probe into all larger windows, which gives the upper half of the order-topology limit.

## References

- Truth anchor: `D5/S3/Weil/ZetaAnalytic/FiniteWindowGlobalBoundary.finite_window_positive_global_boundary`
- Dependency: [D5/S3/Weil/ZetaAnalytic/WhiteFloorSamplingDuality](WhiteFloorSamplingDuality.md)
