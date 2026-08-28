# Finite Toroidal Frame Reconstruction

## Abstract

A compact pointwise-nonvanishing twist cover yields finite weighted frames that reconstruct the completed-zeta amplitude.

**Theorem 1.1 (Finite weighted period frames reconstruct xi).**

$$\forall Index \in \operatorname{Type}\left(\right), K \in \operatorname{Set}\left(\operatorname{Complex}\left(\right)\right), P \in Index \to \left(\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)\right), T \in Index \to \left(\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)\right),\; \left(\left(\forall i \in Index,\; \operatorname{Continuous}\left(T\left(i\right)\right)\right) \land \left(\left(\forall i \in Index, s \in \operatorname{Complex}\left(\right),\; P\left(i\right)\left(s\right) = xiReading\left(s\right) \times T\left(i\right)\left(s\right)\right) \land \left(\operatorname{IsCompact}\left(K\right) \land \left(\forall s \in \operatorname{Complex}\left(\right),\; \operatorname{mem}\left(s, K\right) \Rightarrow \left(\exists i \in Index,\; T\left(i\right)\left(s\right) \ne 0\right)\right)\right)\right)\right) \Rightarrow \left(\exists I \in \operatorname{Finset}\left(Index\right),\; \left(\forall s \in \operatorname{Complex}\left(\right),\; \operatorname{mem}\left(s, K\right) \Rightarrow \left(\exists i \in Index,\; \operatorname{mem}\left(i, I\right) \land T\left(i\right)\left(s\right) \ne 0\right)\right) \land \left(\forall w \in Index \to \operatorname{Real}\left(\right),\; \left(\forall i \in Index,\; \operatorname{mem}\left(i, I\right) \Rightarrow 0 < w\left(i\right)\right) \Rightarrow \left(\forall s \in \operatorname{Complex}\left(\right),\; \operatorname{mem}\left(s, K\right) \Rightarrow \left(\operatorname{weightedFrame}\left(I, w, T, s\right) \ne 0 \land xiReading\left(s\right) = \frac{\operatorname{inner}\left(\operatorname{Complex}\left(\right), \operatorname{weightedFrame}\left(I, w, T, s\right), \operatorname{weightedFrame}\left(I, w, P, s\right)\right)}{\left\lVert \operatorname{weightedFrame}\left(I, w, T, s\right) \right\rVert^{2}}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/FiniteToroidalFrameReconstruction.finite_toroidal_frame_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuity makes each twist-nonvanishing locus open. Compactness then extracts a finite subcover from the pointwise nonvanishing family.

Positive square-root weights construct a nonzero complex Euclidean carrier frame at every point of the window. The period factorization constructs the observed frame as its canonical xi multiple.

The displayed inner product is ordered carrier first because Lean is conjugate linear in its first argument. It therefore represents the source convention that is linear in the period-frame argument.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/FiniteToroidalFrameReconstruction.finite_toroidal_frame_reconstruction`
- Dependency: [D5/S3/Analytic/Adelic/ToroidalCechCompletion](ToroidalCechCompletion.md)
