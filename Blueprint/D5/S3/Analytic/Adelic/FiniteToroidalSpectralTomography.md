# Finite Toroidal Spectral Tomography

## Abstract

A compact spectral window admits a finite normalized toroidal-period family that detects both xi zeros and their multiplicities.

**Theorem 1.1 (Finite toroidal families detect zeros and multiplicities).**

$$\forall Index \in \operatorname{Type}\left(\right), K \in \operatorname{Set}\left(\operatorname{Complex}\left(\right)\right), T \in Index \to \left(\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)\right),\; \left(\left(\forall i \in Index,\; \operatorname{Differentiable}\left(\operatorname{Complex}\left(\right), T\left(i\right)\right)\right) \land \left(\operatorname{IsCompact}\left(K\right) \land \left(\forall s \in \operatorname{Complex}\left(\right),\; \operatorname{mem}\left(s, K\right) \Rightarrow \left(\exists i \in Index,\; T\left(i\right)\left(s\right) \ne 0\right)\right)\right)\right) \Rightarrow \left(\exists I \in \operatorname{Finset}\left(Index\right),\; \{s \in K \mid \forall i \in Index,\; \operatorname{mem}\left(i, I\right) \Rightarrow xiReading\left(s\right) \times T\left(i\right)\left(s\right) = 0\} = \{s \in K \mid xiReading\left(s\right) = 0\} \land \left(\forall rho \in \operatorname{Complex}\left(\right),\; \operatorname{mem}\left(rho, K\right) \Rightarrow \operatorname{analyticOrderAt}\left(xiReading, rho\right) = \operatorname{iInf}\left(i \in I, \operatorname{analyticOrderAt}\left(xiReading \times T\left(i\right), rho\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/FiniteToroidalSpectralTomography.finite_toroidal_spectral_tomography` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The twist-nonvanishing loci cover the compact window. The frozen finite-frame theorem supplies one finite selected subfamily that remains pointwise nonvanishing on that window.

Each normalized period is constructed as xiReading times its twist. The selected common-zero set therefore equals the xi zero set inside the window.

At every point, all selected product orders dominate the xi order, and the selected nonzero twist realizes equality. Thus the finite indexed infimum is the asserted minimum.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/FiniteToroidalSpectralTomography.finite_toroidal_spectral_tomography`
- Dependency: [D5/S3/Analytic/Adelic/FiniteToroidalFrameReconstruction](FiniteToroidalFrameReconstruction.md)
