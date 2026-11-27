# Global paired Mellin quadrature

## Abstract

A single estimate compares the positive half-line integral with the entire shifted positive lattice.

**Theorem 1.1 (Absolute summability, integrability, and a global error bound).**

$$\begin{gathered}\forall \beta\in \mathbb{R}, n,K,M\in \mathbb{N},\\{}0\le\beta\le\frac{3}{4} \land 0<n \land 0<K \land 2\cdot n<M \land \frac{M}{n}\le\delta^{-1}\longrightarrow\\{}\operatorname{Summable}\left(i\mapsto\left\lvert \operatorname{sample}\left(\beta, \frac{2}{n}, \frac{i+1}{n}\right)\right\rvert\right) \land \operatorname{IntegrableOn}\left(s\mapsto\operatorname{sample}\left(\beta, 0, s\right), (0,\infty)\right) \land\\{}\left\lvert \int_{(0,\infty)}\operatorname{sample}\left(\beta, 0, s\right)\,ds-\frac{1}{n}\sum_{i=0}^{\infty}\operatorname{sample}\left(\beta, \frac{2}{n}, \frac{i+1}{n}\right)\right\rvert\le\\{}64\cdot \delta^{\frac{3}{2}}+112\cdot \delta^{\frac{1}{4}}+16\cdot n^{-\frac{1}{4}}+\frac{32\cdot \delta^{-\frac{17}{4}}}{n}+8\cdot R^{-\frac{1}{2}}\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/OccupiedMellinGlobalMesh.global_mesh_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set delta equal to K/n and R equal to (M-1)/n. Ratios and powers are real. The size condition forces delta below one half. All integration is with respect to Lebesgue measure on the positive half-line. The sample in the integral is unshifted; the mesh uses the exact shift 2/n.

The discrete blocks are the positive indices below K, the left regular block, the center block, the right regular block through M-1, and the tail beginning at M. The corresponding continuous partition stops the right regular block at M/n, not at R. The continuous tail bound is enlarged using R at most M/n. Each regular block compares the left samples against its integral. The center estimate bounds a larger block, including the right endpoint, so it bounds the half-open center block without counting that endpoint twice.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedMellinGlobalMesh.global_mesh_error`
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedMellinCutoffs](OccupiedMellinCutoffs.md)
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedMellinDiscreteCenter](OccupiedMellinDiscreteCenter.md)
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedMellinDiscreteTails](OccupiedMellinDiscreteTails.md)
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedMellinInterior](OccupiedMellinInterior.md)
