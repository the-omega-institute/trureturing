# Archimedean Convergence

## Abstract

Every repository Weil test function is archimedean-convergent, so the prime-side Weil criterion needs no separate integrability hypothesis.

**Theorem 1.1 (Every Weil test function is archimedean-convergent).**

$$\forall g \in WeilTestFunction,\; \operatorname{Integrable}\left((t \mapsto \operatorname{archimedeanIntegrand}\left(g, t\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/ArchimedeanConvergence.archimedeanConvergent_of_weilTestFunction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here WeilTestFunction is this repository's even, smooth, compactly supported test-function carrier. Closed-strip decay of its Fourier-Laplace transform supplies quadratic decay on the real axis.

The digamma vertical-growth bound needed for integrability comes from this repository's Zeta23 layer. The pinned Mathlib has no corresponding bound; the proof binds the frozen Zeta23 gamma-factor integrability theorem and gamma bracket.

**Theorem 1.2 (RH is equivalent to prime-side positivity without hArch).**

$$\forall Z \in ZeroData,\; \operatorname{RiemannHypothesis} \Leftrightarrow \left(\forall g \in WeilTestFunction,\; 0 \le \Re (\operatorname{poleTerm}\left(\operatorname{convolutionSquare}\left(g\right)\right) - \operatorname{primeTerm}\left(\operatorname{convolutionSquare}\left(g\right)\right) + \operatorname{archimedeanTerm}\left(\operatorname{convolutionSquare}\left(g\right), \operatorname{archimedeanConvergentOfWeilTestFunction}\left(\operatorname{convolutionSquare}\left(g\right)\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/ArchimedeanConvergence.rh_iff_primeSidePositivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen explicit-formula Weil criterion is instantiated with the preceding convergence theorem for each convolution square. No new explicit-formula or Weil-positivity argument is reproved.

The equivalence is relative to a supplied ZeroData only. Existence of ZeroData is not asserted, and M1-b remains open.

Its quantifier ranges over this repository's WeilTestFunction. This hArch-free reformulation is not a proof of the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Weil/Separator/ArchimedeanConvergence.archimedeanConvergent_of_weilTestFunction`
- Truth anchor: `D5/S3/Weil/Separator/ArchimedeanConvergence.rh_iff_primeSidePositivity`
- Dependency: [D5/S3/Weil/Separator/ExplicitFormulaWeilCriterion](ExplicitFormulaWeilCriterion.md)
- Dependency: [D5/S3/Weil/TestFunctions/FourierLaplaceClosedStripDecay](../TestFunctions/FourierLaplaceClosedStripDecay.md)
