# Golden Germ Zeta Boundary

## Abstract

At the golden germ convergence boundary, the formal data isolate regularity of the normalized factor as a sufficient missing input.

**Theorem 1.1 (Boundary data isolate regularity as a sufficient missing input).**

$$\begin{aligned}G: \mathbb{C} \to \mathbb{C},\\\forall s\in \mathbb{C}, \operatorname{G}(s) := \prod_{p\in \operatorname{Primes}(\mathbb{N})}(1 - p^{-s \times \varphi^{2}}) \times \sum_{v\in \mathbb{N}}p^{-s \times \operatorname{o5Beta}(v)},\\\exists Zqc: \{s\in \mathbb{C} \mid \frac{1}{\varphi^{3}} < \Re(s)\} \to \mathbb{C},\\(\forall s\in \mathbb{C}, \frac{1}{\varphi^{3}} < \Re(s) \Rightarrow \operatorname{Zqc}(s) = \operatorname{riemannZeta}(\varphi^{2} \times s) \times \operatorname{G}(s)) \land\\\frac{1}{\varphi^{3}} < \frac{1}{\varphi^{2}} \land\\(0 < \Re(\operatorname{G}(\frac{1}{\varphi^{2}})) \land \operatorname{Im}(\operatorname{G}(\frac{1}{\varphi^{2}})) = 0) \land\\(\forall s\in \mathbb{C}, \frac{1}{\varphi^{3}} < \Re(s) \Rightarrow (s - \frac{1}{\varphi^{2}}) \times \operatorname{Zqc}(s) = ((\varphi^{2} \times s - 1) \times \operatorname{riemannZeta}(\varphi^{2} \times s)) \times (\operatorname{G}(s) / \varphi^{2})) \land\\\operatorname{Tendsto}((s: \mathbb{C}) \mapsto (\varphi^{2} \times s - 1) \times \operatorname{riemannZeta}(\varphi^{2} \times s), \operatorname{nhdsWithin}(\frac{1}{\varphi^{2}}, \mathbb{C} \setminus \{\frac{1}{\varphi^{2}}\}), \operatorname{nhds}(1)) \land\\\operatorname{Tendsto}((sigma: \mathbb{R}) \mapsto ((sigma - \frac{1}{\varphi^{2}}) \times \prod_{p\in \operatorname{Primes}(\mathbb{N})}\sum_{v\in \mathbb{N}}p^{-sigma \times \operatorname{o5Beta}(v)}) / \operatorname{G}(sigma), \operatorname{nhdsWithin}(\frac{1}{\varphi^{2}}, \operatorname{Ioi}(\frac{1}{\varphi^{2}})), \operatorname{nhds}(\frac{1}{\varphi^{2}})) \land \operatorname{NeBot}(\operatorname{nhdsWithin}(\frac{1}{\varphi^{2}}, \mathbb{C} \setminus \{\frac{1}{\varphi^{2}}\})).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EulerGerm/GoldenGermZetaBoundary.golden_germ_zeta_boundary_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The point one over phi squared lies strictly to the right of one over phi cubed, so it is inside the continued half-plane. The exact identity isolates the transported zeta residue from G. The frozen real-ray positivity also holds at the boundary itself.

Pinned Mathlib supplies the punctured limit of (z-1) times zeta(z) at z=1. Multiplication by phi squared transports that limit to s=1/phi squared. Restriction to the real ray, frozen factorization, and positive real-ray nonvanishing give the divided-factor limit. The complex punctured source filter is explicitly non-bottom.

STOPPING JUSTIFICATION: the complex-neighborhood conclusion remains Rung 1 and does not establish that the abscissa is a genuine singularity. The divided-factor limit is the real-axis analogue of Rung 2, but pointwise positivity does not prevent G from tending to zero along that ray. Complex Rung 2 needs G nonzero on a punctured complex neighborhood. Continuity of G at one over phi squared is a sufficient future input for Rung 3; it is not asserted here, and the frozen cancellation majorants needed for it are private.

Downward, direct projections and standard equivalences from this conjunction are corollaries without distinct declarations because no consumer, independent semantics, dependency barrier, or substantial proof content was demonstrated. Upward, continuity or complex-neighborhood nonvanishing crosses the identified dependency barrier and has substantial analytic proof content, so it warrants a distinct future regularity contract.

## References

- Truth anchor: `D5/S3/Analytic/EulerGerm/GoldenGermZetaBoundary.golden_germ_zeta_boundary_reduction`
- Dependency: [D5/S3/Analytic/EulerGerm/GoldenGermZetaContinuation](GoldenGermZetaContinuation.md)
