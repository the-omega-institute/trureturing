# Archimedean Confinement

## Abstract

Proper growth of the completed-zeta frequency multiplier confines each strict sublevel to finitely many symmetric bounded open intervals.

**Theorem 1.1 (The dangerous frequency set is bounded, symmetric, and interval-finite).**

$$\begin{aligned}\forall L, a: \mathbb{R},\\{}\operatorname{Tendsto}\left((xi: \mathbb{R} \mapsto 2 \pi (\operatorname{mu}\left(xi\right) + \operatorname{PX}\left(\operatorname{exp}\left(2L\right), xi\right))), \operatorname{cocompact}\left(\mathbb{R}\right), atTop\right) \Rightarrow\\{}\operatorname{let} B := \{xi \in \mathbb{R} | 2 \pi (\operatorname{mu}\left(xi\right) + \operatorname{PX}\left(\operatorname{exp}\left(2L\right), xi\right)) < a\},\\{}\operatorname{IsBounded}\left(B\right) \land -B = B \land\\{}\exists I: \operatorname{Finset}\left(\mathbb{R} \times \mathbb{R}\right), B = \operatorname{iUnion}\left(p \in I, \operatorname{Ioo}\left(\operatorname{fst}\left(p\right), \operatorname{snd}\left(p\right)\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/ArchimedeanConfinement.archimedean_confinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The multiplier is the canonical two-pi rescaling of the existing digamma density mu plus the finite von Mangoldt cosine polynomial PX at exp(2L). The displayed Tendsto premise is the previously established proper-growth clause.

Analytic isolated zeros make the threshold level finite inside a compact confinement set. Each connected component is the open interval between its infimum and supremum; both endpoints lie in the finite frontier, giving the displayed finite index set.

Repository and pinned-Mathlib searches found no exact existing theorem. The proof directly reuses Zeta23.mu, Zeta23.PX, mu_even, differentiableAt_digamma, analytic isolated-zero codiscreteness, and compact codiscrete finiteness.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/ArchimedeanConfinement.archimedean_confinement`
