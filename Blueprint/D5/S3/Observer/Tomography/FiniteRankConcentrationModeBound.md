# Finite-Rank Concentration Mode Bound

## Abstract

A finite trace budget bounds and finitely supports every positive spectral superlevel.

**Theorem 1.1 (Finite trace permits only finitely many strong modes).**

$$\begin{gathered}\forall \lambda: \mathbb{N} \to \mathbb{R}, L, m, eta \in \mathbb{R},\\(\forall j \in \mathbb{N}, 0 \leq \lambda\left(j\right)) \land \operatorname{Summable}\left(\lambda\right) \land \sum_{j=0}^{\infty} \lambda\left(j\right) = \frac{L m}{\pi} \land 0 < eta \Rightarrow\\\operatorname{Finite}\left(\{j \in \mathbb{N} \mid eta \leq \lambda\left(j\right)\}\right) \land \operatorname{ncard}\left(\{j \in \mathbb{N} \mid eta \leq \lambda\left(j\right)\}\right) \leq \frac{L m}{\pi eta}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Tomography/FiniteRankConcentrationModeBound.finite_rank_concentration_mode_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let lambda be a nonnegative summable sequence of concentration eigenvalues. Its trace is the interval radius L times the finite frequency measure m, divided by pi.

For every positive threshold eta, summability forces the eta-superlevel set to be finite. The frozen innovation-count owner then bounds its cardinality by the total trace divided by eta, which is exactly L m divided by pi eta.

Repository search found the frozen general count owner and this theorem applies it directly. Pinned Mathlib has the supporting convergence and finite-sum estimates but no theorem exposing both finiteness and the trace-normalized cardinality bound.

## References

- Truth anchor: `D5/S3/Observer/Tomography/FiniteRankConcentrationModeBound.finite_rank_concentration_mode_bound`
- Dependency: [D5/S3/Observer/Tomography/InnovationCountBound](InnovationCountBound.md)
