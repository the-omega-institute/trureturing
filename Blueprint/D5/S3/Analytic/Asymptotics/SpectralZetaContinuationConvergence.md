# Spectral Zeta Continuation With Convergence

## Abstract

Linear spectral density yields a convergent spectral series and its meromorphic continuation.

**Theorem 1.1 (Linear density gives convergence, continuation, and residue).**

$$\begin{aligned}\forall \lambda: \mathbb{N}\to\mathbb{R}, c: \mathbb{R};\\{}\left(Z_{\lambda}\right)\left(s\right) := \sum_{n: \mathbb{N}} (\lambda\left(n\right):\mathbb{C})^{-s};\\{}\left(Zc_{\lambda}\right)\left(s\right) := \operatorname{continuedSpectralZeta}(\lambda, c, s);\\{}(\forall n: \mathbb{N}, 0 < \lambda\left(n\right)) \land \operatorname{StrictMono}(\lambda) \land\\{}(\forall u: \mathbb{R}, \operatorname{Finite}(\{n \in \mathbb{N} \mid \lambda\left(n\right) \leq u\})) \land \operatorname{IsBigO}(atTop, u \mapsto \left(N_{\lambda}\right)\left(u\right) - c u, u \mapsto 1) \Rightarrow\\{}(\operatorname{MeromorphicOn}(Zc_{\lambda}, \{s \in \mathbb{C} \mid 0 < \Re(s)\}) \land \forall s: \mathbb{C}, 1 < \Re(s) \Rightarrow \left(Zc_{\lambda}\right)\left(s\right) = \left(Z_{\lambda}\right)\left(s\right)) \land\\{}\forall s: \mathbb{C}, 1 < \Re(s) \Rightarrow \operatorname{Summable}((n: \mathbb{N}) \mapsto (\lambda\left(n\right):\mathbb{C})^{-s}) \land\\{}\operatorname{Tendsto}((s: \mathbb{C}) \mapsto (s - 1) \left(Zc_{\lambda}\right)\left(s\right), \operatorname{nhdsWithin}(1, \mathbb{C} \setminus \{1\}), \operatorname{nhds}((c:\mathbb{C}))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/SpectralZetaContinuationConvergence.linear_density_spectral_zeta_continuation_with_convergence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let lambda be a positive strictly increasing real spectrum with finite sublevel sets. Its counting function N_lambda(u) counts the indices whose spectral value is at most u, and the density hypothesis is N_lambda(u)-c u=O(1) at infinity.

The named continued spectral zeta function is meromorphic on Re(s)>0 and agrees with the displayed spectral Dirichlet series on Re(s)>1. The statement separately exposes summability of the exact complex terms lambda(n)^(-s) throughout that initial half-plane, so the displayed series is not merely a totalized infinite sum.

The continuation also has residue c at s=1, expressed as the exact punctured-neighborhood limit of (s-1) times the continuation. The continuation and residue clauses reuse the frozen owner theorem; the new proof supplies only the previously private convergence witness.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/SpectralZetaContinuationConvergence.linear_density_spectral_zeta_continuation_with_convergence`
- Dependency: [D5/S3/Analytic/Asymptotics/SpectralZetaContinuation](SpectralZetaContinuation.md)
