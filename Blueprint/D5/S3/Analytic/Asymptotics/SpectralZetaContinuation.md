# Spectral Zeta Continuation

## Abstract

Linear spectral density continues the spectral zeta function with residue c.

**Theorem 1.1 (Linear density continues the spectral zeta function).**

$$\begin{aligned}\forall \lambda: \mathbb{N}\to\mathbb{R}, c: \mathbb{R};\\{}\left(Z_{\lambda}\right)\left(s\right) := \sum_{n: \mathbb{N}} (\lambda\left(n\right):\mathbb{C})^{-s};\\{}\left(N_{\lambda}\right)\left(u\right) := \operatorname{card}(\{n \in \mathbb{N} \mid \lambda\left(n\right) \leq u\});\\{}\left(Zc_{\lambda}\right)\left(s\right) := \operatorname{continuedSpectralZeta}(\lambda, c, s);\\{}(\forall n: \mathbb{N}, 0 < \lambda\left(n\right)) \land \operatorname{StrictMono}(\lambda) \land\\{}(\forall u: \mathbb{R}, \operatorname{Finite}(\{n \in \mathbb{N} \mid \lambda\left(n\right) \leq u\})) \land \operatorname{IsBigO}(atTop, u \mapsto \left(N_{\lambda}\right)\left(u\right) - c u, u \mapsto 1) \Rightarrow\\{}(\operatorname{MeromorphicOn}(Zc_{\lambda}, \{s \in \mathbb{C} \mid 0 < \Re(s)\}) \land \forall s: \mathbb{C}, 1 < \Re(s) \Rightarrow \left(Zc_{\lambda}\right)\left(s\right) = \left(Z_{\lambda}\right)\left(s\right)) \land\\{}\operatorname{Tendsto}((s: \mathbb{C}) \mapsto (s - 1) \left(Zc_{\lambda}\right)\left(s\right), \operatorname{nhdsWithin}(1, \mathbb{C} \setminus \{1\}), \operatorname{nhds}((c:\mathbb{C}))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/SpectralZetaContinuation.linear_density_spectral_zeta_continuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let lambda be a positive strictly increasing real spectrum with finite sublevel sets. Its counting function N_lambda(u) is the cardinality of the indices whose spectral value is at most u, and the stated density hypothesis is N_lambda(u)-c u=O(1) at infinity.

The Lean sequence is zero-indexed: its term lambda(0) carries the source term lambda_1. Thus the displayed sum over natural indices is the source series Z_lambda(s)=sum_{n at least 1} lambda_n^{-s} under the canonical index shift.

The named function continuedSpectralZeta(lambda,c) is meromorphic on the open half-plane Re(s)>0 and agrees with the spectral Dirichlet series at every point of its original half-plane Re(s)>1. Both clauses are present in the Lean continuation predicate.

Its residue at s=1 is represented by the exact punctured-neighborhood limit of (s-1) times the continuation, which tends to c. This is a direct-theorem-layer consequence of the local density assumptions and uses no Riemann hypothesis or other unproved conjecture.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/SpectralZetaContinuation.linear_density_spectral_zeta_continuation`
- Dependency: [D5/S3/Analytic/Asymptotics/FiniteCountertermMellinContinuation](FiniteCountertermMellinContinuation.md)
- Dependency: [D5/S3/Analytic/Asymptotics/LinearDensityHeatTrace](LinearDensityHeatTrace.md)
