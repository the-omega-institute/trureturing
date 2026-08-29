# Finite Moment Infeasibility Certificate

## Abstract

Infeasibility of the finite interval-constrained positive-semidefinite moment problem excludes every compatible real-axis even positive completion.

**Theorem 1.1 (Finite SDP infeasibility is a strict completion certificate).**

$$\forall N: \mathbb{N}, Rlower, Rupper: \mathbb{R},\\{}target: \mathbb{R} \to \operatorname{Fin}\left(N + 1\right) \to \mathbb{R}, tau: \operatorname{Fin}\left(N + 1\right) \to \mathbb{R},\\{}T: (\operatorname{Fin}\left(N + 1\right) \to \mathbb{R}) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(N + 1\right), \operatorname{Fin}\left(N + 1\right), \mathbb{R}\right), C: \operatorname{Type},\\{}RealAxis, Even, Positive, LocalSource, CayleyCompact: C \to \operatorname{Prop},\\{}B: C \to \mathbb{R}, m: C \to \operatorname{Fin}\left(N + 1\right) \to \mathbb{R},\\{}(\forall c: C, m(c)(0) = B(c)) \Rightarrow\\{}(\forall c: C, RealAxis(c) \land Even(c) \land Positive(c) \land LocalSource(c) \land CayleyCompact(c) \Rightarrow \forall i: \operatorname{Fin}\left(N + 1\right), \operatorname{abs}\left(m(c)(i) - target(B(c))(i)\right) \leq B(c) \cdot tau(i)) \Rightarrow\\{}(\forall c: C, RealAxis(c) \land Even(c) \land Positive(c) \land CayleyCompact(c) \Rightarrow \operatorname{PosSemidef}\left(T(m(c))\right)) \Rightarrow\\{}(\neg \exists R: \mathbb{R}, v: \operatorname{Fin}\left(N + 1\right) \to \mathbb{R}, Rlower \leq R \land R \leq Rupper \land v(0) = R \land\\{}(\forall i: \operatorname{Fin}\left(N + 1\right), \operatorname{abs}\left(v(i) - target(R)(i)\right) \leq R \cdot tau(i)) \land \operatorname{PosSemidef}\left(T(v)\right)) \Rightarrow\\{}\neg \exists c: C, RealAxis(c) \land Even(c) \land Positive(c) \land LocalSource(c) \land Rlower \leq B(c) \land B(c) \leq Rupper \land CayleyCompact(c).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/FiniteMomentInfeasibilityCertificate.finite_moment_infeasibility_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hypotheses expose the completion-to-moment construction, its zero moment, every source interval, and the Toeplitz positivity law.

A putative real-axis even positive completion with local-source consistency, an in-range resolvent budget, and a Cayley compactification would therefore construct the forbidden SDP witness.

## References

- Truth anchor: `D5/S3/Weil/Budget/FiniteMomentInfeasibilityCertificate.finite_moment_infeasibility_certificate`
