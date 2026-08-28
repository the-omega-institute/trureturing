# Finite Prime-Time Rectangle Certificate

## Abstract

A finite dimension-bounded quantum certificate extends to a finite rectangular window.

**Theorem 1.1 (A complete effect family has a complete finite rectangle).**

$$\forall d\in \mathbb{N}, \operatorname{NeZero}\left(d\right),\\{}E: \mathbb{N}\times\mathbb{N} \to \operatorname{HermitianTraceZero}\left(\operatorname{Fin}\left(d\right)\right),\\{}\operatorname{span}\left(\mathbb{R}, \operatorname{range}\left(E\right)\right) = \operatorname{top}\left(\right) \Rightarrow\\{}\exists S: \operatorname{Finset}\left(\mathbb{N}\times\mathbb{N}\right), \operatorname{card}\left(S\right) \leq d^{2} - 1 \land\\{}\operatorname{span}\left(\mathbb{R}, \operatorname{range}\left(\operatorname{restrict}\left(E, S\right)\right)\right) = \operatorname{top}\left(\right) \land\\{}(\forall \rho, \sigma: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), (\forall q\in S, \Re(\operatorname{Tr}\left(\operatorname{matrix}\left(\rho\right) E\left((\operatorname{fst}\left(q\right), \operatorname{snd}\left(q\right))\right)\right)) = \Re(\operatorname{Tr}\left(\operatorname{matrix}\left(\sigma\right) E\left((\operatorname{fst}\left(q\right), \operatorname{snd}\left(q\right))\right)\right))) \Rightarrow \rho = \sigma) \land\\{}\text{let } J := \operatorname{image}\left(fst, S\right); T := 1 + \operatorname{sup}\left(snd, S\right);\\{}\forall \rho, \sigma: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), (\forall p\in J, t\in \mathbb{N}, t < T, \Re(\operatorname{Tr}\left(\operatorname{matrix}\left(\rho\right) E\left((p, t)\right)\right)) = \Re(\operatorname{Tr}\left(\operatorname{matrix}\left(\sigma\right) E\left((p, t)\right)\right))) \Rightarrow \rho = \sigma.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PredictionDepth/FinitePrimeTimeRectangleCertificate.finite_prime_time_rectangle_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The input family consists of centered effects on the canonical real trace-zero Hermitian carrier. If its full real span is the carrier, at most d squared minus one concrete index-time pairs already span it and separate all density states.

From those pairs, J is constructed as their first-coordinate image and T as one plus the supremum of their second coordinates. Every selected pair lies in J times the times below T, so equality on the whole rectangle implies equality on the selected certificate.

The proof imports the frozen finite-pair certificate and adds only the canonical finite-rectangle construction required by the source.

## References

- Truth anchor: `D5/S3/Quantum/PredictionDepth/FinitePrimeTimeRectangleCertificate.finite_prime_time_rectangle_certificate`
- Dependency: [D5/S3/Quantum/PredictionDepth/FinitePrimeTimeCertificate](FinitePrimeTimeCertificate.md)
