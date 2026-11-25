# Brézis–Lieb power defect

## Abstract

Full L1 power splitting for complex functions on an arbitrary measure space.

The universe u, measurable space Omega and measure mu are arbitrary. Real powers are taken of nonnegative norms. Write r(n)(x) = f(n)(x) - g(x), d(n)(x) = norm(f(n)(x))^p - norm(r(n)(x))^p - norm(g(x))^p, A(h) = lintegral mu (x maps to enorm(h(x))^p), and E(h) = integral mu (x maps to norm(h(x))^p). The coercion ofNNReal sends the finite nonnegative bound M into ENNReal. AE(mu,P) means that P holds mu-almost everywhere; Integrable is real Bochner integrability.

**Theorem 1.1 (Full absolute defect and signed energy splitting).**

$$\begin{aligned}\forall Omega: Type_{u}, [\operatorname{MeasurableSpace}\left(Omega\right)]\\\forall mu: \operatorname{Measure}\left(Omega\right), \forall p: Real, 0 < p \Rightarrow\\\forall M: NNReal, \forall f: Nat \to Omega \to Complex, \forall g: Omega \to Complex, \\(\forall n: Nat, \operatorname{AEStronglyMeasurable}\left(f(n), mu\right)) \Rightarrow\\\operatorname{AE}\left(mu, (x \mapsto \operatorname{Tendsto}\left((n \mapsto f(n)(x)), atTop, \operatorname{nhds}\left(g(x)\right)\right))\right) \Rightarrow\\(\forall n: Nat, \operatorname{A}\left(f(n)\right) \leq \operatorname{ofNNReal}\left(M\right)) \Rightarrow\\\operatorname{AEStronglyMeasurable}\left(g, mu\right)\\\land \operatorname{A}\left(g\right) \leq \operatorname{ofNNReal}\left(M\right)\\\land \operatorname{Integrable}\left((x \mapsto \Vert g(x)\Vert ^{p}), mu\right)\\\land (\forall n: Nat, \operatorname{Integrable}\left((x \mapsto \Vert f(n)(x)\Vert ^{p}), mu\right) \land \operatorname{Integrable}\left((x \mapsto \Vert r(n)(x)\Vert ^{p}), mu\right) \land \operatorname{Integrable}\left(d(n), mu\right))\\\land \operatorname{Tendsto}\left((n \mapsto \operatorname{integral}\left(mu, (x \mapsto \lvert d(n)(x)\rvert )\right)), atTop, \operatorname{nhds}\left(0\right)\right)\\\land \operatorname{Tendsto}\left((n \mapsto \operatorname{E}\left(f(n)\right) - \operatorname{E}\left(r(n)\right)), atTop, \operatorname{nhds}\left(\operatorname{E}\left(g\right)\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/BrezisLiebPowerDefect.brezis_lieb_power_defect` (`✓ std3`). ∎

*Citation.* Haïm Brézis and Elliott H. Lieb (1983). *A relation between pointwise convergence of functions and convergence of functionals*. DOI: [10.1090/S0002-9939-1983-0699419-3](https://doi.org/10.1090/S0002-9939-1983-0699419-3). URL: <https://sites.math.rutgers.edu/~brezis/PUBlications/99-journal.pdf>.

*Commentary.*

The assumptions are almost-everywhere strong measurability of every f(n), almost-everywhere convergence of the whole sequence to g, and the common finite positive-power mass bound. The conclusions include measurability and the same mass bound for g, integrability of its power, integrability of each original power, residual power and real defect, convergence to zero of the integral of the absolute defect, and the signed difference of the two energies tending to the energy of g.

Fatou's lemma gives the limit mass bound. The Lp algebra gives integrability of the residual powers, also when 0 < p < 1. The scalar estimate below separates a small multiple of the original power from an integrable multiple of the limit power. For fixed positive epsilon, F(n)(x) = max(abs(d(n)(x)) - epsilon norm(f(n)(x))^p, 0) is bounded by (C + 1) norm(g(x))^p and tends almost everywhere to zero. Dominated convergence applies to F. The integral of abs(d(n)) is at most epsilon M plus the integral of F(n). Letting epsilon decrease to zero gives the full L1 conclusion. The integral norm inequality and the explicit integrability statements then give signed splitting.

For every p > 0 and epsilon > 0 there is a nonnegative real C such that, for all complex a and b, abs(norm(a+b)^p - norm(a)^p) <= epsilon norm(a)^p + C norm(b)^p. Continuity of the power at one handles b small relative to a; the complementary case bounds a by a multiple of b. This is the power estimate used in the proof, with no differentiability or convexity assumption.

There is no finiteness, sigma-finiteness, semifiniteness or completeness assumption on mu. No common dominator, uniform integrability, tightness, weak convergence, subsequence or convergence of the individual energies is assumed. Empty spaces, zero measures, M = 0, g = 0, p = 1, fractional p below one, noninteger p above one and arbitrary complex phases are included.

A nonzero example on the natural numbers with counting measure is g(k) = i at k = 0 and zero elsewhere, while f(n)(k) = i at k = 0 or k = n+1 and zero elsewhere. For every p > 0, the original power mass is two, the limit power mass is one, and the residual pulse has power mass one. The defect is identically zero. The moving residual does not tend to zero in power mass, and the original sequence has no common integrable power dominator. Splitting therefore does not assert strong Lp convergence of the original sequence.

The strong L1 statement is the power specialization of Theorem 2, Remark (ii) and Example (a) in Brézis and Lieb's 1983 paper. Theorem 1 separately states signed splitting. The application after (2.25) in arXiv:2611.26428v1 combines signed nonlinear splitting with separate kinetic estimates and nonvanishing information; the power theorem alone supplies neither of those inputs.

## References

- Truth anchor: `D5/S3/Topology/Measures/BrezisLiebPowerDefect.brezis_lieb_power_defect`
