# Nonlinear Brézis–Lieb defect

## Abstract

Full nonlinear cancellation on arbitrary measure spaces, without separate integrability of the two terms.

The universe u, measurable space Omega and measure mu are arbitrary. The nonlinearity j maps Complex to Complex. The families phi and psi have type Real -> Complex -> Real. The predicate admissible(epsilon) means 0 < epsilon and epsilon < epsilon0. The function g has type Omega -> Complex, v has type Nat -> Omega -> Complex, and M is a finite NNReal bound. Write A(n)(x) = j(g(x)+v(n)(x)) - j(v(n)(x)) and D(n)(x) = A(n)(x) - j(g(x)). For a real function h on Omega, mass(h) = lintegral mu (x maps to ENNReal.ofReal(h(x))). The coercion ofNNReal embeds M into ENNReal. Integral and Integrable use Bochner integration in the stated value space. AE(mu,P) means that P holds mu-almost everywhere.

**Theorem 1.1 (Integrable cancellation and full L1 decay).**

$$\begin{aligned}\forall Omega: Type_{u}, [\operatorname{MeasurableSpace}\left(Omega\right)]\\\forall mu: \operatorname{Measure}\left(Omega\right), \forall j: Complex \to Complex, \\(\operatorname{Continuous}\left(j\right) \land j(0) = 0) \Rightarrow\\\forall epsilon0: Real, 0 < epsilon0 \Rightarrow\\\forall phi: Real \to Complex \to Real, \forall psi: Real \to Complex \to Real, \\(\forall epsilon: Real, \operatorname{admissible}\left(epsilon\right) \Rightarrow\operatorname{Continuous}\left(phi(epsilon)\right) \land (\forall z: Complex, 0 \leq phi(epsilon)(z))) \Rightarrow\\(\forall epsilon: Real, \operatorname{admissible}\left(epsilon\right) \Rightarrow(\forall z: Complex, 0 \leq psi(epsilon)(z))) \Rightarrow\\(\forall epsilon: Real, \operatorname{admissible}\left(epsilon\right) \Rightarrow\forall a: Complex, \forall b: Complex, \\\Vert j(a + b) - j(a)\Vert  \leq epsilon phi(epsilon)(a) + psi(epsilon)(b)) \Rightarrow\\\forall M: NNReal, \forall g: Omega \to Complex, \forall v: Nat \to Omega \to Complex, \\\operatorname{AEStronglyMeasurable}\left(g, mu\right) \Rightarrow\\(\forall n: Nat, \operatorname{AEStronglyMeasurable}\left(v(n), mu\right)) \Rightarrow\\\operatorname{AE}\left(mu, (x \mapsto \operatorname{Tendsto}\left((n \mapsto v(n)(x)), atTop, \operatorname{nhds}\left(0\right)\right))\right) \Rightarrow\\\operatorname{Integrable}\left((x \mapsto j(g(x))), mu\right) \Rightarrow\\(\forall epsilon: Real, \operatorname{admissible}\left(epsilon\right) \Rightarrow\operatorname{Integrable}\left((x \mapsto psi(epsilon)(g(x))), mu\right)) \Rightarrow\\(\forall epsilon: Real, \operatorname{admissible}\left(epsilon\right) \Rightarrow\forall n: Nat, \operatorname{mass}\left((x \mapsto phi(epsilon)(v(n)(x)))\right) \leq \operatorname{ofNNReal}\left(M\right)) \Rightarrow\\(\forall n: Nat, \operatorname{Integrable}\left(A(n), mu\right) \land \operatorname{Integrable}\left(D(n), mu\right))\\\land \operatorname{Tendsto}\left((n \mapsto \operatorname{integral}\left(mu, (x \mapsto \Vert D(n)(x)\Vert )\right)), atTop, \operatorname{nhds}\left(0\right)\right)\\\land \operatorname{Tendsto}\left((n \mapsto \operatorname{integral}\left(mu, A(n)\right)), atTop, \operatorname{nhds}\left(\operatorname{integral}\left(mu, (x \mapsto j(g(x)))\right)\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/BrezisLiebNonlinearDefect.brezis_lieb_nonlinear_defect` (`✓ std3`). ∎

*Citation.* Haïm Brézis and Elliott H. Lieb (1983). *A relation between pointwise convergence of functions and convergence of functionals*. DOI: [10.1090/S0002-9939-1983-0699419-3](https://doi.org/10.1090/S0002-9939-1983-0699419-3). URL: <https://sites.math.rutgers.edu/~brezis/PUBlications/99-journal.pdf>.

*Commentary.*

The function j is continuous and vanishes at zero. For every admissible epsilon, phi(epsilon) is continuous and nonnegative, psi(epsilon) is nonnegative, and their increment inequality holds for every pair of complex a and b. The same finite M bounds the nonnegative integrals of phi(epsilon,v(n)) for every admitted epsilon and every n. The function j(g) is integrable, as is each psi(epsilon,g). Both g and every v(n) are almost-everywhere strongly measurable, and v(n) tends almost everywhere to zero.

Every A(n) and D(n) is integrable. The integrals of norm(D(n)) tend to zero, and the complex integrals of A(n) tend to the integral of j(g). Individual integrability of j(g+v(n)) and j(v(n)) is absent. No finite or sigma-finite measure, common integrable dominator, uniform integrability, separate energy convergence or subsequence is assumed.

A fixed admitted epsilon first gives integrability of A(n) through its increment bound. Continuity and j(0)=0 give almost-everywhere cancellation. For an arbitrary positive error coefficient, choose an admitted smaller coefficient. The nonnegative error is bounded by that coefficient times phi applied to v(n), plus psi applied to g and norm(j(g)). The common epsilon-domination theorem therefore yields full L1 decay. The integral norm inequality then gives the complex integral limit. Only fixed-epsilon integrability of the compensation term is required; it need not tend to zero with epsilon.

This is the complex arbitrary-measure statement of Brézis–Lieb Theorem 2, including the separate-integrability boundary in Remark (i) and strong L1 conclusion in Remark (ii). The existing positive-power theorem uses the same extracted integral-control inference. The growth estimate and mass hypotheses still have to be established for any new integrand or application; the theorem supplies no additional compactness, nonvanishing or PDE existence premise.

## References

- Truth anchor: `D5/S3/Topology/Measures/BrezisLiebNonlinearDefect.brezis_lieb_nonlinear_defect`
- Dependency: [D5/S3/Topology/Measures/IntegralEpsilonDomination](IntegralEpsilonDomination.md)
