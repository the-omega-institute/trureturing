# Datko Stability

## Abstract

Separate finite squared orbit energies characterize uniform exponential stability on arbitrary real Banach spaces, including the zero space.

**Theorem 1.1 (Squared orbit energy and a common exponential operator bound).**

$$\forall E \in \operatorname{RealBanachSpace}\left(\right),\; \forall S \in \operatorname{StronglyContinuousContractionSemigroup}\left(E\right),\; \left(\forall x \in E,\; \operatorname{IntegrableOn}\left(t\mapsto\left\lVert S\left(\operatorname{toNNReal}\left(t\right)\right)\left(x\right) \right\rVert^{2}, \operatorname{Ioi}\left(0\right), volume\right)\right) \Leftrightarrow \left(\exists M \in \operatorname{Real}\left(\right),\; \exists omega \in \operatorname{Real}\left(\right),\; 1 \le M \land \left(0 < omega \land \left(\forall t \in \operatorname{NNReal}\left(\right),\; \left\lVert S\left(t\right) \right\rVert \le M \cdot \operatorname{exp}\left(-omega \cdot \operatorname{toReal}\left(t\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/DatkoStability.integrable_sq_orbit_iff_exponential_stability` (`✓ std3`). ∎

*Citation.* Roland Schnaubelt (2026). *Evolution Equations, Lemma 4.4*. URL: <https://iana.math.kit.edu/downloads/iana3/schnaubelt/Skripten/evgl-skript.pdf>.

*Commentary.*

Let E be any real Banach space in any universe: a normed additive commutative group, a real normed vector space, and a complete space. Let S be a strongly continuous contraction semigroup of continuous real linear endomorphisms of E. Thus S(0) is the identity, S(s+t)=S(s) composed with S(t), every operator norm is at most one, and every vector orbit is continuous. The formula uses real Lebesgue measure volume and Ioi(0)=(0,infinity). Real.toNNReal only extends the nonnegative-time orbit to a function on the reals; its values at negative times do not enter the energy condition.

For every vector x separately, require integrability of the real function t maps to norm(S(Real.toNNReal(t))x)^2 on Ioi(0). This is equivalent to existence of a single real pair M, omega with M>=1 and omega>0 such that norm(S(t))<=M*exp(-omega*t) for every nonnegative real t. The pair is independent of the vector and of time. The norm in this conclusion is the operator norm. No common energy constant is assumed. The zero space is included; the conclusion does not require the identity operator to have norm one.

For each finite horizon T>=0, send x to the L2 class of the orbit multiplied by the indicator of (0,T]. Contractivity bounds this linear map by the L2 norm of the scalar indicator of (0,T]. The individual infinite energy hypotheses bound all these truncated maps at each x by the L2 norm of its full positive-time orbit. Banach-Steinhaus gives a single operator bound. Squaring its norm and enlarging the constant gives C>0 such that the integral from 0 to T of norm(S(s)x)^2 is at most C*norm(x)^2 for every horizon and every vector.

The semigroup law and contractivity make s maps to norm(S(s)x) nonincreasing. Consequently T*norm(S(T)x)^2 is bounded above by the energy on (0,T]. At tau=4*C+1, this implies norm(S(tau))<=1/2<1. Iteration gives norm(S(n*tau))<=2^(-n). For an arbitrary nonnegative time t, use n=floor(t/tau) and contractivity on the remaining time. Then norm(S(t))<=2*exp(-(log(2)/tau)*t). This covers all times, including t=0; it is not a bounded-horizon estimate.

Conversely, the operator estimate bounds each squared orbit by M^2*norm(x)^2*exp((-2*omega)*t). Since omega>0, the real exponential is integrable on (0,infinity). The continuous orbit supplies measurability and domination gives the required integrability.

This is the classical Datko criterion specialized to contraction semigroups, not a claim of mathematical originality. Schnaubelt's Evolution Equations, Lemma 4.4, gives the real or complex Banach finite-p implication and the truncated-orbit-map argument. Duoc's arXiv:2009.04178v1 recalls the squared-energy equivalence for evolutionary families; its semigroup specialization follows by time translation. The formal statement here uses real scalars and p=2. It assumes no Hilbert structure, dimension bound, separability, compactness, spectral description, generator domain or spectral gap. It does not establish energy hypotheses for any particular heat model, and does not turn individual positive eigenvalue rates into a uniform gap.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/DatkoStability.integrable_sq_orbit_iff_exponential_stability`
- Dependency: [D5/S3/Quantum/Analysis/ContractionSemigroup](ContractionSemigroup.md)
