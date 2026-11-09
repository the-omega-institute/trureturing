# The Full Pointwise North-South Selector

## Abstract

Every literal pointwise north-south homeomorphism of a compact metric locally equiconnected space has a continuous exactly equivariant selector on a full closed integer pseudoorbit domain.

**Theorem 1.1 (A single selector on the entire closed domain).**

$$\forall M: CompactMetricSpace, \forall f: \operatorname{Homeomorphism}(M), \forall N: M, \forall S: M, \operatorname{Pointwise}(f, N, S) \Rightarrow \operatorname{LocalEquiconnection}(M) \Rightarrow \exists delta: \mathbb{R}, 0 < delta \land \exists Q: \operatorname{Space}(f, delta) \to M, \operatorname{Continuous}(Q) \land (\forall p: M, \operatorname{Q}(\operatorname{trueOrbit}(f, p)) = p) \land (\forall k: \mathbb{Z}, \forall x: \operatorname{Space}(f, delta), \operatorname{Q}(\operatorname{shift}(f, k, x)) = \operatorname{iterate}(f, k, \operatorname{Q}(x)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/NorthSouthSelector.pointwise_north_south_selector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

M is an arbitrary compact metric space. The homeomorphism f has distinct fixed poles N,S, and each other point tends pointwise to S under positive iterates and to N under inverse iterates. A local equiconnection is explicit data: one open W in M×M containing the diagonal, and one continuous H:W×[0,1]→M with both endpoint equalities and the all-parameter diagonal identity. Stability, compact uniform attraction and a strict height are derived from the pointwise assumptions in the imported suppliers.

There are δ>0 and Q on the entire closed set Pδ of sequences x:Z→M with dist(x(i+1),f(x(i)))≤δ for every integer i. Q is continuous for the inherited product topology, fixes every true orbit, and satisfies Q(shift(k,x))=f^k(Q(x)) for all integers k. The shift reads x(k+i); commutativity of integer addition identifies the primary x(i+k) convention. Errors equal to δ and infinitely many nonzero errors remain in scope.

For the constructed strict height h, compact separation gives a positive closed-link tolerance, a one-way sign barrier, a uniform positive crossing denominator, and a compact band containing every interpolation output. At a weak crossing j the formula is f^(-j) applied to H(x(j),f^(-1)(x(j+1)), -h(x(j))/(h(x(j+1))-h(x(j)))). Adjacent crossings at a zero entry give exactly the same output by the two endpoint identities. A finite closed cover proves continuity near each crossing. At every all-negative or all-positive history, including arbitrary nonconstant histories, one far coordinate and compact uniform attraction prove continuity at the corresponding cap. The two-point space is included: the punctured clock is empty and the same proof gives the full selector. No finite-window replacement is made.

For a topological sphere, transport the explicit normalized straight connector from the Euclidean unit sphere through the given homeomorphism. Its nonantipodal pair domain is open, its chord is nonzero throughout [0,1], and normalization supplies both endpoints and the diagonal. Thus the theorem applies to an arbitrary literal pointwise north-south sphere homeomorphism for every compatible metric. No smooth, hyperbolic, flow or dimension bound is introduced; compact LEC implies ANR is not claimed.

The same Q supplies CompactSelector.global_and_limit_shadowing. For each ε>0 it gives 0<γ≤δ such that every x in Pγ satisfies dist(f^k(Q(inclusion(x))),x(k))<ε for every integer k. For every x in the original Pδ whose literal link errors tend to zero in the cofinite filter on Z, the discrepancies for Q(x) also tend to zero in that filter; the supplier also gives the explicit natAbs tail. Domain inclusion is literal sequence inclusion. The exact supplier source is reused unchanged from commit 5c2269ceb35eac4b8cf436d183defc9e2a1ffbc3, SHA-256 df66b7c5c21214ee7ba72379e228e16f19bdb386ccbec713f83fef198a30834d.

The construction follows the supplied terminal mathematical source public-proof.txt SHA-256 9d2c8af332171841b0de2122a8a6d18d3f094b8ee563ff2b50646332144306bc and lean-route.txt SHA-256 1a51a2083580f57293ae2e0f032afb5257d891328f247d26b97b81b483360a97. The proof constructs the selector from derived stability, a strict height, crossing interpolation and continuity at arbitrary cap histories. Its topological-sphere application supplies the existence asked in Alfonso Artigue, Shadowing maps, final Question 5.19, printed page 52, DOI 10.2140/om.2027.4.29 (arXiv:2504.00171v1 Question 5.21). The primary paper's Proposition 5.18 proves non-equivariance of its particular bracket construction. The present selector uses a different formula and the literal pointwise hypotheses. Attribution and kernel verification do not establish literature priority, exhaustive novelty or official acceptance. The existing full vertical suspension theorem is preserved as a separate result.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/NorthSouthSelector.pointwise_north_south_selector`
- Dependency: [D5/S1/Dynamics/Shadowing/LocalEquiconnection](LocalEquiconnection.md)
- Dependency: [D5/S1/Dynamics/Shadowing/NorthSouthOrbitClock](NorthSouthOrbitClock.md)
