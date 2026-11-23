# Optimization on the finite probability simplex

## Abstract

Exact simplex minima for the reduced Wu graph quartic.

Let G be a simple graph on a finite nonempty vertex type V. The probability simplex consists of nonnegative functions w on V that sum to one. The support is the finite set of vertices with positive mass. For a nonempty finite set s, uniform(s) has weight 1/card(s) on s and zero elsewhere. The notation real casts a natural number to a real, and image applies a function to a set. The objective is the sum of the linear penalties eta(i) w(i) and kappa times the sum of the squared masses and the products w(i) w(j) over ordered adjacent pairs. Thus each undirected edge contributes twice.

**Theorem 1.1 (Independent-support improvements and attainment).**

$$\forall V \in \operatorname{Type}\left(u\right),\; [\operatorname{Fintype}\left(V\right)] [\operatorname{Nonempty}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall eta \in V \to \mathbb{R},\; \forall kappa \in \mathbb{R},\; (\forall w \in V \to \mathbb{R},\; (w \in \operatorname{simplex}\left(V\right)) \Rightarrow (\exists u \in V \to \mathbb{R},\; (u \in \operatorname{simplex}\left(V\right)) \land ((\operatorname{IsIndepSet}\left(G, \operatorname{support}\left(u\right)\right)) \land ((\operatorname{subset}\left(\operatorname{support}\left(u\right), \operatorname{support}\left(w\right)\right)) \land (\operatorname{graphObjective}\left(G, eta, kappa, u\right) \le \operatorname{graphObjective}\left(G, eta, kappa, w\right)))))) \land (\exists u \in V \to \mathbb{R},\; (u \in \operatorname{simplex}\left(V\right)) \land ((\operatorname{IsIndepSet}\left(G, \operatorname{support}\left(u\right)\right)) \land (\forall w \in V \to \mathbb{R},\; (w \in \operatorname{simplex}\left(V\right)) \Rightarrow (\operatorname{graphObjective}\left(G, eta, kappa, u\right) \le \operatorname{graphObjective}\left(G, eta, kappa, w\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuQuarticGraph.independent_support_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For adjacent vertices with positive mass, transfer a signed amount t from the second to the first. The simplex permits the whole interval from minus the first mass to the second mass. The two squares and both orientations of the edge sum to the square of the fixed combined mass. All remaining terms are affine in t, so an endpoint has cost at most the initial cost. That endpoint strictly reduces the positive support. Strong induction on its cardinality gives the first assertion. Compactness of the simplex and continuity of the objective yield a minimizer, to which the same improvement applies. This argument allows arbitrary real linear penalties and scales.

**Theorem 1.2 (The sharp unpenalized minimum).**

$$\forall V \in \operatorname{Type}\left(u\right),\; [\operatorname{Fintype}\left(V\right)] [\operatorname{Nonempty}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall kappa \in \mathbb{R},\; (0 < kappa) \Rightarrow (\exists s \in \operatorname{Finset}\left(V\right),\; (\operatorname{IsNIndepSet}\left(G, \operatorname{indepNum}\left(G\right), s\right)) \land ((\operatorname{uniform}\left(s\right) \in \operatorname{simplex}\left(V\right)) \land ((\operatorname{graphObjective}\left(G, 0, kappa, \operatorname{uniform}\left(s\right)\right) = \frac{kappa}{\operatorname{real}\left(\operatorname{indepNum}\left(G\right)\right)}) \land (\operatorname{IsLeast}\left(\operatorname{image}\left(\operatorname{graphObjective}\left(G, 0, kappa\right), \operatorname{simplex}\left(V\right)\right), \frac{kappa}{\operatorname{real}\left(\operatorname{indepNum}\left(G\right)\right)}\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuQuarticGraph.unpenalized_minimum` (`✓ std3`). ∎

*Citation.* T. S. Motzkin and E. G. Straus (1965). *Maxima for Graphs and a New Proof of a Theorem of Turán*. DOI: [10.4153/CJM-1965-053-6](https://doi.org/10.4153/CJM-1965-053-6).

*Commentary.*

On the simplex, the zero-penalty objective divided by kappa is one minus twice the sum of weight products over unordered edges of the complement. Motzkin–Straus, Section 1, Theorem 1, gives the maximum of that sum, attained at equal weights on a maximum clique of the complement. This clique is a maximum independent set of G.

The Lean proof uses the independent-support improvement above. On independent support the objective is kappa times the sum of squared weights. Cauchy–Schwarz bounds that sum below by the reciprocal of the support size, and the support size is at most the independence number. Equal weights on a maximum independent set attain the bound.

**Theorem 1.3 (The positive-temperature Wu coefficient and sharp graph minimum).**

$$\forall V \in \operatorname{Type}\left(u\right),\; [\operatorname{Fintype}\left(V\right)] [\operatorname{Nonempty}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall beta \in \mathbb{R},\; \forall p \in \mathbb{R},\; \forall r \in \mathbb{R},\; ((0 < beta) \land ((1 < p) \land (p < r))) \Rightarrow (\exists s \in \operatorname{Finset}\left(V\right),\; (\operatorname{IsNIndepSet}\left(G, \operatorname{indepNum}\left(G\right), s\right)) \land ((\operatorname{uniform}\left(s\right) \in \operatorname{simplex}\left(V\right)) \land ((\operatorname{graphObjective}\left(G, 0, \operatorname{wuCoefficient}\left(beta, p, r\right), \operatorname{uniform}\left(s\right)\right) = \frac{\operatorname{wuCoefficient}\left(beta, p, r\right)}{\operatorname{real}\left(\operatorname{indepNum}\left(G\right)\right)}) \land (\forall m \in \mathbb{R},\; (\operatorname{IsLeast}\left(\operatorname{image}\left(\operatorname{graphObjective}\left(G, 0, \operatorname{wuCoefficient}\left(beta, p, r\right)\right), \operatorname{simplex}\left(V\right)\right), m\right)) \Leftrightarrow ((m = \frac{\operatorname{wuCoefficient}\left(beta, p, r\right)}{\operatorname{real}\left(\operatorname{indepNum}\left(G\right)\right)}) \land ((0 < m) \land (\operatorname{real}\left(\operatorname{indepNum}\left(G\right)\right) = \frac{\operatorname{wuCoefficient}\left(beta, p, r\right)}{m})))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuQuarticGraph.wu_unpenalized_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Write B_p(beta) = sinh((1 − 1/p) beta/2) / sinh(beta/(2p)). Set kappa = B_p(beta)²/4 times the exponential Schur complement from WuCriticalQuartic. The factor converts the coherence-normalized Schur complement to squared Gibbs masses. Both factors are strictly positive for beta > 0 and 1 < p < r.

Apply the sharp unpenalized bound at the Wu coefficient. Dividing kappa by the positive minimum recovers the independence number.

The graph statements start from the reduced objective. The signed operator-model Taylor expansion and the limit that produces the finite penalties are separate analytic steps. The explicit coefficient statement concerns positive inverse temperature. The graph optimization theorem also applies to an independently supplied coefficient at zero inverse temperature.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuQuarticGraph.independent_support_minimum`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuQuarticGraph.unpenalized_minimum`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuQuarticGraph.wu_unpenalized_minimum`
- Dependency: [D5/S3/Quantum/Semigroups/WuCriticalQuartic](WuCriticalQuartic.md)
