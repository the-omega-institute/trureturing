# Categorical increments and full product Poisson counts

## Abstract

Finite categorical increments admit a uniform comparison with the full independent Poisson count vector.

**Definition 1.1 (One mark as a count vector).**

$$\forall J: \operatorname{Type}(), [\operatorname{DecidableEq}(J)] \forall j: J, \forall i: J, \operatorname{eval}(\operatorname{unitMark}(j), i)=\operatorname{ite}(i=j, 1, 0)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/CategoricalProductPoisson.unitMark` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vector has one at the selected mark and zero at every other mark.

**Definition 1.2 (Categorical increment law).**

$$\forall J: \operatorname{Type}(), [\operatorname{Fintype}(J)] [\operatorname{DecidableEq}(J)] \forall a: J\to \operatorname{NNReal}(), \operatorname{categoricalIncrement}(a)={\operatorname{ofReal}(1-\sum_{j: J} {\operatorname{eval}(a, j)})} \cdot {\operatorname{dirac}(\operatorname{zeroVector}(J))}+\sum_{j: J} {{\operatorname{eval}(a, j)} \cdot {\operatorname{dirac}(\operatorname{unitMark}(j))}}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/CategoricalProductPoisson.categoricalIncrement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rates are nonnegative real numbers, identified with their extended nonnegative real coercions when scaling measures. zeroVector(J) is the identically zero natural count vector. ofReal converts a real number to a nonnegative extended real, clipping negative values to zero. Under total rate rho at most one, this is a probability measure: the zero vector has probability one minus rho and the unit vector at j has probability a(j).

**Definition 1.3 (Coordinatewise time aggregation).**

$$\forall J: \operatorname{Type}(), \forall s: \operatorname{Nat}(), \forall x: \operatorname{Fin}(s)\to J\to \operatorname{Nat}(), \forall j: J, \operatorname{eval}(\operatorname{aggregateCounts}(s, x), j)=\sum_{t: \operatorname{Fin}(s)} {\operatorname{eval}(\operatorname{eval}(x, t), j)}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/CategoricalProductPoisson.aggregateCounts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every coordinate is summed along the same complete history of s increments. An empty history produces the zero vector.

**Definition 1.4 (Law of independent increments).**

$$\forall J: \operatorname{Type}(), \forall mu: \operatorname{Measure}(J\to \operatorname{Nat}()), \forall s: \operatorname{Nat}(), \operatorname{independentSumLaw}(mu, s)=\operatorname{pushforward}(\operatorname{aggregateCounts}(s), \operatorname{finiteProduct}(\operatorname{Fin}(s), mu))$$

*Formalization.* `D5/S3/Estimation/TimeArrow/CategoricalProductPoisson.independentSumLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

finiteProduct denotes the measure product with one copy of mu for each element of Fin(s). pushforward maps that joint measure through aggregateCounts. Independence is part of the full increment law, rather than an assertion about separate marginals.

**Theorem 1.5 (Every-event product Poisson comparison).**

$$\forall J: \operatorname{Type}(), [\operatorname{Fintype}(J)] [\operatorname{DecidableEq}(J)] \forall a: J\to \operatorname{NNReal}(), \sum_{j: J} {\operatorname{eval}(a, j)} \leq 1 \Rightarrow \forall s: \operatorname{Nat}(), \forall E: \operatorname{Set}(J\to \operatorname{Nat}()), \lvert \operatorname{eventMass}(\operatorname{independentSumLaw}(\operatorname{categoricalIncrement}(a), s), E)-\operatorname{eventMass}(\operatorname{poissonProduct}(\operatorname{scaledRates}(s, a)), E) \rvert \leq {s} \cdot {{\sum_{j: J} {\operatorname{eval}(a, j)}}^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/CategoricalProductPoisson.categorical_product_poisson` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

eventMass is Measure.real applied to the event. poissonProduct is the measure product over all marks of the Poisson laws, and scaledRates(s,a)(j) is s times a(j). The theorem quantifies every finite alphabet, all nonnegative rates of total at most one, every natural s, and every event of the entire natural count vector. Empty alphabets, total rate zero, individual zero rates, and s equal to zero or one remain included.

The proof constructs a common submeasure. It retains the categorical mass at zero and the full product Poisson mass exp(-rho) a(j) at each unit vector. Its mass is 1-rho(1-exp(-rho)). The s-fold increment product retains the corresponding power of this mass. Mapping the whole history to its count vector preserves domination. Bernoulli's inequality and exp(-rho) at least 1-rho give the displayed uniform bound. All events outside the unit vectors, including arbitrarily many Poisson arrivals, remain in the complement controlled by the common-submeasure argument.

Time aggregation of the full product Poisson measure is proved through the finite product equivalence and Mathlib's poissonMeasure_conv_poissonMeasure, giving independent coordinates at rates s a(j). This is a finite categorical reference comparison. A comparison from the native path law to this reference is a separate mathematical obligation.

For signed support marks J=Fin(q)+Fin(q), n=2M and a(j,+)=(1+r)/(2n), a(j,-)=(1-r)/(2n), the total rate is q/n and the final rates are L(1+r)/2 and L(1-r)/2, where L=s/n. The same joint count carrier is used for both signs; this application alone does not prove the native path comparison or close all clauses of the parent theorem.

For the native application, assume 1 <= q < M, 0 < r < 1 and rq/(M-q) < 1. Fix S : Support(M,q) and an injective enumeration m : Fin(q) -> Fin(M) with every m(j) in S. On a native path observation o, define N(o)(inl(j)) = count(path,o,m(j),1) and N(o)(inr(j)) = count(path,o,m(j),-1). Its event probability is the sum of probability(r,path,S,o) over exactly the observations with N(o) in E. If a separate native comparison bounds its difference from independentSumLaw(categoricalIncrement(a),s)(E) by eta, the triangle inequality and this theorem give eta + s(q/n)^2 for its difference from the full product Poisson event probability. This implication preserves the fixed support and uses all counts on the same actual history; the native comparison premise remains a separate obligation.

## References

- Truth anchor: `D5/S3/Estimation/TimeArrow/CategoricalProductPoisson.aggregateCounts`
- Truth anchor: `D5/S3/Estimation/TimeArrow/CategoricalProductPoisson.categoricalIncrement`
- Truth anchor: `D5/S3/Estimation/TimeArrow/CategoricalProductPoisson.categorical_product_poisson`
- Truth anchor: `D5/S3/Estimation/TimeArrow/CategoricalProductPoisson.independentSumLaw`
- Truth anchor: `D5/S3/Estimation/TimeArrow/CategoricalProductPoisson.unitMark`
