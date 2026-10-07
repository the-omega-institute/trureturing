# Native One and Two Row Relative Poisson Transfer

## Abstract

Native marked departure counts and their relative Poisson comparison.

**Theorem 1.1 (Uniform native relative count estimate).**

$$\forall kappa,Czero:Real, 0<kappa<1 \land 1\leq Czero \Rightarrow \exists A:Real, \exists Mzero:Nat, \exists etazero:Real, 0<A \land 1\leq Mzero \land 0<etazero \land \forall M,q,lambda,k:Nat, \forall r:Real, Mzero\leq M \land 1\leq q<M \land 0<r\leq 1-kappa \land \operatorname{compensation}(M, q, r)\leq 1-kappa \land 1\leq lambda \land \frac{lambda}{M}\leq etazero \land (k=1 \lor k=2) \Rightarrow \forall S:\operatorname{Support}(M, q), \forall m:\operatorname{Fin}(k)\to\operatorname{Fin}(M), \operatorname{injective}(m) \Rightarrow \forall {n}^{+},{n}^{-}:\operatorname{Fin}(k)\to Nat, (\forall j:\operatorname{Fin}(k), {{n}^{+}}_{j}\leq Czerolambda \land {{n}^{-}}_{j}\leq Czerolambda) \Rightarrow \forall e:\operatorname{Experiment}(), \lvert \frac{\operatorname{P}(M, q, lambda, r, S, m, {n}^{+}, {n}^{-}, e)}{\operatorname{Q}(M, q, lambda, r, S, m, {n}^{+}, {n}^{-})}-1 \rvert\leq \frac{A{lambda}^{k+1}}{M}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/ActualMarkedCountPoissonRelative.actual_marked_count_poisson_relative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constants A, Mzero and etazero depend only on kappa and Czero. There are k = 1 or k = 2 distinct marked positive states m(j). S is a native support of cardinality q. The native compensation is c = rq/(M-q), with natural difference in the denominator. The experiment e ranges over the native pair and uniform-start path experiments.

In the displayed formula P is the sum of native history masses over all histories of T = 2M lambda transitions for which every marked positive and negative destination-parity count equals the prescribed natural count. Counts of zero are included. Each pair history has mass equal to the product of (2M)^(-1) transition(x,y); a path history has mass (2M)^(-1) times the product of its consecutive transition factors. The transition is (1+b(x) chi(y))/(2M), where chi is the destination parity.

Q is the product, over marked states and both destination parities, of exp(-mu) mu^n/n!. The means are muplus(j) = lambda(1+b(m(j)))/2 and muminus(j) = lambda(1-b(m(j)))/2. The profile b is r on the positive support, -c on its positive complement, and zero on negative states. P and Q use the same support and marked rows; no independent path-row model is used.

Positive radii (n+1)/mu extract both native and Poisson count coefficients from their generating functions on a product torus. The pair and path exponential estimates bound the integrated coefficient difference. A factorial estimate, including n = 0, gives the relative normalization.

## References

- Truth anchor: `D5/S3/Estimation/TimeArrow/ActualMarkedCountPoissonRelative.actual_marked_count_poisson_relative`
- Dependency: [D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint](../../Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.md)
- Dependency: [D5/S3/Estimation/TimeArrow/ActualMarkedPathPgfPoissonEnvelope](ActualMarkedPathPgfPoissonEnvelope.md)
