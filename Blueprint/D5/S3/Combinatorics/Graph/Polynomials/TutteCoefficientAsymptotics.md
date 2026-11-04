# Uniform signed graph coefficient estimate

## Abstract

For each forward-degree bound D and coefficient index k, the signed rank-state polynomial of every connected simple graph with that ordered degree bound differs from the negative-binomial comparison coefficient by at most C(D,k)(e+1)^(k−1). The constant is independent of the graph and carrier size. No forest equality, cyclic-state count, or term estimate is assumed: the proof consumes the graph-derived fixed-rank count and term bounds in CyclicRankEstimate.

The graph polynomial is the finite sum over actual edge subsets S of (−1)^|S| z^q(S) (1+z)^(v−1+|S|−2q(S)), with q(S)=v−c(S) counting all connected components, including isolated vertices. Its exponents are proved nonnegative. The cyclomatic number is the natural number e+1−v; connectedness and v>0 justify its integer interpretation, including trees and the one-vertex graph.

The proof uses the integer-binomial comparison term (−1)^s choose(v−1−s,k−s) for s≤k. Summing it over all edge subsets gives choose(−b,k) by the powerset insertion identity and Pascal recurrence. On forests this term equals the actual coefficient. Consequently the forest error is exactly minus the comparison sum over cyclic states. This error generally does not vanish: the triangle has forest polynomial 1−z+z² and cubic coefficient zero, whereas choose(−1,3)=−1. Integer binomial coefficients keep negative comparison exponents intact, so small vertex sets require no asymptotic restriction.

Grouping cyclic states by their actual graph rank j≤k, the finite support-pattern injection gives O(D,j)((e+1)^(j−1)) states. Each actual state term and each comparison term has growth O(k)((e+1)^(k−j)). Their products therefore have the common exponent k−1. Cyclic graph rank is at least two, giving the exact first coefficient −b. States above rank k vanish. This establishes both the approximate forest contribution and the full uniform estimate.

**Definition 1.1 (Finite cyclic-error constant).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/TutteCoefficientAsymptotics.cyclicErrorConstant`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/TutteCoefficientAsymptotics.cyclicErrorConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum the proved rank-specific pattern constants from j=0 through k. It depends only on D and k.

**Theorem 1.2 (Actual cyclic contribution).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/TutteCoefficientAsymptotics.graph_cyclic_coefficient_estimate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/TutteCoefficientAsymptotics.graph_cyclic_coefficient_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The absolute cyclic coefficient is bounded by 2^k times the cyclic-error constant times (e+1)^(k−1). The proof uses actual graph ranks, the finite-injection count, and derived state-term growth.

**Theorem 1.3 (Approximate forest contribution).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/TutteCoefficientAsymptotics.graph_forest_coefficient_estimate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/TutteCoefficientAsymptotics.graph_forest_coefficient_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forest coefficient differs from choose(−b,k) by at most (2k+3)^k times the cyclic-error constant times (e+1)^(k−1). Forest equality is neither assumed nor claimed.

**Definition 1.4 (Uniform coefficient constant).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/TutteCoefficientAsymptotics.uniformCoefficientConstant`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/TutteCoefficientAsymptotics.uniformCoefficientConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constant is (2^k+(2k+3)^k) times the cyclic-error constant; it is independent of e, v and the graph.

**Theorem 1.5 (Uniform coefficient theorem).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/TutteCoefficientAsymptotics.signed_tutte_coefficient_estimate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/TutteCoefficientAsymptotics.signed_tutte_coefficient_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every connected simple graph on Fin v with v>0 and forward degree at most D, and every k≥1, the absolute difference between the kth signed state coefficient and (−1)^k choose(b+k−1,k) is at most C(D,k)(e+1)^(k−1). The statement includes small graphs and trees. This is a theorem about the explicit rank-state polynomial, not a geometric Jones identification or a resolution of the weaving conjecture.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/TutteCoefficientAsymptotics.cyclicErrorConstant`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/TutteCoefficientAsymptotics.graph_cyclic_coefficient_estimate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/TutteCoefficientAsymptotics.graph_forest_coefficient_estimate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/TutteCoefficientAsymptotics.signed_tutte_coefficient_estimate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/TutteCoefficientAsymptotics.uniformCoefficientConstant`
- Dependency: [D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate](CyclicRankEstimate.md)
