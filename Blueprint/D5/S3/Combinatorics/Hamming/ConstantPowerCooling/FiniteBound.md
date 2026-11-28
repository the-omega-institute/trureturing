# The finite cooling-code upper bound

## Abstract

The clique-packing leave bounds the number of cooling-code information classes.

**Theorem 1.1 (The finite cooling-code upper bound).**

Lean statement: `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/FiniteBound.finite_cpecc_support_upper_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/FiniteBound.finite_cpecc_support_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shuangqing Liu, Qianfei Zhang, Shikang Yu, Menglong Zhang, Lijun Ji (2026). *Optimal bounds for (n,t,w,w−2)-constant-power error-correcting cooling codes*. URL: <https://arxiv.org/abs/2611.34386v1>.

*Commentary.*

Let V be a finite point set of cardinality n, and let P be a finite indexed family of information classes. Each word is a w-subset, each deletion of t points misses a word in every class, and words in different classes meet in at most one point. Put k = w + t. Assume k ≤ n, 1 ≤ t, t + 3 < w, 1 ≤ g < w, k − 1 divides n − g, k(k − 1) divides n(n − g), and k(k + g − 2) ≤ 2B(w,t). Then the number of classes is at most J = n(n − g)/(k(k − 1)). Write R = (n − g)/(k − 1). Choose one k-clique from each of the b shadows with such a clique. If a point is covered r times, its leave degree is (g − 1) + (k − 1)(R − r). The remaining shadows live on points with R − r positive, since their support degrees are at least w − 1. Summing the deficits gives k(J − b), so twice the edge count of the induced leave is at most k(k + g − 2)(J − b). The Appendix A threshold pays for each remaining shadow.

## References

- Truth anchor: `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/FiniteBound.finite_cpecc_support_upper_bound`
- Dependency: [D5/S3/Combinatorics/Hamming/ConstantPowerCooling/CliquePacking](CliquePacking.md)
- Dependency: [D5/S3/Combinatorics/Hamming/ConstantPowerCooling/Shadows](Shadows.md)
