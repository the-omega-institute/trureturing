# Polynomial Fock Sugawara Support

## Abstract

The polynomial Fock action has an explicit state-dependent finite support interval for its normal-ordered quadratic field.

Let F be the complex polynomial algebra in variables X_k. Positive Heisenberg modes act by (k+1) times partial differentiation in X_k, negative modes by multiplication by X_k, and the zero mode vanishes. The current is the Laurent field assembled from these modes. For a state p, N(p) is two more than the largest variable index occurring in p; the supremum of the empty variable set is zero.

**Theorem 1.1 (Normal-ordering has explicit polynomial support).**

$$\forall n\in\mathbb{Z}, p\in F,\ \operatorname{supp}\left(k\mapsto\operatorname{normalPair}\left(n-k, k, p\right)\right) \subseteq (n-\operatorname{N}\left(p\right),\operatorname{N}\left(p\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/PolynomialFockSugawaraSupport.normalPair_support_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A mode beyond N(p) differentiates in a variable absent from p and therefore vanishes. Normal ordering makes the larger of the two mode indices act first. A surviving summand consequently has both indices below N(p), which places k strictly inside the displayed interval.

**Theorem 1.2 (Finite intervals compute the Sugawara action).**

$$\forall n,a,b\in\mathbb{Z}, p\in F,\ a\leq n-\operatorname{N}\left(p\right) \land \operatorname{N}\left(p\right)\leq b \Rightarrow \operatorname{L}\left(n, p\right)=2^{-1} \sum_{k=a}^{b}\operatorname{normalPair}\left(n-k, k, p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/PolynomialFockSugawaraSupport.L_interval_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pointwise finite normal-ordered sum defines L_n. Any closed integer interval containing its explicit support produces the same value on p. The theorem applies to every polynomial state and every integer mode, without asserting the Virasoro commutator.

## References

- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockSugawaraSupport.L_interval_sum`
- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockSugawaraSupport.normalPair_support_interval`
