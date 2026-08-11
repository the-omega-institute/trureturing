# Product Additivity of Finite Renyi Divergence

## Abstract

Finite Renyi divergence is additive on products of nonnegative finite mass functions with nonvanishing marginal power sums at every real order.

**Theorem 1.1 (Finite Renyi divergence is additive on products).**

$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] [\operatorname{Fintype}(\kappa)],\\\forall \alpha \in \mathbb{R},\\\forall p, q: \iota\to \mathbb{R}, p', q': \kappa\to \mathbb{R},\\((\forall i, 0\le p(i)) \land (\forall i, 0\le q(i)) \land \\(\forall j, 0\le p'(j)) \land (\forall j, 0\le q'(j)) \land \\(\sum _{i} p(i)^{\alpha } q(i)^{1-\alpha })\neq 0 \land \\(\sum _{j} p'(j)^{\alpha } q'(j)^{1-\alpha })\neq 0)) \Rightarrow \\D_{\alpha }((i, j)\mapsto p(i)p'(j)\Vert \Vert (i, j)\mapsto q(i)q'(j))=\\D_{\alpha }(p\Vert \Vert q)+D_{\alpha }(p'\Vert \Vert q').\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/ProductAdditivity.renyi_divergence_product_additive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Independent finite experiments add their Renyi divergences. This product law is what makes the family behave as an information measure across independent structure, and it is the Renyi counterpart of the frozen classical theorem kl_divergence_product_additive.

The hypotheses are strictly weaker than those of that classical analogue. The classical theorem requires every coordinate of all four mass functions to be strictly positive and normalizes the two first distributions. Here all four functions need only be pointwise nonnegative, and the two marginal power sums need only be nonzero. No normalization is required. Zero coordinates are permitted provided each marginal power sum remains nonzero. This weakening is available because Real.rpow is well defined on nonnegative arguments, whereas the classical proof takes the logarithm of a ratio.

The proof first applies Real.mul_rpow to split each joint summand into the product of its two marginal summands. Fintype.sum_prod_type exposes the iterated finite sum, and Fintype.sum_mul_sum factors it as the product of the two marginal power sums. Real.log_mul then splits the joint logarithm, after which the shared prefactor distributes over the sum.

The prefactor 1/(alpha-1) imposes no order restriction here. In the monotonicity and data-processing results, its sign changes across alpha = 1, reverses inequalities below one, and makes a straddling claim false. Product additivity is instead an equality: the same prefactor multiplies the joint logarithm and both marginal logarithms, so it distributes algebraically rather than reversing an inequality. The theorem consequently holds for every real alpha, below and above one alike. It also holds literally at alpha = 1, where totalized real division makes the prefactor zero and both sides vanish.

The two non-vanishing assumptions are forced by the single Real.log_mul step. Without them, the convention Real.log 0 = 0 does not satisfy log(0*y) = log 0 + log y: when one marginal power sum vanishes, factorization can therefore turn a false divergence identity into an apparently formal logarithmic split. The stated hypotheses are exactly what Real.log_mul requires, rather than a positive-overlap condition, which would be stronger than necessary.

No n-fold product or i.i.d. form, sample-complexity corollary, order-one limit, or measure-theoretic analogue is claimed. All logarithms are natural, so the units are nats.

## References

- Truth anchor: `D5/S3/RenyiDivergence/ProductAdditivity.renyi_divergence_product_additive`
- Dependency: [D5/S3/RenyiDivergence/Basic](Basic.md)
