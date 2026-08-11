# Bhattacharyya Affinity on Finite Products

## Abstract

Bhattacharyya affinity is multiplicative on finite products under nonnegativity of only the first marginal radicands, consistently with half-order Renyi additivity.

**Theorem 1.1 (Bhattacharyya affinity is multiplicative on products).**

$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] [\operatorname{Fintype}(\kappa)],\\\forall p, q: \iota\to \mathbb{R}, p', q': \kappa\to \mathbb{R},\\(\forall i, 0\le p(i)q(i)) \Rightarrow \\\operatorname{BC}((i, j)\mapsto p(i)p'(j)\Vert \Vert (i, j)\mapsto q(i)q'(j))=\\\operatorname{BC}(p\Vert \Vert q)\operatorname{BC}(p'\Vert \Vert q').\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/BhattacharyyaProduct.bhattacharyya_product_multiplicative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Bhattacharyya affinity of a product is the product of the two marginal affinities. Overlap therefore multiplies across independent finite experiments, whereas a distance would add. This is the multiplicative face of the additivity enjoyed by the Renyi family.

The hypothesis is unusually weak and records a signature asymmetry, not a symmetric positivity convention. It assumes only that the pointwise product p(i)q(i) is nonnegative. Neither p nor q is required to be nonnegative individually: p(i) = q(i) = -1 satisfies the hypothesis because their product is 1. The second marginal functions p' and q' carry no sign condition at all, and none of the four functions is normalized.

This exact hypothesis set is forced by the asymmetric signature of Real.sqrt_mul. That lemma requires nonnegativity only of its first argument. The proof groups each joint radicand as (p(i)q(i))(p'(j)q'(j)), placing the entire sign burden on the first group and leaving the second argument unrestricted. It then exposes the iterated finite sum and factors the two marginal sums with Finset.sum_mul_sum. Nothing was assumed merely for symmetry's sake.

The declaration renyi_divergence_product_additive_one_half_consistency is a compiled check rather than a second mathematical result. Taking -2 log of the multiplicativity identity gives exactly product additivity at alpha = 1/2. The declaration states that same half-order equality twice as a conjunction of two identical copies. One conjunct is discharged through the new multiplicativity theorem, together with renyi_divergence_one_half and Real.log_mul; the other is discharged by specializing the frozen general-alpha Renyi additivity theorem to alpha = 1/2.

Compiling the conjunction checks that the two independently derived routes agree; disagreement would make the new multiplicativity statement the suspect. The stronger assumptions in the consistency declaration come from the frozen Renyi route: it requires four pointwise nonnegativity hypotheses and non-vanishing of both marginal half-order power sums. The multiplicativity theorem itself needs only nonnegativity of p(i)q(i), so those additional hypotheses belong to the check's frozen-theorem side rather than to the new product law.

No n-fold product or i.i.d. form, statement at any other Renyi order, equality characterization, or measure-theoretic analogue is claimed.

## References

- Truth anchor: `D5/S3/TotalVariation/BhattacharyyaProduct.bhattacharyya_product_multiplicative`
- Dependency: [D5/S3/RenyiDivergence/ProductAdditivity](../RenyiDivergence/ProductAdditivity.md)
