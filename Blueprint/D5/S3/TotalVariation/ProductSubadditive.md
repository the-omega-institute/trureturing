# Product Subadditivity of Total Variation

## Abstract

Total variation is subadditive over finite products under absolute-mass bounds in exactly the two hybrid scaling positions, and the bound is strict on a concrete Bool product.

**Theorem 1.1 (Total variation is subadditive over independent products).**

$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] [\operatorname{Fintype}(\kappa)],\\\forall p, q: \iota\to \mathbb{R},\\\forall p', q': \kappa\to \mathbb{R},\\(\sum _{i} \Vert p(i)\Vert \le 1 \land \sum _{k} \Vert q'(k)\Vert \le 1) \Rightarrow\\\operatorname{TV}((i, k) \mapsto p(i) \cdot p'(k), (i, k) \mapsto q(i) \cdot q'(k)) \le \\\operatorname{TV}(p, q)+\operatorname{TV}(p', q').\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ProductSubadditive.total_variation_product_subadditive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For probability laws, the theorem says that running two independent experiments cannot separate a pair of laws by more than the sum of the separations available from the two experiments individually. The formal statement is stronger: its four inputs are arbitrary real-valued functions subject only to the two displayed absolute-mass bounds.

The proof inserts the hybrid product p tensor q' between p tensor p' and q tensor q', then applies the frozen triangle inequality for total variation. The first leg changes only the second factor, while the second leg changes only the first. This decomposition exposes exactly which fixed factor scales each marginal distance.

The hypotheses are asymmetric, and the asymmetry is forced by the two collapse identities. The first is TV(p tensor p', p tensor q') = (sum_i |p(i)|) TV(p',q'), so sum_i |p(i)| <= 1 bounds that leg by TV(p',q'). The second is TV(p tensor q', q tensor q') = (sum_k |q'(k)|) TV(p,q), so sum_k |q'(k)| <= 1 bounds that leg by TV(p,q).

Thus the hypothesis set consists exactly of the two scaling positions: p in the first collapse and q' in the second. The other two factors, q and p', require no hypothesis whatsoever. In particular, the assumptions are absolute-mass bounds, not normalization conditions; unit mass has been weakened to absolute mass at most one.

Pointwise nonnegativity is not required anywhere. Both collapses retain the absolute masses directly, and the identity abs_mul separates the absolute value of each product without a sign rewrite. The asymmetric assumptions are therefore earned by the proof rather than omitted by oversight.

**Theorem 1.2 (Product subadditivity is strict on a Bool witness).**

$$\begin{gathered}p=\Delta_{\operatorname{true}},\\q(\operatorname{true})=\frac{1}{\pi}, q(\operatorname{false})=1-\frac{1}{\pi},\\\operatorname{TV}((b_{1}, b_{2}) \mapsto p(b_{1}) \cdot p(b_{2}), (b_{1}, b_{2}) \mapsto q(b_{1}) \cdot q(b_{2}))=1-\frac{1}{\pi^{2}}<2-\frac{2}{\pi}=\\\operatorname{TV}(p, q)+\operatorname{TV}(p, q),\\(2-\frac{2}{\pi})-(1-\frac{1}{\pi^{2}})=(1-\frac{1}{\pi})^{2}> 0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ProductSubadditive.total_variation_product_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The strictness witness is the mathematical content that distinguishes product behavior here. Renyi divergence is exactly additive over products, whereas total variation is only subadditive; the weak inequality alone would not reveal that distinction.

On Bool, let p be the point mass at true and let q assign 1/pi to true and 1-1/pi to false. Each of the two identical marginal comparisons has total variation 1-1/pi. Their product comparison has total variation 1-1/pi^2, while the sum of the marginal total variations is 2-2/pi.

Consequently the difference between the right and left sides is (2-2/pi)-(1-1/pi^2) = (1-1/pi)^2. Since pi > 1, this perfect square is strictly positive. The formal theorem proves the resulting strict inequality for the concrete Bool product rather than merely recording a numerical example.

No n-fold product or i.i.d. specialization is claimed. The module gives no characterization of equality, no reverse inequality, and no measure-theoretic analogue.

## References

- Truth anchor: `D5/S3/TotalVariation/ProductSubadditive.total_variation_product_strict`
- Truth anchor: `D5/S3/TotalVariation/ProductSubadditive.total_variation_product_subadditive`
- Dependency: [D5/S3/TotalVariation/Metric](Metric.md)
