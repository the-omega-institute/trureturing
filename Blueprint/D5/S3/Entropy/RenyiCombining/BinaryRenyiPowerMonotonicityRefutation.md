# A decrease between orders one quarter and one half

## Abstract

Powered binary Renyi entropy can decrease as its positive order increases.

**Definition 1.1 (The powered binary entropy).**

$$\forall alpha \in \mathbb{R},\; \forall x \in \mathbb{R},\; \operatorname{powered}\left(alpha, x\right) = (\frac{\operatorname{hRenyi}\left(alpha, x\right)}{\operatorname{Real.log}\left(2\right)})^{\frac{2}{alpha}}$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/BinaryRenyiPowerMonotonicityRefutation.powered` (`✓ std3`).

*Citation.* Yupan Liu (2026). *Computational hardness of estimating quantum entropies via binary entropy bounds*. DOI: [10.4230/LIPIcs.STACS.2026.66](https://doi.org/10.4230/LIPIcs.STACS.2026.66). URL: <https://arxiv.org/abs/2601.03734v2>.

*Commentary.*

The binary Renyi entropy with natural logarithms is

$$
\forall alpha \in \mathbb{R},\; \forall x \in \mathbb{R},\; \operatorname{hRenyi}\left(alpha, x\right) = \frac{1}{1 - alpha} \cdot \operatorname{Real.log}\left(x^{alpha} + (1 - x)^{alpha}\right)
$$

The normalization is log(2), and the outer exponent is a real power. This is the expression in Liu's question in Section 1.4(b).

**Definition 1.2 (Monotonicity in the order).**

$$\operatorname{claim} \Leftrightarrow (\forall x \in \mathbb{R},\; (x \in [0, 1]) \Rightarrow (\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; (0 < a) \Rightarrow ((a < b) \Rightarrow ((\neg a = 1) \Rightarrow ((\neg b = 1) \Rightarrow (\operatorname{powered}\left(a, x\right) \le \operatorname{powered}\left(b, x\right)))))))$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/BinaryRenyiPowerMonotonicityRefutation.claim` (`✓ std3`).

*Citation.* Yupan Liu (2026). *Computational hardness of estimating quantum entropies via binary entropy bounds*. DOI: [10.4230/LIPIcs.STACS.2026.66](https://doi.org/10.4230/LIPIcs.STACS.2026.66). URL: <https://arxiv.org/abs/2601.03734v2>.

*Commentary.*

For every binary probability, the proposed monotonicity compares any two positive orders a < b distinct from one. Order one is excluded because the source defines its entropy by a limit.

**Theorem 1.3 (The monotonicity proposition is false).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/BinaryRenyiPowerMonotonicityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/liu-2026-powered-binary-renyi-monotonicity-refutation` (refuted) by `D5/S3/Entropy/RenyiCombining/BinaryRenyiPowerMonotonicityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"liu-2026-powered-binary-renyi-monotonicity-refutation","declaration_gid":"D5/S3/Entropy/RenyiCombining/BinaryRenyiPowerMonotonicityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Yupan Liu (2026). *Computational hardness of estimating quantum entropies via binary entropy bounds*. DOI: [10.4230/LIPIcs.STACS.2026.66](https://doi.org/10.4230/LIPIcs.STACS.2026.66). URL: <https://arxiv.org/abs/2601.03734v2>.

*Commentary.*

Take x = 1/17 and the orders 1/4 and 1/2. The identities 16^(1/4) = 2 and 16^(1/2) = 4 give the closed forms

$$
\operatorname{hRenyi}\left(\frac{1}{4}, \frac{1}{17}\right) = \frac{4}{3} \cdot (\operatorname{Real.log}\left(3\right) - \frac{\operatorname{Real.log}\left(17\right)}{4})
$$

$$
\operatorname{hRenyi}\left(\frac{1}{2}, \frac{1}{17}\right) = \operatorname{Real.log}\left(\frac{25}{17}\right)
$$

The integer comparisons 17^4 times 2^9 < 3^16 and 25^16 < 17^16 times 2^9 imply, by strict monotonicity of the natural logarithm,

$$
4 \cdot \operatorname{Real.log}\left(17\right) + 9 \cdot \operatorname{Real.log}\left(2\right) < 16 \cdot \operatorname{Real.log}\left(3\right) \land 16 \cdot \operatorname{Real.log}\left(\frac{25}{17}\right) < 9 \cdot \operatorname{Real.log}\left(2\right)
$$

Since log(2) is positive, these comparisons give hRenyi(1/4,1/17)/log(2) > 3/4 and 0 < hRenyi(1/2,1/17)/log(2) < 9/16. Raising the positive bounds to the eighth and fourth powers, respectively, and using (3/4)^8 = (9/16)^4 yields powered(1/2,1/17) < powered(1/4,1/17). Both orders are positive and distinct from one, and 1/17 lies in [0,1].

## References

- Truth anchor: `D5/S3/Entropy/RenyiCombining/BinaryRenyiPowerMonotonicityRefutation.claim`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/BinaryRenyiPowerMonotonicityRefutation.powered`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/BinaryRenyiPowerMonotonicityRefutation.result`
- Dependency: [D5/S3/Entropy/RenyiCombining/BinaryRenyiCombining](BinaryRenyiCombining.md)
