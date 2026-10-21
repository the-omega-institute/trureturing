# Rational reconstruction from the Lotka–Volterra integrals

## Abstract

In every dimension at least two over a characteristic-zero field, the specified Lotka–Volterra integrals and the last coordinate generate the rational function field.

Coordinates have indices starting at zero: x(F,n,i) is the source coordinate x with index i+1. Integral indices start at one. Write m = half(n); the source uses n = 2m−1 in the odd case and n = 2m in the even case. All index arithmetic is in the natural numbers, with subtraction truncated at zero. Empty sums are zero and empty products are one. Division in the function field is total, with inverse of zero equal to zero.

**Definition 1.1 (The rational function field).**

$$\forall (F: \operatorname{Type}*) [\operatorname{Field}\left(F\right)] , (\forall (n: \mathbb{N}), (\operatorname{FunctionField}\left(F, n\right) = \operatorname{FractionRing}\left(\operatorname{MvPolynomial}\left(\operatorname{Fin}\left(n\right), F\right)\right)))$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.FunctionField` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the fraction field of the polynomial ring on Fin(n), the set of indices from zero to n−1. The coefficient field is arbitrary and n may be zero.

**Definition 1.2 (The coordinate functions).**

$$\forall (F: \operatorname{Type}*) [\operatorname{Field}\left(F\right)] , (\forall (n: \mathbb{N}), (\forall (i: \mathbb{N}), (\operatorname{x}\left(F, n, i\right) = \begin{cases}\operatorname{algebraMap}\left(\operatorname{MvPolynomial}\left(\operatorname{Fin}\left(n\right), F\right), \operatorname{FunctionField}\left(F, n\right), X_{i}\right)&i < n\\0&n \le i\end{cases})))$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.x` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For i < n, X_i denotes the polynomial indeterminate at the corresponding element of Fin(n), and algebraMap is the canonical map from the polynomial ring to its fraction field. Thus x(F,n,i) is the source's x_{i+1}. For every natural i at least n, the coordinate function is defined to be zero.

**Definition 1.3 (The partial sums).**

$$\forall (F: \operatorname{Type}*) [\operatorname{Field}\left(F\right)] , (\forall (n: \mathbb{N}), (\forall (i: \mathbb{N}), (\operatorname{S}\left(F, n, i\right) = \sum_{j \in \operatorname{Finset.range}\left(i\right)} (\operatorname{x}\left(F, n, j\right)))))$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.S` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

S(F,n,i) is the sum of the first i coordinates, so it is the source's x_1 + ⋯ + x_i when i ≤ n. It is zero for i = 0 and remains equal to S(F,n,n) for i ≥ n because the remaining coordinates are zero.

**Definition 1.4 (The number of forward integrals).**

$$\forall (n: \mathbb{N}), (\operatorname{half}\left(n\right) = \operatorname{Nat.div}\left(n + 1, 2\right))$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.half` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nat.div is natural-number floor division, giving m = floor((n+1)/2). Hence n = 2m−1 for positive odd n, and n = 2m for even n, including zero.

**Definition 1.5 (The forward integrals in both parities).**

$$\forall (F: \operatorname{Type}*) [\operatorname{Field}\left(F\right)] , (\forall (n: \mathbb{N}), (\forall (k: \mathbb{N}), (\operatorname{Fk}\left(F, n, k\right) = \begin{cases}(\operatorname{S}\left(F, n, 2 \cdot (k) - 1\right)) \cdot (\prod_{s \in \operatorname{Finset.Ico}\left(k, \operatorname{half}\left(n\right)\right)} (\frac{\operatorname{x}\left(F, n, 2 \cdot (s)\right)}{\operatorname{x}\left(F, n, 2 \cdot (s) - 1\right)}))&\operatorname{Nat.mod}\left(n, 2\right) = 1\\(\operatorname{S}\left(F, n, 2 \cdot (k)\right)) \cdot (\prod_{s \in \operatorname{Finset.Ico}\left(k, \operatorname{half}\left(n\right)\right)} (\frac{\operatorname{x}\left(F, n, 2 \cdot (s) + 1\right)}{\operatorname{x}\left(F, n, 2 \cdot (s)\right)}))&\operatorname{Nat.mod}\left(n, 2\right) \ne 1\end{cases})))$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.Fk` (`✓ std3`).

*Citation.* Ian Marquette; Peter H. van der Kamp; G. R. W. Quispel (2026). *Subalgebras of integrals, commutants, and superintegrable deformations of Lotka-Volterra systems*. URL: <https://arxiv.org/abs/2602.17945v1>.

*Commentary.*

Section 3 defines F_k for 1 ≤ k ≤ m. After shifting coordinate indices down by one, the odd factors x_{2s+1}/x_{2s} become x(F,n,2s)/x(F,n,2s−1), and the even factors x_{2s+2}/x_{2s+1} become x(F,n,2s+1)/x(F,n,2s). The finite interval Ico(k,m) contains k ≤ s < m. The displayed definition also specifies Fk for all natural n and k.

**Definition 1.6 (The reversed integrals).**

$$\forall (F: \operatorname{Type}*) [\operatorname{Field}\left(F\right)] , (\forall (n: \mathbb{N}), (\forall (k: \mathbb{N}), (\operatorname{Gk}\left(F, n, k\right) = (\operatorname{S}\left(F, n, n\right) - \operatorname{S}\left(F, n, 2 \cdot (\operatorname{half}\left(n\right) - k)\right)) \cdot (\prod_{s \in \operatorname{Finset.range}\left(\operatorname{half}\left(n\right) - k\right)} (\frac{\operatorname{x}\left(F, n, 2 \cdot (s)\right)}{\operatorname{x}\left(F, n, 2 \cdot (s) + 1\right)})))))$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.Gk` (`✓ std3`).

*Citation.* Ian Marquette; Peter H. van der Kamp; G. R. W. Quispel (2026). *Subalgebras of integrals, commutants, and superintegrable deformations of Lotka-Volterra systems*. URL: <https://arxiv.org/abs/2602.17945v1>.

*Commentary.*

In Section 3, G_k is obtained from F_k by reversing the n coordinates. For 1 ≤ k ≤ m, its initial sum is S(F,n,n) − S(F,n,2(m−k)), and its product is the prefix of ratios of source odd coordinates to source even coordinates. Reindexing the reversed product gives the same expression in both parities. The total definition uses natural subtraction when k exceeds m.

**Definition 1.7 (The n rational inputs).**

$$\forall (F: \operatorname{Type}*) [\operatorname{Field}\left(F\right)] , (\forall (n: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(n\right)), (\operatorname{inputs}\left(F, n, i\right) = \begin{cases}\operatorname{Fk}\left(F, n, \operatorname{Fin.val}\left(i\right) + 1\right)&\operatorname{Fin.val}\left(i\right) < \operatorname{half}\left(n\right)\\\operatorname{Gk}\left(F, n, (\operatorname{Fin.val}\left(i\right) - \operatorname{half}\left(n\right)) + (\begin{cases}2&\operatorname{Nat.mod}\left(n, 2\right) = 1\\1&\operatorname{Nat.mod}\left(n, 2\right) \ne 1\end{cases})\right)&(\operatorname{half}\left(n\right) \le \operatorname{Fin.val}\left(i\right)) \land (\operatorname{Fin.val}\left(i\right) + 1 < n)\\\operatorname{x}\left(F, n, n - 1\right)&(\operatorname{half}\left(n\right) \le \operatorname{Fin.val}\left(i\right)) \land (n \le \operatorname{Fin.val}\left(i\right) + 1)\end{cases})))$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.inputs` (`✓ std3`).

*Citation.* Ian Marquette; Peter H. van der Kamp; G. R. W. Quispel (2026). *Subalgebras of integrals, commutants, and superintegrable deformations of Lotka-Volterra systems*. URL: <https://arxiv.org/abs/2602.17945v1>.

*Commentary.*

For n ≥ 2, the list begins with F_1 through F_m and ends with the source coordinate x_n = x(F,n,n−1). Between them are G_2 through G_{m−1} when n is odd, and G_1 through G_{m−1} when n is even. There are n entries in either case; an empty middle range contributes no entries. These are the distinct integrals of Section 3, with F_m = G_m equal to the total sum and, in odd dimension, F_1 = G_1. The even list includes G_1, which the list in Appendix A.2 omits. The formula uses v = Fin.val(i), the zero-based value of i, and retains the definition for every n, including zero and one.

**Definition 1.8 (Generation of the full function field).**

$$\operatorname{claim} \Leftrightarrow (\forall (F: \operatorname{Type}*) [\operatorname{Field}\left(F\right)] [\operatorname{CharZero}\left(F\right)] , (\forall (n: \mathbb{N}), ((2 \le n) \Rightarrow (\operatorname{IntermediateField.adjoin}\left(F, \operatorname{Set.range}\left(\operatorname{inputs}\left(F, n\right)\right)\right) = \operatorname{top}))))$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.claim` (`✓ std3`).

*Citation.* Ian Marquette; Peter H. van der Kamp; G. R. W. Quispel (2026). *Subalgebras of integrals, commutants, and superintegrable deformations of Lotka-Volterra systems*. URL: <https://arxiv.org/abs/2602.17945v1>.

*Commentary.*

The birationality conjecture in Section 2 and Appendix A is expressed as generation of the rational function field by the n specified inputs. The assertion quantifies over every characteristic-zero field and every n ≥ 2. Here top is the full intermediate field inside FunctionField(F,n); no evaluation at a particular coordinate tuple or nonvanishing assumption on such a tuple is imposed.

**Theorem 1.9 (The integrals and last coordinate generate the field).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.result` (`✓ std3`). ∎

*Resolves.* `Problems/marquette-vanderkamp-quispel-2026-lotka-volterra-birationality` (proved) by `D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"marquette-vanderkamp-quispel-2026-lotka-volterra-birationality","declaration_gid":"D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ian Marquette; Peter H. van der Kamp; G. R. W. Quispel (2026). *Subalgebras of integrals, commutants, and superintegrable deformations of Lotka-Volterra systems*. URL: <https://arxiv.org/abs/2602.17945v1>.

*Commentary.*

Use the integrals of Marquette, van der Kamp and Quispel. For the reconstruction, write y_j = x(F,n,j−1) with 1 ≤ j ≤ n, T_i = S(F,n,i), H = T_n, and suppress F and n in Fk and Gk. Thus T_0 = 0 and T_i − T_{i−1} = y_i. Each coordinate and each nonempty consecutive sum of coordinates is a nonzero rational function, by linear independence of polynomial indeterminates.

For odd n = 2m−1, put C = F_1 = G_1. Cancellation of products gives F_k G_{m−k}/C = T_{2k−1}(H − T_{2k})/y_{2k} for 1 ≤ k < m, and F_k G_{m−k+1}/C = T_{2k−1}(H − T_{2k−2})/y_{2k−1} for 1 ≤ k ≤ m. Set D_{2k} = F_k G_{m−k}/C and D_{2k−1} = F_k G_{m−k+1}/C − H. These identities give D_i y_i = T_{i−1}(H − T_i). Since G_m = H and G_1 = C, all the D_i needed for 2 ≤ i < n lie in the field of the inputs.

Starting at T_{n−1} = H − y_n, recover the partial sums downwards by T_{i−1} = D_i T_i/(H − T_i + D_i), for i = n−1 down to 2. The denominator is nonzero: its product with y_i is (H − T_i)T_i, a product of two nonempty consecutive sums. Differences of consecutive partial sums then recover every coordinate.

For even n = 2m with m ≥ 2, write u = y_n and f = F_{m−1}. The second-to-last coordinate is y_{n−1} = u(H − u)/(f + u). The ratio product P = product over 1 ≤ j ≤ m of y_{2j}/y_{2j−1} is u(H + f)/(G_1(H − u)). For 1 ≤ k < m, recover T_{2k} = H F_k/(F_k + P G_{m−k}) and R_k = G_{m−k}/(H − T_{2k}), where R_k is the product over 1 ≤ j ≤ k of y_{2j−1}/y_{2j}. The endpoints are T_0 = 0, T_{2m} = H, R_0 = 1 and R_m = 1/P. Thus r_k = R_k/R_{k−1} is y_{2k−1}/y_{2k}. With q_k = T_{2k} − T_{2k−2}, obtain y_{2k} = q_k/(1+r_k) and y_{2k−1} = q_k − y_{2k}, for 1 ≤ k ≤ m. The denominators are nonzero by the coordinate and consecutive-sum identities. When n = 2, simply use y_1 = H − y_2.

In either parity, all coordinates belong to the intermediate field generated by the inputs. This field contains every polynomial in the coordinates and every quotient of such polynomials, so it is the whole rational function field.

## References

- Truth anchor: `D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.Fk`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.FunctionField`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.Gk`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.S`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.claim`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.half`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.inputs`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.result`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.x`
