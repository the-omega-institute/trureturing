# The multiplicative Hornich–Hlawka inequality

## Abstract

The multiplicative Hornich–Hlawka inequality holds in every real or complex inner product space.

Marinescu and Niculescu, A survey of the Hornich-Hlawka inequality, arXiv:2407.03278v1, §6, the paragraph applying Theorem 8 to the logarithm: “Applying Theorem 8 to the function f (x) = ln(1 + x) one obtains the multiplicative analog of the inequality (2.1), (1 + |x|)(1 + |y|)(1 + |z|)(1 + |x + y + z|) ≥ (1 + |x + y|)(1 + |y + z|)(1 + |z + x|), for all x, y, z ∈ R. No extension of this remark to the case of inner product spaces is known.”

**Definition 1.1 (The inner-product-space claim).**

$$claim \Leftrightarrow (\forall K: Type, [\operatorname{RCLike}\left(K\right)], \forall E: Type, [\operatorname{NormedAddCommGroup}\left(E\right)], [\operatorname{InnerProductSpace}\left(K, E\right)], \forall x: E, \forall y: E, \forall z: E, (1 + \left\lVert x + y \right\rVert) \cdot (1 + \left\lVert y + z \right\rVert) \cdot (1 + \left\lVert z + x \right\rVert) \le (1 + \left\lVert x \right\rVert) \cdot (1 + \left\lVert y \right\rVert) \cdot (1 + \left\lVert z \right\rVert) \cdot (1 + \left\lVert x + y + z \right\rVert))$$

*Formalization.* `D5/S3/Geometry/MultiplicativeHornichHlawka.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D.-Ş. Marinescu; C. P. Niculescu (2024). *A survey of the Hornich-Hlawka inequality*. URL: <https://arxiv.org/abs/2407.03278v1>.

*Commentary.*

The scalar type K has RCLike, and E has NormedAddCommGroup and InnerProductSpace K E. Thus the statement covers every real or complex inner product space and every triple x, y, z. It requires neither finite dimension nor completeness. The claim extends the scalar multiplicative inequality in §6 of the survey.

**Theorem 1.2 (Proof of the multiplicative inequality).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/MultiplicativeHornichHlawka.result` (`✓ std3`). ∎

*Resolves.* `Problems/marinescu-niculescu-2024-multiplicative-hornich-hlawka` (proved) by `D5/S3/Geometry/MultiplicativeHornichHlawka.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"marinescu-niculescu-2024-multiplicative-hornich-hlawka","declaration_gid":"D5/S3/Geometry/MultiplicativeHornichHlawka.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* D.-Ş. Marinescu; C. P. Niculescu (2024). *A survey of the Hornich-Hlawka inequality*. URL: <https://arxiv.org/abs/2407.03278v1>.

*Commentary.*

Set a = ‖x‖, b = ‖y‖, c = ‖z‖, d = ‖x+y+z‖, u = ‖x+y‖, v = ‖y+z‖, w = ‖z+x‖. Ptolemy gives uv ≤ ac+bd, vw ≤ ab+cd, and wu ≤ bc+ad, hence the second elementary symmetric function comparison. The Fréchet identity a²+b²+c²+d² = u²+v²+w², together with these Ptolemy comparisons, gives u+v+w ≤ a+b+c+d. With S = a+b+c+d and R = abc+abd+acd+bcd, the identity R² − (ab+cd)(ac+bd)(bc+ad) = abcd(S² − 2(a²+b²+c²+d²)) gives uvw ≤ R: the four triangle inequalities imply each of a, b, c, d is at most S/2, so the defect is nonnegative. Comparing the linear, quadratic, and cubic terms, together with abcd ≥ 0, proves the product inequality. These steps are established in scalar_inequality; ptolemy_sum, frechet_identity, and norm_triangle_four provide its geometric premises. The underlying real inner product supplied by InnerProductSpace.rclikeToReal also covers complex spaces. Equality classification and extensions to all Hornich–Hlawka normed spaces or all Bernstein functions are not established by this module.

## References

- Truth anchor: `D5/S3/Geometry/MultiplicativeHornichHlawka.claim`
- Truth anchor: `D5/S3/Geometry/MultiplicativeHornichHlawka.result`
