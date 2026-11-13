# Iterated Beatty Range: the Universal Extension Fails

## Abstract

The positive fixed point two at modulus sqrt two defeats the full proposed extension.

**Definition 1.1 (The source's natural floor map).**

$$\forall \alpha\in \mathbb{R}, \forall k \in \mathbb{N},\; \operatorname{nativeBeatty}\left(\alpha, k\right) = \lfloor \alpha \cdot k \rfloor_{\mathbb{N}}$$

*Formalization.* `D5/S3/Arith/Beatty/IteratedBeattyRangeRefutation.nativeBeatty` (`✓ std3`).

*Citation.* Mohsen Khani, Ali N. Valizadeh and Afshin Zarei (2026). *A Note on Iterated Beatty Sequences*. URL: <https://arxiv.org/abs/2607.12817v1>.

*Commentary.*

nativeBeatty(alpha,k) is Mathlib's natural floor of the real product alpha k. For alpha>1 all products at natural inputs are nonnegative, so natural floor has exactly the integer value of the source's floor.

**Definition 1.2 (The native iterated range).**

$$\forall \alpha\in \mathbb{R}, \forall n \in \mathbb{N},\; \forall x \in \mathbb{N},\; (\operatorname{nativeRange}\left(\alpha, n, x\right)) \Leftrightarrow (\exists k \in \mathbb{N},\; (1 \le k) \land (\left((\operatorname{nativeBeatty}\left(\alpha\right))^{[n]}\right)\left(k\right) = x))$$

*Formalization.* `D5/S3/Arith/Beatty/IteratedBeattyRangeRefutation.nativeRange` (`✓ std3`).

*Citation.* Mohsen Khani, Ali N. Valizadeh and Afshin Zarei (2026). *A Note on Iterated Beatty Sequences*. URL: <https://arxiv.org/abs/2607.12817v1>.

*Commentary.*

The superscript [n] denotes Function.iterate, the actual n-fold composition, including each intermediate floor. It is not floor(alpha^n k). The preimage k is a positive natural. For alpha>1 and k>=1, k<=alpha k, hence k<=floor(alpha k). Induction keeps every intermediate value positive, so this is exactly the source's natural floor-map composition on positive naturals.

$$
\operatorname{frac}\left(t\right) = t - \lfloor t \rfloor
$$

**Definition 1.3 (Every strict source condition).**

$$\forall \alpha\in \mathbb{R}, \forall n \in \mathbb{N},\; \forall x \in \mathbb{N},\; (\operatorname{fractionalTest}\left(\alpha, n, x\right)) \Leftrightarrow (((1 - \frac{1}{\alpha} < \operatorname{frac}\left(\frac{x}{\alpha}\right)) \land (\operatorname{frac}\left(\frac{x}{\alpha}\right) < 1)) \land (\forall i \in \mathbb{N},\; (2 \le i) \Rightarrow ((i \le n) \Rightarrow ((1 - \frac{2}{\alpha} < \operatorname{frac}\left(\frac{x}{\alpha^{i}}\right) - \frac{\operatorname{frac}\left(\frac{x}{\alpha^{i - 1}}\right)}{\alpha}) \land (\operatorname{frac}\left(\frac{x}{\alpha^{i}}\right) - \frac{\operatorname{frac}\left(\frac{x}{\alpha^{i - 1}}\right)}{\alpha} < 1 - \frac{1}{\alpha})))))$$

*Formalization.* `D5/S3/Arith/Beatty/IteratedBeattyRangeRefutation.fractionalTest` (`✓ std3`).

*Citation.* Mohsen Khani, Ali N. Valizadeh and Afshin Zarei (2026). *A Note on Iterated Beatty Sequences*. URL: <https://arxiv.org/abs/2607.12817v1>.

*Commentary.*

The function frac is Int.fract: t minus its integer floor. Every division is real division. Exponents and i-1 are natural-number operations; i>=2 prevents truncated subtraction from changing the source index. Both bounds are strict. The first condition and every i from 2 through n are retained, including both endpoints of that integer index range.

**Definition 1.4 (The full positive-natural extension).**

$$(claim) \Leftrightarrow (\forall \alpha\in \mathbb{R}, (\operatorname{Irrational}\left(\alpha\right)) \Rightarrow ((1 < \alpha) \Rightarrow ((\alpha < \frac{3 + \sqrt{5}}{2}) \Rightarrow (\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\forall x \in \mathbb{N},\; (1 \le x) \Rightarrow ((\operatorname{nativeRange}\left(\alpha, n, x\right)) \Leftrightarrow (\operatorname{fractionalTest}\left(\alpha, n, x\right))))))))$$

*Formalization.* `D5/S3/Arith/Beatty/IteratedBeattyRangeRefutation.claim` (`✓ std3`).

*Citation.* Mohsen Khani, Ali N. Valizadeh and Afshin Zarei (2026). *A Note on Iterated Beatty Sequences*. URL: <https://arxiv.org/abs/2607.12817v1>.

*Commentary.*

Question 1 on printed page 8 asks whether the page-one characterization extends below c=(3+sqrt(5))/2. The claim quantifies over every irrational real alpha in the full interval (1,c), every natural n>=1, and every positive natural x. It asserts the complete equivalence between native iterate-range membership and all fractional conditions. The internal split rho, the greatest real root of t^4-2t^3-t+1, is included even though the displayed union of open branches omits it. The source's convention on including zero is unresolved; this definition uses positive naturals.

**Theorem 1.5 (Literal negation of the extension).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Beatty/IteratedBeattyRangeRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/khani-valizadeh-zarei-2026-iterated-beatty-extension` (refuted) by `D5/S3/Arith/Beatty/IteratedBeattyRangeRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"khani-valizadeh-zarei-2026-iterated-beatty-extension","declaration_gid":"D5/S3/Arith/Beatty/IteratedBeattyRangeRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mohsen Khani, Ali N. Valizadeh and Afshin Zarei (2026). *A Note on Iterated Beatty Sequences*. URL: <https://arxiv.org/abs/2607.12817v1>.

*Commentary.*

Take alpha=sqrt(2), n=3, x=2 and the positive preimage k=2. Existing Mathlib theorems supply irrationality, 1<sqrt(2)<3/2<c and its exact square. The strict bounds 2<2sqrt(2)<3 give nativeBeatty(sqrt(2),2)=2. Function.iterate_fixed therefore gives actual third-iterate membership. The fractional parts at indices two and three are 0 and 1/sqrt(2). At i=3 the tested expression is 1/sqrt(2), strictly greater than 1-1/sqrt(2), because 2/sqrt(2)=sqrt(2)>1. Thus the required upper bound fails. Both the input and iterate witness are 2, so the same counterexample applies if the source's naturals also include zero. The polynomial defining rho has value -1 at 2 and 25 at 3; continuity gives a root in (2,3), so its greatest root exceeds 2. Consequently this witness is in the lower printed branch as well. The theorem originally restricted to alpha>c is not refuted.

## References

- Truth anchor: `D5/S3/Arith/Beatty/IteratedBeattyRangeRefutation.claim`
- Truth anchor: `D5/S3/Arith/Beatty/IteratedBeattyRangeRefutation.fractionalTest`
- Truth anchor: `D5/S3/Arith/Beatty/IteratedBeattyRangeRefutation.nativeBeatty`
- Truth anchor: `D5/S3/Arith/Beatty/IteratedBeattyRangeRefutation.nativeRange`
- Truth anchor: `D5/S3/Arith/Beatty/IteratedBeattyRangeRefutation.result`
