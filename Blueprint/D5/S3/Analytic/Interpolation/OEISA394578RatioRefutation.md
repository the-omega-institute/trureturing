# The moving-point interpolation ratio cannot tend to one quarter

## Abstract

A uniform enclosure for the native moving-point interpolant excludes the asserted consecutive-ratio limit of one quarter.

**Definition 1.1 (The native rational interpolant).**

$$\forall n \in \mathbb{N},\; \operatorname{p}\left(n\right) = \operatorname{Lagrange.interpolate}\left(\operatorname{range}\left(n + 1\right), (fun i:\mathbb{N} \mapsto \operatorname{Nat.cast}\left(\mathbb{Q}, i\right) + 1), (fun i:\mathbb{N} \mapsto \operatorname{ite}\left(i = 0, 0, 1\right))\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OEISA394578RatioRefutation.p` (`✓ std3`).

*Citation.* Clark Kimberling (2026). *A394578: a(n) = 2^(2*n-1) * p(n, n+1/2), where p(n,x) is the Lagrange interpolating polynomial through (1,0) and (k,1) for k=2..n+1*. URL: <https://oeis.org/A394578/internal>.

*Commentary.*

The source says: p(n,x) is the Lagrange interpolating polynomial through (1,0) and (k,1) for k=2..n+1. The finite set range(n+1) contains indices 0 through n. The node map i -> i+1 is injective over Q and the value map is zero at index zero and one at every other index. Mathlib's Lagrange.interpolate gives exactly the unique polynomial of degree at most n with those values. The source node k corresponds to i+1, while n is unchanged.

**Definition 1.2 (The source normalization).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \frac{4^{n}}{2} \cdot \operatorname{eval}\left(\operatorname{p}\left(n\right), \operatorname{Nat.cast}\left(\mathbb{Q}, n\right) + \frac{1}{2}\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OEISA394578RatioRefutation.a` (`✓ std3`).

*Citation.* Clark Kimberling (2026). *A394578: a(n) = 2^(2*n-1) * p(n, n+1/2), where p(n,x) is the Lagrange interpolating polynomial through (1,0) and (k,1) for k=2..n+1*. URL: <https://oeis.org/A394578/internal>.

*Commentary.*

The source defines a(n) = 2^(2*n-1) p(n,n+1/2); its displayed program uses (1/2) 4^n p(n,n+1/2). The normalization is the rational expression 4^n/2 for every natural n, including zero. At n=0 the sole interpolation value is zero, so p_0 is the zero polynomial and a(0)=0. eval denotes polynomial evaluation over Q; the half in the moving argument is rational.

**Definition 1.3 (The printed ratio-limit assertion).**

$$claim \Leftrightarrow \operatorname{Tendsto}\left((fun n:\mathbb{N} \mapsto \frac{\operatorname{Rat.cast}\left(\mathbb{R}, \operatorname{a}\left(n + 1\right)\right)}{\operatorname{Rat.cast}\left(\mathbb{R}, \operatorname{a}\left(n\right)\right)}), atTop, \operatorname{nhds}\left(\frac{1}{4}\right)\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OEISA394578RatioRefutation.claim` (`✓ std3`).

*Citation.* Clark Kimberling (2026). *A394578: a(n) = 2^(2*n-1) * p(n, n+1/2), where p(n,x) is the Lagrange interpolating polynomial through (1,0) and (k,1) for k=2..n+1*. URL: <https://oeis.org/A394578/internal>.

*Commentary.*

The source assertion is: Conjecture: a(n+1)/a(n) -> 1/4. Rat.cast embeds the rational sequence values into R before real division. The ratio function uses the original unshifted indices. Tendsto uses natural atTop and the real neighborhood filter at 1/4. Lean division is total, but a(n) is positive for every n>=1 in the argument below, so all tail denominators are nonzero. A value at n=0 does not affect this limit.

**Theorem 1.4 (The ratio-limit assertion is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/OEISA394578RatioRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a394578-interpolation-ratio-limit` (refuted) by `D5/S3/Analytic/Interpolation/OEISA394578RatioRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a394578-interpolation-ratio-limit","declaration_gid":"D5/S3/Analytic/Interpolation/OEISA394578RatioRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Clark Kimberling (2026). *A394578: a(n) = 2^(2*n-1) * p(n, n+1/2), where p(n,x) is the Lagrange interpolating polynomial through (1,0) and (k,1) for k=2..n+1*. URL: <https://oeis.org/A394578/internal>.

*Commentary.*

The sum of the Lagrange bases is one. Removing the basis for node 1 therefore gives p_n. Its error at n+1/2 is the product, for 0<=j<n, of (n-j-3/2)/(-(j+1)). Reversing the numerator factors yields absolute values |j-1/2|. For n>=1 the first factor is 1/2, and each remaining factor is at most its corresponding positive denominator factor. The absolute error is at most 1/2, so p_n(n+1/2) lies in [1/2,3/2]. Positive normalization yields positive a(n) on this tail and the adjacent enclosures give a(n+1)/a(n)>=4/3. A sequence with this eventual lower bound cannot converge to 1/4. This conclusion concerns exactly the printed ratio assertion; it asserts no correct limit, recurrence, integrality or D-finiteness property.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/OEISA394578RatioRefutation.a`
- Truth anchor: `D5/S3/Analytic/Interpolation/OEISA394578RatioRefutation.claim`
- Truth anchor: `D5/S3/Analytic/Interpolation/OEISA394578RatioRefutation.p`
- Truth anchor: `D5/S3/Analytic/Interpolation/OEISA394578RatioRefutation.result`
