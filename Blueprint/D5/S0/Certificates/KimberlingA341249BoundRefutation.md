# Kimberling's OEIS A341249 Bound

## Abstract

The term n = 2 refutes the upper bound in the OEIS A341249 conjecture.

**Definition 1.1 (The outer multiplier).**

$$r:\mathbb{R} = 2 + \sqrt{2}$$

*Formalization.* `D5/S0/Certificates/KimberlingA341249BoundRefutation.r` (`✓ std3`).

*Citation.* Clark Kimberling (2021). *OEIS A341249: a(n) = floor(r*floor(s*n)), where r = 2 + sqrt(2) and s = sqrt(2).*. URL: <https://oeis.org/A341249>.

*Commentary.*

OEIS A341249, NAME, revision 10 (unpaginated): "a(n) = floor(r*floor(s*n)), where r = 2 + sqrt(2) and s = sqrt(2)." The outer multiplier r is a real number.

**Definition 1.2 (The inner multiplier).**

$$s:\mathbb{R} = \sqrt{2}$$

*Formalization.* `D5/S0/Certificates/KimberlingA341249BoundRefutation.s` (`✓ std3`).

*Citation.* Clark Kimberling (2021). *OEIS A341249: a(n) = floor(r*floor(s*n)), where r = 2 + sqrt(2) and s = sqrt(2).*. URL: <https://oeis.org/A341249>.

*Commentary.*

OEIS A341249, NAME, revision 10 (unpaginated): "a(n) = floor(r*floor(s*n)), where r = 2 + sqrt(2) and s = sqrt(2)." The inner multiplier s is a real number.

**Definition 1.3 (The nested-floor sequence).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \lfloor r \cdot (\lfloor s \cdot (n:\mathbb{R})\rfloor:\mathbb{R})\rfloor$$

*Formalization.* `D5/S0/Certificates/KimberlingA341249BoundRefutation.a` (`✓ std3`).

*Citation.* Clark Kimberling (2021). *OEIS A341249: a(n) = floor(r*floor(s*n)), where r = 2 + sqrt(2) and s = sqrt(2).*. URL: <https://oeis.org/A341249>.

*Commentary.*

OEIS A341249, NAME, revision 10 (unpaginated): "a(n) = floor(r*floor(s*n)), where r = 2 + sqrt(2) and s = sqrt(2)." The index n is natural, and both floors take integer values. Integer and natural values in real products are cast to Real. The source begins at n = 1 with 3, 6, 13, 17; the Lean function also has its formula-defined value at zero.

**Definition 1.4 (The conjectured two strict bounds).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; 1 \le n \Rightarrow ((1 < r \cdot s \cdot (n:\mathbb{R}) - (\operatorname{a}\left(n\right):\mathbb{R})) \land (r \cdot s \cdot (n:\mathbb{R}) - (\operatorname{a}\left(n\right):\mathbb{R}) < 2)))$$

*Formalization.* `D5/S0/Certificates/KimberlingA341249BoundRefutation.claim` (`✓ std3`).

*Citation.* Clark Kimberling (2021). *OEIS A341249: a(n) = floor(r*floor(s*n)), where r = 2 + sqrt(2) and s = sqrt(2).*. URL: <https://oeis.org/A341249>.

*Commentary.*

OEIS A341249, COMMENTS, revision 10 (unpaginated): "Conjecture:  1 < r*s*n - a(n) < 2 for n >= 1." The index n ranges over the natural numbers with n at least 1. Both inequalities are strict and are evaluated in Real.

**Theorem 1.5 (The upper bound fails at n = 2).**

$$\neg (\forall n \in \mathbb{N},\; 1 \le n \Rightarrow ((1 < r \cdot s \cdot (n:\mathbb{R}) - (\operatorname{a}\left(n\right):\mathbb{R})) \land (r \cdot s \cdot (n:\mathbb{R}) - (\operatorname{a}\left(n\right):\mathbb{R}) < 2)))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/KimberlingA341249BoundRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/kimb341249-bound` (refuted) by `D5/S0/Certificates/KimberlingA341249BoundRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kimb341249-bound","declaration_gid":"D5/S0/Certificates/KimberlingA341249BoundRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Clark Kimberling (2021). *OEIS A341249: a(n) = floor(r*floor(s*n)), where r = 2 + sqrt(2) and s = sqrt(2).*. URL: <https://oeis.org/A341249>.

*Commentary.*

At n = 2, the inner floor is 2 and the outer floor is 6. The difference r*s*2 - a(2) is 4*sqrt(2) - 2, which exceeds 2 because sqrt(2) > 1. Thus the universal conjunction is false.

## References

- Truth anchor: `D5/S0/Certificates/KimberlingA341249BoundRefutation.a`
- Truth anchor: `D5/S0/Certificates/KimberlingA341249BoundRefutation.claim`
- Truth anchor: `D5/S0/Certificates/KimberlingA341249BoundRefutation.r`
- Truth anchor: `D5/S0/Certificates/KimberlingA341249BoundRefutation.result`
- Truth anchor: `D5/S0/Certificates/KimberlingA341249BoundRefutation.s`
