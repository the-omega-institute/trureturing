---
bibkey: zabolotskii2025a385672
authors: Andrei Zabolotskii
year: 2025
title: "OEIS A385672, Irregular triangle read by rows: T(n, k) is the number of n-step walks on the square lattice having algebraic area k"
doi: null
url: https://oeis.org/A385672
claim: "The entry tabulates the number of n-step square-lattice walks by their algebraic area, the integral of y dx, and conjectures T(2n, n^2 - k) = 2 A029552(k) and T(2n+1, n^2 + n - k) = 4 A098613(k) for k < n."
strata_touched:
  - D5/S3/Combinatorics/LatticeWalkNearMaximalArea
license: citation-only
triage: anchor
---

# OEIS A385672

A385672 (Andrei Zabolotskii, 2025-08-04) is the triangle

> Irregular triangle read by rows: T(n, k) is the number of n-step walks on
> the square lattice having algebraic area k; n >= 0, 0 <= k <= floor(n^2/4).

with the COMMENTS lines

> Rows can be extended to negative k with T(n, -k) = T(n, k). Sums of such
> extended rows give 4^n.
>
> The algebraic area is Integral y dx over the walk, which equals
> (Sum_{steps right} y) - (Sum_{steps left} y).

and the FORMULA line

> It appears that T(2*n, n^2 - k) = 2 * A029552(k) for k < n and
> T(2*n+1, n^2+n - k) = 4 * A098613(k) for k < n.

Its rows begin `1; 4; 12, 2; 40, 8, 4; 124, 42, 16, 6, 2`.

A029552 is the "Expansion of phi(x) / f(-x) in powers of x where phi(), f()
are Ramanujan theta functions", with the FORMULA line

> G.f.: (1 + 2 * Sum_{k>0} x^(k^2)) / (Product_{k>0} (1 - x^k)).

A098613 is the "Expansion of psi(x^2) / f(-x) in powers of x", with the
FORMULA line

> G.f.: (Sum_{k>0} x^(k^2-k)) / (Product_{k>0} (1 - x^k)).

## Verified locator

- URL: https://oeis.org/A385672 (revision of 2025-08-05, FORMULA), retrieved
  2026-09-27.
- Related entries: https://oeis.org/A029552 (last modified 2025-09-16),
  https://oeis.org/A098613 (last modified 2026-06-08),
  https://oeis.org/A000041.
