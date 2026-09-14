# Rounded Half-Root-Two Differences

## Abstract

Rounded multiples of one over sqrt two have binary differences at the two shifted Beatty position sequences.

**Definition 1.1 (Nearest integers to multiples of one over sqrt two).**

$$\forall n \in \mathrm{Nat},\; a\left(n\right) = round\left(n / \sqrt{2}\right)$$

*Formalization.* `D5/S1/Deficit/Beatty/KimberlingRoundedHalfRootTwoDifference.a` (`✓ std3`).

*Citation.* N. J. A. Sloane; Clark Kimberling (2014). *OEIS A049473, Nearest integer to n/sqrt(2)*. URL: <https://oeis.org/A049473>.

*Commentary.*

For each natural n, a(n) is the nearest integer to n divided by sqrt two, with the rounding convention supplied by the real ordered ring.

**Definition 1.2 (The lower shifted Beatty sequence).**

$$\forall k \in \mathrm{Nat},\; lower\left(k\right) = \lfloor(k + 1 / 2) \cdot \sqrt{2}\rfloor$$

*Formalization.* `D5/S1/Deficit/Beatty/KimberlingRoundedHalfRootTwoDifference.lower` (`✓ std3`).

*Citation.* N. J. A. Sloane; Clark Kimberling (2014). *OEIS A049473, Nearest integer to n/sqrt(2)*. URL: <https://oeis.org/A049473>.

*Commentary.*

For each natural k, lower(k) is the floor of (k+1/2) times sqrt two. These are the positions at which the rounded sequence increases by one.

**Definition 1.3 (The upper shifted Beatty sequence).**

$$\forall k \in \mathrm{Nat},\; upper\left(k\right) = \lfloor(k + 1 / 2) \cdot (2 + \sqrt{2})\rfloor$$

*Formalization.* `D5/S1/Deficit/Beatty/KimberlingRoundedHalfRootTwoDifference.upper` (`✓ std3`).

*Citation.* N. J. A. Sloane; Clark Kimberling (2014). *OEIS A049473, Nearest integer to n/sqrt(2)*. URL: <https://oeis.org/A049473>.

*Commentary.*

For each natural k, upper(k) is the floor of (k+1/2) times two plus sqrt two. These are the positions at which the rounded sequence has zero difference.

**Theorem 1.4 (The difference and position characterization).**

$$\forall n \in \mathrm{Nat},\; (a\left(n + 1\right) - a\left(n\right) = 0 \lor a\left(n + 1\right) - a\left(n\right) = 1) \land \left((a\left(n + 1\right) - a\left(n\right) = 1 \Leftrightarrow \left(\exists k \in \mathrm{Nat},\; intCast\left(n\right) = lower\left(k\right)\right)) \land (a\left(n + 1\right) - a\left(n\right) = 0 \Leftrightarrow \left(\exists k \in \mathrm{Nat},\; intCast\left(n\right) = upper\left(k\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Beatty/KimberlingRoundedHalfRootTwoDifference.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a049473-kimberling-rounded-half-root-two-difference` (proved) by `D5/S1/Deficit/Beatty/KimberlingRoundedHalfRootTwoDifference.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a049473-kimberling-rounded-half-root-two-difference","declaration_gid":"D5/S1/Deficit/Beatty/KimberlingRoundedHalfRootTwoDifference.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane; Clark Kimberling (2014). *OEIS A049473, Nearest integer to n/sqrt(2)*. URL: <https://oeis.org/A049473>.

*Commentary.*

Every adjacent difference of a is zero or one. The jump-position characterization identifies the unit differences exactly with lower, while the zero differences are exactly upper. The complementary shifted Beatty partition used in the position argument is the classical 2-Wythoff complementarity.

## References

- Truth anchor: `D5/S1/Deficit/Beatty/KimberlingRoundedHalfRootTwoDifference.a`
- Truth anchor: `D5/S1/Deficit/Beatty/KimberlingRoundedHalfRootTwoDifference.lower`
- Truth anchor: `D5/S1/Deficit/Beatty/KimberlingRoundedHalfRootTwoDifference.result`
- Truth anchor: `D5/S1/Deficit/Beatty/KimberlingRoundedHalfRootTwoDifference.upper`
