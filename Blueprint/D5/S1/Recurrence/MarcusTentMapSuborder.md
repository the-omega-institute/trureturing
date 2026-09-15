# Marcus's Tent-Map Cycle Length

## Abstract

Marcus's tent-map cycle length equals the signed suborder of two.

The tent map on [0,1] sends x to 1-|2x-1|. The symbols n, N, k, and m denote natural numbers; N=2n+1 in the theorem. For N>0 and k<=N, tent(N,k) is its numerator action at the rational point k/N. Subtraction is natural subtraction, with no truncation in either orbit branch. The function minimalPeriod gives the least positive return time of a point, or zero when there is no positive return. The signed suborder of 2 modulo 2n+1 is the least m>0 with 2^m congruent to 1 or -1; the latter residue is written 2n. Congruence means that the modulus divides the integer difference, and IsLeast asserts membership in the displayed set and a lower bound for every member. Only Marcus's Jul 16 2025 cycle-length sentence in A003558 is settled here. Kaprekar cycles, x^2-2 iteration, and the Kappraff-Adamson base conjecture are not claimed. The hypothesis n>0 excludes n=0, where N=1 and 2/N is outside [0,1].

**Definition 1.1 (The numerator tent map).**

$$\forall N \in \mathbb{N}, k \in \mathbb{N},\; \operatorname{tent}\left(N, k\right) = \begin{cases}2 \cdot k& (2 \cdot k \le N)\\2 \cdot N - 2 \cdot k& (N < 2 \cdot k)\end{cases}$$

*Formalization.* `D5/S1/Recurrence/MarcusTentMapSuborder.tent` (`✓ std3`).

*Citation.* N. J. A. Sloane; Michel Marcus (2025). *OEIS A003558, least m with 2^m = ±1 mod 2n+1, with Marcus's tent-map cycle-length conjecture*. URL: <https://oeis.org/A003558>.

*Commentary.*

If 2k<=N, the absolute-value expression equals 2k/N. If N<2k and k<=N, it equals (2N-2k)/N, and the nonnegative numerator agrees with natural subtraction. The displayed definition is total on natural N and k; its interpretation as a rational tent-map numerator uses N>0 and k<=N.

**Theorem 1.2 (The cycle-length conjecture).**

$$\forall n \in \mathbb{N},\; (0 < n) \Rightarrow (\operatorname{IsLeast}\left(\left\{m \in \mathbb{N} \mid (0 < m) \land ((2^{m} \equiv 1 (\operatorname{mod} 2 \cdot n + 1)) \lor (2^{m} \equiv 2 \cdot n (\operatorname{mod} 2 \cdot n + 1)))\right\}, \operatorname{minimalPeriod}\left(\operatorname{tent}\left(2 \cdot n + 1\right), 2\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/MarcusTentMapSuborder.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a003558-marcus-tent-map-suborder` (proved) by `D5/S1/Recurrence/MarcusTentMapSuborder.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a003558-marcus-tent-map-suborder","declaration_gid":"D5/S1/Recurrence/MarcusTentMapSuborder.result","resolution_kind":"proved"} -->

*Citation.* N. J. A. Sloane; Michel Marcus (2025). *OEIS A003558, least m with 2^m = ±1 mod 2n+1, with Marcus's tent-map cycle-length conjecture*. URL: <https://oeis.org/A003558>.

*Commentary.*

For N=2n+1, induction shows that every iterate from numerator 2 stays even and at most N, and represents either sign of 2^(m+1) modulo N. Since N is odd, the even representative of either sign of 2 in this interval must be 2. Cancelling the unit 2 therefore makes a return at time m equivalent to 2^m being congruent to 1 or -1. Euler's theorem supplies a positive return, and minimalPeriod gives the least one. Division by the fixed positive N preserves equality of numerators, so these are also the return times of 2/N.

## References

- Truth anchor: `D5/S1/Recurrence/MarcusTentMapSuborder.result`
- Truth anchor: `D5/S1/Recurrence/MarcusTentMapSuborder.tent`
