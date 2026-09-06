# Convolution Recurrence Odd Exactly at Powers of Two

## Abstract

Reflection of a convolution sum modulo two proves the parity conjecture for OEIS A397588.

**Definition 1.1 (The natural-number convolution sequence).**

$$\begin{aligned}a: \mathbb{N} \to \mathbb{N},\\\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{ite}\left(n = 1, 1, (n + 1) \cdot (\sum_{k \in \operatorname{attach}\left(\operatorname{Icc}\left(1, n - 1\right)\right)} \operatorname{a}\left(\operatorname{val}\left(k\right)\right) \cdot \operatorname{a}\left(n - \operatorname{val}\left(k\right)\right))\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The definition uses the recurrence of OEIS A397588, Paul D. Hanna, July 3, 2026; the symmetric formula is credited there to Seiichi Manyama. The operator ite selects its second argument when its first argument holds, and its third otherwise. Icc is the inclusive natural-number interval; attach retains its membership proofs, and val forgets them. All subtractions in indices are natural subtraction, truncated at zero. Well-founded recursion uses strictly smaller indices in the sum. At zero the sum is empty, giving a(0)=0 outside the source domain. The standard well-founded fix combinator implements this recursive equation, using the membership bounds to justify both recursive calls.

**Theorem 1.2 (Initial value).**

$$\operatorname{a}\left(1\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.a_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This unfolds the initial-value clause of the definition and supplies the base case of the parity characterization.

**Theorem 1.3 (The source recurrence).**

$$\forall n: \mathbb{N}, (1 < n) \Rightarrow \operatorname{a}\left(n\right) = (n + 1) \cdot (\sum_{k \in \operatorname{Icc}\left(1, n - 1\right)} \operatorname{a}\left(k\right) \cdot \operatorname{a}\left(n - k\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.a_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing only the membership-proof attachment exposes the exact source sum from one through n-1 for every n greater than one.

**Theorem 1.4 (Off-diagonal cancellation).**

$$\begin{aligned}\forall f: (\mathbb{N} \to \operatorname{ZMod}\left(2\right)), \forall m: \mathbb{N}, \\(1 \le m) \Rightarrow \sum_{k \in \operatorname{Icc}\left(1, 2 \cdot m - 1\right)} \operatorname{f}\left(k\right) \cdot \operatorname{f}\left(2 \cdot m - k\right) = \operatorname{f}\left(m\right)^{2}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.convolution_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Erase the midpoint m. Reflection k to 2m-k preserves the remaining interval, has no fixed point there, and is an involution. Each paired product occurs twice and cancels in ZMod(2). Restoring the midpoint leaves its square. This is the general pairing witness used in the halving theorem.

**Theorem 1.5 (Even-index reduction through the midpoint square).**

$$\forall m: \mathbb{N}, (1 \le m) \Rightarrow (\operatorname{cast}\left(\operatorname{a}\left(2 \cdot m\right), \operatorname{ZMod}\left(2\right)\right) = \operatorname{cast}\left(\operatorname{a}\left(m\right), \operatorname{ZMod}\left(2\right)\right)^{2}) \land (\operatorname{cast}\left(\operatorname{a}\left(m\right), \operatorname{ZMod}\left(2\right)\right)^{2} = \operatorname{cast}\left(\operatorname{a}\left(m\right), \operatorname{ZMod}\left(2\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.a_halving_via_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive m, the recurrence and convolution pairing first identify the cast of a(2m) with the square of the cast of a(m). The second conjunct records that every element of ZMod(2) equals its square.

**Theorem 1.6 (Halving an even index).**

$$\forall m: \mathbb{N}, (1 \le m) \Rightarrow \operatorname{cast}\left(\operatorname{a}\left(2 \cdot m\right), \operatorname{ZMod}\left(2\right)\right) = \operatorname{cast}\left(\operatorname{a}\left(m\right), \operatorname{ZMod}\left(2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.a_halving` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here and below cast(x,ZMod(2)) denotes the natural-number cast into the ring of integers modulo two. The recurrence factor 2m+1 casts to one. Pairing leaves the square of the midpoint value, and every element of ZMod(2) equals its square.

**Theorem 1.7 (Odd indices greater than one).**

$$\forall n: \mathbb{N}, (1 < n) \Rightarrow \operatorname{Odd}\left(n\right) \Rightarrow \operatorname{cast}\left(\operatorname{a}\left(n\right), \operatorname{ZMod}\left(2\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.a_odd_index_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For odd n greater than one, the factor n+1 is even, so the recurrence casts to zero. The parity characterization consumes this companion in its odd-index branch.

**Theorem 1.8 (Odd values occur exactly at powers of two).**

$$\forall n: \mathbb{N}, (1 \le n) \Rightarrow (\operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \Leftrightarrow (\exists r: \mathbb{N}, n = 2^{r}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.a_odd_iff_power_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

OEIS A397588 states this as a conjecture in its July 3, 2026 entry; the proof is derived here. Strong induction handles n=1 directly, halves positive even indices, and excludes odd indices greater than one. The bridge is that the natural cast into ZMod(2) equals one exactly when the natural number is Odd. The existential exponent is a natural number, hence nonnegative. Both directions hold for every positive index.

## References

- Truth anchor: `D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.a`
- Truth anchor: `D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.a_halving`
- Truth anchor: `D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.a_halving_via_square`
- Truth anchor: `D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.a_odd_iff_power_two`
- Truth anchor: `D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.a_odd_index_zero`
- Truth anchor: `D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.a_one`
- Truth anchor: `D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.a_recurrence`
- Truth anchor: `D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.convolution_pairing`
