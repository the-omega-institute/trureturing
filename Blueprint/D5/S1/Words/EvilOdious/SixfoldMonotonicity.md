# SixfoldMonotonicity

## Abstract

Dyadic coefficient recurrences control the sixfold evil and odious representation counts.

**Theorem 1.1 (initialr 0).**

$$\operatorname{initialChunk} 1 38 0 32 = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SixfoldMonotonicity.initialr_0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.2 (initialr 1).**

$$\operatorname{initialChunk} 1 38 32 32 = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SixfoldMonotonicity.initialr_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.3 (tail positive).**

$$\forall (\operatorname{sigma} : \mathbb{Z}) , (\operatorname{sigma} = 1 \lor \operatorname{sigma} = - 1) \to \forall (n : \mathbb{N}) , (2048 \le n) \to 0 < ((n + 4) . \operatorname{choose} 4 : \mathbb{Z}) + \operatorname{errorTerm} \operatorname{sigma} n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SixfoldMonotonicity.tail_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.4 (claim).**

$$\operatorname{claim} \iff (((\exists (N : \mathbb{N}) , \forall (n : \mathbb{N}) , n \ge N \to r 6 n < r 6 (n + 1)) \land (\exists (N : \mathbb{N}) , \forall (n : \mathbb{N}) , n \ge N \to s 6 n < s 6 (n + 1))) \land (\forall (n : \mathbb{N}) , n \ge 37 \to r 6 n < r 6 (n + 1)) \land (\forall (n : \mathbb{N}) , n \ge 5 \to s 6 n < s 6 (n + 1)))$$

*Formalization.* `D5/S1/Words/EvilOdious/SixfoldMonotonicity.claim` (`✓ std3`).

*Citation.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

Conjecture 12, page 10: “(a) Both r₆(n) and s₆(n) are eventually strictly increasing. (a) r₆(n) < r₆(n + 1) for n ≥ 37. (b) s₆(n) < s₆(n + 1) for n ≥ 5.” The duplicated label (a) is printed in the source. Both eventual clauses quantify a natural threshold and all natural n beyond it. Tuple coordinates are ordered, range over the nonnegative integers, and admit repetitions.

**Theorem 1.5 (result).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SixfoldMonotonicity.result` (`✓ std3`). ∎

*Resolves.* `Problems/allouche-shallit-2021-sixfold-evil-odious` (proved) by `D5/S1/Words/EvilOdious/SixfoldMonotonicity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"allouche-shallit-2021-sixfold-evil-odious","declaration_gid":"D5/S1/Words/EvilOdious/SixfoldMonotonicity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

## References

- Truth anchor: `D5/S1/Words/EvilOdious/SixfoldMonotonicity.claim`
- Truth anchor: `D5/S1/Words/EvilOdious/SixfoldMonotonicity.initialr_0`
- Truth anchor: `D5/S1/Words/EvilOdious/SixfoldMonotonicity.initialr_1`
- Truth anchor: `D5/S1/Words/EvilOdious/SixfoldMonotonicity.result`
- Truth anchor: `D5/S1/Words/EvilOdious/SixfoldMonotonicity.tail_positive`
- Dependency: [D5/S1/Words/EvilOdious/DyadicPrefixBounds](DyadicPrefixBounds.md)
