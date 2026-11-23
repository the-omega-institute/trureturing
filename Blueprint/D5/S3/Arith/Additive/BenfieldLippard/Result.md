# Oscillation of stable exception-set sizes

## Abstract

The sizes of the stable exception sets have strict adjacent rises and falls in every tail.

**Theorem 1.1 (Benfield–Lippard Conjecture 10.5).**

Lean statement: `D5/S3/Arith/Additive/BenfieldLippard/Result.conjecture_10_5`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/BenfieldLippard/Result.conjecture_10_5` (`✓ std3`). ∎

*Resolves.* `Problems/benfield-lippard-2025-exception-set-oscillation` (proved) by `D5/S3/Arith/Additive/BenfieldLippard/Result.conjecture_10_5`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"benfield-lippard-2025-exception-set-oscillation","declaration_gid":"D5/S3/Arith/Additive/BenfieldLippard/Result.conjecture_10_5","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Brennan Benfield, Oliver Lippard (2025). *Integers that are not the sum of positive powers*. URL: <https://arxiv.org/abs/2404.08193v2>.

*Commentary.*

Conjecture 10.5 (p. 10). The sequence |Bₖ| for k = 2, 3, … never becomes monotone. For every exponent k ≥ 2, there is a finite set B(k) that equals the set of positive offsets s missing from the sums j+s of exactly j positive kth powers, for every sufficiently large j. The j bases are indexed by Fin j and may repeat.

Given a cutoff N ≥ 2, choose a prime p ≥ max(193,N+2). The lower bound at p−1 exceeds the upper bounds at the two odd exponents p−2 and p. Thus the strict rise at p−2 and the strict fall at p−1 both lie in the prescribed tail.

## References

- Truth anchor: `D5/S3/Arith/Additive/BenfieldLippard/Result.conjecture_10_5`
- Dependency: [D5/S3/Arith/Additive/BenfieldLippard/EvenBound](EvenBound.md)
- Dependency: [D5/S3/Arith/Additive/BenfieldLippard/OddBound](OddBound.md)
