# The printed preperiod formula for the strict greedy sequence with seeds 5 and 21

## Abstract

The strict greedy sequence with seeds 5 and 21 has no positive gap period after nine gaps.

**Definition 1.1 (The specialized assertion).**

$$\operatorname{HasGapPreperiod}\left(\operatorname{S}\left(5, 21\right), 9\right)$$

*Formalization.* `D5/S1/Words/Sumfree/StrictTwoSumfreePreperiodRefutation.claim` (`✓ std3`).

*Citation.* Daan van Berkel, Wieb Bosma (2026). *Periodicity conjectures for all 2-sumfree sequences*. DOI: [10.48550/arXiv.2609.18522](https://doi.org/10.48550/arXiv.2609.18522). URL: <https://arxiv.org/abs/2609.18522v1>.

*Commentary.*

S(5,21) starts with 5 and 21. Each later entry is the least larger natural number avoiding sums of two distinct earlier entries. HasGapPreperiod(S,k) says that k is the least number of initial differences to discard for the remaining differences to have a positive period. At d=16=6+1*10, Definition 8(e) gives 30 and (k1) subtracts 21. Conjecture 9 applied to these seeds therefore asserts preperiod length 9. Example 10 lists 15 for the same pair.

**Theorem 1.2 (No positive gap period starts after nine gaps).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sumfree/StrictTwoSumfreePreperiodRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/van-berkel-bosma-2026-conjecture-9` (refuted) by `D5/S1/Words/Sumfree/StrictTwoSumfreePreperiodRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"van-berkel-bosma-2026-conjecture-9","declaration_gid":"D5/S1/Words/Sumfree/StrictTwoSumfreePreperiodRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Daan van Berkel, Wieb Bosma (2026). *Periodicity conjectures for all 2-sumfree sequences*. DOI: [10.48550/arXiv.2609.18522](https://doi.org/10.48550/arXiv.2609.18522). URL: <https://arxiv.org/abs/2609.18522v1>.

*Commentary.*

The explicit increasing enumeration has a finite head and translates of a fourteen-entry block by multiples of 56. The greedy recurrence is certified through 288 and by strict-sum residue arguments from 288 onward. The least-next-entry rule gives uniqueness. At zero-based gap index 14, the difference from 51 to 61 is 10. Every later difference is at most 9, so any positive shift of gap 14 violates the proposed periodicity. The source and independent certificate are recorded under issue #34312.

## References

- Truth anchor: `D5/S1/Words/Sumfree/StrictTwoSumfreePreperiodRefutation.claim`
- Truth anchor: `D5/S1/Words/Sumfree/StrictTwoSumfreePreperiodRefutation.result`
