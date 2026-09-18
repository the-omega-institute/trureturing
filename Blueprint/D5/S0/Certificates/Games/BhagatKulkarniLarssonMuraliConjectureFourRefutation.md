# A Counterexample to Conjecture 4 of Bhagat, Kulkarni, Larsson and Murali

## Abstract

For {4,22,35,38} at heap 161, Bob gains from 77 to 78 under AvA instead of FvF.

Conjecture 4 of Bhagat, Kulkarni, Larsson and Murali states: "Consider any subtraction set S, and suppose both players act friendly in case of indifference. Then each player's PSPE utility is never worse than if both players have antagonistic tie-breaking rules." The paper orders outcome pairs coordinatewise. Its Definition 2 uses the dual convention at every move; at the initial heap, the first coordinate belongs to Alice and the second to Bob.

**Definition 1.1 (The coordinatewise conjecture).**

$$(claim) \Leftrightarrow (\forall subtractions \in \operatorname{List}\left(\mathrm{Nat}\right),\; (subtractions \ne []) \Rightarrow ((\forall s \in \mathrm{Nat},\; (s \in subtractions) \Rightarrow (0 < s)) \Rightarrow ((subtractions.Nodup) \Rightarrow (\forall heap \in \mathrm{Nat},\; ((\operatorname{outcome}\left(subtractions, AvA, heap\right)).1 \le (\operatorname{outcome}\left(subtractions, FvF, heap\right)).1) \land ((\operatorname{outcome}\left(subtractions, AvA, heap\right)).2 \le (\operatorname{outcome}\left(subtractions, FvF, heap\right)).2)))))$$

*Formalization.* `D5/S0/Certificates/Games/BhagatKulkarniLarssonMuraliConjectureFourRefutation.claim` (`✓ std3`).

*Citation.* Anjali Bhagat; Tanmay Kulkarni; Urban Larsson; Divya Murali (2026). *Tie-breaking in self interest cumulative subtraction games*. URL: <https://arxiv.org/abs/2510.24280v2>.

*Commentary.*

A duplicate-free, nonempty list of positive natural numbers represents a finite nonempty subtraction set. Every natural heap is covered. For each such list and heap, both coordinates of the AvA outcome are required to be at most the corresponding FvF coordinates. The outcome recurrence realizes Definition 2; only positive steps no larger than the heap are legal.

**Definition 1.2 (The subtraction set).**

$$witnessSubtractions: \operatorname{List}\left(\mathrm{Nat}\right) = [4,22,35,38]$$

*Formalization.* `D5/S0/Certificates/Games/BhagatKulkarniLarssonMuraliConjectureFourRefutation.witnessSubtractions` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anjali Bhagat; Tanmay Kulkarni; Urban Larsson; Divya Murali (2026). *Tie-breaking in self interest cumulative subtraction games*. URL: <https://arxiv.org/abs/2510.24280v2>.

*Commentary.*

The four distinct positive steps are 4, 22, 35 and 38. The list represents the set without repeated elements.

**Theorem 1.3 (The conjecture fails at heap 161).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/BhagatKulkarniLarssonMuraliConjectureFourRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bhagat-kulkarni-larsson-murali-conjecture-4-refutation` (refuted) by `D5/S0/Certificates/Games/BhagatKulkarniLarssonMuraliConjectureFourRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bhagat-kulkarni-larsson-murali-conjecture-4-refutation","declaration_gid":"D5/S0/Certificates/Games/BhagatKulkarniLarssonMuraliConjectureFourRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Anjali Bhagat; Tanmay Kulkarni; Urban Larsson; Divya Murali (2026). *Tie-breaking in self interest cumulative subtraction games*. URL: <https://arxiv.org/abs/2510.24280v2>.

*Commentary.*

At heap 161 the outcomes are FvF = (84,77), AvF = (84,77), FvA = (83,78) and AvA = (83,78). The two values used in the proof are checked by kernel reduction of the outcome function. Bob's AvA total 78 exceeds his FvF total 77, so the second coordinate of the conjecture fails. The same paper's Problem 6 is settled by SelfInterestConventionDeviationGain; this result settles only Conjecture 4. No global minimality or classification of counterexamples is asserted.

## References

- Truth anchor: `D5/S0/Certificates/Games/BhagatKulkarniLarssonMuraliConjectureFourRefutation.claim`
- Truth anchor: `D5/S0/Certificates/Games/BhagatKulkarniLarssonMuraliConjectureFourRefutation.result`
- Truth anchor: `D5/S0/Certificates/Games/BhagatKulkarniLarssonMuraliConjectureFourRefutation.witnessSubtractions`
- Dependency: [D5/S0/Certificates/SelfInterestConventionDeviationGain](../SelfInterestConventionDeviationGain.md)
