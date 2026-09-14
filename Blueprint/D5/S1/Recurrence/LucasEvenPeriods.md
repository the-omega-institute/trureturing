# Even Lucas Periods

## Abstract

The two even-parameter open period questions are settled: the matrix and companion periods agree exactly outside q = 1, modulus 4, and 4 dividing p.

Fiebig, Mbirika and Spilker's Questions 5.3 and 5.4 ask whether the matrix and companion periods agree when p and the modulus are both even. This theorem settles both questions as an iff: the periods agree exactly outside the single case q = 1, m = 4, and 4 divides p. The proof here is repository work and uses neither Ballot's equality theorem nor McDaniel's 1991 gcd theorem; the paper's Corollary 3.13 does not reach the case where p and m are both even.

The exception is sharp. Over ZMod(2^v) with v at least 2, a zero of the companion sequence and Cayley--Hamilton give M^2 = -q. For q = 1 the trace sequence is 2, 0, -2, 0, ...; it drops to period 2 exactly when 2 = -2, namely v = 2. The remaining dyadic case v = 1 is computed on its own: the matrix period is 2 and the companion period is 1. For p congruent to 2 modulo 4 and modulus 4, the companion sequence is constantly 2 modulo 4, so no zero exists and the hypothesis is vacuous; this confines the exception to 4 dividing p rather than all even p.

**Theorem 1.1 (Exact equality criterion for even Lucas periods).**

$$\begin{aligned}\forall p: \mathbb{Z},\\\forall q: \operatorname{Units}\left(\mathbb{Z}\right),\\\forall m: \mathbb{N},\\\operatorname{Even}\left(p\right) \Rightarrow \operatorname{Even}\left(m\right) \Rightarrow 2 < m \Rightarrow \\\left(\exists r: \mathbb{N}, 0 < r \land \operatorname{lucasV}\left(\operatorname{Cast}\left(p, \operatorname{ZMod}\left(m\right)\right), \operatorname{reducedUnit}\left(m, q\right), r\right) = 0\right)\\ \\\Rightarrow\\ \\\left(\operatorname{matrixPeriod}\left(\operatorname{Cast}\left(p, \operatorname{ZMod}\left(m\right)\right), \operatorname{reducedUnit}\left(m, q\right)\right) = \operatorname{companionPeriod}\left(\operatorname{Cast}\left(p, \operatorname{ZMod}\left(m\right)\right), \operatorname{reducedUnit}\left(m, q\right)\right) \iff \neg \left(q = 1 \land m = 4 \land 4 \mid \operatorname{Cast}\left(p, \mathbb{Z}\right)\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasEvenPeriods.even_lucas_periods` (`✓ std3`). ∎

*Resolves.* `Problems/fiebig-mbirika-spilker-even-period-exception` (proved) by `D5/S1/Recurrence/LucasEvenPeriods.even_lucas_periods`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fiebig-mbirika-spilker-even-period-exception","declaration_gid":"D5/S1/Recurrence/LucasEvenPeriods.even_lucas_periods","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Morgan Fiebig, aBa Mbirika, Jürgen Spilker (2025). *Period patterns, entry points, and orders in the Lucas sequences: theory and applications*. URL: <https://arxiv.org/abs/2408.14632v2>.

*Commentary.*

This is the settled result corresponding to the paper's Questions 5.3 and 5.4. Its hypotheses include even p, even m with 2 < m, and a positive companion zero modulo m. Integer units encode q = plus or minus 1. All definitions and the proof route are from this repository.

## References

- Truth anchor: `D5/S1/Recurrence/LucasEvenPeriods.even_lucas_periods`
- Dependency: [D5/S1/Recurrence/LucasCompanion](LucasCompanion.md)
