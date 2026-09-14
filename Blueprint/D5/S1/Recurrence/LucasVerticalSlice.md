# Lucas Vertical Slices

## Abstract

Vertical slices admit criteria in terms of two consecutive traces, integer companion powers under a unit discriminant, and half the companion period when four is nonzero. The unit-discriminant hypothesis is not removable.

Let R be any commutative ring, p an element of R, and q a unit of R. A vertical slice is an integer shift s for which lucasV(p, q, n) + lucasV(p, q, n + s) = 0 for every integer n. The first criterion characterizes its existence by two consecutive companion traces: lucasV(p, q, s) = -2 and lucasV(p, q, s + 1) = -p. The second criterion, under the hypothesis that p squared minus 4q is a unit, characterizes its existence by an integer power of the companion matrix equal to minus one. The first criterion carries no hypothesis and is the one that answers a question Fiebig, Mbirika and Spilker leave open, for every unit q and with no restriction on the order statistic or the discriminant; the second refines it under a hypothesis that result proves is not removable. The proofs are repository work, with the source paper acknowledged.

The third criterion, verticalSlice_iff_half_companionPeriod, assumes that four is nonzero in R. It states that a vertical slice exists exactly when there is a natural number T such that the companion period equals 2T and the traces at T and T + 1 are -2 and -p. The non-removability of the nonzero-four hypothesis in the half-period criterion is measured but not proved.

**Theorem 1.1 (Two consecutive traces characterize a slice).**

$$\forall p: R, \forall q: \operatorname{Units}\left(R\right), \left(\exists s: \mathbb{Z}, \forall n: \mathbb{Z}, \operatorname{lucasV}\left(p, q, n\right) + \operatorname{lucasV}\left(p, q, n + s\right) = 0\right) \iff \left(\exists s: \mathbb{Z}, \left(\operatorname{lucasV}\left(p, q, s\right) = -2 \land \operatorname{lucasV}\left(p, q, s + 1\right) = -p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasVerticalSlice.verticalSlice_iff_two_traces` (`✓ std3`). ∎

*Resolves.* `Problems/fiebig-mbirika-spilker-vertical-slice` (proved) by `D5/S1/Recurrence/LucasVerticalSlice.verticalSlice_iff_two_traces`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fiebig-mbirika-spilker-vertical-slice","declaration_gid":"D5/S1/Recurrence/LucasVerticalSlice.verticalSlice_iff_two_traces","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Morgan Fiebig, aBa Mbirika, Jürgen Spilker (2025). *Period patterns, entry points, and orders in the Lucas sequences: theory and applications*. URL: <https://arxiv.org/abs/2408.14632v2>.

*Commentary.*

Over every commutative ring R, the existence of a shift cancelling every companion trace is equivalent to the existence of a shift with the two stated trace values. Both shifts range over all integers, and q ranges over all units of R. This criterion carries no hypothesis, so it answers the question Fiebig, Mbirika and Spilker leave open without restricting q, the order statistic, or the discriminant.

**Theorem 1.2 (A unit discriminant detects minus one).**

$$\forall p: R, \forall q: \operatorname{Units}\left(R\right), \operatorname{IsUnit}\left(p^{2} - 4 \cdot \operatorname{Cast}\left(q, R\right)\right) \Rightarrow \left(\left(\exists s: \mathbb{Z}, \forall n: \mathbb{Z}, \operatorname{lucasV}\left(p, q, n\right) + \operatorname{lucasV}\left(p, q, n + s\right) = 0\right) \iff \left(\exists s: \mathbb{Z}, \operatorname{companion}\left(p, q\right)^{s} = -1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasVerticalSlice.verticalSlice_iff_neg_one_mem_zpowers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Morgan Fiebig, aBa Mbirika, Jürgen Spilker (2025). *Period patterns, entry points, and orders in the Lucas sequences: theory and applications*. URL: <https://arxiv.org/abs/2408.14632v2>.

*Commentary.*

If p squared minus 4q is a unit, a vertical slice exists exactly when an integer power of companion(p, q) is minus the identity. The scalar q in the discriminant is the underlying element of R of the unit q. No hypothesis restricts the order statistic.

**Theorem 1.3 (The unit-discriminant hypothesis is not removable).**

$$\neg \left(\forall m: \mathbb{N}, \forall p: \operatorname{ZMod}\left(m\right), \forall q: \operatorname{Units}\left(\operatorname{ZMod}\left(m\right)\right), \left(\left(\exists s: \mathbb{Z}, \forall n: \mathbb{Z}, \operatorname{lucasV}\left(p, q, n\right) + \operatorname{lucasV}\left(p, q, n + s\right) = 0\right) \iff \left(\exists s: \mathbb{Z}, \operatorname{companion}\left(p, q\right)^{s} = -1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasVerticalSlice.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Morgan Fiebig, aBa Mbirika, Jürgen Spilker (2025). *Period patterns, entry points, and orders in the Lucas sequences: theory and applications*. URL: <https://arxiv.org/abs/2408.14632v2>.

*Commentary.*

The definition claim asserts the companion-power equivalence over every ZMod(m) without a discriminant hypothesis. The theorem result proves that the unit-discriminant hypothesis is not removable by refuting claim, with the witness p = 4, q = 1, modulus 6. The shift s = 1 gives a vertical slice, but no integer companion power equals minus one. The displayed negation scopes over the entire universal claim.

## References

- Truth anchor: `D5/S1/Recurrence/LucasVerticalSlice.result`
- Truth anchor: `D5/S1/Recurrence/LucasVerticalSlice.verticalSlice_iff_neg_one_mem_zpowers`
- Truth anchor: `D5/S1/Recurrence/LucasVerticalSlice.verticalSlice_iff_two_traces`
- Dependency: [D5/S1/Recurrence/LucasCompanion](LucasCompanion.md)
