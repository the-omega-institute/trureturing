# Acquiring the original on the same source

## Abstract

Finite dyadic acquisition recovers every original rational with acquired cap two or preset cap four.

**Lemma 1.1 (Deterministic terminal runs agree).**

$$\operatorname{Run}\left(C, x, s, w, o, v, A\right)\land \operatorname{Run}\left(C, x, s, w, o1, v1, A1\right)\longrightarrow o=o1\land v=v1\land A=A1$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/RationalRouting/Acquisition.run_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two finite runs of the same deterministic code, original source, initial state and starting chronological prefix have identical whole outputs, final words and read histories. Induction through each actual instruction compares the unique report continuation. The output type is arbitrary. This also applies when the final local calculation constructs a different exact original view.

**Theorem 1.2 (Pointwise finite full-rational acquisition).**

$$\operatorname{Correct}\left(Crec, id\right)\land\operatorname{Cap}\left(Crec, 2\right)\land \operatorname{Correct}\left(Cpre, id\right)\land\operatorname{Cap}\left(Cpre, 4\right)\land \operatorname{Preset}\left(Cpre, LLRL\right)\land \forall x\in P, 0<x$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/RationalRouting/Acquisition.actual_rational_acquisition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit source-independent instruction function has two modes. Both actually read q_2 at the original cut. In acquired mode this report selects LL on the first band and RL on the second. Preset mode follows LLRL throughout, stopping motion after LL on the first band and after its fourth letter on the second. No letters are skipped or restarted. The state contains only a phase, acquired band and public remaining word, or candidate and scale counters, or a recovered rational ready for output.

At the attained cut the endpoint reports are respectively floor(8z)=1, floor(8z)=5 and floor(16z)=9. Strict increase makes equality with that integer equivalent to the original being its band's included endpoint. This finite read resolves each accumulation endpoint without waiting for a nondyadic equality.

Otherwise, for each candidate j starting at 12, form the public midpoint between f_u(c_i-1/j) and f_u(c_i-1/(j+1)). Repeated actual reads at the same attained cut refine a dyadic cell. Stop the comparison when its upper endpoint is at most the midpoint or its lower endpoint is strictly larger. Every promised transformed tail point differs from this midpoint; a sufficiently small cell therefore stops. For actual index n, comparisons are above until j=n and below at n. The nested loops are finite on each member, with no uniform bound on n, scales, read count, arithmetic or output length.

The conjunction asserts finite correct whole-rational output for both modes, acquired cap 2, preset cap 4, compliance with the one LLRL schedule, and positivity of every prior member. Run uniqueness supplies correctness and action counts for every completed run. The source is never reset, copied, inverted or queried through an exact unknown rational argument.

## References

- Truth anchor: `D5/S3/Observer/RationalRouting/Acquisition.actual_rational_acquisition`
- Truth anchor: `D5/S3/Observer/RationalRouting/Acquisition.run_unique`
- Dependency: [D5/S3/Observer/RationalRouting/LowerBounds](LowerBounds.md)
