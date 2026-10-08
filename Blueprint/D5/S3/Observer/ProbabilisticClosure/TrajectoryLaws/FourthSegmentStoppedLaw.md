# First completion and the full stopped-word law

## Abstract

Complete stopped Read words from the fourth payload segment.

Letters 0 and 1 represent alpha and beta. The two active phases are p and beta. At p, alpha completes bit 0 and beta suspends the parser; at beta, alpha returns to p and beta completes bit 1. Completion reaches pending b. Its sole legal operation is Stop b, leading to delivered. Neither terminal phase permits Read. A state-preserving totalization is used only to evaluate mathematical traces beyond a terminal prefix.

The output is the entire prefix consumed through the least trace index reaching pending. It is some word for finite first completion and none for infinite noncompletion. The alphabet stream has a product measurable structure; the ambient output carrier Option (List (Fin 2)) has the discrete measurable structure. The output definition uses the execution trace, independently of the following word families.

Write L(j) for j repetitions of beta-alpha. At p, the complete words are L(j)-alpha for bit 0 and L(j)-beta-beta for bit 1, for every natural j. At beta, they are the one-letter beta for bit 1, or alpha prepended to a p word. The beta already acquired before the beta-phase cut is absent from the future word.

**Theorem 1.1 (The exact completion language).**

$$\forall s:ActivePhase, (\forall w:\operatorname{List}(Letter), (\forall b:Letter, (\operatorname{Parses}(\operatorname{active}(s),w,b)\Leftrightarrow\operatorname{WordFamily}(s,b,w))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw.parses_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the finite input word follows the actual Read table. A completing letter permits no additional word suffix. A beta-alpha return restores p without completing. These cases give both directions of the language characterization, including arbitrary return lengths.

**Theorem 1.2 (First completion and its full prefix).**

$$\forall s:ActivePhase, (\forall x:Stream, (\forall b:Letter, (\forall n:Nat, (\operatorname{FirstStop}(totalRead,pendingColor,\operatorname{active}(s),x,b,n)\Leftrightarrow\exists w:\operatorname{List}(Letter), \operatorname{length}(w)=n\land\operatorname{Prefix}(x,w)\land\operatorname{WordFamily}(s,b,w)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw.first_completion_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

FirstStop is the chronological trace condition: the terminal color is some b at length n and none at every smaller index. Finite parsing is equivalent to that condition on the length-n stream prefix. Thus every actual first completion is exactly a family word, and every matching family prefix is an actual first completion.

**Theorem 1.3 (Finite output fibers).**

$$\forall s:ActivePhase, (\forall x:Stream, (\forall w:\operatorname{List}(Letter), (\operatorname{stoppedReadWord}(s,x)=\operatorname{some}(w)\Leftrightarrow\operatorname{Prefix}(x,w)\land(\exists b:Letter, \operatorname{WordFamily}(s,b,w)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw.stopped_word_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite output fiber is its entire chronological prefix cylinder when the word belongs to the completion language, and is empty otherwise. Letters after first completion are not consumed and add no likelihood factors.

**Theorem 1.4 (Measurability of first-completion output).**

$$\forall s:ActivePhase, (\operatorname{Measurable}(\operatorname{stoppedReadWord}(s)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw.measurable_stopped_read_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each finite fiber is a measurable prefix cylinder or the empty set. The noncompletion fiber is the complement of the countable union of finite fibers. Countability of the output carrier therefore establishes measurability without requiring a countable stream domain.

For an arbitrary closed-unit-interval parameter r, rawReadLaw is the homogeneous trajectory law with initial Bernoulli alpha probability r and the same constant Bernoulli transition kernel at every coordinate. Set R=r, S=1-r and A=RS, interpreted as nonnegative extended-real weights. The explicit p law is the sum over all natural j of R A^j times the Dirac measure at some pWord(j,0), plus S^2 A^j times the Dirac measure at some pWord(j,1). The explicit beta law has an S Dirac atom at some [1], followed by atoms of weights R^2 A^j and R S^2 A^j at alpha prepended to the respective p words. There is no Dirac term at none or any invalid finite word.

**Theorem 1.5 (The unique infinite continuation).**

$$\forall s:ActivePhase, (\forall x:Stream, (\operatorname{stoppedReadWord}(s,x)=none\Leftrightarrow x=\operatorname{infiniteTail}(s)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw.noncompletion_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

None occurs precisely on beta-alpha repeated forever from p, or alpha followed by that sequence from beta. The alternating stream remains active at every finite trace index and never delivers Stop. All other streams complete at a finite first index.

**Theorem 1.6 (Zero actual mass of infinite noncompletion).**

$$\forall r:unitInterval, (\forall s:ActivePhase, (\operatorname{mass}(\operatorname{rawReadLaw}(r),\{x:Stream\Vert \operatorname{stoppedReadWord}(s,x)=none\})=0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw.actual_noncompletion_mass_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A surviving p execution must repeatedly read beta-alpha. A surviving beta execution must first read alpha, then follow the same returns. Their noncompletion events lie in every such finite prefix cylinder, whose masses are A^j and R A^j. Since A is at most one quarter, these upper bounds tend to zero. This proof includes r=0 and r=1; it retains none in the carrier and does not condition on completion.

**Theorem 1.7 (The actual full stopped-word law).**

$$\forall r:unitInterval, (\forall s:ActivePhase, (\operatorname{Measurable}(\operatorname{stoppedReadWord}(s))\land\operatorname{map}(\operatorname{rawReadLaw}(r),\operatorname{stoppedReadWord}(s))=\operatorname{explicitStoppedWordLaw}(s,r)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw.actual_fourth_segment_stopped_word_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prefix-product formula for the constant Bernoulli kernel gives the advertised finite atom masses on the actual first-completion fibers. Infinite noncompletion has mass zero. Equality on all singletons in the countable discrete output carrier proves equality of the two measures. Normalization of the explicit law follows from this equality with the measurable image of a probability law, rather than being an assumption.

This is the fixed-parameter raw fourth-segment projection. For a fixed source depth k, substitute its parameter r_k separately. Conditional freshness after random actual histories, the shared-depth posterior mixture, and the measurable correspondence with the full original record and event transcript are separate mathematical bridges. The current phase theorem adds no runtime history, posterior service or future conditioning. Held records B, Qplus and Z must be retained in a full transcript construction. The coherence-price and common-attainment conclusions require further estimates beyond this law.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw.actual_fourth_segment_stopped_word_law`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw.actual_noncompletion_mass_zero`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw.first_completion_normal_form`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw.measurable_stopped_read_word`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw.noncompletion_fiber`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw.parses_normal_form`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw.stopped_word_fiber`
- Dependency: [D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation](../../../Arith/FibonacciAtomic/TriangularSharedImplementation.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkovPrefixMass](MarkovPrefixMass.md)
