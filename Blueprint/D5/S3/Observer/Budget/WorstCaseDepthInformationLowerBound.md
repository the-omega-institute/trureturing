# Worst-Case Depth Information Lower Bound

## Abstract

Fixed-branch adaptive protocols have at most exponentially many leaves, forcing the ceiling-logarithmic worst-case identification depth.

**Theorem 1.1 (A bounded-depth tree has at most exponentially many leaves).**

$$1 \leq B \implies \operatorname{card}\left(\operatorname{adaptiveLeaves}\left(pi\right)\right) \leq B^{h}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.adaptive_leaf_count_le_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction bounds each child subtree by B^d. Prefixing by one of the B answers and taking their union gives at most B^(d+1) leaves; a root leaf under unused budget uses the explicit premise 1 <= B.

**Theorem 1.2 (Exact identification injects states into budgeted leaves).**

$$1 \leq B \land \operatorname{ExactAtDepth}\left(q, h\right) \implies \operatorname{card}\left(X\right) \leq B^{h}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.exact_identification_card_le_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exactness makes the transcript map injective. Finite-cardinality monotonicity and the leaf count yield the state bound B^h.

**Theorem 1.3 (Worst-case exact depth is at least the upper logarithm).**

$$1 \leq B \land \operatorname{Identifiable}\left(q\right) \implies \operatorname{clog}\left(B, \operatorname{card}\left(X\right)\right) \leq \operatorname{adaptiveIdentificationDepth}\left(q\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.worst_case_depth_information_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The named adaptive depth is the least depth at which exact recognition exists. Its exact protocol gives |X| <= B^D, and mathlib's upper-log adjunction yields clog B |X| <= D.

**Lemma 1.4 (Positive branching is necessary for the budget-depth count).**

$$\operatorname{ExactAtDepth}\left(q, 1\right) \land \neg(1 \leq 0^{1}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.positive_branching_factor_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At B=0, a zero-round protocol exactly identifies Unit and has depth at most one. Its single root leaf cannot satisfy 1 <= 0^1, giving the required concrete counterexample.

**Lemma 1.5 (Empty and singleton carriers need no questions).**

$$\operatorname{ExactAtDepth}\left(qEmpty, 0\right) \land \operatorname{ExactAtDepth}\left(qUnit, 0\right) \land \operatorname{clog}\left(B, 0\right) = 0 \land \operatorname{clog}\left(B, 1\right) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.empty_and_singleton_depth_zero_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty transcript is injective on Empty and Unit. Their cardinalities are zero and one, and mathlib assigns upper logarithm zero to both.

**Lemma 1.6 (Unary branching identifies at most one state).**

$$\operatorname{ExactAtDepth}\left(q, d\right) \implies \operatorname{card}\left(X\right) \leq 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.unary_exact_identification_card_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For B=1 every transcript type has cardinality one, independently of depth. An injective transcript therefore permits at most one state.

**Lemma 1.7 (Binary branching gives the standard base-two lower bound).**

$$\operatorname{ExactAtDepth}\left(q, d\right) \implies \operatorname{clog}\left(2, \operatorname{card}\left(X\right)\right) \leq d.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.binary_exact_identification_depth_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Specializing the fixed branching factor to two gives the usual ceiling binary logarithm lower bound for every exact protocol.

**Lemma 1.8 (Depth zero identifies at most one state).**

$$\operatorname{ExactAtDepth}\left(q, 0\right) \implies \operatorname{card}\left(X\right) \leq 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.zero_depth_exact_identification_card_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Without asking a question there is only the empty transcript. Exact recognition therefore forces the state carrier to be a subsingleton.

**Lemma 1.9 (A constant readout cannot distinguish Boolean states).**

$$\neg\operatorname{ExactAtDepth}\left(\operatorname{constantZero}\left(2\right), h\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.constant_zero_readout_not_exact_on_bool` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every reachable question returns zero on both Boolean states, so their transcripts agree at every depth and exactness is impossible.

**Lemma 1.10 (The exponential leaf bound is attained).**

$$\operatorname{card}\left(\operatorname{TranscriptSpace}\left(B, h\right)\right) = B^{h} \land \operatorname{ExactAtDepth}\left(\operatorname{coordinateReadout}\left(\operatorname{TranscriptSpace}\left(B, h\right)\right), h\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.full_transcript_space_attains_leaf_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take states to be all B-valued transcripts of length h and ask for one coordinate each round. The identity transcript is injective and the state cardinality is exactly B^h.

## References

- Truth anchor: `D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.adaptive_leaf_count_le_pow`
- Truth anchor: `D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.binary_exact_identification_depth_lower_bound`
- Truth anchor: `D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.constant_zero_readout_not_exact_on_bool`
- Truth anchor: `D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.empty_and_singleton_depth_zero_audit`
- Truth anchor: `D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.exact_identification_card_le_pow`
- Truth anchor: `D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.full_transcript_space_attains_leaf_bound`
- Truth anchor: `D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.positive_branching_factor_is_necessary`
- Truth anchor: `D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.unary_exact_identification_card_le_one`
- Truth anchor: `D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.worst_case_depth_information_lower_bound`
- Truth anchor: `D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.zero_depth_exact_identification_card_le_one`
