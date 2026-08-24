# Single-Sample Law Nonimplication

## Abstract

One supported coupled equality need not identify either laws or states.

**Theorem 1.1 (One coupled sample identifies neither law nor state).**

$$\begin{gathered}\exists K: Bool \to \operatorname{PMF}\left(Bool\right),\\{}\exists gamma: \operatorname{PMF}\left(\operatorname{Prod}\left(Bool, Bool\right)\right), omega: \operatorname{Prod}\left(Bool, Bool\right),\\{}\operatorname{map}\left(fst, gamma\right) = K(false) \land\\{}\operatorname{map}\left(snd, gamma\right) = K(true) \land\\{}gamma(omega) \neq 0 \land fst(omega) = snd(omega) \land\\{}K(false) \neq K(true) \land false \neq true.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/SingleSampleLawNonimplication.single_coupled_sample_does_not_determine_law_or_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public witnesses form a discrete stochastic channel K on Bool, a joint probability mass gamma, and one sampled pair omega. The first two equations certify that gamma has the channel laws at false and true as its two marginals.

The explicit pair omega has nonzero gamma mass and equal coordinates, so it is a genuinely possible equal-output observation rather than a zero-mass point.

Nevertheless, the two marginal laws are publicly unequal and the two source states are publicly distinct. Both nonimplication clauses therefore hold in the same coupled countermodel.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/SingleSampleLawNonimplication.single_coupled_sample_does_not_determine_law_or_state`
