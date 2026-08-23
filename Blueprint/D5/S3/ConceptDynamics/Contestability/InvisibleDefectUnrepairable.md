# Invisible Defects Are Unrepairable by Blind Review

## Abstract

Challenge-indistinguishable states with different required outcomes defeat every challenge-blind reviewer.

**Theorem 1.1 (Blind review cannot separate an invisible defect).**

$$\begin{gathered}\forall State, Challenge, Response, Outcome: \operatorname{Type},\\{}ask: Challenge \to \left(State \to Response\right), required: State \to Outcome,\\{}x: State, y: State,\\{}(\forall c: Challenge, ask\left(c, x\right) = ask\left(c, y\right) \land required\left(x\right) \neq required\left(y\right)) \Rightarrow\\{}\neg (\exists review: State \to Outcome,\\{}\operatorname{ChallengeBlind}\left(ask, review\right) \land {\forall s: State, review\left(s\right) = required\left(s\right)}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Contestability/InvisibleDefectUnrepairable.challenge_blind_review_cannot_separate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Challenge blindness makes a reviewer constant on every class of states that gives identical answers to all available challenges.

If two such states require different outcomes, universal correctness would identify both required outcomes through the common reviewed outcome. Their required difference therefore rules out every challenge-blind reviewer that is correct on all states.

The obstruction is independent of finiteness, decidability, or any additional structure on states, challenges, responses, and outcomes.

**Proposition 1.2 (Coverage exactly characterizes correct blind review).**

$$\begin{gathered}\forall State, Challenge, Response, Outcome: \operatorname{Type},\\{}ask: Challenge \to \left(State \to Response\right), required: State \to Outcome,\\{}(\exists review: State \to Outcome,\\{}\operatorname{ChallengeBlind}\left(ask, review\right) \land {\forall u: State, review\left(u\right) = required\left(u\right)}) \iff\\{}\forall s, t: State,\\{}{\forall c: Challenge, ask\left(c, s\right) = ask\left(c, t\right)} \Rightarrow required\left(s\right) = required\left(t\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Contestability/InvisibleDefectUnrepairable.correct_challenge_blind_review_exists_iff_coverage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A fully correct challenge-blind reviewer exists exactly when the required outcome is constant on each fiber determined by all challenge answers.

Necessity follows because blindness equates the reviewed outcomes of any answer-indistinguishable pair, while correctness transfers that equality to their requirements. For sufficiency, the required-outcome map itself is a reviewer, and the coverage condition makes it blind.

**Lemma 1.3 (A constant challenge misses a Boolean defect).**

$$(\forall c: Unit, \operatorname{constantUnit}\left(c, false\right) = \operatorname{constantUnit}\left(c, true\right)) \land\\{}id\left(false\right) \neq id\left(true\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Contestability/InvisibleDefectUnrepairable.constant_unit_challenge_is_blind_to_bool_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sole Unit-valued challenge returns the same Unit response for the Boolean states false and true, so those states are indistinguishable to any reviewer constrained by its answers.

The identity target nevertheless assigns different required outcomes to the two states. This gives a concrete mixed fiber witnessing the general obstruction.

**Lemma 1.4 (Constant challenges cannot implement the Boolean identity target).**

$$\neg (\exists review: Bool \to Bool,\\{}\operatorname{ChallengeBlind}\left(constantUnit, review\right) \land {\forall state: Bool, review\left(state\right) = id\left(state\right)}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Contestability/InvisibleDefectUnrepairable.constant_unit_challenge_cannot_review_bool` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every reviewer blind to the constant Unit challenge must return one outcome for both Boolean states, whereas the identity target requires false and true respectively.

Applying the general separation obstruction to this explicit pair proves that no such reviewer can be correct on every Boolean state.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Contestability/InvisibleDefectUnrepairable.challenge_blind_review_cannot_separate`
- Truth anchor: `D5/S3/ConceptDynamics/Contestability/InvisibleDefectUnrepairable.constant_unit_challenge_cannot_review_bool`
- Truth anchor: `D5/S3/ConceptDynamics/Contestability/InvisibleDefectUnrepairable.constant_unit_challenge_is_blind_to_bool_defect`
- Truth anchor: `D5/S3/ConceptDynamics/Contestability/InvisibleDefectUnrepairable.correct_challenge_blind_review_exists_iff_coverage`
