# Full Contestability and Correct Review

## Abstract

Complete contestability turns accepted statewise challenges into correct review, while missing or observationally blind challenges expose precise obstructions.

**Theorem 1.1 (Full contestability yields correct challenge-blind review).**

$$\begin{gathered}\forall State, Challenge, Outcome: \operatorname{Type},\\{}Erroneous: State \to Prop,\\{}Applicable: State \to \left(Challenge \to Prop\right), Valid: State \to \left(Challenge \to Prop\right),\\{}judgment: Challenge \to \left(State \to Outcome\right), target: State \to Outcome,\\{}\operatorname{FullyContestable}\left(Erroneous, Applicable, Valid, judgment, target\right) \Rightarrow\\{}\exists selected: \operatorname{ErrorState}\left(State, Erroneous\right) \to Challenge,\\{}{\forall x: \operatorname{ErrorState}\left(State, Erroneous\right), Applicable\left(x, selected\left(x\right)\right) \land Valid\left(x, selected\left(x\right)\right) \land judgment\left(selected\left(x\right), x\right) = target\left(x\right)} \land\\{}\exists review: \operatorname{ErrorState}\left(State, Erroneous\right) \to Outcome,\\{}\operatorname{ChallengeBlind}\left(\operatorname{selectedChallengeAnswer}\left(judgment, selected\right), review\right) \land {\forall x: \operatorname{ErrorState}\left(State, Erroneous\right), review\left(x\right) = target\left(x\right)}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Contestability/FullContestability.full_contestability_yields_correct_review` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete contestability supplies an applicable and institutionally valid challenge at every erroneous state, with judgment equal to the state's target outcome. Choosing one such challenge at each error state produces a selector with all three guarantees.

The selected challenge answers determine a challenge-blind reviewer on the error-state subtype. Whenever two error states have the same selected answer, the correctness of their selected challenges forces their target outcomes to agree, so the reviewer returns the target throughout that subtype.

**Proposition 1.2 (Absent challenges and blindness prevent correct review).**

$$\begin{gathered}\forall State, Challenge, Outcome: \operatorname{Type},\\{}Erroneous: State \to Prop,\\{}Applicable: State \to \left(Challenge \to Prop\right), Valid: State \to \left(Challenge \to Prop\right),\\{}judgment: Challenge \to \left(State \to Outcome\right), target: State \to Outcome,\\{}x: State, y: State,\\{}{Erroneous\left(x\right) \land\\{}{\forall w: Challenge, \neg {Applicable\left(x, w\right) \land Valid\left(x, w\right) \land judgment\left(w, x\right) = target\left(x\right)}} \land\\{}{\forall w: Challenge, judgment\left(w, x\right) = judgment\left(w, y\right)} \land\\{}target\left(x\right) \neq target\left(y\right)} \Rightarrow\\{}\neg \operatorname{FullyContestable}\left(Erroneous, Applicable, Valid, judgment, target\right) \land\\{}{\forall review: State \to Outcome, \operatorname{UsesAcceptedChallengeAt}\left(Applicable, Valid, judgment, review, x\right) \Rightarrow review\left(x\right) \neq target\left(x\right)} \land\\{}\neg {\exists review: State \to Outcome,\\{}\operatorname{ChallengeBlind}\left(judgment, review\right) \land {\forall s: State, review\left(s\right) = target\left(s\right)}}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Contestability/FullContestability.absent_challenge_and_blindness_prevent_review` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose an erroneous state has no challenge that is simultaneously applicable, valid, and correct there. Then complete contestability fails, and any review output supported by an accepted challenge at that state must differ from its target.

If every challenge also gives the same judgment at that state and at a second state with a different target, challenge blindness creates a global obstruction: no challenge-blind reviewer can equal the target on every state.

**Lemma 1.3 (The Boolean identity is nontrivially fully contestable).**

$${\exists b: Bool, True} \land\\{}\operatorname{FullyContestable}\left({x \mapsto True}, {(x, w) \mapsto w = x}, {(x, w) \mapsto True}, {(w, x) \mapsto w}, {x \mapsto x}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Contestability/FullContestability.bool_identity_is_nontrivially_fully_contestable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both Boolean states are declared erroneous, so the instance has a nonempty error population. At each state, choosing that state itself as the challenge satisfies the applicability equality, while validity holds automatically.

The challenge judgment returns the chosen Boolean value and the target is the identity. The state-selected challenge therefore returns exactly the required outcome, giving a concrete nonvacuous instance of full contestability.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Contestability/FullContestability.absent_challenge_and_blindness_prevent_review`
- Truth anchor: `D5/S3/ConceptDynamics/Contestability/FullContestability.bool_identity_is_nontrivially_fully_contestable`
- Truth anchor: `D5/S3/ConceptDynamics/Contestability/FullContestability.full_contestability_yields_correct_review`
- Dependency: [D5/S3/ConceptDynamics/Contestability/InvisibleDefectUnrepairable](InvisibleDefectUnrepairable.md)
