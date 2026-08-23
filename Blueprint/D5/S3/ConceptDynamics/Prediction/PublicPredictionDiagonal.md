# Public Prediction Diagonal

## Abstract

Fixed-point-free public reactions defeat universal prediction, while a fixed point supports a correct constant predictor.

**Theorem 1.1 (Fixed-point-free public reactions defeat universal prediction).**

$$\begin{gathered}\forall State, Action: \operatorname{Type},\\{}predict: State \to Action, react: Action \to Action,\\{}(\forall action: Action, react\left(action\right) \neq action) \land \operatorname{Nonempty}\left(State\right) \Rightarrow \\{}\neg \forall state: State, predict\left(state\right) = \operatorname{actual}\left(predict, react, state\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Prediction/PublicPredictionDiagonal.no_correct_public_predictor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual action is obtained by feeding the public prediction into the subject's response. If a predictor were correct at every state, then at any state its predicted action would equal the response to that same action.

A nonempty state space supplies such a state. The resulting action is a fixed point of the response, contradicting the assumption that the response has no fixed points. Hence no public predictor is universally correct.

**Lemma 1.2 (Boolean negation defeats every public predictor).**

$$\begin{gathered}\forall predict: Unit \to Bool,\\{}\neg \forall state: Unit, predict\left(state\right) = \operatorname{actual}\left(predict, Bool.not, state\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Prediction/PublicPredictionDiagonal.bool_not_no_correct_public_predictor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the one-state space, every public predictor announces one Boolean value. The response is its negation, which is always the opposite value and has no fixed point. Thus every predictor is wrong about the action produced after its announcement is read.

**Lemma 1.3 (A fixed point yields a correct constant public predictor).**

$$\begin{gathered}\forall State, Action: \operatorname{Type},\\{}react: Action \to Action, action: Action,\\{}react\left(action\right) = action \Rightarrow \\{}\exists predict: State \to Action,\\{}\forall state: State, predict\left(state\right) = \operatorname{actual}\left(predict, react, state\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Prediction/PublicPredictionDiagonal.exists_correct_public_predictor_of_fixed_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the response fixes an action, the predictor that announces that action at every state is universally correct. Reading the announcement and responding leaves the fixed action unchanged, showing that the fixed-point-free hypothesis in the obstruction is essential.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Prediction/PublicPredictionDiagonal.bool_not_no_correct_public_predictor`
- Truth anchor: `D5/S3/ConceptDynamics/Prediction/PublicPredictionDiagonal.exists_correct_public_predictor_of_fixed_point`
- Truth anchor: `D5/S3/ConceptDynamics/Prediction/PublicPredictionDiagonal.no_correct_public_predictor`
- Dependency: [D5/S0/Diagonal/Feedback/StrategicResponseObstruction](../../../S0/Diagonal/Feedback/StrategicResponseObstruction.md)
