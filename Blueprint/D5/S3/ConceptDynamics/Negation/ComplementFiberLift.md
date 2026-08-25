# Complement Fiber Lift

## Abstract

A section lifts base complement, and the lift square is its fiber retraction.

**Theorem 1.1 (A right-inverse section lifts base complement).**

$$\begin{gathered}\forall q: X \to Q, baseNegation: Q \to Q,\\{}sect: Q \to X, \operatorname{RightInverse}\left(sect, q\right) \Rightarrow\\{}\operatorname{IsComplementLift}\left(q, baseNegation, \operatorname{sectionLift}\left(q, baseNegation, sect\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Negation/ComplementFiberLift.sectionLift_isComplementLift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The section lift first reads the base value, applies the supplied base negation, and then chooses the section representative over that negated value.

The right-inverse hypothesis projects this representative back to the negated base value. This is exactly the pointwise complement-lift condition, with no injectivity requirement on the section.

**Theorem 1.2 (The lift square is the section retraction).**

$$\begin{gathered}\forall q: X \to Q, baseNegation: Q \to Q,\\{}sect: Q \to X, (\operatorname{RightInverse}\left(sect, q\right) \land \operatorname{Involutive}\left(baseNegation\right)) \Rightarrow\\{}\operatorname{sectionLift}\left(q, baseNegation, sect\right) \circ \operatorname{sectionLift}\left(q, baseNegation, sect\right) = sect \circ q.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Negation/ComplementFiberLift.sectionLift_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After the first lift, the right-inverse section exposes the complemented base value. Applying the lift again invokes base negation a second time.

Base involutivity cancels those two negations. The square of the lift is therefore not asserted to be the identity on all of the total space; it is exactly the retraction that sends each point to its chosen section representative.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Negation/ComplementFiberLift.sectionLift_isComplementLift`
- Truth anchor: `D5/S3/ConceptDynamics/Negation/ComplementFiberLift.sectionLift_square`
- Dependency: [D5/S3/ConceptDynamics/Negation/InvolutiveNegation](InvolutiveNegation.md)
