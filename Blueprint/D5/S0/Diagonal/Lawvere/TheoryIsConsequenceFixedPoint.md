# Theories as Consequence Fixed Points

## Abstract

Deductively closed sets are precisely the fixed points of consequence closure, whose fixed points form a complete lattice under intersections.

**Theorem 1.1 (Theories are exactly consequence fixed points).**

$$\begin{gathered}\forall Formula: \operatorname{Type},\\{}Cn: \operatorname{ConsequenceOperator}\left(Formula\right), S: \operatorname{Set}\left(Formula\right),\\{}\operatorname{IsTheory}\left(Cn, S\right) \iff S \in \operatorname{fixedPoints}\left(Cn\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Lawvere/TheoryIsConsequenceFixedPoint.theory_iff_consequence_fixedPoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A theory contains every consequence generated from itself. Since a closure operator is extensive, the reverse inclusion already holds, so deductive closure is equivalent to equality with the consequence closure.

Thus the theories of an arbitrary Tarskian consequence operator are exactly its fixed points. The statement uses only the closure laws and imposes no finiteness condition on formulas or theories.

**Lemma 1.2 (Consequence closure is a fixed point).**

$$\begin{gathered}\forall Formula: \operatorname{Type},\\{}Cn: \operatorname{ConsequenceOperator}\left(Formula\right), S: \operatorname{Set}\left(Formula\right),\\{}\operatorname{Cn}\left(S\right) \in \operatorname{fixedPoints}\left(Cn\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Lawvere/TheoryIsConsequenceFixedPoint.consequenceClosure_is_fixedPoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Closing any set of formulas produces a deductively closed set. Applying the same consequence operator again changes nothing, by the idempotence law for closure operators.

**Lemma 1.3 (Consequence closure is least above its generators).**

$$\begin{gathered}\forall Formula: \operatorname{Type},\\{}Cn: \operatorname{ConsequenceOperator}\left(Formula\right), S: \operatorname{Set}\left(Formula\right),\\{}\operatorname{IsLeast}\left(\{T: \operatorname{Set}\left(Formula\right) \mid S \subseteq T \land T \in \operatorname{fixedPoints}\left(Cn\right)\}, \operatorname{Cn}\left(S\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Lawvere/TheoryIsConsequenceFixedPoint.consequenceClosure_isLeast_fixedPoint_above` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closure of a generating set contains every generator and is itself a fixed point. If another fixed point contains the generators, closure minimality places the generated closure inside it.

Consequently the deductive closure is the least closed theory extending the chosen assumptions, not merely one closed extension among many.

**Lemma 1.4 (Fixed points are closed under arbitrary intersections).**

$$\begin{gathered}\forall Formula: \operatorname{Type},\\{}Cn: \operatorname{ConsequenceOperator}\left(Formula\right), families: \operatorname{Set}\left(\operatorname{Set}\left(Formula\right)\right),\\{}(\forall T, T \in families, T \in \operatorname{fixedPoints}\left(Cn\right)) \Rightarrow \\{}\operatorname{sInf}\left(families\right) \in \operatorname{fixedPoints}\left(Cn\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Lawvere/TheoryIsConsequenceFixedPoint.fixedPoints_closed_under_sInf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The intersection of any family of consequence fixed points is again a fixed point. No nonemptiness assumption is needed: closed sets of a closure operator are preserved by arbitrary infima.

Together with the inherited order, this intersection law supplies the meet structure behind the complete lattice of theories.

## References

- Truth anchor: `D5/S0/Diagonal/Lawvere/TheoryIsConsequenceFixedPoint.consequenceClosure_isLeast_fixedPoint_above`
- Truth anchor: `D5/S0/Diagonal/Lawvere/TheoryIsConsequenceFixedPoint.consequenceClosure_is_fixedPoint`
- Truth anchor: `D5/S0/Diagonal/Lawvere/TheoryIsConsequenceFixedPoint.fixedPoints_closed_under_sInf`
- Truth anchor: `D5/S0/Diagonal/Lawvere/TheoryIsConsequenceFixedPoint.theory_iff_consequence_fixedPoint`
