# Target-Relative Commitment Protection

## Abstract

One commitment can protect balance while exposing three other history targets.

**Theorem 1.1 (Commitment protection must name its history target).**

$$\begin{gathered}History := Bool \times Bool \times Bool \times Bool \times Bool,\\{}edit((m, b, o, i, a)) := \operatorname{if}\left(m, (m, \operatorname{not}\left(b\right), o, i, a), (m, b, \operatorname{not}\left(o\right), \operatorname{not}\left(i\right), \operatorname{not}\left(a\right))\right),\\{}commitment((m, b, o, i, a)) := \operatorname{not}\left(b\right), balance((m, b, o, i, a)) := b,\\{}eventOrder((m, b, o, i, a)) := o, identitySource((m, b, o, i, a)) := i, contractAuthorization((m, b, o, i, a)) := a,\\{}otherEdit := (false, false, false, false, false),\\{}(\forall gamma\in History, commitment(gamma) = commitment(edit(gamma)) \Rightarrow balance(gamma) = balance(edit(gamma))) \land\\{}commitment(otherEdit) = commitment(edit(otherEdit)) \land\\{}eventOrder(otherEdit) \neq eventOrder(edit(otherEdit)) \land\\{}identitySource(otherEdit) \neq identitySource(edit(otherEdit)) \land\\{}contractAuthorization(otherEdit) \neq contractAuthorization(edit(otherEdit)) \land\\{}\neg (\forall T: History \to Bool, \forall gamma\in History, commitment(gamma) = commitment(edit(gamma)) \Rightarrow T(gamma) = T(edit(gamma))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Audits/TargetRelativeCommitment.commitment_protection_is_target_relative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A history carries a mode bit followed by balance, event-order, identity-source, and contract-authorization coordinates.

The unauthorized edit changes balance in the first mode and changes the other three targets in the second. The commitment stores the Boolean complement of balance, so its injectivity detects every balance change.

At the second witness, the commitment and balance remain equal across the edit while order, identity source, and authorization all change on that same history. The negative clauses therefore cannot be separated into unrelated witnesses.

The final public clause applies the same collision to the order target and rules out protection that is independent of the named target.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Audits/TargetRelativeCommitment.commitment_protection_is_target_relative`
