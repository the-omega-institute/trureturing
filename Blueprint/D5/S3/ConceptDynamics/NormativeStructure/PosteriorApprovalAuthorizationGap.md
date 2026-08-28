# Posterior Approval Does Not Establish Prior Authorization

## Abstract

A change can produce the approval standard under which it is later accepted.

**Theorem 1.1 (Posterior approval can coexist with prior nonauthorization).**

$$\begin{gathered}A: Bool \times Bool \to Bool, A((a, r)) = a,\\{}R: Bool \times Bool \to Bool, R((a, r)) = r,\\{}G((a, r)) = (\neg A((a, r)), \neg R((a, r))),\\{}\forall y: Bool \times Bool, P: Bool \times Bool \to Bool \times Bool, \operatorname{Auth}\left(P\right)_{y} \Leftrightarrow (R(y) = \operatorname{true} \land P(y) \neq y),\\{}x = (\operatorname{false}, \operatorname{false}):\\{}A(G(x)) \neq A(x) \land\\{}R(G(x)) \neq R(x) \land\\{}\neg \operatorname{Auth}\left(G\right)_{x} \land \operatorname{Auth}\left(G\right)_{G(x)} \land\\{}\neg(\operatorname{Auth}\left(G\right)_{G(x)} \Rightarrow \operatorname{Auth}\left(G\right)_{x}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/NormativeStructure/PosteriorApprovalAuthorizationGap.posterior_approval_does_not_imply_prior_authorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A subject state consists of an action-preference bit and an approval-standard bit. The displayed process negates both components, so the model records both changes publicly.

A state authorizes a process exactly when its approval bit is true and the process changes that state. Starting from two false bits, the original state does not authorize the process, while the resulting state does.

The final public clause exhibits the failed implication from posterior approval to prior authorization. The process and authorization rule are constructed independently of that failed implication.

## References

- Truth anchor: `D5/S3/ConceptDynamics/NormativeStructure/PosteriorApprovalAuthorizationGap.posterior_approval_does_not_imply_prior_authorization`
