# Named Cognitive-State Forgetting Certificate

## Abstract

Finite forgetting and recall histories preserve irreversible ledger marks and incompatible-claim separation.

**Theorem 1.1 (The cognitive alphabet has six named states).**

$$\operatorname{card}(CognitiveState)=6.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/FiniteForgettingCertificate.cognitive_state_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inductive alphabet consists exactly of Remember, NeverKnown, Forgotten, Misremember, Recall, and AccessRevoked. These are semantic constructors, not points of a coordinate product. The count supports the certificate but does not serve as its principal invariant.

**Theorem 1.2 (Remember-forget-recall is a nonempty certified history).**

$$\operatorname{Coherent}(r0) \land \operatorname{FiniteHistory}(r0,r2) \land\\\operatorname{ForgottenLogged}(r2) \land \neg(\operatorname{MisrememberOpen}(r2) \land \operatorname{RecallOpen}(r2)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/FiniteForgettingCertificate.remember_forget_recall_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A concrete coherent Remember certificate executes Forget and then Recall as two distinct admitted transitions through Forgotten. The final Recall certificate still carries forgottenLogged and cannot simultaneously carry an open Misremember claim. This supplies an occupied, non-reflexive history rather than relying on the reflexive case of finite closure.

**Theorem 1.3 (Access revocation is terminal).**

$$\forall s,t,\ \operatorname{state}(s)=\mathrm{AccessRevoked} \Rightarrow \neg\operatorname{Transition}(s,t).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/FiniteForgettingCertificate.access_revoked_terminal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

AccessRevoked has no outgoing admitted action. Its certificate carries a typed revocation reason; this reason-bearing entry separates administrative loss of access from epistemic Forgotten and cannot be silently rewritten.

**Theorem 1.4 (Misremember cannot jump directly to Recall).**

$$\forall s,t,\ (\operatorname{state}(s)=\mathrm{Misremember} \land \operatorname{state}(t)=\mathrm{Recall}) \Rightarrow \neg\operatorname{Transition}(s,t).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/FiniteForgettingCertificate.misremember_cannot_recall_directly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A false-memory claim must first be retracted to Forgotten. The dynamics has no direct Misremember-to-Recall arc, preventing a single transition from treating incompatible false and accurate claims as interchangeable.

**Theorem 1.5 (Finite histories preserve the certificate invariants).**

$$\forall s,t,\ (\operatorname{Coherent}(s) \land \operatorname{FiniteHistory}(s,t)) \Rightarrow\\\operatorname{Coherent}(t) \land (\operatorname{ForgottenLogged}(s) \Rightarrow \operatorname{ForgottenLogged}(t)) \land\\(\operatorname{RevokedLogged}(s) \Rightarrow \operatorname{reason}(t)=\operatorname{reason}(s)) \land\\\neg(\operatorname{MisrememberOpen}(t) \land \operatorname{RecallOpen}(t)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/FiniteForgettingCertificate.finite_history_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every coherent source and every finite chain of admitted transitions, the target remains coherent. A prior Forgotten mark stays set; a prior reason-bearing AccessRevoked entry keeps the same reason; and the target cannot carry simultaneous active Misremember and Recall claims. This closure and monotonicity result is the certificate's principal theorem.

## References

- Truth anchor: `D5/S3/Observer/FiniteForgettingCertificate.access_revoked_terminal`
- Truth anchor: `D5/S3/Observer/FiniteForgettingCertificate.cognitive_state_card`
- Truth anchor: `D5/S3/Observer/FiniteForgettingCertificate.finite_history_certificate`
- Truth anchor: `D5/S3/Observer/FiniteForgettingCertificate.misremember_cannot_recall_directly`
- Truth anchor: `D5/S3/Observer/FiniteForgettingCertificate.remember_forget_recall_certificate`
