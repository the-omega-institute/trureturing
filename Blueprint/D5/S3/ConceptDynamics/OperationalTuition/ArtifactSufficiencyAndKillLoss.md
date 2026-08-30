# Artifact Sufficiency and Kill Loss

## Abstract

Persistent artifact sufficiency exactly characterizes zero required-byte loss under every external kill in the finite toy transition system.

**Theorem 1.1 (Artifact sufficiency is equivalent to zero byte loss for every kill).**

$$\begin{aligned}\forall Byte: \operatorname{Type},\\{}[\operatorname{DecidableEq}\left(Byte\right)],\\tau: \operatorname{ToyTrajectory}\left(Byte\right),\\(\operatorname{ArtifactSufficient}\left(\operatorname{finalState}\left(tau\right)\right) \iff \forall k: KillAction, \operatorname{byteLoss}\left(\operatorname{finalState}\left(tau\right), k\right) = \emptyset) \land\\{}(\neg \operatorname{ArtifactSufficient}\left(\operatorname{finalState}\left(tau\right)\right) \Rightarrow \exists k: KillAction, \operatorname{Nonempty}\left(\operatorname{byteLoss}\left(\operatorname{finalState}\left(tau\right), k\right)\right)) \land\\{}(\forall k: KillAction, \operatorname{clockLoss}\left(\operatorname{finalState}\left(tau\right), k\right) = \operatorname{checkpointAge}\left(\operatorname{finalState}\left(tau\right)\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/OperationalTuition/ArtifactSufficiencyAndKillLoss.artifact_sufficient_iff_every_kill_zero_byte_loss` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A toy state separately records required bytes, persistent artifact bytes, volatile session bytes, and checkpoint age. A finite event list is executed by foldl; work creates required session bytes, while a checkpoint persists the session and resets its age.

Process-group clearing and session interruption are distinct finite kill actions with the same persistence boundary: both erase the session and leave the artifact unchanged. Byte loss is required information absent from the resulting recoverable bytes.

Artifact sufficiency and zero post-kill loss are independently defined as finite-set inclusion and transition-system loss. Their equivalence uses finite-set difference. Insufficiency explicitly yields a session kill with nonempty loss, and clock loss equals checkpoint age.

## References

- Truth anchor: `D5/S3/ConceptDynamics/OperationalTuition/ArtifactSufficiencyAndKillLoss.artifact_sufficient_iff_every_kill_zero_byte_loss`
