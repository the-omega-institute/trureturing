# Misleading Receiver Exclusion

## Abstract

Factorized targets and image-correct decoding exclude misleading reception.

**Theorem 1.1 (Misleading reception is impossible under correct image decoding).**

$$\begin{gathered}A, M, Y,\\{}M_{S}: A \to M, T: A \to Y, delta: M \to Y, d: M \to Y,\\{}T = d \circ M_{S},\\{}\forall m, m \in \operatorname{range}(M_{S}) \Rightarrow delta(m) = d(m),\\{}\forall a, \neg\operatorname{Misleading}(M_{S}, T, delta, a).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Transport/MisleadingReceiverExclusion.misleading_impossible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M_S map an actual state to its message, let T be the target value, let d be the correct decoder, and let delta be the receiver's decoder. A receiver is misleading at state a exactly when delta(M_S(a)) differs from T(a).

If the target factors as T = d composed with M_S and delta agrees with d on the actual message image, then every actual message decodes to its target. Thus no state is misleading.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Transport/MisleadingReceiverExclusion.misleading_impossible`
