# Jet Resolvent Semisimplification

## Abstract

A finite nilpotent jet pencil reduces to one simple pole carrying its length as weight.

**Theorem 1.1 (Trace and logarithmic derivative retain only jet multiplicity).**

$$\forall m \in \mathbb{N}, rho \in \mathbb{C}, s \in \mathbb{C},\; s \ne rho \Rightarrow \left(\operatorname{trace}\left(\operatorname{jetPencil}\left(m, rho, s\right)^{-1}\right) = \frac{m}{s - rho} \land \left(\operatorname{logDeriv}\left((z \mapsto \operatorname{det}\left(\operatorname{jetPencil}\left(m, rho, z\right)\right)), s\right) = \frac{m}{s - rho} \land \operatorname{trace}\left(\operatorname{jetPencil}\left(m, rho, s\right)^{-1}\right) = \operatorname{logDeriv}\left((z \mapsto \operatorname{det}\left(\operatorname{jetPencil}\left(m, rho, z\right)\right)), s\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/JetResolventSemisimplification.jet_resolvent_semisimplification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For length m, nilpotentJetShift has value one exactly one step below the diagonal and zero elsewhere. The named jetPencil is (s-rho) times the identity minus that shift.

The displayed non-pole premise is the exact invertibility domain of the source resolvent. The logarithmic derivative is Mathlib's branch-independent deriv(f)/f operation, so no principal-log branch condition is introduced.

Lower triangularity makes the pencil determinant (s-rho)^m and every diagonal inverse entry (s-rho)^(-1). Summing the diagonal and differentiating the determinant therefore give the same simple pole of weight m, exposed again by the final conjunct.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/JetResolventSemisimplification.jet_resolvent_semisimplification`
