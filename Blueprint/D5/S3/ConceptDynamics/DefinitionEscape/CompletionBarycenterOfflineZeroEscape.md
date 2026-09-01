# Completion Barycenter Offline-Zero Escape

## Abstract

A completion barycenter observer cannot recover squared offline displacement.

**Theorem 1.1 (Squared displacement escapes the completion barycenter).**

$$\neg \exists f: Complex \to Real, \forall x: SpectralState, squareTarget(x) = f(completionObserver(x)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/CompletionBarycenterOfflineZeroEscape.completion_barycenter_offline_zero_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A spectral state is a pair (gamma, delta) whose displacement lies strictly between negative one half and one half. The completion observer reads one half plus i times gamma, whereas the target is the square of delta.

The legal states (0, 1/4) and (0, 1/3) both read as one half. Their target values are computed as 1/16 and 1/9, so they form a nonempty target-sensitive observer fiber.

The accepted target recovery criterion turns this explicit defect into the stated failure of every real-valued recovery function on complex observations. The proof therefore reuses the repository's general factorization theorem rather than duplicating it.

The companion residual theorem applies the accepted residual join law: adjoining the squared displacement itself makes the target defect empty. A positive control computes different observations for (1, 0) and (2, 0), confirming that only the displacement direction is lost in these witnesses.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/CompletionBarycenterOfflineZeroEscape.completion_barycenter_offline_zero_escape`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/ResidualJoinLaw](ResidualJoinLaw.md)
- Dependency: [D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion](../Restoration/TargetRecoveryCriterion.md)
