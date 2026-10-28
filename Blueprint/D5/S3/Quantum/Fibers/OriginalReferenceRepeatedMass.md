# Loss is the decrease of the surviving mode weight

## Abstract

Mode balance and completeness for native repeated quantum outputs.

**Theorem 1.1 (Every original control and every subinterval).**

$$\forall c \in Real, a \in Real, T \in Real, k \in \operatorname{Function}\left(Real, Real\right), i \in \operatorname{Fin}\left(5\right), s \in Real, t \in Real,\; \left(\operatorname{lt}\left(c, \operatorname{divide}\left(1, 2\right)\right) \land \left(\operatorname{memIoo}\left(a, 0, c\right) \land \left(\operatorname{OriginalConstantPhaseControl}\left(c, T, k\right) \land \operatorname{orderedSubinterval}\left(s, t, 0, T\right)\right)\right)\right) \Rightarrow \left(\operatorname{IntegrableOn}\left(\operatorname{modeCoefficient}\left(c, a, k, i\right), \operatorname{Ioc}\left(s, t\right)\right) \land \operatorname{integral}\left(\operatorname{modeCoefficient}\left(c, a, k, i\right), \operatorname{Ioc}\left(s, t\right)\right) = \operatorname{divide}\left(\operatorname{survival}\left(c, k, s\right) \cdot \operatorname{p}\left(c, \operatorname{apply}\left(k, s\right), i\right) - \operatorname{survival}\left(c, k, t\right) \cdot \operatorname{p}\left(c, \operatorname{apply}\left(k, t\right), i\right), \operatorname{p}\left(c, a, i\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalReferenceRepeatedMass.native_mode_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix c<1/2, 0<a<c and an original height k on [0,T] with constant phase zero. For each original mode i, let p_i(k) be its positive double-wall probability, S(t)=exp(-integral_0^t hazard(c,k)) its native survival, and f_i(t) the squared literal jump amplitude. For every 0<=s<=t<=T, f_i is integrable on (s,t] and its integral equals [S(s)p_i(k(s))-S(t)p_i(k(t))]/p_i(a). No initial-height equality is needed for this general balance law.

The original regularity alternatives imply absolute continuity of k. The integrable native hazard has an absolutely continuous primitive. Exponentiation preserves absolute continuity on its compact range, and multiplication by each affine probability coordinate preserves it. Almost everywhere, logarithmic differentiation gives g_i=hazard-p_i'/p_i. The explicit five coordinates show g_i>=0. Consequently the literal squared square-root amplitude is g_i S p_i/p_i(a), which is minus the derivative of S p_i divided by p_i(a). The fundamental theorem for absolutely continuous functions gives the balance identity. Exceptional derivative values at corners have zero Lebesgue mass.

**Theorem 1.2 (The same arbitrary joint input across prefix and suffix).**

$$\forall H \in CompleteComplexHilbertSpace, B \in OriginalSupportBand, n \in Natural, e \in Bool, rho \in \operatorname{PositiveJointTraceClass}\left(H\right),\; \operatorname{atLeastOne}\left(n\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(5\right),\; \left(\forall t \in Real,\; \operatorname{memIoc}\left(t, 1, 2\right) \Rightarrow \operatorname{apply}\left(\operatorname{modeOutput}\left(B, \operatorname{literalEarlyLate}\left(B, n, e\right), i, rho\right), t\right) = \operatorname{smul}\left(\operatorname{power}\left(\operatorname{q}\left(B\right), n\right), \operatorname{apply}\left(\operatorname{modeOutput}\left(B, \operatorname{literalSuffix}\left(B, e\right), i, rho\right), t - 1\right)\right)\right) \land \left(\operatorname{integral}\left(\operatorname{modeCoefficient}\left(B, \operatorname{literalEarlyLate}\left(B, n, e\right), i\right), \operatorname{Ioc}\left(0, 1\right)\right) = 1 - \operatorname{power}\left(\operatorname{q}\left(B\right), n\right) \land \left(\operatorname{integral}\left(\operatorname{modeCoefficient}\left(B, \operatorname{literalEarlyLate}\left(B, n, e\right), i\right), \operatorname{Ioc}\left(1, 2\right)\right) = \operatorname{power}\left(\operatorname{q}\left(B\right), n\right) \cdot \left(1 - \operatorname{q}\left(B\right)\right) \land \left(\operatorname{integral}\left(\operatorname{modeCoefficient}\left(B, \operatorname{literalEarlyLate}\left(B, n, e\right), i\right), \operatorname{Ioc}\left(0, 2\right)\right) = 1 - \operatorname{power}\left(\operatorname{q}\left(B\right), n + 1\right) \land \operatorname{integral}\left(\operatorname{modeOutput}\left(B, \operatorname{literalEarlyLate}\left(B, n, e\right), i, rho\right), \operatorname{Ioc}\left(1, 2\right)\right) = \operatorname{smul}\left(\operatorname{power}\left(\operatorname{q}\left(B\right), n\right) \cdot \left(1 - \operatorname{q}\left(B\right)\right), \operatorname{referenceCompression}\left(rho, i\right)\right)\right)\right)\right)\right) \land \left(\operatorname{sumModeOutputIntegralNorms}\left(B, \operatorname{literalEarlyLate}\left(B, n, e\right), rho, \operatorname{Ioc}\left(1, 2\right)\right) = \operatorname{power}\left(\operatorname{q}\left(B\right), n\right) \cdot \left(1 - \operatorname{q}\left(B\right)\right) \cdot \operatorname{norm}\left(rho\right) \land \operatorname{sumModeOutputIntegralNorms}\left(B, \operatorname{literalEarlyLate}\left(B, n, e\right), rho, \operatorname{Ioc}\left(0, 2\right)\right) + \operatorname{norm}\left(\operatorname{smul}\left(\operatorname{power}\left(\operatorname{q}\left(B\right), n + 1\right), rho\right)\right) = \operatorname{norm}\left(rho\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalReferenceRepeatedMass.repeated_reference_completeness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let B be any band 0<a<b<c<1/2, n>=1 and e either literal early or late history k. Put q=(a/b)(c-b)/(c-a). H is any complete complex Hilbert space, including nonseparable spaces. rho is any positive trace-class operator on Blocks(Fin5,H), with no normalization, finite-rank, separability or product-state assumption. A_i is the positive trace-class compression of that same rho to reference block i. The actual reference-output density is F_i(t)=f_i(t) A_i, as identified with tensor-amplified Kraus conjugation by OriginalReferenceOutputMeasure.repeated_failure_event.

For every mode i and every 1<t<=2, F_i(t)=q^n F_i^suffix(t-1), where the suffix uses the same rho and the original earlySuffix or lateSuffix control. This is exact prefix scaling of each reference operator, using the already established chronological Kraus action. The coefficient integrals on (0,1], (1,2] and (0,2] are respectively 1-q^n, q^n(1-q) and 1-q^(n+1). In particular the suffix Bochner integral is q^n(1-q) A_i. The endpoint heights and native survival values are supplied by OriginalRepeatedPrefix; they are applied to the general mode balance identity.

Summing the norms of the five suffix event outputs gives q^n(1-q) norm(rho). Summing the norms of the five full failure event outputs and adding norm(q^(n+1) rho) gives norm(rho). Positivity turns each scalar multiple into its nonnegative coefficient times norm(A_i), and the same-input block trace partition gives sum_i norm(A_i)=norm(rho). Thus all modes and their unchanged reference correlations contribute to exact mass completeness. The terminal term here is the scalar successful endpoint action. The result does not claim the operational supremum or a distance formula for general initially stopped six-coordinate inputs.

The operational supremum, general live-stopped coherences and the inverse/resource applications require further statements. The present identities retain their unnormalized form; normalized live inputs have norm(rho)=1.

**Theorem 1.3 (Common prefix cancellation and disjoint suffix windows).**

$$\forall H \in CompleteComplexHilbertSpace, B \in OriginalSupportBand, n \in Natural, rho \in \operatorname{PositiveJointTraceClass}\left(H\right),\; \operatorname{atLeastOne}\left(n\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(5\right), E \in \operatorname{Set}\left(Real\right),\; \operatorname{MeasurableSet}\left(E\right) \Rightarrow \operatorname{integral}\left(\operatorname{modeOutput}\left(B, \operatorname{literalEarly}\left(B, n\right), i, rho\right), \operatorname{intersection}\left(\operatorname{Ioc}\left(0, 1\right), E\right)\right) = \operatorname{integral}\left(\operatorname{modeOutput}\left(B, \operatorname{literalLate}\left(B, n\right), i, rho\right), \operatorname{intersection}\left(\operatorname{Ioc}\left(0, 1\right), E\right)\right)\right) \land \operatorname{sumModesIntegralNormDifference}\left(B, \operatorname{literalEarly}\left(B, n\right), \operatorname{literalLate}\left(B, n\right), rho, \operatorname{Ioc}\left(0, 2\right)\right) = 2 \cdot \operatorname{power}\left(\operatorname{q}\left(B\right), n\right) \cdot \left(1 - \operatorname{q}\left(B\right)\right) \cdot \operatorname{norm}\left(rho\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalReferenceRepeatedMass.repeated_reference_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every band B, n>=1, arbitrary complete complex Hilbert reference H and positive joint trace-class rho, every mode's prefix Bochner outputs agree on (0,1] intersect every Borel event E. Moreover sum_i integral_(0,2] norm(F_i^early(t)-F_i^late(t)) equals 2 q^n(1-q) norm(rho). Both densities use the same rho, including all entanglement with its unchanged reference.

Before time one, the literal heights, native survival and jump rates coincide almost everywhere. The seam has zero Lebesgue mass, giving equality on every restricted event. The late suffix is constant before its excursion and the early suffix is constant after its excursion. Local constancy makes both the height derivative and logarithmic probability derivative vanish, so the actual jump coefficient vanishes on the corresponding waiting window. Exact prefix scaling carries these zero densities to the original clock. Except at the middle seam, one of the two suffix densities is zero. Thus the norm of their difference equals the sum of their norms, without comparing independent inputs or replacing joint operators by marginal probabilities.

Split the full interval into prefix and suffix. The prefix difference integrates to zero, and the suffix norm integral is the sum of the two positive suffix masses. The preceding completeness theorem supplies each mass q^n(1-q) norm(rho). For normalized live rho, the half-sum convention therefore gives q^n(1-q) for this failure-density contribution. This theorem does not itself define an operational supremum, prove the general six-coordinate initial-state extension, or close the inverse and resource statements.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/OriginalReferenceRepeatedMass.native_mode_balance`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalReferenceRepeatedMass.repeated_reference_completeness`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalReferenceRepeatedMass.repeated_reference_distance`
- Dependency: [D5/S3/Quantum/Fibers/OriginalReferenceOutputMeasure](OriginalReferenceOutputMeasure.md)
