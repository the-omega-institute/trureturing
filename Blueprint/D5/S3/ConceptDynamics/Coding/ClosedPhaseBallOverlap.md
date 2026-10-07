# Closed Circular Phase Ball Overlap

## Abstract

Closed phase balls intersect exactly at the doubled-radius distance bound.

**Theorem 1.1 (Exact closed-ball intersection).**

$$\forall P: \left(\mathbb{N}\right), \left(\forall eps: \left(\mathbb{R}\right), \left(\forall x: \left(\operatorname{AddCircle}\left(\operatorname{real}\left(P\right)\right)\right), \left(\forall y: \left(\operatorname{AddCircle}\left(\operatorname{real}\left(P\right)\right)\right), \left(\left(\exists q: \left(\operatorname{AddCircle}\left(\operatorname{real}\left(P\right)\right)\right), \left(\left(\operatorname{dist}\left(q, x\right) \le eps\right) \land \left(\operatorname{dist}\left(q, y\right) \le eps\right)\right)\right) \iff \left(\operatorname{dist}\left(x, y\right) \le \left(2\right) \cdot \left(eps\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ClosedPhaseBallOverlap.closed_phase_ball_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a natural period P and a real radius eps, two closed balls in the real additive circle meet exactly when their centers have distance at most 2eps. The triangle inequality gives necessity. For sufficiency, choose a shortest lift of the displacement and take its midpoint. Equality is included.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ClosedPhaseBallOverlap.closed_phase_ball_overlap`
