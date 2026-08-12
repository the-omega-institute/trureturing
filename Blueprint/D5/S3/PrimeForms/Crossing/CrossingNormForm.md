# The Crossing Form is the Eisenstein Norm Curve

## Abstract

The discriminant -3 crossing form represents exactly the Eisenstein norms, for every parameter.

**Theorem 1.1 (The crossing form represents exactly the Eisenstein norms for every t).**

$$Q_t(P,Q) = P^{2}-(2t+1)PQ+(t^{2}+t+1)Q^{2}, \operatorname{disc} = -3\\\operatorname{range} Q_t = \operatorname{range}(x^{2}+xy+y^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Crossing/CrossingNormForm.Qform_range_eq_eisNorm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The one-parameter crossing form Q_t(P,Q) = P^2 - (2t+1)PQ + (t^2+t+1)Q^2 has discriminant b^2 - 4ac = (2t+1)^2 - 4(t^2+t+1) = -3, identically in the parameter t, and reduces under the explicit unimodular substitution (P,Q) -> (P-(t+1)Q, Q) to the principal Eisenstein (Loeschian) norm form x^2 + xy + y^2. Consequently, for every integer t, the values represented by Q_t are exactly the Eisenstein norms: the whole one-parameter family collapses to the single value-set of the principal form.

The reduction Q_t(P,Q) = eisNorm(P-(t+1)Q, Q) and the discriminant identity are ring identities. The value-set equality is both inclusions via the explicit unimodular change of variables and its inverse: the reduction gives range Q_t contained in range eisNorm, and eisNorm(x,y) = Q_t(x+(t+1)y, y) gives the reverse containment, so the two ranges coincide.

Mathlib has no representation lemma for x^2 + xy + y^2 and no such parameterized-form reduction, so this is a genuine construction rather than a library restatement. It records the algebraic unified foundation of residual E.63 — the discriminant -3 identification of the crossing form with the Eisenstein norm curve. The criterion's crossing-if-and-only-if-continued-fraction-orbit biconditional, the three generation-mechanism laws, and the self-insertion ladder are not covered.

## References

- Truth anchor: `D5/S3/PrimeForms/Crossing/CrossingNormForm.Qform_range_eq_eisNorm`
