# Normalized coefficient contractions

## Abstract

A strict improvement of coefficient agreement gives a unique normalized formal power-series fixed point.

**Theorem 1.1 (A normalized contraction has a unique fixed point).**

$$\forall R: Type, [\operatorname{CommRing}\left(R\right)], \forall step: \operatorname{PowerSeries}\left(R\right) \to \operatorname{PowerSeries}\left(R\right), (\forall f: \operatorname{PowerSeries}\left(R\right), (\operatorname{constantCoeff}\left(f\right) = 1) \implies (\operatorname{constantCoeff}\left(\operatorname{step}\left(f\right)\right) = 1)) \implies ((\forall d: \mathbb{N}, \forall f: \operatorname{PowerSeries}\left(R\right), \forall g: \operatorname{PowerSeries}\left(R\right), (1 \le d) \implies ((\operatorname{constantCoeff}\left(f\right) = 1) \implies ((\operatorname{constantCoeff}\left(g\right) = 1) \implies ((\operatorname{Agree}\left(d, f, g\right)) \implies (\operatorname{Agree}\left((d) + (1), \operatorname{step}\left(f\right), \operatorname{step}\left(g\right)\right)))))) \implies (\exists f: \operatorname{PowerSeries}\left(R\right), (\operatorname{constantCoeff}\left(f\right) = 1) \land ((f = \operatorname{step}\left(f\right)) \land (\forall g: \operatorname{PowerSeries}\left(R\right), (\operatorname{constantCoeff}\left(g\right) = 1) \implies ((g = \operatorname{step}\left(g\right)) \implies (g = f))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.exists_unique_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nth coefficient is read from the nth iterate. Improving agreement stabilizes these coefficients; induction proves the fixed-point identity and uniqueness.

**Theorem 1.2 (Geometric zero).**

$$\forall R: Type, [\operatorname{CommRing}\left(R\right)], \operatorname{constantCoeff}\left((\operatorname{geometric}: \operatorname{PowerSeries}\left(R\right))\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.geometric_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The geometric series X times mk 1 has constant coefficient zero.

**Theorem 1.3 (Geometric one).**

$$\forall R: Type, [\operatorname{CommRing}\left(R\right)], \operatorname{coeff}\left(1, (\operatorname{geometric}: \operatorname{PowerSeries}\left(R\right))\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.geometric_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient of X in X times mk 1 is one.

**Theorem 1.4 (Geometric coeff).**

$$\forall R: Type, [\operatorname{CommRing}\left(R\right)], \forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{coeff}\left(n, (\operatorname{geometric}: \operatorname{PowerSeries}\left(R\right))\right) = 1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.geometric_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive coefficient of the geometric series is one.

**Theorem 1.5 (Geometric mul).**

$$\forall R: Type, [\operatorname{CommRing}\left(R\right)], ((\operatorname{geometric}: \operatorname{PowerSeries}\left(R\right))) \cdot ((1) - (X)) = X$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.geometric_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the geometric series by one minus X gives X.

**Theorem 1.6 (Map subst pow).**

$$\forall R: Type, [\operatorname{CommRing}\left(R\right)], \forall S: Type, [\operatorname{CommRing}\left(S\right)], \forall hom: R \to^{+*} S, \forall f: \operatorname{PowerSeries}\left(R\right), \forall k: \mathbb{N}, (k \neq 0) \implies (\operatorname{map}\left(hom, \operatorname{subst}\left((X)^{k}, f\right)\right) = \operatorname{subst}\left((X)^{k}, \operatorname{map}\left(hom, f\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.map_subst_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mapping coefficients along a ring homomorphism commutes with substitution by a positive power of X.

**Theorem 1.7 (Geometric subst mul).**

$$\forall R: Type, [\operatorname{CommRing}\left(R\right)], \forall k: \mathbb{N}, (k \neq 0) \implies ((\operatorname{subst}\left((X)^{k}, (\operatorname{geometric}: \operatorname{PowerSeries}\left(R\right))\right)) \cdot ((1) - ((X)^{k})) = (X)^{k})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.geometric_subst_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituting X to a positive power in the geometric identity preserves multiplication.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.exists_unique_fixed`
- Truth anchor: `D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.geometric_coeff`
- Truth anchor: `D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.geometric_mul`
- Truth anchor: `D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.geometric_one`
- Truth anchor: `D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.geometric_subst_mul`
- Truth anchor: `D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.geometric_zero`
- Truth anchor: `D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.map_subst_pow`
- Dependency: [D5/S1/Recurrence/Invariants/CompositionalIterateCongruence](CompositionalIterateCongruence.md)
- Dependency: [D5/S1/Recurrence/Invariants/ScaledReversionCongruence](ScaledReversionCongruence.md)
- Dependency: [D5/S1/Recurrence/Invariants/UnitReversionSquareParity](UnitReversionSquareParity.md)
