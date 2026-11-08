# Bala A281440 Totient-Square Period

## Abstract

Totient-square periods of integral derivation coefficients.

**Definition 1.1 (claim).**

$$claim = (\exists (H C : PowerSeries \mathbb{Q}) , \operatorname{PowerSeries}.\operatorname{constantCoeff} H = 0 \land \operatorname{PowerSeries}.\operatorname{derivative} H = C^{7} \land C = \operatorname{PowerSeries}.\operatorname{C} (1 / 2 : \mathbb{Q}) \cdot (\operatorname{PowerSeries}.\operatorname{subst} H (\operatorname{PowerSeries}.\operatorname{exp} \mathbb{Q}) + \operatorname{PowerSeries}.\operatorname{subst} (- H) (\operatorname{PowerSeries}.\operatorname{exp} \mathbb{Q})) \land (\exists a : \mathbb{N} \to \mathbb{Z} , (\forall n : \mathbb{N} , (a n : \mathbb{Q}) = eCoeff (C^{1}) (2 \cdot n)) \land (\forall k : \mathbb{N} , 1 \le k \implies \exists N : \mathbb{N} , \forall n : \mathbb{N} , N \le n \implies \operatorname{Int}.\operatorname{ModEq} (k : \mathbb{Z}) (a (n + (\operatorname{Nat}.\operatorname{totient} k)^{2})) (a n))))$$

*Formalization.* `D5/S1/Recurrence/Periodic/BalaA281440TotientSquarePeriod.claim` (`✓ std3`).

*Citation.* Peter Bala (2026). *OEIS A281180 and its hyperbolic EGF family: totient-square periods*. URL: <https://oeis.org/A281180>.

*Commentary.*

E.g.f. C(x) satisfies: C(x) = cosh( Integral C(x)^7 dx ). Conjecture: the sequence {a(n)} reduced modulo a positive integer k is eventually periodic with the period dividing phi(k)^2, where phi(n) = A000010(n). An example is given below. - _Peter Bala_, Feb 19 2026 The source is unpaginated. The primitive has constant coefficient zero, eCoeff is factorial times the ordinary coefficient, and all sequences take integer values. Natural subtraction is truncated subtraction.

**Theorem 1.2 (result).**

$$\exists (H C : PowerSeries \mathbb{Q}) , \operatorname{PowerSeries}.\operatorname{constantCoeff} H = 0 \land \operatorname{PowerSeries}.\operatorname{derivative} H = C^{7} \land C = \operatorname{PowerSeries}.\operatorname{C} (1 / 2 : \mathbb{Q}) \cdot (\operatorname{PowerSeries}.\operatorname{subst} H (\operatorname{PowerSeries}.\operatorname{exp} \mathbb{Q}) + \operatorname{PowerSeries}.\operatorname{subst} (- H) (\operatorname{PowerSeries}.\operatorname{exp} \mathbb{Q})) \land (\exists a : \mathbb{N} \to \mathbb{Z} , (\forall n : \mathbb{N} , (a n : \mathbb{Q}) = eCoeff (C^{1}) (2 \cdot n)) \land (\forall k : \mathbb{N} , 1 \le k \implies \exists N : \mathbb{N} , \forall n : \mathbb{N} , N \le n \implies \operatorname{Int}.\operatorname{ModEq} (k : \mathbb{Z}) (a (n + (\operatorname{Nat}.\operatorname{totient} k)^{2})) (a n)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/BalaA281440TotientSquarePeriod.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2026). *OEIS A281180 and its hyperbolic EGF family: totient-square periods*. URL: <https://oeis.org/A281180>.

*Commentary.*

The integral derivation flow supplies the series and its integer exponential coefficients. Prime-power operator annihilators give the prescribed shift, and divisibility assembles all positive moduli.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281440TotientSquarePeriod.claim`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281440TotientSquarePeriod.result`
- Dependency: [D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod](BalaA281181TotientSquarePeriod.md)
- Dependency: [D5/S1/Recurrence/Residue/IntegralEGFComposition](../Residue/IntegralEGFComposition.md)
