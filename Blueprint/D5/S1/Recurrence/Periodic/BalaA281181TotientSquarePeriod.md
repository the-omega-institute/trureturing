# Bala A281181 Totient-Square Period

## Abstract

Totient-square periods of integral derivation coefficients.

**Definition 1.1 (c).**

$$\operatorname{BalaPolynomialSystem}.\operatorname{c} = (\operatorname{MvPolynomial}.\operatorname{X} false : MvPolynomial Bool \mathbb{Z})$$

*Formalization.* `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.c` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first coordinate is indexed by false.

**Definition 1.2 (s).**

$$\operatorname{BalaPolynomialSystem}.\operatorname{s} = (\operatorname{MvPolynomial}.\operatorname{X} true : MvPolynomial Bool \mathbb{Z})$$

*Formalization.* `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.s` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second coordinate is indexed by true.

**Definition 1.3 (deriv).**

$$\forall (q : \mathbb{N}) , \operatorname{BalaPolynomialSystem}.\operatorname{deriv} q = \operatorname{MvPolynomial}.\operatorname{mkDerivation} \mathbb{Z} (fun b : Bool \mapsto if b then (\operatorname{BalaPolynomialSystem}.\operatorname{c})^{q + 1} else (\operatorname{BalaPolynomialSystem}.\operatorname{c})^{q} \cdot \operatorname{BalaPolynomialSystem}.\operatorname{s})$$

*Formalization.* `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.deriv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two polynomial coordinate derivatives are c to the power q times s, and c to the power q plus one.

**Definition 1.4 (initial).**

$$\operatorname{BalaPolynomialSystem}.\operatorname{initial} = \operatorname{MvPolynomial}.\operatorname{eval} (fun b : Bool \mapsto if b then (0 : \mathbb{Z}) else 1)$$

*Formalization.* `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.initial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial evaluation sends c to one and s to zero.

**Definition 1.5 (C).**

$$\forall (q : \mathbb{N}) , \operatorname{BalaPolynomialSystem}.\operatorname{C} q = \operatorname{BalaFlow}.\operatorname{flow} (\operatorname{BalaPolynomialSystem}.\operatorname{deriv} q) \operatorname{BalaPolynomialSystem}.\operatorname{initial} \operatorname{BalaPolynomialSystem}.\operatorname{c}$$

*Formalization.* `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first coordinate flow has initial value one.

**Definition 1.6 (S).**

$$\forall (q : \mathbb{N}) , \operatorname{BalaPolynomialSystem}.\operatorname{S} q = \operatorname{BalaFlow}.\operatorname{flow} (\operatorname{BalaPolynomialSystem}.\operatorname{deriv} q) \operatorname{BalaPolynomialSystem}.\operatorname{initial} \operatorname{BalaPolynomialSystem}.\operatorname{s}$$

*Formalization.* `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.S` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second coordinate flow has initial value zero.

**Theorem 1.7 (constant S).**

$$\forall (q : \mathbb{N}) , \operatorname{PowerSeries}.\operatorname{constantCoeff} (\operatorname{BalaPolynomialSystem}.\operatorname{S} q) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.constant_S` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second flow starts at zero.

**Theorem 1.8 (A281180 ode).**

$$\operatorname{PowerSeries}.\operatorname{derivative} (\operatorname{BalaPolynomialSystem}.\operatorname{S} 3) = (1 + (\operatorname{BalaPolynomialSystem}.\operatorname{S} 3)^{2})^{2}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.A281180_ode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At q equal to three, the invariant reduces the second coordinate equation to the quartic scalar equation.

**Definition 1.9 (H).**

$$\forall (q : \mathbb{N}) , \operatorname{BalaPolynomialSystem}.\operatorname{H} q = \operatorname{D5}.\operatorname{S1}.\operatorname{Recurrence}.\operatorname{Algebraic}.\operatorname{SchroderIntegralEGF}.\operatorname{primitive} ((\operatorname{BalaPolynomialSystem}.\operatorname{C} q)^{q})$$

*Formalization.* `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Integrate C to the power q with constant coefficient zero.

**Theorem 1.10 (constant H).**

$$\forall (q : \mathbb{N}) , \operatorname{PowerSeries}.\operatorname{constantCoeff} (\operatorname{BalaPolynomialSystem}.\operatorname{H} q) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.constant_H` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The primitive has constant coefficient zero.

**Theorem 1.11 (derivative H).**

$$\forall (q : \mathbb{N}) , \operatorname{PowerSeries}.\operatorname{derivative} (\operatorname{BalaPolynomialSystem}.\operatorname{H} q) = (\operatorname{BalaPolynomialSystem}.\operatorname{C} q)^{q}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.derivative_H` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiating the primitive recovers C to the power q.

**Theorem 1.12 (cosh identity).**

$$\forall (q : \mathbb{N}) , \operatorname{BalaPolynomialSystem}.\operatorname{C} q = \operatorname{PowerSeries}.\operatorname{C} (1 / 2 : \mathbb{Q}) \cdot ((\operatorname{PowerSeries}.\operatorname{subst} (\operatorname{BalaPolynomialSystem}.\operatorname{H} q) (\operatorname{PowerSeries}.\operatorname{exp} \mathbb{Q})) + (\operatorname{PowerSeries}.\operatorname{subst} (- (\operatorname{BalaPolynomialSystem}.\operatorname{H} q)) (\operatorname{PowerSeries}.\operatorname{exp} \mathbb{Q})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.cosh_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum and difference of the coordinate flows solve scalar linear differential equations, giving the two exponentials.

**Theorem 1.13 (log derivative).**

$$\forall (q : \mathbb{N}) , \operatorname{PowerSeries}.\operatorname{derivative} (\operatorname{PowerSeries}.\operatorname{logOf} (\operatorname{BalaPolynomialSystem}.\operatorname{C} q + \operatorname{BalaPolynomialSystem}.\operatorname{S} q)) = (\operatorname{BalaPolynomialSystem}.\operatorname{C} q)^{q}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.log_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The logarithmic derivative of C plus S is C to the power q.

**Definition 1.14 (evenSequence).**

$$\forall (q e n : \mathbb{N}) , \operatorname{BalaPolynomialSystem}.\operatorname{evenSequence} q e n = \operatorname{BalaPolynomialSystem}.\operatorname{initial} (\operatorname{Nat}.\operatorname{iterate} (\operatorname{BalaPolynomialSystem}.\operatorname{deriv} q) (2 \cdot n) ((\operatorname{BalaPolynomialSystem}.\operatorname{c})^{e}))$$

*Formalization.* `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.evenSequence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The even derivative values of a coordinate power form an integer sequence.

**Theorem 1.15 (even sequence coefficient).**

$$\forall (q e n : \mathbb{N}) , (\operatorname{BalaPolynomialSystem}.\operatorname{evenSequence} q e n : \mathbb{Q}) = eCoeff ((\operatorname{BalaPolynomialSystem}.\operatorname{C} q)^{e}) (2 \cdot n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.even_sequence_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

These integer values are exactly the even exponential coefficients.

**Theorem 1.16 (even sequence period).**

$$\forall (q : \mathbb{N}) , (q = 3 \lor q = 7) \implies \forall (e : \mathbb{N}) , \forall (k : \mathbb{N}) , 1 \le k \implies \exists (N : \mathbb{N}) , 1 \le N \land (\forall (n : \mathbb{N}) , N \le n \implies \operatorname{Int}.\operatorname{ModEq} (k : \mathbb{Z}) (\operatorname{BalaPolynomialSystem}.\operatorname{evenSequence} q e (n + (\operatorname{Nat}.\operatorname{totient} k)^{2})) (\operatorname{BalaPolynomialSystem}.\operatorname{evenSequence} q e n))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.even_sequence_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Odd-prime square-root coordinates and a separate second-order argument at two establish every positive modulus for q equal to three or seven.

**Definition 1.17 (claim).**

$$claim = (\exists (H C : PowerSeries \mathbb{Q}) , \operatorname{PowerSeries}.\operatorname{constantCoeff} H = 0 \land \operatorname{PowerSeries}.\operatorname{derivative} H = C^{3} \land C = \operatorname{PowerSeries}.\operatorname{C} (1 / 2 : \mathbb{Q}) \cdot (\operatorname{PowerSeries}.\operatorname{subst} H (\operatorname{PowerSeries}.\operatorname{exp} \mathbb{Q}) + \operatorname{PowerSeries}.\operatorname{subst} (- H) (\operatorname{PowerSeries}.\operatorname{exp} \mathbb{Q})) \land (\exists a : \mathbb{N} \to \mathbb{Z} , (\forall n : \mathbb{N} , (a n : \mathbb{Q}) = eCoeff (C^{1}) (2 \cdot n)) \land (\forall k : \mathbb{N} , 1 \le k \implies \exists N : \mathbb{N} , \forall n : \mathbb{N} , N \le n \implies \operatorname{Int}.\operatorname{ModEq} (k : \mathbb{Z}) (a (n + (\operatorname{Nat}.\operatorname{totient} k)^{2})) (a n))))$$

*Formalization.* `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.claim` (`✓ std3`).

*Citation.* Peter Bala (2026). *OEIS A281180 and its hyperbolic EGF family: totient-square periods*. URL: <https://oeis.org/A281180>.

*Commentary.*

E.g.f. C(x) satisfies C(x) = cosh( Integral C(x)^3 dx ). More generally, we conjecture that the sequence {a(n)} reduced modulo a positive integer k is eventually periodic with the period dividing phi(k)^2, where phi(n) = A000010(n). An example is given below. - _Peter Bala_, Feb 16 2026 The source is unpaginated. The primitive has constant coefficient zero, eCoeff is factorial times the ordinary coefficient, and all sequences take integer values. Natural subtraction is truncated subtraction.

**Theorem 1.18 (result).**

$$\exists (H C : PowerSeries \mathbb{Q}) , \operatorname{PowerSeries}.\operatorname{constantCoeff} H = 0 \land \operatorname{PowerSeries}.\operatorname{derivative} H = C^{3} \land C = \operatorname{PowerSeries}.\operatorname{C} (1 / 2 : \mathbb{Q}) \cdot (\operatorname{PowerSeries}.\operatorname{subst} H (\operatorname{PowerSeries}.\operatorname{exp} \mathbb{Q}) + \operatorname{PowerSeries}.\operatorname{subst} (- H) (\operatorname{PowerSeries}.\operatorname{exp} \mathbb{Q})) \land (\exists a : \mathbb{N} \to \mathbb{Z} , (\forall n : \mathbb{N} , (a n : \mathbb{Q}) = eCoeff (C^{1}) (2 \cdot n)) \land (\forall k : \mathbb{N} , 1 \le k \implies \exists N : \mathbb{N} , \forall n : \mathbb{N} , N \le n \implies \operatorname{Int}.\operatorname{ModEq} (k : \mathbb{Z}) (a (n + (\operatorname{Nat}.\operatorname{totient} k)^{2})) (a n)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2026). *OEIS A281180 and its hyperbolic EGF family: totient-square periods*. URL: <https://oeis.org/A281180>.

*Commentary.*

The integral derivation flow supplies the series and its integer exponential coefficients. Prime-power operator annihilators give the prescribed shift, and divisibility assembles all positive moduli.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.A281180_ode`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.C`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.H`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.S`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.c`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.claim`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.constant_H`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.constant_S`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.cosh_identity`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.deriv`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.derivative_H`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.evenSequence`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.even_sequence_coefficient`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.even_sequence_period`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.initial`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.log_derivative`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.result`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.s`
- Dependency: [D5/S1/Recurrence/Algebraic/SchroderIntegralEGF](../Algebraic/SchroderIntegralEGF.md)
- Dependency: [D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod](AutonomousDerivationTotientSquarePeriod.md)
- Dependency: [D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod](BalaA281180TotientSquarePeriod.md)
- Dependency: [D5/S1/Recurrence/Residue/IntegralEGFComposition](../Residue/IntegralEGFComposition.md)
- Dependency: [D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence](../Residue/ParametricExponentialSquareCongruence.md)
