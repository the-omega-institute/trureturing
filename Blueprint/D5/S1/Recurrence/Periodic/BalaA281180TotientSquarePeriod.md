# Bala A281180 Totient-Square Period

## Abstract

Totient-square periods of integral derivation coefficients.

**Definition 1.1 (flow).**

$$\forall (A : Type) [CommRing A] [Algebra \mathbb{Z} A] (d : Derivation \mathbb{Z} A A) (\varepsilon : RingHom A \mathbb{Z}) (f : A) , \operatorname{BalaFlow}.\operatorname{flow} d \varepsilon f = \operatorname{D5}.\operatorname{S1}.\operatorname{Recurrence}.\operatorname{Residue}.\operatorname{QuarticEGFFixedPoint}.\operatorname{encode} (fun n : \mathbb{N} \mapsto (\varepsilon (\operatorname{Nat}.\operatorname{iterate} d n f) : \mathbb{Q}))$$

*Formalization.* `D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod.flow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing factorial-scaled encoder sends the integer values of iterated derivations to a rational exponential generating series.

**Theorem 1.2 (eCoeff flow).**

$$\forall (A : Type) [CommRing A] [Algebra \mathbb{Z} A] (d : Derivation \mathbb{Z} A A) (\varepsilon : RingHom A \mathbb{Z}) (f : A) (n : \mathbb{N}) , eCoeff (\operatorname{BalaFlow}.\operatorname{flow} d \varepsilon f) n = (\varepsilon (\operatorname{Nat}.\operatorname{iterate} d n f) : \mathbb{Q})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod.eCoeff_flow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponential coefficient of the flow is the corresponding integer derivative value.

**Theorem 1.3 (flow derivative).**

$$\forall (A : Type) [CommRing A] [Algebra \mathbb{Z} A] (d : Derivation \mathbb{Z} A A) (\varepsilon : RingHom A \mathbb{Z}) (f : A) , \operatorname{PowerSeries}.\operatorname{derivative} (\operatorname{BalaFlow}.\operatorname{flow} d \varepsilon f) = \operatorname{BalaFlow}.\operatorname{flow} d \varepsilon (d f)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod.flow_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiation shifts the iterated derivation by one.

**Definition 1.4 (flowMap).**

$$\forall (A : Type) [CommRing A] [Algebra \mathbb{Z} A] (d : Derivation \mathbb{Z} A A) (\varepsilon : RingHom A \mathbb{Z}) , \operatorname{BalaFlow}.\operatorname{flowMap} d \varepsilon = \operatorname{Classical}.\operatorname{choose} (\operatorname{BalaFlow}.\operatorname{existsFlowMap} d \varepsilon)$$

*Formalization.* `D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod.flowMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose the ring homomorphism with the derivation flow as its underlying function.

**Theorem 1.5 (constantCoeff flow).**

$$\forall (A : Type) [CommRing A] [Algebra \mathbb{Z} A] (d : Derivation \mathbb{Z} A A) (\varepsilon : RingHom A \mathbb{Z}) (f : A) , \operatorname{PowerSeries}.\operatorname{constantCoeff} (\operatorname{BalaFlow}.\operatorname{flow} d \varepsilon f) = (\varepsilon f : \mathbb{Q})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod.constantCoeff_flow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant coefficient is evaluation of the initial observable.

**Theorem 1.6 (flow of d eq zero).**

$$\forall (A : Type) [CommRing A] [Algebra \mathbb{Z} A] (d : Derivation \mathbb{Z} A A) (\varepsilon : RingHom A \mathbb{Z}) (f : A) , d f = 0 \implies \operatorname{BalaFlow}.\operatorname{flow} d \varepsilon f = \operatorname{PowerSeries}.\operatorname{C} (\varepsilon f : \mathbb{Q})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod.flow_of_d_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An invariant of the derivation gives a constant flow.

**Theorem 1.7 (prime power periods to all moduli).**

$$\forall (a : \mathbb{N} \to \mathbb{Z}) , (\forall (p r : \mathbb{N}) , \operatorname{Nat}.\operatorname{Prime} p \implies 0 < r \implies \forall (n : \mathbb{N}) , (p^{r})^{2} \le n \implies \operatorname{Int}.\operatorname{ModEq} ((p^{r} : \mathbb{N}) : \mathbb{Z}) (a (n + (\operatorname{Nat}.\operatorname{totient} (p^{r}))^{2})) (a n)) \implies \forall (k : \mathbb{N}) , 1 \le k \implies \exists (N : \mathbb{N}) , 1 \le N \land (\forall (n : \mathbb{N}) , N \le n \implies \operatorname{Int}.\operatorname{ModEq} (k : \mathbb{Z}) (a (n + (\operatorname{Nat}.\operatorname{totient} k)^{2})) (a n))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod.prime_power_periods_to_all_moduli` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Prime-power congruences combine into the specified period for every positive modulus, since totients respect divisibility.

**Definition 1.8 (claim).**

$$claim = (\exists S : PowerSeries \mathbb{Q} , \operatorname{PowerSeries}.\operatorname{constantCoeff} S = 0 \land \operatorname{PowerSeries}.\operatorname{derivative} S = (1 + S^{2})^{2} \land (\exists a : \mathbb{N} \to \mathbb{Z} , (\forall n : \mathbb{N} , 1 \le n \implies (a n : \mathbb{Q}) = eCoeff S (2 \cdot n - 1)) \land (\forall k : \mathbb{N} , 1 \le k \implies \exists N : \mathbb{N} , 1 \le N \land (\forall n : \mathbb{N} , N \le n \implies \operatorname{Int}.\operatorname{ModEq} (k : \mathbb{Z}) (a (n + (\operatorname{Nat}.\operatorname{totient} k)^{2})) (a n)))))$$

*Formalization.* `D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod.claim` (`✓ std3`).

*Citation.* Peter Bala (2026). *OEIS A281180 and its hyperbolic EGF family: totient-square periods*. URL: <https://oeis.org/A281180>.

*Commentary.*

a(n) = (2*n-1)! * [x^(2*n-1)] S(x), where S(x) = Integral (1 + S(x)^2)^2 dx. Conjecture: the sequence {a(n)} reduced modulo a positive integer k is eventually periodic with the period dividing phi(k)^2, where phi(n) = A000010(n). An example is given below. - _Peter Bala_, Feb 18 2026 The source is unpaginated. The primitive has constant coefficient zero, eCoeff is factorial times the ordinary coefficient, and all sequences take integer values. Natural subtraction is truncated subtraction.

**Theorem 1.9 (result).**

$$\exists S : PowerSeries \mathbb{Q} , \operatorname{PowerSeries}.\operatorname{constantCoeff} S = 0 \land \operatorname{PowerSeries}.\operatorname{derivative} S = (1 + S^{2})^{2} \land (\exists a : \mathbb{N} \to \mathbb{Z} , (\forall n : \mathbb{N} , 1 \le n \implies (a n : \mathbb{Q}) = eCoeff S (2 \cdot n - 1)) \land (\forall k : \mathbb{N} , 1 \le k \implies \exists N : \mathbb{N} , 1 \le N \land (\forall n : \mathbb{N} , N \le n \implies \operatorname{Int}.\operatorname{ModEq} (k : \mathbb{Z}) (a (n + (\operatorname{Nat}.\operatorname{totient} k)^{2})) (a n))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2026). *OEIS A281180 and its hyperbolic EGF family: totient-square periods*. URL: <https://oeis.org/A281180>.

*Commentary.*

The integral derivation flow supplies the series and its integer exponential coefficients. Prime-power operator annihilators give the prescribed shift, and divisibility assembles all positive moduli.

**Theorem 1.10 (existsFlowMap).**

$$\forall (A : Type) [CommRing A] [Algebra \mathbb{Z} A] (d : Derivation \mathbb{Z} A A) (\varepsilon : RingHom A \mathbb{Z}) , \exists (\varphi : RingHom A (PowerSeries \mathbb{Q})) , \forall (f : A) , \varphi f = \operatorname{BalaFlow}.\operatorname{flow} d \varepsilon f$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod.existsFlowMap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The iterated Leibniz rule makes the derivation flow multiplicative, and its zero, one and addition laws complete the ring homomorphism.

**Theorem 1.11 (flowMapApply).**

$$\forall (A : Type) [CommRing A] [Algebra \mathbb{Z} A] (d : Derivation \mathbb{Z} A A) (\varepsilon : RingHom A \mathbb{Z}) (f : A) , \operatorname{BalaFlow}.\operatorname{flowMap} d \varepsilon f = \operatorname{BalaFlow}.\operatorname{flow} d \varepsilon f$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod.flowMapApply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The chosen homomorphism evaluates to the derivation flow at every observable.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod.claim`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod.constantCoeff_flow`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod.eCoeff_flow`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod.existsFlowMap`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod.flow`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod.flowMap`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod.flowMapApply`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod.flow_derivative`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod.flow_of_d_eq_zero`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod.prime_power_periods_to_all_moduli`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod.result`
- Dependency: [D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod](AutonomousDerivationTotientSquarePeriod.md)
- Dependency: [D5/S1/Recurrence/Residue/IntegralEGFComposition](../Residue/IntegralEGFComposition.md)
- Dependency: [D5/S1/Recurrence/Residue/QuarticEGFFixedPoint](../Residue/QuarticEGFFixedPoint.md)
