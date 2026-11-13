# Integral Derivations and Prime-Power Periods

## Abstract

Totient-square periods of integral derivation coefficients.

**Theorem 1.1 (iterate leibniz).**

$$\forall (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module R A] (d : Derivation R A A) (n : \mathbb{N}) (f g : A) , \operatorname{Nat}.\operatorname{iterate} d n (f \cdot g) = \operatorname{Finset}.\operatorname{sum} (\operatorname{Finset}.\operatorname{range} (n + 1)) (fun k \mapsto \operatorname{SMul}.\operatorname{smul} (\operatorname{Nat}.\operatorname{choose} n k) ((\operatorname{Nat}.\operatorname{iterate} d (n - k) f) \cdot (\operatorname{Nat}.\operatorname{iterate} d k g)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.iterate_leibniz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Iterating a derivation distributes over products with binomial coefficients.

**Theorem 1.2 (root pow zero).**

$$\forall (R : Type) [CommRing R] (L : \mathbb{N}) , (\operatorname{AdjoinRoot}.\operatorname{root} (\operatorname{Polynomial}.\operatorname{X}^{L} : Polynomial R))^{L} = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.root_pow_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The root of X to the power L is nilpotent of exponent L.

**Definition 1.3 (jetDerivation).**

$$\forall (R : Type) [CommRing R] (L : \mathbb{N}) (hL : (L : R) = 0) (P : Polynomial R) , \operatorname{BalaJets}.\operatorname{jetDerivation} L hL P = \operatorname{Classical}.\operatorname{choose} (\operatorname{BalaJets}.\operatorname{existsJetDerivation} L hL P)$$

*Formalization.* `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.jetDerivation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose a quotient derivation with the action specified by existsJetDerivation.

**Theorem 1.4 (jetDerivation root).**

$$\forall (R : Type) [CommRing R] (L : \mathbb{N}) (hL : (L : R) = 0) (P : Polynomial R) , \operatorname{BalaJets}.\operatorname{jetDerivation} L hL P (\operatorname{AdjoinRoot}.\operatorname{root} (\operatorname{Polynomial}.\operatorname{X}^{L} : Polynomial R)) = \operatorname{AdjoinRoot}.\operatorname{mk} (\operatorname{Polynomial}.\operatorname{X}^{L} : Polynomial R) P$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.jetDerivation_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quotient derivation sends its coordinate to the polynomial P.

**Definition 1.5 (matrix).**

$$\forall (R : Type) [CommRing R] (L : \mathbb{N}) (P : Polynomial R) , \operatorname{BalaTruncated}.\operatorname{matrix} R L P = \operatorname{LinearMap}.\operatorname{toMatrixAlgEquiv} ' (\operatorname{BalaTruncated}.\operatorname{truncation} L (\operatorname{Derivation}.\operatorname{toLinearMap} (\operatorname{Polynomial}.\operatorname{mkDerivation} R P)))$$

*Formalization.* `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.matrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite derivation operator is represented in the standard coefficient basis.

**Theorem 1.6 (matrix natural).**

$$\forall (R S : Type) [CommRing R] [CommRing S] (f : RingHom R S) (L : \mathbb{N}) (P : Polynomial R) , \operatorname{RingHom}.\operatorname{mapMatrix} f (\operatorname{BalaTruncated}.\operatorname{matrix} R L P) = \operatorname{BalaTruncated}.\operatorname{matrix} S L (\operatorname{Polynomial}.\operatorname{map} f P)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.matrix_natural` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Changing coefficients commutes with forming the truncated derivation matrix.

**Theorem 1.7 (integer matrix totient square).**

$$\forall (p : \mathbb{N}) [Fact (\operatorname{Nat}.\operatorname{Prime} p)] (P : Polynomial \mathbb{Z}) , \operatorname{Polynomial}.\operatorname{coeff} P 0 = 1 \implies \forall (s : \mathbb{N}) , (p : Matrix (Fin (p^{s + 1})) (Fin (p^{s + 1})) \mathbb{Z})^{s + 1} \mid (\operatorname{BalaTruncated}.\operatorname{matrix} \mathbb{Z} (p^{s + 1}) P)^{p^{2 \cdot s + 1}} \cdot ((\operatorname{BalaTruncated}.\operatorname{matrix} \mathbb{Z} (p^{s + 1}) P)^{(\operatorname{Nat}.\operatorname{totient} (p^{s + 1}))^{2}} - 1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.integer_matrix_totient_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The characteristic-p filtration and integral matrix lift give the prescribed totient-square annihilator at each prime power.

**Theorem 1.8 (jet annihilator of matrix).**

$$\forall (R : Type) [CommRing R] (L : \mathbb{N}) (hL : (L : R) = 0) (P : Polynomial R) (u t : \mathbb{N}) , (\operatorname{BalaTruncated}.\operatorname{matrix} R L P)^{u} \cdot ((\operatorname{BalaTruncated}.\operatorname{matrix} R L P)^{t} - 1) = 0 \implies \forall (f : Polynomial R) , \operatorname{Nat}.\operatorname{iterate} (\operatorname{BalaJets}.\operatorname{jetDerivation} L hL P) u ((\operatorname{Nat}.\operatorname{iterate} (\operatorname{BalaJets}.\operatorname{jetDerivation} L hL P) t (\operatorname{AdjoinRoot}.\operatorname{mk} (\operatorname{Polynomial}.\operatorname{X}^{L} : Polynomial R) f)) - (\operatorname{AdjoinRoot}.\operatorname{mk} (\operatorname{Polynomial}.\operatorname{X}^{L} : Polynomial R) f)) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.jet_annihilator_of_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A matrix annihilator transfers to every element of the truncated polynomial ring.

**Theorem 1.9 (prime power derivative period).**

$$\forall (p : \mathbb{N}) [Fact (\operatorname{Nat}.\operatorname{Prime} p)] (P : Polynomial \mathbb{Z}) , \operatorname{Polynomial}.\operatorname{coeff} P 0 = 1 \implies \forall (s : \mathbb{N}) (f : Polynomial \mathbb{Z}) (m : \mathbb{N}) , p^{2 \cdot s + 1} \le m \implies \operatorname{Int}.\operatorname{ModEq} ((p^{s + 1} : \mathbb{N}) : \mathbb{Z}) (\operatorname{Polynomial}.\operatorname{coeff} (\operatorname{Nat}.\operatorname{iterate} (\operatorname{Polynomial}.\operatorname{mkDerivation} \mathbb{Z} P) (m + (\operatorname{Nat}.\operatorname{totient} (p^{s + 1}))^{2}) f) 0) (\operatorname{Polynomial}.\operatorname{coeff} (\operatorname{Nat}.\operatorname{iterate} (\operatorname{Polynomial}.\operatorname{mkDerivation} \mathbb{Z} P) m f) 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.prime_power_derivative_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every integral polynomial observable has the stated derivative-index period after the explicit prime-power threshold.

**Theorem 1.10 (square root in finite jet).**

$$\forall (R : Type) [CommRing R] (p : \mathbb{N}) , \operatorname{Nat}.\operatorname{Prime} p \implies p \neq 2 \implies \forall (s : \mathbb{N}) , (p : R)^{s + 1} = 0 \implies \forall (x : R) , x^{p^{s + 1}} = 0 \implies \exists (b : R) , b^{2} = 1 + x \land (\exists (m : \mathbb{N}) , b = (1 + x)^{m})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.square_root_in_finite_jet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an odd prime, a suitable power of one plus a nilpotent is its square root.

**Definition 1.11 (truncation).**

$$\forall (R : Type) [CommRing R] (L : \mathbb{N}) (F : \operatorname{Module}.\operatorname{End} R (Polynomial R)) , \operatorname{BalaTruncated}.\operatorname{truncation} L F = \operatorname{LinearMap}.\operatorname{comp} (\operatorname{Polynomial}.\operatorname{toFn} L) (\operatorname{LinearMap}.\operatorname{comp} F (\operatorname{Polynomial}.\operatorname{ofFn} L))$$

*Formalization.* `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.truncation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A polynomial linear operator acts on the finite coefficient space by encoding and decoding.

**Theorem 1.12 (decode zero iff).**

$$\forall (R : Type) [CommRing R] (L : \mathbb{N}) (f : Polynomial R) , \operatorname{Polynomial}.\operatorname{toFn} L f = 0 \iff \operatorname{Polynomial}.\operatorname{X}^{L} \mid f$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.decode_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Vanishing of the first L coefficients is divisibility by X to the power L.

**Theorem 1.13 (decode semiconj).**

$$\forall (R : Type) [CommRing R] (L : \mathbb{N}) (F : \operatorname{Module}.\operatorname{End} R (Polynomial R)) , (\forall (f : Polynomial R) , \operatorname{Polynomial}.\operatorname{X}^{L} \mid f \implies \operatorname{Polynomial}.\operatorname{X}^{L} \mid F f) \implies \operatorname{Function}.\operatorname{Semiconj} (\operatorname{Polynomial}.\operatorname{toFn} L) F (\operatorname{BalaTruncated}.\operatorname{truncation} L F)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.decode_semiconj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An operator preserving the truncation ideal commutes with coefficient truncation.

**Definition 1.14 (secondOrder).**

$$\forall (R : Type) [CommRing R] (a b : Polynomial R) , \operatorname{BalaLinearTruncation}.\operatorname{secondOrder} a b = \operatorname{LinearMap}.\operatorname{comp} (\operatorname{LinearMap}.\operatorname{mulLeft} R a) ((\operatorname{Polynomial}.\operatorname{derivative} : \operatorname{Module}.\operatorname{End} R (Polynomial R))^{2}) + \operatorname{LinearMap}.\operatorname{comp} (\operatorname{LinearMap}.\operatorname{mulLeft} R b) \operatorname{Polynomial}.\operatorname{derivative}$$

*Formalization.* `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.secondOrder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the linear operator a times the second derivative plus b times the first derivative.

**Theorem 1.15 (secondOrder apply).**

$$\forall (R : Type) [CommRing R] (a b f : Polynomial R) , \operatorname{BalaLinearTruncation}.\operatorname{secondOrder} a b f = a \cdot (\operatorname{Polynomial}.\operatorname{derivative} (\operatorname{Polynomial}.\operatorname{derivative} f)) + b \cdot (\operatorname{Polynomial}.\operatorname{derivative} f)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.secondOrder_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluation of the second-order operator gives its two differential terms.

**Theorem 1.16 (secondOrder stable).**

$$\forall (R : Type) [CommRing R] (L : \mathbb{N}) , (L : R) = 0 \implies \forall (a b f : Polynomial R) , \operatorname{Polynomial}.\operatorname{X}^{L} \mid f \implies \operatorname{Polynomial}.\operatorname{X}^{L} \mid \operatorname{BalaLinearTruncation}.\operatorname{secondOrder} a b f$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.secondOrder_stable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the scalar L vanishes, both derivatives preserve the ideal generated by X to the power L.

**Definition 1.17 (secondOrderMatrix).**

$$\forall (R : Type) [CommRing R] (L : \mathbb{N}) (a b : Polynomial R) , \operatorname{BalaSecondOrderMatrix}.\operatorname{secondOrderMatrix} R L a b = \operatorname{LinearMap}.\operatorname{toMatrixAlgEquiv} ' (\operatorname{BalaTruncated}.\operatorname{truncation} L (\operatorname{BalaLinearTruncation}.\operatorname{secondOrder} a b))$$

*Formalization.* `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.secondOrderMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Represent the truncated second-order operator in the standard coefficient basis.

**Theorem 1.18 (secondOrderMatrix natural).**

$$\forall (R S : Type) [CommRing R] [CommRing S] (f : RingHom R S) (L : \mathbb{N}) (a b : Polynomial R) , \operatorname{RingHom}.\operatorname{mapMatrix} f (\operatorname{BalaSecondOrderMatrix}.\operatorname{secondOrderMatrix} R L a b) = \operatorname{BalaSecondOrderMatrix}.\operatorname{secondOrderMatrix} S L (\operatorname{Polynomial}.\operatorname{map} f a) (\operatorname{Polynomial}.\operatorname{map} f b)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.secondOrderMatrix_natural` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second-order matrix also commutes with changing coefficients.

**Theorem 1.19 (integral annihilator).**

$$\forall (a b : Polynomial \mathbb{Z}) , \operatorname{Polynomial}.\operatorname{coeff} b 0 = 1 \implies \forall (s : \mathbb{N}) , (2 : Matrix (Fin (2^{s + 1})) (Fin (2^{s + 1})) \mathbb{Z})^{s + 1} \mid (\operatorname{BalaSecondOrderMatrix}.\operatorname{secondOrderMatrix} \mathbb{Z} (2^{s + 1}) a b)^{2^{2 \cdot s + 1}} \cdot ((\operatorname{BalaSecondOrderMatrix}.\operatorname{secondOrderMatrix} \mathbb{Z} (2^{s + 1}) a b)^{(\operatorname{Nat}.\operatorname{totient} (2^{s + 1}))^{2}} - 1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.integral_annihilator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In characteristic two the second derivative vanishes; the first-order matrix theorem and integral lift then supply this annihilator.

**Theorem 1.20 (existsJetDerivation).**

$$\forall (R : Type) [CommRing R] (L : \mathbb{N}) , (L : R) = 0 \implies \forall (P : Polynomial R) , \exists (d : Derivation R (AdjoinRoot (\operatorname{Polynomial}.\operatorname{X}^{L} : Polynomial R)) (AdjoinRoot (\operatorname{Polynomial}.\operatorname{X}^{L} : Polynomial R))) , \forall (f : Polynomial R) , d (\operatorname{AdjoinRoot}.\operatorname{mk} (\operatorname{Polynomial}.\operatorname{X}^{L} : Polynomial R) f) = \operatorname{AdjoinRoot}.\operatorname{mk} (\operatorname{Polynomial}.\operatorname{X}^{L} : Polynomial R) ((\operatorname{Polynomial}.\operatorname{derivative} f) \cdot P)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.existsJetDerivation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polynomial derivation preserves the quotient ideal and therefore induces a derivation with the displayed action on every polynomial class.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.decode_semiconj`
- Truth anchor: `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.decode_zero_iff`
- Truth anchor: `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.existsJetDerivation`
- Truth anchor: `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.integer_matrix_totient_square`
- Truth anchor: `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.integral_annihilator`
- Truth anchor: `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.iterate_leibniz`
- Truth anchor: `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.jetDerivation`
- Truth anchor: `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.jetDerivation_root`
- Truth anchor: `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.jet_annihilator_of_matrix`
- Truth anchor: `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.matrix`
- Truth anchor: `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.matrix_natural`
- Truth anchor: `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.prime_power_derivative_period`
- Truth anchor: `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.root_pow_zero`
- Truth anchor: `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.secondOrder`
- Truth anchor: `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.secondOrderMatrix`
- Truth anchor: `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.secondOrderMatrix_natural`
- Truth anchor: `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.secondOrder_apply`
- Truth anchor: `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.secondOrder_stable`
- Truth anchor: `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.square_root_in_finite_jet`
- Truth anchor: `D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod.truncation`
