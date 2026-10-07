/- GID: D5/S3/VertexAlgebra/LatticeAllStateField
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeAllStateField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual fields of every lattice state are creative and translation covariant. -/

import D5.S3.VertexAlgebra.LatticeSugawaraConformal
import D5.S3.VertexAlgebra.FieldNormalProduct
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Sort
import Mathlib.RingTheory.MvPolynomial.Basic

/-
Actual all-charge, all-oscillator state-field construction.

Carrier: (Fin D.rank → ℤ) →₀ MvPolynomial (Fin D.rank × ℕ) ℂ.
No positivity, nondegeneracy, unimodularity, or nonzero-rank premise.

References: Bakalov--Kac, math/0402315v1, §4.1 (actual fields and translation);
Matsuo--Nagatomo, hep-th/9706118v1, Theorem 5.4.1 (nested divided derivatives).
Proof organization adapts the private word-creation and binomial-covariance
arguments of PolynomialFockStateField at a9f81b99; no Fock theorem is transported.
The normal-product suppliers retain Carnahan/native adaptation attribution.
The concrete translation supplier is the terminal c73c0130 source precursor,
compiled locally as an input, not claimed as a standalone admitted result.
This file proves creation and covariance, not all-state locality or Jacobi.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeAllStateField

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraConformal FieldNormalProduct MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

def vacuum (D : LatticeData) : Carrier D := Finsupp.single 0 1

/-- Every step is already an actual truncated vertex operator on the actual carrier. -/
def wordField (D : LatticeData) (δ : Charge D) :
    List (Index D) → VertexOperator ℂ (Carrier D)
  | [] => actualField D δ
  | x :: tail => (normalMinusOne (dividedDerivative x.2 (neutralField D x.1))
      (wordField D δ tail)).1

/-- A finite occurrence enumeration; its multiset is proved below. -/
def occurrences (D : LatticeData) (e : Index D →₀ ℕ) : List (Index D) :=
  e.toMultiset.toList

def polynomialField (D : LatticeData) (δ : Charge D) :
    Oscillator D →ₗ[ℂ] VertexOperator ℂ (Carrier D) :=
  (basisMonomials (Index D) ℂ).constr ℂ (fun e => wordField D δ (occurrences D e))

/-- The actual all-state linear map, with finite charge support. -/
def Y (D : LatticeData) : Carrier D →ₗ[ℂ] VertexOperator ℂ (Carrier D) :=
  Finsupp.lsum ℂ (polynomialField D)

@[simp] theorem Y_single (D : LatticeData) (δ : Charge D) (p : Oscillator D) :
    Y D (Finsupp.single δ p) = polynomialField D δ p := by
  simp [Y]

theorem polynomialField_monomial (D : LatticeData) (δ : Charge D)
    (e : Index D →₀ ℕ) :
    polynomialField D δ (monomial e 1) = wordField D δ (occurrences D e) :=
  (basisMonomials (Index D) ℂ).constr_basis ℂ _ e

theorem exponential_constant (D : LatticeData) (δ : Charge D) :
    PowerSeries.coeff 0 (creationExponential D δ) = 1 := by
  have hA : PowerSeries.constantCoeff (creationSeries D δ) = 0 := by
    simp [creationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [creationExponential, PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' hA), finsum_eq_single _ 0]
  · simp [PowerSeries.coeff_exp]
  · intro n hn
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hA]
    simp [zero_pow hn]

private theorem actual_vacuum_coeff (D : LatticeData) (δ : Charge D) (m : ℤ) :
    ((actualField D δ)[[m]]) (vacuum D) =
      Finsupp.single δ (creationCoeff D δ (-m - 1)) := by
  rw [actualField, VertexOperator.ncoeff_of_coeff]
  rw [vacuum, (actual_creation_coefficient_transport D δ δ).2.2.1]
  have hs : (1 : Polynomial (Oscillator D)).support = {0} := by
    simpa using Polynomial.support_C (show (1 : Oscillator D) ≠ 0 from one_ne_zero)
  simp [rawSingle, translatedPolynomial, hs, bilinear, epsilon, lowerCocycleExponent,
    paritySign]

private theorem actual_ground_creation (D : LatticeData) (δ : Charge D) :
    ((actualField D δ)[[-1]]) (vacuum D) = Finsupp.single δ 1 := by
  rw [actual_vacuum_coeff]
  simp [creationCoeff, exponential_constant]

private theorem actual_creativity (D : LatticeData) (δ : Charge D) (m : ℤ)
    (hm : 0 ≤ m) : ((actualField D δ)[[m]]) (vacuum D) = 0 := by
  rw [actual_vacuum_coeff]
  simp [creationCoeff, show -m - 1 < 0 by omega]

theorem neutral_modes (D : LatticeData) (i : Fin D.rank) (m : ℤ) :
    ((neutralField D i)[[m]]) = neutralMode D i m := by
  rw [neutralField, VertexOperator.ncoeff_of_coeff]
  rw [show -(-m - 1) - 1 = m by omega]

private theorem neutral_creativity (D : LatticeData) (i : Fin D.rank) (m : ℤ)
    (hm : 0 ≤ m) : neutralMode D i m (vacuum D) = 0 := by
  classical
  by_cases hz : m = 0
  · subst m
    simp [neutralMode, neutralPolynomialMode, vacuum, bilinear]
  · simp [neutralMode, neutralPolynomialMode, vacuum, not_lt.mpr hm, hz]

private theorem derivative_modes (D : LatticeData) (x : Index D) (m : ℤ) :
    ((dividedDerivative x.2 (neutralField D x.1))[[m]]) =
      ((Ring.choose (-m - 1 + x.2) x.2 : ℤ) : ℂ) • neutralMode D x.1 (m - x.2) := by
  apply LinearMap.ext
  intro v
  change Ring.choose (-m - 1 + x.2) x.2 •
    HVertexOperator.coeff (neutralField D x.1) (-m - 1 + x.2) v = _
  rw [VertexOperator.coeff_eq_ncoeff, neutral_modes]
  rw [show -(-m - 1 + x.2) - 1 = m - x.2 by omega]
  simp only [LinearMap.smul_apply, Int.cast_smul_eq_zsmul]

private theorem derivative_creativity (D : LatticeData) (x : Index D) (m : ℤ)
    (hm : 0 ≤ m) :
    ((dividedDerivative x.2 (neutralField D x.1))[[m]]) (vacuum D) = 0 := by
  rw [derivative_modes, LinearMap.smul_apply]
  by_cases h : (x.2 : ℤ) ≤ m
  · rw [neutral_creativity D x.1 (m - x.2) (by omega), smul_zero]
  · have hp : 0 ≤ -m - 1 + (x.2 : ℤ) := by omega
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hp
    have hs : n < x.2 := by omega
    rw [hn, Ring.choose_natCast, Nat.choose_eq_zero_of_lt hs]
    simp

private theorem derivative_creation (D : LatticeData) (x : Index D)
    (δ : Charge D) (p : Oscillator D) :
    ((dividedDerivative x.2 (neutralField D x.1))[[-1]]) (Finsupp.single δ p) =
      Finsupp.single δ (X x * p) := by
  rw [derivative_modes]
  have h : (-1 : ℤ) - x.2 = Int.negSucc x.2 := by omega
  simp [h, Ring.choose_natCast, neutralMode, neutralPolynomialMode]

/-- The pre-Y invariant is computed on the actual vacuum, by word induction. -/
theorem word_creation (D : LatticeData) (δ : Charge D) (w : List (Index D)) :
    ((wordField D δ w)[[-1]]) (vacuum D) =
      Finsupp.single δ (w.map (fun x => (X x : Oscillator D))).prod ∧
    ∀ m : ℤ, 0 ≤ m → ((wordField D δ w)[[m]]) (vacuum D) = 0 := by
  induction w with
  | nil => exact ⟨actual_ground_creation D δ, actual_creativity D δ⟩
  | cons x tail ih =>
    have coefficient (m : ℤ) :=
      (normalMinusOne (dividedDerivative x.2 (neutralField D x.1))
        (wordField D δ tail)).2 m (vacuum D)
    constructor
    · rw [wordField, coefficient]
      have secondZero : ∀ j : ℕ,
          ((wordField D δ tail)[[-1 - j - 1]])
            (((dividedDerivative x.2 (neutralField D x.1))[[j]]) (vacuum D)) = 0 := by
        intro j
        rw [derivative_creativity D x j (by omega), map_zero]
      simp only [secondZero, finsum_zero, add_zero]
      rw [finsum_eq_single _ 0]
      · simpa [ih.1] using derivative_creation D x δ
          (tail.map (fun x => (X x : Oscillator D))).prod
      · intro j hj
        rw [ih.2 (-1 + j) (by omega), map_zero]
    · intro m hm
      rw [wordField, coefficient]
      have firstZero : ∀ j : ℕ,
          ((dividedDerivative x.2 (neutralField D x.1))[[-(j : ℤ) - 1]])
            (((wordField D δ tail)[[m + j]]) (vacuum D)) = 0 := by
        intro j
        rw [ih.2 (m + j) (by omega), map_zero]
      have secondZero : ∀ j : ℕ,
          ((wordField D δ tail)[[m - j - 1]])
            (((dividedDerivative x.2 (neutralField D x.1))[[j]]) (vacuum D)) = 0 := by
        intro j
        rw [derivative_creativity D x j (by omega), map_zero]
      simp [firstZero, secondZero]

theorem occurrences_product (D : LatticeData) (e : Index D →₀ ℕ) :
    ((occurrences D e).map (fun x => (X x : Oscillator D))).prod = monomial e 1 := by
  rw [occurrences, Multiset.prod_map_toList]
  induction e using Finsupp.induction with
  | zero => simp
  | single_add x n tail absent nonzero ih =>
    rw [Finsupp.toMultiset_add, Multiset.map_add, Multiset.prod_add,
      Finsupp.toMultiset_single, Multiset.map_nsmul, Multiset.prod_nsmul,
      Multiset.map_singleton, Multiset.prod_singleton, ih, monomial_single_add]

private def evaluation (D : LatticeData) (m : ℤ) :
    VertexOperator ℂ (Carrier D) →ₗ[ℂ] Carrier D where
  toFun A := (A[[m]]) (vacuum D)
  map_add' A B := by simp
  map_smul' c A := by simp

private theorem polynomial_creation (D : LatticeData) (δ : Charge D) :
    (evaluation D (-1)).comp (polynomialField D δ) = Finsupp.lsingle δ := by
  apply (basisMonomials (Index D) ℂ).ext
  intro e
  change ((polynomialField D δ (monomial e 1))[[-1]]) (vacuum D) = _
  rw [polynomialField_monomial, (word_creation D δ (occurrences D e)).1,
    occurrences_product]
  rfl

private theorem polynomial_creativity (D : LatticeData) (δ : Charge D) (m : ℤ)
    (hm : 0 ≤ m) : (evaluation D m).comp (polynomialField D δ) = 0 := by
  apply (basisMonomials (Index D) ℂ).ext
  intro e
  change ((polynomialField D δ (monomial e 1))[[m]]) (vacuum D) = 0
  rw [polynomialField_monomial]
  exact (word_creation D δ (occurrences D e)).2 m hm

/-- Full-state creation on the actual charge-times-polynomial carrier. -/
theorem stateField_creation (D : LatticeData) (v : Carrier D) :
    ((Y D v)[[-1]]) (vacuum D) = v := by
  have h : (evaluation D (-1)).comp (Y D) = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro δ p
    change evaluation D (-1) (Y D (Finsupp.single δ p)) = Finsupp.single δ p
    rw [Y_single]
    exact congrArg (fun f : Oscillator D →ₗ[ℂ] Carrier D => f p)
      (polynomial_creation D δ)
  exact congrArg (fun f : Module.End ℂ (Carrier D) => f v) h

/-- All nonnegative modes annihilate the actual vacuum for every state. -/
theorem stateField_creativity (D : LatticeData) (v : Carrier D) (m : ℤ)
    (hm : 0 ≤ m) : ((Y D v)[[m]]) (vacuum D) = 0 := by
  have h : (evaluation D m).comp (Y D) = 0 := by
    apply Finsupp.lhom_ext
    intro δ p
    change evaluation D m (Y D (Finsupp.single δ p)) = 0
    rw [Y_single]
    exact congrArg (fun f : Oscillator D →ₗ[ℂ] Carrier D => f p)
      (polynomial_creativity D δ m hm)
  exact congrArg (fun f : Module.End ℂ (Carrier D) => f v) h

/-- Every integral-charge ground field is recovered, without a generating-subset premise. -/
theorem stateField_ground (D : LatticeData) (δ : Charge D) :
    Y D (Finsupp.single δ (1 : Oscillator D)) = actualField D δ := by
  rw [Y_single]
  have h := (basisMonomials (Index D) ℂ).constr_basis ℂ
    (fun e => wordField D δ (occurrences D e)) 0
  simpa [polynomialField, occurrences, wordField] using h

/-- The exact nested-field formula for each actual charge-monomial basis state. -/
theorem stateField_monomial (D : LatticeData) (δ : Charge D) (e : Index D →₀ ℕ) :
    Y D (Finsupp.single δ (monomial e 1)) = wordField D δ (occurrences D e) := by
  rw [Y_single, polynomialField_monomial]

/-- Explicit finite coefficient and finite charge extension of the nested-field formula. -/
theorem stateField_expansion (D : LatticeData) (v : Carrier D) :
    Y D v = ∑ δ ∈ v.support,
      ∑ e ∈ ((basisMonomials (Index D) ℂ).repr (v δ)).support,
        ((basisMonomials (Index D) ℂ).repr (v δ) e) •
          wordField D δ (occurrences D e) := by
  simp only [Y, Finsupp.lsum_apply, Finsupp.sum, polynomialField,
    Module.Basis.constr_apply]

private theorem binomial_shift (a : ℤ) (k : ℕ) :
    Ring.choose a k * (a - k) = a * Ring.choose (a - 1) k := by
  have h := Ring.choose_smul_choose a (n := k + 1) (k := k) (by omega)
  have h' := Ring.choose_smul_choose a (n := k + 1) (k := 1) (by omega)
  rw [Nat.choose_succ_self_right, Nat.add_sub_cancel_left, Ring.choose_one_right] at h
  rw [Nat.choose_one_right, Ring.choose_one_right, Nat.add_sub_cancel] at h'
  exact h.symm.trans h'

private theorem derivative_covariance (D : LatticeData) (x : Index D) (m : ℤ) :
    translation D * ((dividedDerivative x.2 (neutralField D x.1))[[m]]) -
      ((dividedDerivative x.2 (neutralField D x.1))[[m]]) * translation D =
        -(m : ℂ) • ((dividedDerivative x.2 (neutralField D x.1))[[m - 1]]) := by
  rw [derivative_modes, derivative_modes, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc]
  rw [← smul_sub (((Ring.choose (-m - 1 + x.2) x.2 : ℤ) : ℂ))
    (translation D * neutralMode D x.1 (m - x.2))
    (neutralMode D x.1 (m - x.2) * translation D),
    neutral_translation_covariance, smul_smul]
  rw [show m - x.2 - 1 = m - 1 - x.2 by omega, smul_smul]
  have h := congrArg (fun z : ℤ => (z : ℂ)) (binomial_shift (-m + x.2) x.2)
  push_cast at h
  rw [show -m + (x.2 : ℤ) - 1 = -m - 1 + x.2 by omega] at h
  rw [show -(m - 1) - 1 + (x.2 : ℤ) = -m + x.2 by omega]
  congr 1
  push_cast
  linear_combination -h

/-- Concrete translation covariance of every actual recursively constructed word. -/
theorem word_covariance (D : LatticeData) (δ : Charge D) (w : List (Index D))
    (m : ℤ) :
    translation D * ((wordField D δ w)[[m]]) -
      ((wordField D δ w)[[m]]) * translation D =
        -(m : ℂ) • ((wordField D δ w)[[m - 1]]) := by
  induction w generalizing m with
  | nil => exact actual_lattice_translation_covariance D δ m
  | cons x tail ih =>
    exact normalMinusOne_translation (translation D)
      (dividedDerivative x.2 (neutralField D x.1)) (wordField D δ tail)
      (derivative_covariance D x) ih m

private def covarianceDefect (D : LatticeData) (m : ℤ) :
    VertexOperator ℂ (Carrier D) →ₗ[ℂ] Module.End ℂ (Carrier D) where
  toFun A := translation D * (A[[m]]) - (A[[m]]) * translation D +
    (m : ℂ) • (A[[m - 1]])
  map_add' A B := by
    simp only [map_add, Pi.add_apply, mul_add, add_mul, smul_add]
    abel
  map_smul' c A := by
    simp only [map_smul, RingHom.id_apply, Pi.smul_apply, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, smul_add, smul_comm (m : ℂ) c]
    rw [smul_sub c (translation D * (A[[m]])) ((A[[m]]) * translation D)]

/-- All-state covariance, using the concrete actual translation rather than an assumption. -/
theorem stateField_covariance (D : LatticeData) (v : Carrier D) (m : ℤ) :
    translation D * ((Y D v)[[m]]) - ((Y D v)[[m]]) * translation D =
      -(m : ℂ) • ((Y D v)[[m - 1]]) := by
  have hp (δ : Charge D) : (covarianceDefect D m).comp (polynomialField D δ) = 0 := by
    apply (basisMonomials (Index D) ℂ).ext
    intro e
    change covarianceDefect D m (polynomialField D δ (monomial e 1)) = 0
    rw [polynomialField_monomial]
    change (translation D * ((wordField D δ (occurrences D e))[[m]]) -
      ((wordField D δ (occurrences D e))[[m]]) * translation D) +
        (m : ℂ) • ((wordField D δ (occurrences D e))[[m - 1]]) = 0
    rw [word_covariance]
    rw [neg_smul (m : ℂ) ((wordField D δ (occurrences D e))[[m - 1]])]
    exact neg_add_cancel _
  have h : (covarianceDefect D m).comp (Y D) = 0 := by
    apply Finsupp.lhom_ext
    intro δ p
    change covarianceDefect D m (Y D (Finsupp.single δ p)) = 0
    rw [Y_single]
    exact congrArg (fun f : Oscillator D →ₗ[ℂ] Module.End ℂ (Carrier D) => f p) (hp δ)
  have hv := congrArg (fun f : Carrier D →ₗ[ℂ] Module.End ℂ (Carrier D) => f v) h
  change (translation D * ((Y D v)[[m]]) - ((Y D v)[[m]]) * translation D) +
    (m : ℂ) • ((Y D v)[[m - 1]]) = 0 at hv
  exact (eq_neg_of_add_eq_zero_left hv).trans
    (neg_smul (m : ℂ) ((Y D v)[[m - 1]])).symm

theorem translation_kills_vacuum (D : LatticeData) : translation D (vacuum D) = 0 :=
  translation_vacuum D

theorem identity_modes (D : LatticeData) (m : ℤ) :
    ((identityField : VertexOperator ℂ (Carrier D))[[m]]) =
      if m = -1 then LinearMap.id else 0 := by
  rw [identityField, VertexOperator.ncoeff_of_coeff]
  simp only [show -m - 1 = 0 ↔ m = -1 by omega]

private theorem translated_zero (D : LatticeData) (p : Oscillator D) :
    translatedPolynomial D 0 p = Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [translatedPolynomial]
  | add p q hp hq =>
    simpa only [translatedPolynomial, map_add] using congrArg₂ (· + ·) hp hq
  | mul_X p x hp =>
    change translatedPolynomial D 0 (p * X x) = _
    simpa [translatedPolynomial, translationVariable, bilinear] using
      congrArg (fun q => q * Polynomial.C (X x)) hp

private theorem creationCoeff_zero (D : LatticeData) (t : ℤ) :
    creationCoeff D 0 t = if t = 0 then 1 else 0 := by
  have hs : creationSeries D 0 = 0 := by
    ext n
    simp [creationSeries]
  have he : creationExponential D 0 = 1 := by
    rw [creationExponential, hs, PowerSeries.subst_zero_eq_C_constantCoeff]
    simp
  by_cases h0 : t = 0
  · subst t
    simp [creationCoeff, he]
  · by_cases ht : t < 0
    · simp [creationCoeff, ht, h0]
    · simp [creationCoeff, ht, h0, he, show t.toNat ≠ 0 by omega]

theorem actual_zero (D : LatticeData) :
    actualField D 0 = (identityField : VertexOperator ℂ (Carrier D)) := by
  apply HVertexOperator.coeff_inj
  funext k
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
    actualField, VertexOperator.ncoeff_of_coeff, identityField,
    VertexOperator.ncoeff_of_coeff]
  rw [show -(-k - 1) - 1 = k by omega]
  apply Finsupp.lhom_ext
  intro δ p
  rw [(actual_creation_coefficient_transport D 0 0).2.2.1]
  by_cases hp : p = 0
  · subst p
    simp [rawSingle, translatedPolynomial]
  · have hs : (Polynomial.C p).support = {0} := Polynomial.support_C hp
    simp [rawSingle, translated_zero, hs, epsilon, lowerCocycleExponent, paritySign,
      bilinear, creationCoeff_zero]
    split_ifs <;> simp

theorem stateField_vacuum (D : LatticeData) :
    Y D (vacuum D) = (identityField : VertexOperator ℂ (Carrier D)) := by
  rw [vacuum, stateField_ground, actual_zero]

private theorem normal_right_identity (D : LatticeData)
    (A : VertexOperator ℂ (Carrier D)) : (normalMinusOne A identityField).1 = A := by
  apply HVertexOperator.coeff_inj
  funext power
  apply LinearMap.ext
  intro v
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
    (normalMinusOne A identityField).2]
  let m : ℤ := -power - 1
  change (∑ᶠ j : ℕ, (A[[-(j : ℤ) - 1]])
      (((identityField : VertexOperator ℂ (Carrier D))[[m + j]]) v)) +
    (∑ᶠ j : ℕ, ((identityField : VertexOperator ℂ (Carrier D))[[m - j - 1]])
      ((A[[j]]) v)) = (A[[m]]) v
  by_cases hm : 0 ≤ m
  · have hz : ∀ j : ℕ, (A[[-(j : ℤ) - 1]])
        (((identityField : VertexOperator ℂ (Carrier D))[[m + j]]) v) = 0 := by
      intro j
      simp [identity_modes, show m + j ≠ -1 by omega]
    simp only [hz, finsum_zero, zero_add]
    rw [finsum_eq_single _ m.toNat]
    · simp [identity_modes, Int.toNat_of_nonneg hm]
    · intro j hj
      simp [identity_modes, show m - (j : ℤ) - 1 ≠ -1 by omega]
  · have hz : ∀ j : ℕ,
        ((identityField : VertexOperator ℂ (Carrier D))[[m - j - 1]])
          ((A[[j]]) v) = 0 := by
      intro j
      simp [identity_modes, show m - j - 1 ≠ -1 by omega]
    simp only [hz, finsum_zero, add_zero]
    rw [finsum_eq_single _ (-m - 1).toNat]
    · rw [identity_modes, Int.toNat_of_nonneg (by omega : 0 ≤ -m - 1),
        if_pos (by omega)]
      simp only [LinearMap.id_apply]
      rw [show -(-m - 1) - 1 = m by omega]
    · intro j hj
      simp [identity_modes, show m + (j : ℤ) ≠ -1 by omega]

private theorem derivative_zero (D : LatticeData)
    (A : VertexOperator ℂ (Carrier D)) : dividedDerivative 0 A = A := by
  apply VertexOperator.ext
  intro v
  simp [dividedDerivative]

/-- The actual neutral current is recovered at its actual vacuum state. -/
theorem stateField_current (D : LatticeData) (i : Fin D.rank) :
    Y D (((neutralField D i)[[-1]]) (vacuum D)) = neutralField D i := by
  have hs : ((neutralField D i)[[-1]]) (vacuum D) =
      Finsupp.single (0 : Charge D) (X (i, 0) : Oscillator D) := by
    rw [neutral_modes]
    simp [neutralMode, neutralPolynomialMode, vacuum]
  rw [hs, X, stateField_monomial]
  simp only [occurrences, Finsupp.toMultiset_single, one_nsmul,
    Multiset.toList_singleton, wordField]
  rw [actual_zero, derivative_zero, normal_right_identity]

end
end D5.S3.VertexAlgebra.LatticeAllStateField
