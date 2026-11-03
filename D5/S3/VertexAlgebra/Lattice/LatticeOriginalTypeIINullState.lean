/- GID: D5/S3/VertexAlgebra/Lattice/LatticeOriginalTypeIINullState
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeOriginalTypeIINullState
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original Type II physical null state and finite Fock coefficient obstruction. -/

import D5.S3.VertexAlgebra.LatticeSugawaraConformal
import D5.S3.VertexAlgebra.SourceBPZ.OriginalMatterHermitian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeOriginalTypeIINullState

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeSugawaraVirasoro LatticeSugawaraConformal
open SourceBPZ.OriginalMatterHermitian MvPolynomial
open scoped BigOperators

noncomputable section

private theorem coeff_linear_mul_X (D : LatticeData) (x y : Index D)
    (P : Oscillator D) :
    coeff (Finsupp.single x 1) (P * X y) = if x = y then coeff 0 P else 0 := by
  classical
  by_cases h : x = y
  · subst y; simp [coeff_mul_X']
  · simp [coeff_mul_X', h, Ne.symm h]

private theorem coeff_zero_derivation (D : LatticeData) (P : Oscillator D) :
    coeff 0 (oscillatorDerivation D P) = 0 := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [oscillatorDerivation]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P x hP =>
    simp [Derivation.leibniz, oscillatorDerivation, MvPolynomial.mkDerivation_X,
      ← constantCoeff_eq, hP]

private theorem coeff_derivation_two (D : LatticeData) (i : Fin D.rank)
    (P : Oscillator D) :
    coeff (Finsupp.single (i, 1) 1) (oscillatorDerivation D P) =
      coeff (Finsupp.single (i, 0) 1) P := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [oscillatorDerivation]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P x hP =>
    rcases x with ⟨j,k⟩
    rw [Derivation.leibniz]
    simp only [oscillatorDerivation, MvPolynomial.mkDerivation_X]
    rw [smul_eq_mul, mul_comm (X (j,k))]
    simp only [coeff_add, mul_smul_comm, coeff_smul, coeff_linear_mul_X,
      coeff_zero_derivation]
    by_cases h : k = 0
    · subst k; simp
    · simp [h, show k + 1 ≠ 1 by omega]

private def ell (D : LatticeData) (p : Charge D) (x : Carrier D) : ℂ :=
  ∑ i : Fin D.rank, (∑ j : Fin D.rank, (D.G i j : ℂ) * (p j : ℂ)) *
    coeff (Finsupp.single (i, 1) 1) (x p)

private theorem charge_scalar (D : LatticeData) (p : Charge D) (i : Fin D.rank) :
    chargeScalar D p i = ∑ j : Fin D.rank, (D.G i j : ℂ) * (p j : ℂ) := by
  simp [chargeScalar, bilinear, unitCharge, Int.cast_sum]

private theorem ell_translation_single (D : LatticeData) (p q : Charge D)
    (P : Oscillator D) :
    ell D p (translation D (Finsupp.single q P)) =
      if q = p then ∑ i : Fin D.rank, chargeScalar D p i *
        coeff (Finsupp.single (i,0) 1) P else 0 := by
  classical
  by_cases h : q = p
  · subst q
    simp only [translation_single, ell, Finsupp.single_eq_same, coeff_add]
    have hc (i : Fin D.rank) : coeff (Finsupp.single (i,1) 1)
        (chargePolynomial D p * P) = 0 := by
      simp [chargePolynomial, Finset.sum_mul, mul_comm _ P, coeff_linear_mul_X]
    simp_rw [hc, add_zero, coeff_derivation_two, ← charge_scalar]
    simp
  · simp [translation_single, ell, Finsupp.single_eq_of_ne h]

private theorem mode_mul_X (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (m : ℤ) (i : Fin D.rank) (k : ℕ) (P : Oscillator D) :
    sectorSugawaraMode D H p m (P * X (i,k)) =
      X (i,k) * sectorSugawaraMode D H p m P +
        ((k+1 : ℕ) : ℂ) • neutralPolynomialMode D i p (m - (k+1 : ℕ)) P := by
  have h := congrArg (fun A : Module.End ℂ (Carrier D) =>
      (A (Finsupp.single p P)) p)
    (sugawaraMode_current_commutator D H hHG hGH i m (-((k+1 : ℕ) : ℤ)))
  have hn : neutralPolynomialMode D i p (-((k+1 : ℕ) : ℤ)) =
      LinearMap.mulLeft ℂ (X (i,k)) := by
    simp [neutralPolynomialMode, show -((k+1 : ℕ) : ℤ) < 0 by omega]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, neutralMode_single,
    sugawaraMode_single_sector, LinearMap.smul_apply, Finsupp.sub_apply,
    Finsupp.single_eq_same, Finsupp.smul_apply, hn, LinearMap.mulLeft_apply] at h
  rw [mul_comm P]
  apply sub_eq_iff_eq_add.mp at h
  convert h using 1 <;> push_cast <;> ring

private theorem coeff_mode_one (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (P : Oscillator D) :
    coeff 0 (sectorSugawaraMode D H p 1 P) =
      ∑ i : Fin D.rank, chargeScalar D p i * coeff (Finsupp.single (i,0) 1) P := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    have hg := sugawaraMode_ground_positive D H p 1 (by omega)
    have hc : Finsupp.single p (C c : Oscillator D) =
        c • Finsupp.single p (1 : Oscillator D) := by simp [← C_mul']
    have hz := congrArg (fun x : Carrier D => x p) (show
        sugawaraMode D H 1 (Finsupp.single p (C c)) = 0 by rw [hc, map_smul, hg, smul_zero])
    simpa [sugawaraMode_single_sector] using hz
  | add P Q hP hQ =>
    simp [hP, hQ, Finset.sum_add_distrib, mul_add]
  | mul_X P x hP =>
    rcases x with ⟨j,k⟩
    rw [mode_mul_X D H hHG hGH]
    simp only [coeff_add, ← constantCoeff_eq, map_mul, constantCoeff_X, zero_mul,
      zero_add, coeff_smul]
    cases k with
    | zero =>
      simp [neutralPolynomialMode, chargeScalar, coeff_linear_mul_X,
        constantCoeff_eq, eq_comm]
    | succ k =>
      have hn : (1 : ℤ) - ((k+1+1 : ℕ) : ℤ) < 0 := by omega
      simp [neutralPolynomialMode, hn, coeff_linear_mul_X, constantCoeff_eq]


private theorem ell_translation (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (u : Carrier D) :
    ell D p (translation D u) = coeff 0 ((sugawaraMode D H 1 u) p) := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp [ell]
  | add x y hx hy =>
    simpa [ell, mul_add, Finset.sum_add_distrib] using congrArg₂ (· + ·) hx hy
  | single q P =>
    rw [ell_translation_single, sugawaraMode_single_sector]
    by_cases h : q = p
    · subst q; simp [coeff_mode_one D H hHG hGH]
    · simp [h, Finsupp.single_eq_of_ne h]

private theorem current_two_constant (D : LatticeData) (p : Charge D)
    (i : Fin D.rank) (P : Oscillator D) :
    coeff 0 (neutralPolynomialMode D i p 2 P) =
      2 * ∑ j : Fin D.rank, (D.G i j : ℂ) * coeff (Finsupp.single (j,1) 1) P := by
  simp [neutralPolynomialMode, coeff_pderiv]

private theorem current_two_extracts_ell (D : LatticeData) (p : Charge D)
    (P : Oscillator D) :
    ∑ i : Fin D.rank, (p i : ℂ) * coeff 0 (neutralPolynomialMode D i p 2 P) =
      2 * ell D p (Finsupp.single p P) := by
  classical
  simp only [current_two_constant, ell, Finsupp.single_eq_same, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [D.symmetric j i]
  ring

private theorem charge_norm (D : LatticeData) (p : Charge D) :
    ∑ i : Fin D.rank, (p i : ℂ) * chargeScalar D p i = (bilinear D p p : ℂ) := by
  simp only [charge_scalar, bilinear, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem ell_minus_two (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) :
    ell D p (sugawaraMode D H (-2) (Finsupp.single p 1)) = (bilinear D p p : ℂ) := by
  classical
  have hc (i : Fin D.rank) :
      coeff 0 (neutralPolynomialMode D i p 2 (sectorSugawaraMode D H p (-2) 1)) =
        2 * chargeScalar D p i := by
    have h := congrArg (fun A : Module.End ℂ (Carrier D) =>
      coeff 0 ((A (Finsupp.single p 1)) p))
      (sugawaraMode_current_commutator D H hHG hGH i (-2) 2)
    have hz : neutralMode D i 2 (Finsupp.single p (1 : Oscillator D)) = 0 := by
      simp [neutralPolynomialMode]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hz, map_zero,
      sugawaraMode_single_sector, neutralMode_single, Finsupp.sub_apply,
      Finsupp.zero_apply, Finsupp.single_eq_same, coeff_sub, coeff_zero,
      LinearMap.smul_apply, Finsupp.smul_apply, coeff_smul] at h
    norm_num [neutralPolynomialMode, chargeScalar] at h ⊢
    linear_combination -h
  rw [sugawaraMode_single_sector]
  have he := current_two_extracts_ell D p (sectorSugawaraMode D H p (-2) 1)
  simp_rw [hc, ← mul_assoc, mul_comm (p _ : ℂ) 2] at he
  rw [← Finset.mul_sum, charge_norm] at he
  linear_combination -he / 2

private theorem ell_translation_squared (D : LatticeData) (p : Charge D) :
    ell D p (translation D (translation D (Finsupp.single p 1))) =
      (bilinear D p p : ℂ) := by
  classical
  simp only [translation_single, map_one, zero_add, mul_one]
  rw [ell_translation_single]
  simp only [ite_true]
  have hc (i : Fin D.rank) : coeff (Finsupp.single (i,0) 1) (chargePolynomial D p) =
      (p i : ℂ) := by simp [chargePolynomial, coeff_X', eq_comm]
  simp_rw [hc, mul_comm (chargeScalar D p _) (p _ : ℂ)]
  exact charge_norm D p

/-- The literal original Type II vector, with its original charge and oscillator carrier. -/
def typeII (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (p : Charge D) : Carrier D :=
  sugawaraMode D H (-2) (Finsupp.single p 1) +
    (3/2 : ℂ) • translation D (translation D (Finsupp.single p 1))

private theorem ell_typeII (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (hp : bilinear D p p = -2) :
    ell D p (typeII D H p) = -5 := by
  have ha (x y : Carrier D) : ell D p (x+y) = ell D p x + ell D p y := by
    simp [ell, mul_add, Finset.sum_add_distrib]
  have hs (c : ℂ) (x : Carrier D) : ell D p (c • x) = c * ell D p x := by
    simp [ell, Finset.mul_sum, mul_left_comm, mul_assoc]
  rw [typeII, ha, hs, ell_minus_two D H hHG hGH, ell_translation_squared, hp]
  norm_num


private theorem typeII_primary (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hr : D.rank = 26) (p : Charge D) (hp : bilinear D p p = -2) :
    sugawaraMode D H 0 (typeII D H p) = typeII D H p ∧
      ∀ n : ℤ, 0 < n → sugawaraMode D H n (typeII D H p) = 0 := by
  let L := sugawaraMode D H
  let v : Carrier D := Finsupp.single p 1
  have ground (m : ℤ) (hm : 0 < m) : L m v = 0 :=
    sugawaraMode_ground_positive D H p m hm
  have weight : L 0 v = (-1 : ℂ) • v := by
    dsimp [L,v]
    rw [sugawaraMode_ground_zero, chargeQuadratic_eq D H hHG hGH, hp]
    norm_num
  have comm (m n : ℤ) (x : Carrier D) :
      L m (L n x) = L n (L m x) + ((m-n : ℤ) : ℂ) • L (m+n) x +
        (if m+n = 0 then (D.rank : ℂ)/12*((m : ℂ)^3-m) else 0) • x := by
    have h := congrArg (fun A : Module.End ℂ (Carrier D) => A x)
      (sugawaraMode_virasoro D H hHG hGH m n)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply] at h
    dsimp [L]
    rw [sub_eq_iff_eq_add] at h
    exact h.trans (by abel)
  have zero_one : L 0 (L (-1) v) = 0 := by
    rw [comm, weight]
    norm_num
  have zero_two : L 0 (L (-2) v) = L (-2) v := by
    rw [comm, weight]
    norm_num
  have zero_one_one : L 0 (L (-1) (L (-1) v)) = L (-1) (L (-1) v) := by
    rw [comm, zero_one]
    norm_num
  have one_one : L 1 (L (-1) v) = (-2 : ℂ) • v := by
    rw [comm, ground 1 (by omega), weight]
    norm_num
  have one_two : L 1 (L (-2) v) = (3 : ℂ) • L (-1) v := by
    rw [comm, ground 1 (by omega)]
    norm_num
  have one_one_one : L 1 (L (-1) (L (-1) v)) = (-2 : ℂ) • L (-1) v := by
    rw [comm, one_one, zero_one]
    norm_num
  have higher_one (n : ℤ) (hn : 1 < n) : L n (L (-1) v) = 0 := by
    rw [comm, ground n (by omega), ground (n + -1) (by omega)]
    simp [show n + -1 ≠ 0 by omega]
  have two_two : L 2 (L (-2) v) = (9 : ℂ) • v := by
    rw [comm, ground 2 (by omega), weight]
    norm_num [hr, ← add_smul]
  have two_one_one : L 2 (L (-1) (L (-1) v)) = (-6 : ℂ) • v := by
    rw [comm, higher_one 2 (by omega)]
    norm_num [one_one, smul_smul]
  have high_two (n : ℤ) (hn : 2 < n) : L n (L (-2) v) = 0 := by
    rw [comm, ground n (by omega), ground (n + -2) (by omega)]
    simp [show n + -2 ≠ 0 by omega]
  have high_one_one (n : ℤ) (hn : 2 < n) : L n (L (-1) (L (-1) v)) = 0 := by
    rw [comm, higher_one n (by omega), higher_one (n + -1) (by omega)]
    simp [show n + -1 ≠ 0 by omega]
  have hT := sugawaraMode_minus_one_eq_translation D H hHG hGH
  rw [typeII, ← hT]
  change L 0 (L (-2) v + (3/2 : ℂ) • L (-1) (L (-1) v)) = _ ∧ _
  constructor
  · simp [zero_two, zero_one_one]
  · intro n hn
    by_cases h1 : n = 1
    · subst n
      simp only [map_add, map_smul, one_two, one_one_one, smul_smul]
      rw [← add_smul]
      norm_num
    · by_cases h2 : n = 2
      · subst n
        simp only [map_add, map_smul, two_two, two_one_one, smul_smul]
        rw [← add_smul]
        norm_num
      · simp [high_two n (by omega), high_one_one n (by omega)]

/-- At rank 26 and norm -2, the original Type II state is a nonzero physical
null state outside the translation of even the kernel of L(1).
The image in the last clause is the literal original positive-primary weight-zero space. -/
theorem original_typeII_null_obstruction (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hr : D.rank = 26) (p : Charge D) (hp : bilinear D p p = -2) :
    sugawaraMode D H 0 (typeII D H p) = typeII D H p ∧
    (∀ n : ℤ, 0 < n → sugawaraMode D H n (typeII D H p) = 0) ∧
    (∀ w : Carrier D, (∀ n : ℤ, 0 < n → sugawaraMode D H n w = 0) →
      Hm (typeII D H p) w = 0) ∧
    typeII D H p ≠ 0 ∧
    (∀ u : Carrier D, sugawaraMode D H 1 u = 0 → translation D u ≠ typeII D H p) ∧
    typeII D H p ∉ (translation D) ''
      {u : Carrier D | sugawaraMode D H 0 u = 0 ∧
        ∀ n : ℤ, 0 < n → sugawaraMode D H n u = 0} := by
  have hprimary := typeII_primary D H hHG hGH hr p hp
  have hcoeff := ell_typeII D H hHG hGH p hp
  have hnonzero : typeII D H p ≠ 0 := by
    intro h
    rw [h] at hcoeff
    norm_num [ell] at hcoeff
  have hnot (u : Carrier D) (hu : sugawaraMode D H 1 u = 0) :
      translation D u ≠ typeII D H p := by
    intro h
    have hzero := ell_translation D H hHG hGH p u
    rw [hu, Finsupp.zero_apply, coeff_zero, h, hcoeff] at hzero
    norm_num at hzero
  refine ⟨hprimary.1, hprimary.2, ?_, hnonzero, hnot, ?_⟩
  · intro w hw
    rw [typeII, Hm_add_left, Hm_smul_left]
    have hT := sugawaraMode_minus_one_eq_translation D H hHG hGH
    rw [← hT, Hm_sugawaraMode H hHG hGH,
      Hm_sugawaraMode H hHG hGH, Hm_sugawaraMode H hHG hGH]
    norm_num [hw 2 (by omega), hw 1 (by omega)]
  · rintro ⟨u,hu,htu⟩
    exact hnot u (hu.2 1 (by omega)) htu

end
end D5.S3.VertexAlgebra.LatticeOriginalTypeIINullState
