/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddUpperRightSkew
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddUpperRightSkew
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The upper-branch odd-source opposite field and mixed BPZ matrix coefficients on the actual twisted carriers. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalMixedBPZ
import D5.S3.VertexAlgebra.TwistedGround.ActualPairingSymmetry
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Batteries.Tactic.OpenPrivate

/-!
The physical variable is the square of the Hahn coordinate. The upper half-turn
in the physical variable sends the Hahn coordinate to `I` times itself.
The opposite field is the product with the physical translation exponential,
as in Huang, hep-th/9406190v7, §3.4. Its coefficient indexed by `n` is at
doubled exponent `-2*n-3`.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator TensorProduct

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew

open LatticeGeneratingFieldLocality LatticeInvolution LatticePositiveEnergy
open LatticeHalfFock LatticeHalfFockCorrectedField LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockGradedTrace LatticeHalfFockParityT
open HalfFock.LatticeHalfFockParityField NativeOddTwistedIntertwiner
open ActualLeechHyperbolic (leechData)
open ActualChargedAdjoint ActualOddGradeOrthogonality
open private stress from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTranslation
open private raising actual_stress_transpose from
  D5.S3.VertexAlgebra.TwistedGround.MixedTranslation
open private T lowering_killed from
  D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private oddCurrent_grade_one groundBasis_energy from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner

/-- The fixed stress mode zero, restricted to the actual twisted parity. -/
def translation (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool) :
    Module.End ℂ (Twisted D hu s) :=
  (fixedParitySlice D hu (paritySign s) (stress D))[[0]]

private theorem translation_val (D : LatticeData) (hu : IsUnit D.G.det)
    (s : Bool) (u : Twisted D hu s) :
    (translation D hu s u).val = raising D hu u.val := by
  change (correctedField D hu
      (LatticeActualConformalState.omega D (HalfFockSpectralFiberSource.actualInverse D))).coeff
        (-2) u.val = _
  rw [LatticeHalfFockCorrectedConformal.correctedField_omega D hu _
    (HalfFockSpectralFiberSource.actualInverse_left D hu)]
  simp only [tensorStressField, HVertexOperator.coeff_of_coeff, stressCoeff,
    show (-2 : ℤ) % 2 = 0 by decide, ite_eq_left,
    show (-(-2 : ℤ)-4)/2 = -1 by decide, raising, tensorL]

/-- The contribution from translation order `ell`, where the native source
mode has physical exponent `-(n+ell)-3/2`. -/
def rightTerm (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool) (n : ℤ)
    (u : Twisted D hu s) (a : OddCarrier D) (ell : ℕ) : Twisted D hu (!s) :=
  (Complex.I ^ (-2 * (n + (ell : ℤ)) - 3) * (ell.factorial : ℂ)⁻¹) •
    (translation D hu (!s) ^ ell) (J D hu s (n + (ell : ℤ)) a u)

theorem rightTerm_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (s : Bool) (n : ℤ) (u : Twisted D hu s) (a : OddCarrier D) :
    Function.HasFiniteSupport (rightTerm D hu s n u a) := by
  classical
  obtain ⟨N, hN⟩ := J_truncation D hu s a u
  refine (Finset.range (N - n).toNat).finite_toSet.subset ?_
  intro ell hell
  by_contra hout
  have hbound : (N - n).toNat ≤ ell :=
    Nat.le_of_not_gt (fun h => hout (Finset.mem_range.mpr h))
  have hzero := hN (n + (ell : ℤ)) (by omega)
  exact hell (by simp only [rightTerm, hzero, map_zero, smul_zero])

/-- The actual coefficient of `exp(z L(-1)) Y^T(a, e^(πi) z) u`. -/
def R (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool) (n : ℤ) :
    Twisted D hu s →ₗ[ℂ] OddCarrier D →ₗ[ℂ] Twisted D hu (!s) where
  toFun u := {
    toFun a := ∑ᶠ ell : ℕ, rightTerm D hu s n u a ell
    map_add' a b := by
      simp only [rightTerm, map_add, LinearMap.add_apply, smul_add]
      exact finsum_add_distrib (rightTerm_finite D hu s n u a)
        (rightTerm_finite D hu s n u b)
    map_smul' c a := by
      simpa only [rightTerm, map_smul, LinearMap.smul_apply, RingHom.id_apply,
        smul_smul, mul_comm] using
        (smul_finsum c (rightTerm D hu s n u a)).symm }
  map_add' u v := by
    apply LinearMap.ext
    intro a
    change (∑ᶠ ell : ℕ, rightTerm D hu s n (u + v) a ell) =
      (∑ᶠ ell : ℕ, rightTerm D hu s n u a ell) +
        (∑ᶠ ell : ℕ, rightTerm D hu s n v a ell)
    simp only [rightTerm, map_add, smul_add]
    exact finsum_add_distrib (rightTerm_finite D hu s n u a)
      (rightTerm_finite D hu s n v a)
  map_smul' c u := by
    apply LinearMap.ext
    intro a
    change (∑ᶠ ell : ℕ, rightTerm D hu s n (c • u) a ell) =
      c • (∑ᶠ ell : ℕ, rightTerm D hu s n u a ell)
    simpa only [LinearMap.smul_apply, rightTerm, map_smul, RingHom.id_apply,
      smul_smul, mul_comm] using
      (smul_finsum c (rightTerm D hu s n u a)).symm

theorem R_truncation (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (u : Twisted D hu s) (a : OddCarrier D) :
    ∃ N : ℤ, ∀ n ≥ N, R D hu s n u a = 0 := by
  obtain ⟨N, hN⟩ := J_truncation D hu s a u
  refine ⟨N, fun n hn => ?_⟩
  change (∑ᶠ ell : ℕ, rightTerm D hu s n u a ell) = 0
  apply finsum_eq_zero_of_forall_eq_zero
  intro ell
  simp only [rightTerm, hN (n + (ell : ℤ)) (by omega), map_zero, smul_zero]

private def doubledCoefficient (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (u : Twisted D hu s) (e : ℤ) : OddCarrier D →ₗ[ℂ] Twisted D hu (!s) :=
  if Even e then 0 else R D hu s ((-e-3)/2) u

private theorem doubled_support (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (u : Twisted D hu s) (a : OddCarrier D) :
    (Function.support (fun e => doubledCoefficient D hu s u e a)).IsPWO := by
  obtain ⟨N, hN⟩ := R_truncation D hu s u a
  apply Set.isPWO_iff_isWF.mpr
  apply BddBelow.isWF
  refine ⟨-2*N-3, ?_⟩
  intro e he
  change -2*N-3 ≤ e
  by_contra h
  have hz := hN ((-e-3)/2) (by omega)
  exact he (by by_cases hEven : Even e <;> simp [doubledCoefficient, hEven, hz])

/-- The parity-changing opposite field in the doubled Hahn coordinate. -/
def rightField (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (u : Twisted D hu s) : HVertexOperator ℤ ℂ (OddCarrier D) (Twisted D hu (!s)) :=
  HVertexOperator.of_coeff (doubledCoefficient D hu s u) (doubled_support D hu s u)

theorem rightField_coeff (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (n : ℤ) (u : Twisted D hu s) (a : OddCarrier D) :
    (rightField D hu s u).coeff (-2*n-3) a = R D hu s n u a := by
  have he : ¬ Even (-2*n-3) := by
    rintro ⟨k, hk⟩
    omega
  simp only [rightField, HVertexOperator.coeff_of_coeff, doubledCoefficient, if_neg he,
    show (-(-2*n-3)-3)/2 = n by omega]

theorem rightField_even_zero (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (e : ℤ) (he : Even e) (u : Twisted D hu s) (a : OddCarrier D) :
    (rightField D hu s u).coeff e a = 0 := by
  simp only [rightField, HVertexOperator.coeff_of_coeff, doubledCoefficient,
    if_pos he, LinearMap.zero_apply]

/-- The coefficient multiplier for the upper physical half-turn on a
doubled-coordinate monomial. -/
theorem upper_half_turn (e : ℤ) :
    Complex.exp ((e : ℂ) * ((Real.pi : ℂ) / 2 * Complex.I)) = Complex.I ^ e := by
  rw [Complex.exp_int_mul, Complex.exp_pi_div_two_mul_I]

/-- The full coefficient convolution with the translation exponential in the
doubled coordinate. Its translation term of order `ell` carries exponent
`2*ell`, while the upper rotation acts on the native input exponent. -/
theorem rightField_convolution (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (e : ℤ) (u : Twisted D hu s) (a : OddCarrier D) :
    (rightField D hu s u).coeff e a =
      ∑ᶠ ell : ℕ, (Complex.I ^ (e - 2 * (ell : ℤ)) * (ell.factorial : ℂ)⁻¹) •
        (translation D hu (!s) ^ ell) ((field D hu s a).coeff (e - 2 * (ell : ℤ)) u) := by
  by_cases he : Even e
  · rw [rightField_even_zero D hu s e he u a]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro ell
    have hEven : Even (e - 2 * (ell : ℤ)) := by
      obtain ⟨k, hk⟩ := he
      exact ⟨k - (ell : ℤ), by omega⟩
    rw [field_even_zero D hu s _ hEven a u, map_zero, smul_zero]
  · obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp he
    let n := -k - 2
    have heq : e = -2*n-3 := by dsimp [n]; omega
    rw [heq, rightField_coeff]
    change (∑ᶠ ell : ℕ, rightTerm D hu s n u a ell) = _
    apply finsum_congr
    intro ell
    rw [show -2*n-3-2*(ell : ℤ) = -2*(n+(ell : ℤ))-3 by ring] <;> rfl

/-- Homogeneity gives an explicit support bound before any translation is
applied. The signed doubled output grade of the raw mode is `E - 2*ell`. -/
theorem R_eq_sum_of_grade (D : LatticeData) (hu : IsUnit D.G.det)
    (s : Bool) (n h : ℤ) (M : ℕ) (u : Twisted D hu s) (a : OddCarrier D)
    (ha : a.val ∈ grade D h) (huM : u.val ∈ actualGrade D hu M) :
    let E : ℤ := (M : ℤ) + 2*h - 2*n - 3
    (∀ ell : ℕ, E < 2 * (ell : ℤ) → J D hu s (n + (ell : ℤ)) a u = 0) ∧
      R D hu s n u a =
        ∑ ell ∈ Finset.range (E / 2 + 1).toNat, rightTerm D hu s n u a ell := by
  classical
  dsimp only
  have tail (ell : ℕ) (hneg : (M : ℤ) + 2*h - 2*n - 3 < 2 * (ell : ℤ)) :
      J D hu s (n + (ell : ℤ)) a u = 0 :=
    J_negative_grade_zero D hu s _ h M a u ha huM (by omega)
  refine ⟨tail, ?_⟩
  change (∑ᶠ ell : ℕ, rightTerm D hu s n u a ell) = _
  apply finsum_eq_sum_of_support_subset
  intro ell hell
  by_contra hout
  have hbound : (((M : ℤ) + 2*h - 2*n - 3) / 2 + 1).toNat ≤ ell :=
    Nat.le_of_not_gt (fun h => hout (Finset.mem_range.mpr h))
  exact hell (by simp only [rightTerm, tail ell (by omega), map_zero, smul_zero])

private theorem R_lowest (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (n h : ℤ) (M : ℕ) (u : Twisted D hu s) (a : OddCarrier D)
    (ha : a.val ∈ grade D h) (huM : u.val ∈ actualGrade D hu M)
    (hlo : 0 ≤ (M : ℤ) + 2*h - 2*n - 3) (hhi : (M : ℤ) + 2*h - 2*n - 3 < 2) :
    R D hu s n u a = Complex.I ^ (-2*n-3) • J D hu s n a u := by
  rw [(R_eq_sum_of_grade D hu s n h M u a ha huM).2,
    show (((M : ℤ) + 2*h - 2*n - 3) / 2 + 1).toNat = 1 by omega]
  simp [rightTerm]

private theorem upper_phase_neg_one : Complex.I ^ (-1 : ℤ) = -Complex.I := by
  rw [zpow_neg, zpow_one, Complex.inv_I]

private theorem upper_phase_neg_three : Complex.I ^ (-3 : ℤ) = Complex.I := by
  rw [zpow_neg, show Complex.I ^ (3 : ℤ) = Complex.I ^ (3 : ℕ) from
    zpow_natCast Complex.I 3, Complex.I_pow_three, inv_neg, Complex.inv_I, neg_neg]

/-- On the native Leech ground and first oscillator, only translation order
zero survives at the indicated modes. Both upper-branch coefficients are
nonzero and have the stated actual doubled output grades. -/
theorem leech_right_normalization (i : Fin leechData.rank) :
    let h := oddCurrent leechData i
    let t := leechGroundVector
    let b := Jplus (-1) h t
    let rPlus := R leechData leechUnit false (-1) t h
    let rMinus := R leechData leechUnit true 0 b h
    rPlus = -Complex.I • b ∧
      rMinus = Complex.I • Jminus 0 h b ∧
      rPlus.val ∈ actualGrade leechData leechUnit 1 ∧
      rMinus.val ∈ actualGrade leechData leechUnit 0 ∧
      rPlus ≠ 0 ∧ rMinus ≠ 0 := by
  dsimp only
  let h := oddCurrent leechData i
  let t := leechGroundVector
  let b := Jplus (-1) h t
  have ht : t.val ∈ actualGrade leechData leechUnit 0 := groundBasis_energy
  have ha : h.val ∈ grade leechData 1 := oddCurrent_grade_one leechData i
  obtain ⟨_, hb, hbne, _, hretne⟩ := leech_normalization i
  change b.val ∈ actualGrade leechData leechUnit 1 at hb
  have hp : R leechData leechUnit false (-1) t h = -Complex.I • b := by
    change R leechData leechUnit false (-1) t h =
      -Complex.I • J leechData leechUnit false (-1) h t
    rw [R_lowest leechData leechUnit false (-1) 1 0 t h ha ht (by norm_num) (by norm_num),
      show (-2 * (-1) - 3 : ℤ) = -1 by norm_num, upper_phase_neg_one]
  have hm : R leechData leechUnit true 0 b h = Complex.I • Jminus 0 h b := by
    change R leechData leechUnit true 0 b h = Complex.I • J leechData leechUnit true 0 h b
    rw [R_lowest leechData leechUnit true 0 1 1 b h ha hb (by norm_num) (by norm_num),
      show (-2 * 0 - 3 : ℤ) = -3 by norm_num, upper_phase_neg_three]
  have hr : (Jminus 0 h b).val ∈ actualGrade leechData leechUnit 0 :=
    J_grade leechData leechUnit true 0 1 1 0 h b ha hb (by norm_num)
  refine ⟨hp, hm, ?_, ?_, ?_, ?_⟩
  · rw [hp, Submodule.coe_smul]
    exact (actualGrade leechData leechUnit 1).smul_mem _ hb
  · rw [hm, Submodule.coe_smul]
    exact (actualGrade leechData leechUnit 0).smul_mem _ hr
  · rw [hp]
    exact smul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hbne
  · rw [hm]
    exact smul_ne_zero Complex.I_ne_zero hretne

/-- The fixed stress mode two on either actual twisted parity. -/
def lowering (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool) :
    Module.End ℂ (Twisted D hu s) :=
  (fixedParitySlice D hu (paritySign s) (stress D))[[2]]

private theorem lowering_val (D : LatticeData) (hu : IsUnit D.G.det)
    (s : Bool) (u : Twisted D hu s) :
    (lowering D hu s u).val = T D hu u.val := by
  change (correctedField D hu
      (LatticeActualConformalState.omega D (HalfFockSpectralFiberSource.actualInverse D))).coeff
        (-6) u.val = _
  rw [LatticeHalfFockCorrectedConformal.correctedField_omega D hu _
    (HalfFockSpectralFiberSource.actualInverse_left D hu)]
  simp only [tensorStressField, HVertexOperator.coeff_of_coeff, stressCoeff,
    show (-6 : ℤ) % 2 = 0 by decide, ite_eq_left,
    show (-(-6 : ℤ)-4)/2 = 1 by decide, T, tensorL]

private theorem lowering_pow_val (D : LatticeData) (hu : IsUnit D.G.det)
    (s : Bool) (j : ℕ) (u : Twisted D hu s) :
    ((lowering D hu s ^ j) u).val = (T D hu ^ j) u.val := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [pow_succ', Module.End.mul_apply, lowering_val, ih]

private theorem actualGrade_eigen (D : LatticeData) (hu : IsUnit D.G.det)
    (M : ℕ) (u : ActualTensor D hu) :
    u ∈ actualGrade D hu M ↔
      actualTensorL0 D hu u = ((D.rank : ℂ) / 16 + (M : ℂ) / 2) • u := by
  simp only [actualGrade, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

private theorem lowering_tail (D : LatticeData) (hu : IsUnit D.G.det)
    (M : ℕ) (u : ActualTensor D hu) (huM : u ∈ actualGrade D hu M)
    (j : ℕ) (hj : M / 2 + 1 ≤ j) : (T D hu ^ j) u = 0 := by
  apply lowering_killed D hu (M : ℤ) u
  · simpa only [Int.cast_natCast] using (actualGrade_eigen D hu M u).mp huM
  · omega

private theorem translation_power_pairing (D : LatticeData) (hu : IsUnit D.G.det)
    (s : Bool) (ell : ℕ) (v : ActualTensor D hu) (w : Twisted D hu s) :
    actualForm D hu v ((translation D hu s ^ ell) w).val =
      actualForm D hu ((T D hu ^ ell) v) w.val := by
  induction ell generalizing v with
  | zero => rfl
  | succ ell ih =>
    rw [pow_succ', Module.End.mul_apply, translation_val]
    have h := (actual_stress_transpose D hu 1 v
      ((translation D hu s ^ ell) w).val).symm
    change actualForm D hu v (raising D hu ((translation D hu s ^ ell) w).val) =
      actualForm D hu (T D hu v) ((translation D hu s ^ ell) w).val at h
    rw [h, ih, pow_succ, Module.End.mul_apply]

/-- Transposing the translation exponential through the native bilinear form
gives a second explicit finite range from the detector grade. -/
theorem R_pairing_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (s : Bool) (n : ℤ) (K : ℕ) (u : Twisted D hu s) (a : OddCarrier D)
    (v : Twisted D hu (!s)) (hv : v.val ∈ actualGrade D hu K) :
    actualForm D hu v.val (R D hu s n u a).val =
      ∑ ell ∈ Finset.range (K / 2 + 1),
        (Complex.I ^ (-2*(n + (ell : ℤ))-3) * (ell.factorial : ℂ)⁻¹) *
          actualForm D hu ((T D hu ^ ell) v.val)
            (J D hu s (n + (ell : ℤ)) a u).val := by
  classical
  let pair : Twisted D hu (!s) →ₗ[ℂ] ℂ :=
    (actualForm D hu v.val).comp (paritySpace D hu (paritySign (!s))).subtype
  let term (ell : ℕ) : ℂ :=
    (Complex.I ^ (-2*(n + (ell : ℤ))-3) * (ell.factorial : ℂ)⁻¹) *
      actualForm D hu ((T D hu ^ ell) v.val) (J D hu s (n + (ell : ℤ)) a u).val
  have htranspose (ell : ℕ) : pair (rightTerm D hu s n u a ell) = term ell := by
    change actualForm D hu v.val (rightTerm D hu s n u a ell).val = _
    simp only [rightTerm, Submodule.coe_smul, map_smul, smul_eq_mul,
      translation_power_pairing, term]
  have hsupport : Function.support term ⊆ (Finset.range (K / 2 + 1) : Set ℕ) := by
    intro ell hell
    apply Finset.mem_range.mpr
    by_contra hout
    have hz := lowering_tail D hu K v.val hv ell (Nat.le_of_not_gt hout)
    exact hell (by simp [term, hz])
  change pair (∑ᶠ ell : ℕ, rightTerm D hu s n u a ell) = _
  rw [map_finsum pair (rightTerm_finite D hu s n u a)]
  calc
    (∑ᶠ ell : ℕ, pair (rightTerm D hu s n u a ell)) = ∑ᶠ ell : ℕ, term ell := by
      simp only [htranspose]
    _ = _ := finsum_eq_sum_of_support_subset term hsupport

/-- Huang's `A_{-1}` transpose as a functional on the actual odd source.
Here `3 + M` is twice the Leech input weight. The index `m` refers to
physical exponent `-m-3/2` of the resulting twisted-pair coefficient.
The grade argument is used on homogeneous inputs. -/
def mixedPairing (s : Bool) (M : ℕ) (m : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s)) :
    Module.Dual ℂ (OddCarrier leechData) :=
  Complex.I ^ (-(3 + (M : ℤ))) •
    ∑ j ∈ Finset.range (M / 2 + 1),
      (j.factorial : ℂ)⁻¹ •
        (((actualForm leechData leechUnit v.val).comp
          (paritySpace leechData leechUnit (paritySign (!s))).subtype).comp
            (R leechData leechUnit s ((M : ℤ) - m - (j : ℤ))
              ((lowering leechData leechUnit s ^ j) u)))

/-- The inversion phase and both finite stress ranges in the mixed BPZ
transpose. On homogeneous inputs increasing either range adds only zero
terms by the actual signed lowering bound. -/
theorem mixedPairing_finite (s : Bool) (M K : ℕ) (m : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (hv : v.val ∈ actualGrade leechData leechUnit K) (a : OddCarrier leechData) :
    mixedPairing s M m u v a =
      Complex.I ^ (-(3 + (M : ℤ))) *
        ∑ j ∈ Finset.range (M / 2 + 1),
          (j.factorial : ℂ)⁻¹ *
            ∑ ell ∈ Finset.range (K / 2 + 1),
              (Complex.I ^ (-2*((M : ℤ) - m - (j : ℤ) + (ell : ℤ))-3) *
                (ell.factorial : ℂ)⁻¹) *
                actualForm leechData leechUnit ((T leechData leechUnit ^ ell) v.val)
                  (J leechData leechUnit s ((M : ℤ) - m - (j : ℤ) + (ell : ℤ))
                    a ((lowering leechData leechUnit s ^ j) u)).val := by
  simp only [mixedPairing, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, smul_eq_mul]
  apply congrArg (fun c : ℂ => Complex.I ^ (-(3 + (M : ℤ))) * c)
  apply Finset.sum_congr rfl
  intro j _
  rw [R_pairing_finite leechData leechUnit s _ K _ a v hv]

/-- In the outer BPZ sum the actual `L(1)` power vanishes past the input
grade, for even and odd oscillator parity alike. -/
theorem mixedPairing_lowering_tail (s : Bool) (M : ℕ)
    (u : Twisted leechData leechUnit s) (hu : u.val ∈ actualGrade leechData leechUnit M)
    (j : ℕ) (hj : M / 2 + 1 ≤ j) : (lowering leechData leechUnit s ^ j) u = 0 := by
  apply Subtype.ext
  rw [lowering_pow_val]
  exact lowering_tail leechData leechUnit M u.val hu j hj

private theorem mixedPairing_lowest (s : Bool) (M : ℕ) (m : ℤ) (hM : M < 2)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (a : OddCarrier leechData) :
    mixedPairing s M m u v a = Complex.I ^ (-(3 + (M : ℤ))) *
      actualForm leechData leechUnit v.val (R leechData leechUnit s ((M : ℤ) - m) u a).val := by
  have hsize : M / 2 + 1 = 1 := by omega
  simp [mixedPairing, hsize, smul_eq_mul]

private theorem upper_phase_neg_four : Complex.I ^ (-4 : ℤ) = 1 := by
  have h : Complex.I ^ (4 : ℕ) = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, Complex.I_sq]
    norm_num
  rw [zpow_neg, show Complex.I ^ (4 : ℤ) = Complex.I ^ (4 : ℕ) from
    zpow_natCast Complex.I 4, h, inv_one]

/-- A nonzero homogeneous twisted vector has an actual bilinear detector of
the same grade and parity. The detector is normalized by its native pairing,
using a basis vector of the matching grade. -/
private theorem exists_grade_detector (D : LatticeData) (hu : IsUnit D.G.det)
    (s : Bool) (M : ℕ) (u : Twisted D hu s) (huM : u.val ∈ actualGrade D hu M)
    (hne : u ≠ 0) (hs : (-1 : ℂ)^M = paritySign s) :
    ∃ v : Twisted D hu s, v.val ∈ actualGrade D hu M ∧
      actualForm D hu v.val u.val = 1 := by
  classical
  let b := actualAmbientBasis D hu
  have hex : ∃ i, actualForm D hu (b i) u.val ≠ 0 := by
    by_contra! hall
    apply hne
    apply Subtype.ext
    apply (actualForm_nondegenerate D hu).2
    intro x
    have hz : (actualForm D hu).flip u.val = 0 := by
      apply b.ext
      intro i
      exact hall i
    exact LinearMap.congr_fun hz x
  obtain ⟨i, hi⟩ := hex
  have hb : b i ∈ actualGrade D hu (oddWeight D i.1) :=
    (actualGrade_eigen D hu _ _).mpr (actual_basis_eigenvalue D hu i.1 i.2)
  have heq : oddWeight D i.1 = M := by
    by_contra hd
    apply hi
    exact actualForm_oddGrade_orthogonal D hu (oddWeight D i.1 : ℤ) (M : ℤ) (b i) u.val
      (by simpa only [Int.cast_natCast] using (actualGrade_eigen D hu _ _).mp hb)
      (by simpa only [Int.cast_natCast] using (actualGrade_eigen D hu _ _).mp huM)
      (by exact_mod_cast hd)
  rw [heq] at hb
  have hpar : b i ∈ paritySpace D hu (paritySign s) := by
    have hp := actualParity_on_actualGrade D hu M ⟨b i, hb⟩
    rw [hs] at hp
    simpa only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] using hp
  let c := (actualForm D hu (b i) u.val)⁻¹
  refine ⟨⟨c • b i, (paritySpace D hu (paritySign s)).smul_mem c hpar⟩,
    (actualGrade D hu M).smul_mem c hb, ?_⟩
  change actualForm D hu ((actualForm D hu (b i) u.val)⁻¹ • b i) u.val = 1
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hi]

/-- The two mixed BPZ matrix coefficients at physical exponent `-5/2`.
The Heisenberg direction has norm two, and the detectors are dual to its
first oscillator and to the specified twisted ground vector. -/
theorem leech_mixed_pairing_normalization (i : Fin leechData.rank) :
    let t := leechGroundVector
    ∃ c : ℂ, c^2 * (leechData.G i i : ℂ) = 2 ∧
    let h := c • oddCurrent leechData i
    let b := Jplus (-1) h t
    ∃ (bDual : TwistedOdd) (tDual : TwistedEven),
      bDual.val ∈ actualGrade leechData leechUnit 1 ∧
      tDual.val ∈ actualGrade leechData leechUnit 0 ∧
      actualForm leechData leechUnit b.val bDual.val = 1 ∧
      actualForm leechData leechUnit t.val tDual.val = 1 ∧
      Jminus 0 h b = t ∧
      mixedPairing false 0 1 t bDual h = 1 ∧
      mixedPairing true 1 1 b tDual h = Complex.I := by
  dsimp only
  let t := leechGroundVector
  let a := oddCurrent leechData i
  let b0 := Jplus (-1) a t
  have hpos : 0 < (leechData.G i i : ℝ) :=
    ActualLeechHyperbolic.leech_spec.2.2.1.diag_pos
  have hG : (leechData.G i i : ℂ) ≠ 0 := by
    exact_mod_cast (show leechData.G i i ≠ 0 from by exact_mod_cast hpos.ne')
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (2 / (leechData.G i i : ℂ))
    (n := 2) (by decide)
  have hnorm : c^2 * (leechData.G i i : ℂ) = 2 :=
    (eq_div_iff hG).mp hc
  refine ⟨c, hnorm, ?_⟩
  let h := c • a
  let b := Jplus (-1) h t
  have ht : t.val ∈ actualGrade leechData leechUnit 0 := groundBasis_energy
  have ha : h.val ∈ grade leechData 1 :=
    (grade leechData 1).smul_mem c (oddCurrent_grade_one leechData i)
  obtain ⟨_, hb0, _, hret0, hret0ne⟩ := leech_normalization i
  change b0.val ∈ actualGrade leechData leechUnit 1 at hb0
  change Jminus 0 a b0 = ((leechData.G i i : ℂ) / 2) • t at hret0
  have htne : t ≠ 0 := by
    intro hz
    exact hret0ne (by rw [hret0, hz, smul_zero])
  have hbscale : b = c • b0 := by
    change Jplus (-1) (c • a) t = c • Jplus (-1) a t
    simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply]
  have hb : b.val ∈ actualGrade leechData leechUnit 1 := by
    rw [hbscale, Submodule.coe_smul]
    exact (actualGrade leechData leechUnit 1).smul_mem c hb0
  have hret : Jminus 0 h b = t := calc
    _ = (c*c) • Jminus 0 a b0 := by
      rw [hbscale]
      simp only [h, map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_smul]
    _ = t := by
      rw [hret0, smul_smul]
      have hscalar : (c*c) * ((leechData.G i i : ℂ) / 2) = 1 := by
        calc
          _ = (c^2 * (leechData.G i i : ℂ)) / 2 := by ring
          _ = 1 := by rw [hnorm]; norm_num
      rw [hscalar, one_smul]
  have hbne : b ≠ 0 := by
    intro hz
    apply htne
    rw [← hret, hz, map_zero]
  obtain ⟨bDual, hbDual, hp⟩ :=
    exists_grade_detector leechData leechUnit true 1 b hb hbne (by norm_num [NativeOddTwistedIntertwiner.paritySign])
  obtain ⟨tDual, htDual, hm⟩ :=
    exists_grade_detector leechData leechUnit false 0 t ht htne (by norm_num [NativeOddTwistedIntertwiner.paritySign])
  have hRplus : R leechData leechUnit false (-1) t h = -Complex.I • b := by
    change R leechData leechUnit false (-1) t h =
      -Complex.I • J leechData leechUnit false (-1) h t
    rw [R_lowest leechData leechUnit false (-1) 1 0 t h ha ht (by norm_num) (by norm_num),
      show (-2 * (-1) - 3 : ℤ) = -1 by norm_num, upper_phase_neg_one]
  have hRminus : R leechData leechUnit true 0 b h = Complex.I • t := by
    rw [R_lowest leechData leechUnit true 0 1 1 b h ha hb (by norm_num) (by norm_num),
      show (-2 * 0 - 3 : ℤ) = -3 by norm_num, upper_phase_neg_three]
    exact congrArg (fun u : TwistedEven => Complex.I • u) hret
  have hsym := (ActualPairingSymmetry.actualForm_symmetric leechData leechUnit).eq
  refine ⟨bDual, tDual, hbDual, htDual, (hsym _ _).trans hp, (hsym _ _).trans hm, hret, ?_, ?_⟩
  · rw [mixedPairing_lowest false 0 1 (by decide),
      show ((0 : ℕ) : ℤ) - 1 = -1 by decide, hRplus, Submodule.coe_smul, map_smul,
      smul_eq_mul, hp, show -(3 + ((0 : ℕ) : ℤ)) = -3 by decide, upper_phase_neg_three]
    simp only [mul_one, mul_neg, Complex.I_mul_I, neg_neg]
  · rw [mixedPairing_lowest true 1 1 (by decide),
      show ((1 : ℕ) : ℤ) - 1 = 0 by decide, hRminus, Submodule.coe_smul, map_smul,
      smul_eq_mul, hm, show -(3 + ((1 : ℕ) : ℤ)) = -4 by decide, upper_phase_neg_four]
    simp

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
