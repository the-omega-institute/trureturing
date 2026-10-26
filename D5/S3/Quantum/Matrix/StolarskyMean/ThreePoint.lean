/- GID: D5/S3/Quantum/Matrix/StolarskyMean/ThreePoint
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/StolarskyMean/ThreePoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.Order.OrderClosed, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Continuity, mathlib/module/Mathlib.Analysis.Convex.SpecificFunctions.Basic]
   utility: none
   digest: Positive planes and asymptotic determinants certify three point inertia. -/

import D5.S3.Quantum.Matrix.StolarskyMean.Reduction
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

noncomputable section
open Matrix Filter
open scoped BigOperators Topology

namespace D5.S3.Quantum.Matrix.StolarskyMean.ThreePoint

open Defs Spectral Reduction

/-- A diagonally weighted three point Toeplitz matrix. -/
def weightedToeplitz (d : Fin 3 → ℝ) (a b : ℝ) :
    _root_.Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => d i * (!![1, a, b; a, 1, a; b, a, 1] i j) * d j

private def positivePlaneMap (d : Fin 3 → ℝ) :
    (Fin 2 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := ![x 0 / d 0, x 1 / d 1, x 0 / d 2]
  map_add' x y := by ext i; fin_cases i <;> simp [add_div]
  map_smul' c x := by ext i; fin_cases i <;> simp [mul_div_assoc]

private theorem positivePlaneMap_injective (d : Fin 3 → ℝ) (hd : ∀ i, d i ≠ 0) :
    Function.Injective (positivePlaneMap d) := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  ext i
  fin_cases i
  · change x 0 / d 0 = y 0 / d 0 at h0
    exact (div_left_inj' (hd 0)).mp h0
  · change x 1 / d 1 = y 1 / d 1 at h1
    exact (div_left_inj' (hd 1)).mp h1

private theorem weightedToeplitz_form (d : Fin 3 → ℝ) (hd : ∀ i, d i ≠ 0)
    (a b : ℝ) (x : Fin 2 → ℝ) :
    RHLinalg.hermForm (weightedToeplitz d a b) (positivePlaneMap d x) =
      (x 1 + 2 * a * x 0) ^ 2 + 2 * (1 + b - 2 * a ^ 2) * (x 0) ^ 2 := by
  simp [RHLinalg.hermForm, weightedToeplitz, positivePlaneMap, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ, hd]
  field_simp [hd]
  <;> ring

/-- A strictly positive symmetric block produces two positive eigenvalues,
independently of the signs of the nonzero diagonal weights. -/
theorem two_le_numPosEig_weightedToeplitz (d : Fin 3 → ℝ)
    (hd : ∀ i, d i ≠ 0) (a b : ℝ) (hdet : 0 < 1 + b - 2 * a ^ 2) :
    2 ≤ numPosEig (weightedToeplitz d a b) := by
  have hM : (weightedToeplitz d a b).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [weightedToeplitz] <;> ring
  let W := LinearMap.range (positivePlaneMap d)
  have hdim : 2 ≤ Module.finrank ℝ W := by
    rw [LinearMap.finrank_range_of_inj (positivePlaneMap_injective d hd)]
    simp
  apply two_le_numPosEig_of_posDefOn hM hdim
  rintro _ ⟨x, rfl⟩ hne
  rw [weightedToeplitz_form d hd]
  by_cases hx : x 0 = 0
  · have hx1 : x 1 ≠ 0 := by
      intro h1
      apply hne
      ext i
      fin_cases i <;> simp [positivePlaneMap, hx, h1]
    simpa [hx] using sq_pos_of_ne_zero hx1
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _)
      (mul_pos (mul_pos (by norm_num) hdet) (sq_pos_of_ne_zero hx))

/-- A normalized determinant with positive limit is eventually positive. -/
private theorem eventually_positive_determinant {ψ : ℝ → ℝ} {C : ℝ}
    (hψ : Tendsto (fun z => Real.exp (-z) * ψ z) atTop (𝓝 C))
    (hC : 0 < C) (hhalf : C < 1 / 2) :
    ∀ᶠ z in atTop, 0 < 1 + ψ (2 * z) - 2 * ψ z ^ 2 := by
  have hscale : Tendsto (fun z : ℝ => 2 * z) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_id
  have htwice := hψ.comp hscale
  have he : Tendsto (fun z : ℝ => Real.exp (-(2 * z))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_neg_atTop_atBot.comp hscale
  have ht : Tendsto
      (fun z : ℝ => Real.exp (-(2 * z)) + Real.exp (-(2 * z)) * ψ (2 * z) -
        2 * (Real.exp (-z) * ψ z) ^ 2) atTop (𝓝 (C - 2 * C ^ 2)) := by
    have hpow : Tendsto (fun z : ℝ => 2 * (Real.exp (-z) * ψ z) ^ 2)
        atTop (𝓝 (2 * C ^ 2)) := tendsto_const_nhds.mul (hψ.pow 2)
    simpa only [Function.comp_def, zero_add] using (he.add htwice).sub hpow
  have hlim : 0 < C - 2 * C ^ 2 := by nlinarith
  filter_upwards [tendsto_const_nhds.eventually_lt ht hlim] with z hz
  have hexp : Real.exp (-(2 * z)) = Real.exp (-z) ^ 2 := by
    rw [← Real.exp_nat_mul (-z) 2]
    congr 1
    ring
  have hid : Real.exp (-(2 * z)) * (1 + ψ (2 * z) - 2 * ψ z ^ 2) =
      Real.exp (-(2 * z)) + Real.exp (-(2 * z)) * ψ (2 * z) -
        2 * (Real.exp (-z) * ψ z) ^ 2 := by rw [hexp]; ring
  rw [← hid] at hz
  exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hz

/-- The asymptotic coefficient below one half supplies a three point
positive spectral plane at every sufficiently large parameter. -/
private theorem eventually_two_le_numPosEig {ψ : ℝ → ℝ} {C : ℝ}
    (hψ : Tendsto (fun z => Real.exp (-z) * ψ z) atTop (𝓝 C))
    (hC : 0 < C) (hhalf : C < 1 / 2) (d : ℝ → Fin 3 → ℝ)
    (hd : ∀ z i, d z i ≠ 0) :
    ∀ᶠ z in atTop, 2 ≤ numPosEig (weightedToeplitz (d z) (ψ z) (ψ (2 * z))) := by
  filter_upwards [eventually_positive_determinant hψ hC hhalf] with z hz
  exact two_le_numPosEig_weightedToeplitz _ (hd z) _ _ hz

private theorem exp_neg_mul_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun z : ℝ => Real.exp (-(c * z))) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
    ((tendsto_const_mul_atTop_of_pos hc).mpr tendsto_id))

private theorem power_coefficient_lt_half {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγ1 : γ ≠ 1) :
    (1 / γ : ℝ) ^ (1 / (γ - 1)) < 1 / 2 := by
  have hsec := (strictConcaveOn_log_Ioi).secant_strict_mono
    (show (0 : ℝ) < 1 by norm_num) hγ (show (0 : ℝ) < 2 by norm_num)
    hγ1 (by norm_num : (2 : ℝ) ≠ 1) hγ2
  simp only [Real.log_one, sub_zero] at hsec
  norm_num at hsec
  rw [Real.rpow_def_of_pos (one_div_pos.mpr hγ)]
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)]
  apply Real.exp_lt_exp.mpr
  rw [Real.log_div one_ne_zero hγ.ne', Real.log_one,
    Real.log_div one_ne_zero (by norm_num : (2 : ℝ) ≠ 0), Real.log_one]
  simpa only [div_eq_mul_inv, one_mul, zero_sub, neg_mul] using neg_lt_neg hsec

private theorem normalized_ratio_limit {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun z : ℝ =>
      ((1 - Real.exp (-(2 * γ * z))) / (γ * (1 - Real.exp (-(2 * z))))) ^
        (1 / (γ - 1))) atTop (𝓝 ((1 / γ) ^ (1 / (γ - 1)))) := by
  have h1 := exp_neg_mul_tendsto (c := 2 * γ) (by positivity)
  have h2 := exp_neg_mul_tendsto (c := 2) (by norm_num)
  have hratio : Tendsto (fun z : ℝ =>
      (1 - Real.exp (-(2 * γ * z))) / (γ * (1 - Real.exp (-(2 * z)))))
      atTop (𝓝 (1 / γ)) := by
    convert (tendsto_const_nhds.sub h1).div
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub h2))
      (show γ * (1 - 0) ≠ 0 by simpa using hγ.ne') using 1 <;> (try simp)
  exact hratio.rpow_const (Or.inl (one_div_ne_zero hγ.ne'))

private theorem normalized_profile_eq {γ z : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≠ 1) (hz : 0 < z) :
    Real.exp (-z) * psi γ z =
      ((1 - Real.exp (-(2 * γ * z))) / (γ * (1 - Real.exp (-(2 * z))))) ^
        (1 / (γ - 1)) := by
  have hγ0 : γ ≠ 0 := hγ.ne'
  have hzγ : z * γ > 0 := mul_pos hz hγ
  have hab : Real.exp (-z) ≠ Real.exp z := by
    intro h
    have := Real.exp_injective h
    linarith
  rw [psi, stolarsky, if_neg hab, if_neg hγ0, if_neg hγ1]
  simp only [← Real.exp_mul]
  let E := Real.exp z
  let F := Real.exp (z * γ)
  have hE : 0 < E := Real.exp_pos _
  have hF : 0 < F := Real.exp_pos _
  have hE1 : 1 < E := Real.one_lt_exp_iff.mpr hz
  have hF1 : 1 < F := Real.one_lt_exp_iff.mpr hzγ
  have he1 : Real.exp (-z * γ) = 1 / F := by
    rw [show -z * γ = -(z * γ) by ring, Real.exp_neg]; simp [one_div, F]
  have he2 : Real.exp (-z) = 1 / E := by rw [Real.exp_neg]; simp [one_div, E]
  have he3 : Real.exp (-(2 * γ * z)) = 1 / F ^ 2 := by
    rw [show -(2 * γ * z) = -(2 * (z * γ)) by ring, Real.exp_neg,
      show 2 * (z * γ) = (z * γ) + (z * γ) by ring, Real.exp_add]
    simp [one_div, F, pow_two]
  have he4 : Real.exp (-(2 * z)) = 1 / E ^ 2 := by
    rw [Real.exp_neg, show (2 : ℝ) * z = z + z by ring, Real.exp_add]
    simp [one_div, E, pow_two]
  rw [he1, he2, he3, he4]
  change 1 / E * ((1 / F - F) / (γ * (1 / E - E))) ^ (1 / (γ - 1)) =
    ((1 - 1 / F ^ 2) / (γ * (1 - 1 / E ^ 2))) ^ (1 / (γ - 1))
  have hQ : 0 < (1 / F - F) / (γ * (1 / E - E)) := by
    apply div_pos_of_neg_of_neg
    · have : 1 / F < 1 := (div_lt_one hF).mpr hF1
      linarith
    · apply mul_neg_of_pos_of_neg hγ
      have : 1 / E < 1 := (div_lt_one hE).mpr hE1
      linarith
  have hefac : (E / F : ℝ) ^ (1 / (γ - 1)) = 1 / E := by
    dsimp [E, F]
    rw [← Real.exp_sub, ← Real.exp_mul]
    rw [show (z - z * γ) * (1 / (γ - 1)) = -z by field_simp [sub_ne_zero.mpr hγ1] <;> ring]
    simpa [one_div] using Real.exp_neg z
  have hrat : (E / F) * ((1 / F - F) / (γ * (1 / E - E))) =
      (1 - 1 / F ^ 2) / (γ * (1 - 1 / E ^ 2)) := by
    have hEn : E ^ 2 ≠ 1 := by nlinarith
    have hden : 1 / E - E ≠ 0 := by
      have : 1 / E < 1 := (div_lt_one hE).mpr hE1
      linarith
    field_simp [hE.ne', hF.ne', hγ0, hEn, hden, sub_ne_zero.mpr (Ne.symm hEn), sub_ne_zero.mpr (ne_of_lt hE1)]
    <;> ring
  calc
    _ = (E / F) ^ (1 / (γ - 1)) *
        ((1 / F - F) / (γ * (1 / E - E))) ^ (1 / (γ - 1)) := by
      rw [hefac]
    _ = _ := by
      rw [← Real.mul_rpow (div_pos hE hF).le hQ.le, hrat]

private theorem normalized_profile_limit {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≠ 1) :
    Tendsto (fun z : ℝ => Real.exp (-z) * psi γ z) atTop
      (𝓝 ((1 / γ) ^ (1 / (γ - 1)))) := by
  apply (normalized_ratio_limit hγ).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
  exact (normalized_profile_eq hγ hγ1 hz).symm

/-- Exponential nodes have a diagonal congruence to a three point Toeplitz
matrix with the Stolarsky profile as its off-diagonal data. -/
private theorem stolarskyMatrix_threePoint (γ z : ℝ) :
    stolarskyMatrix γ ![Real.exp (-2 * z), 1, Real.exp (2 * z)] =
      weightedToeplitz ![Real.exp (-z), 1, Real.exp z] (psi γ z) (psi γ (2 * z)) := by
  have hm := stolarsky_homogeneous γ (Real.exp_pos (-z)) (Real.exp_pos z)
    (Real.exp_pos (-z))
  have hp := stolarsky_homogeneous γ (Real.exp_pos (-z)) (Real.exp_pos z)
    (Real.exp_pos z)
  have he : Real.exp (-z) * Real.exp z = 1 := by rw [← Real.exp_add]; simp
  have hmm : Real.exp (-z) * Real.exp (-z) = Real.exp (-2 * z) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpp : Real.exp z * Real.exp z = Real.exp (2 * z) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he, hmm] at hm
  rw [show Real.exp z * Real.exp (-z) = 1 by rw [mul_comm]; exact he, hpp] at hp
  have hcross (x : ℝ) : Real.exp (-z) * x * Real.exp z = x := by
    calc
      _ = (Real.exp (-z) * Real.exp z) * x := by ring
      _ = x := by rw [he]; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [stolarskyMatrix, weightedToeplitz, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons,
      Fin.reduceFinMk, mul_one, one_mul]
  · simp [stolarsky, hmm]
  · simpa only [psi, mul_comm] using hm
  · dsimp [psi]
    rw [show -(2 * z) = -2 * z by ring]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      (hcross (stolarsky γ (Real.exp (-2 * z)) (Real.exp (2 * z)))).symm
  · rw [stolarsky_symm]; simpa only [psi, mul_comm] using hm
  · simp [stolarsky]
  · simpa only [psi, mul_comm] using hp
  · rw [stolarsky_symm]
    dsimp [psi]
    rw [show -(2 * z) = -2 * z by ring]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      (hcross (stolarsky γ (Real.exp (-2 * z)) (Real.exp (2 * z)))).symm
  · rw [stolarsky_symm]; simpa only [psi, mul_comm] using hp
  · simp [stolarsky, hpp]

/-- Every parameter strictly between zero and two, other than the identric
extension, has three exponential nodes with at least two positive eigenvalues. -/
private theorem exists_threePoint_of_pos_ne_one {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγ1 : γ ≠ 1) :
    ∃ z : ℝ, 0 < z ∧ 2 ≤ numPosEig
      (stolarskyMatrix γ ![Real.exp (-2 * z), 1, Real.exp (2 * z)]) := by
  have hC : 0 < (1 / γ : ℝ) ^ (1 / (γ - 1)) :=
    Real.rpow_pos_of_pos (one_div_pos.mpr hγ) _
  have he := eventually_two_le_numPosEig (normalized_profile_limit hγ hγ1) hC
    (power_coefficient_lt_half hγ hγ2 hγ1)
    (fun z => ![Real.exp (-z), 1, Real.exp z]) (by
      intro z i
      fin_cases i <;> simp [Real.exp_ne_zero])
  obtain ⟨z, hz, hez⟩ := (eventually_gt_atTop (0 : ℝ)).and he |>.exists
  refine ⟨z, hz, ?_⟩
  rw [stolarskyMatrix_threePoint]
  exact hez

private theorem psi_zero_of_pos {z : ℝ} (hz : 0 < z) :
    psi 0 z = Real.sinh z / z := by
  have hab : Real.exp (-z) ≠ Real.exp z := by
    intro h
    have := Real.exp_injective h
    linarith
  simp [psi, stolarsky, hab, Real.log_exp, Real.sinh_eq]
  field_simp
  <;> ring

/-- The logarithmic extension already has a three point counterexample at
exponential spacing four. -/
private theorem exists_threePoint_zero :
    ∃ z : ℝ, 0 < z ∧ 2 ≤ numPosEig
      (stolarskyMatrix 0 ![Real.exp (-2 * z), 1, Real.exp (2 * z)]) := by
  refine ⟨2, by norm_num, ?_⟩
  rw [stolarskyMatrix_threePoint]
  apply two_le_numPosEig_weightedToeplitz
  · intro i
    fin_cases i <;> simp [Real.exp_ne_zero]
  · rw [psi_zero_of_pos (by norm_num : (0 : ℝ) < 2),
      psi_zero_of_pos (by norm_num : (0 : ℝ) < 2 * 2), Real.sinh_two_mul]
    have hs : 0 < Real.sinh 2 := Real.sinh_pos_iff.mpr (by norm_num)
    have hh := mul_pos hs (sub_pos.mpr (Real.sinh_lt_cosh 2))
    nlinarith

private theorem normalized_profile_one_eq {z : ℝ} (hz : 0 < z) :
    Real.exp (-z) * psi 1 z =
      Real.exp (2 * z * Real.exp (-(2 * z)) / (1 - Real.exp (-(2 * z))) - 1) := by
  have hab : Real.exp (-z) ≠ Real.exp z := by
    intro h; have hh := Real.exp_injective h; linarith
  simp only [psi, stolarsky, if_neg hab, one_ne_zero, ↓reduceIte, Real.log_exp]
  rw [← Real.exp_add]; congr 1
  let E := Real.exp z
  have hE : 0 < E := Real.exp_pos z
  have hE1 : 1 < E := Real.one_lt_exp_iff.mpr hz
  have hEn : E ^ 2 ≠ 1 := by nlinarith
  have hden : 1 / E - E ≠ 0 := by
    have hinv : 1 / E < 1 := (div_lt_one hE).mpr hE1; linarith
  have hden2 : 1 - 1 / E ^ 2 ≠ 0 := by
    have hinv : 1 / E ^ 2 < 1 := (div_lt_one (sq_pos_of_pos hE)).mpr (by nlinarith); linarith
  have he1 : Real.exp (-z) = 1 / E := by simp [Real.exp_neg, E, one_div]
  have he2 : Real.exp (-(2 * z)) = 1 / E ^ 2 := by
    simp [Real.exp_neg, E, show (2 : ℝ) * z = z + z by ring, Real.exp_add, pow_two, one_div]
  rw [he1, he2]
  change -z + ((1 / E * -z - E * z) / (1 / E - E) - 1) = 2 * z * (1 / E ^ 2) / (1 - 1 / E ^ 2) - 1
  field_simp [hE.ne', hEn, hden, hden2] <;> ring

private theorem normalized_profile_one_limit :
    Tendsto (fun z : ℝ => Real.exp (-z) * psi 1 z) atTop (𝓝 (Real.exp (-1))) := by
  have hscale : Tendsto (fun z : ℝ => 2 * z) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_id
  have he : Tendsto (fun z : ℝ => Real.exp (-(2 * z))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  have hze : Tendsto (fun z : ℝ => 2 * z * Real.exp (-(2 * z))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one] using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
  have hquot : Tendsto (fun z : ℝ => 2 * z * Real.exp (-(2 * z)) / (1 - Real.exp (-(2 * z)))) atTop (𝓝 0) := by
    convert hze.div (tendsto_const_nhds.sub he) (by norm_num : (1 : ℝ) - 0 ≠ 0) using 1; norm_num
  have hlim : Tendsto (fun z : ℝ => Real.exp (2 * z * Real.exp (-(2 * z)) / (1 - Real.exp (-(2 * z))) - 1)) atTop (𝓝 (Real.exp (-1))) := by
    have harg : Tendsto (fun z : ℝ => 2 * z * Real.exp (-(2 * z)) / (1 - Real.exp (-(2 * z))) - 1) atTop (𝓝 (-1)) := by simpa using hquot.sub_const 1
    simpa only [Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp harg
  apply hlim.congr'; filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
  exact (normalized_profile_one_eq hz).symm

private theorem one_coefficient_lt_half : Real.exp (-1) < 1 / 2 := by
  have h : 2 < Real.exp 1 := by linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
  rw [Real.exp_neg, inv_eq_one_div, div_lt_div_iff₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)]
  simpa using h

private theorem exists_threePoint_one :
    ∃ z : ℝ, 0 < z ∧ 2 ≤ numPosEig (stolarskyMatrix 1 ![Real.exp (-2 * z), 1, Real.exp (2 * z)]) := by
  have hC : 0 < Real.exp (-1) := Real.exp_pos _
  have he := eventually_two_le_numPosEig normalized_profile_one_limit hC one_coefficient_lt_half
    (fun z => ![Real.exp (-z), 1, Real.exp z]) (by intro z i; fin_cases i <;> simp [Real.exp_ne_zero])
  obtain ⟨z, hz, hez⟩ := (eventually_gt_atTop (0 : ℝ)).and he |>.exists
  exact ⟨z, hz, by rw [stolarskyMatrix_threePoint]; exact hez⟩

/-- Every parameter in the conjectured failure interval has a three point witness. -/
theorem exists_threePoint {γ : ℝ} (hγ : 0 ≤ γ) (hγ2 : γ < 2) :
    ∃ z : ℝ, 0 < z ∧ 2 ≤ numPosEig
      (stolarskyMatrix γ ![Real.exp (-2 * z), 1, Real.exp (2 * z)]) := by
  rcases eq_or_lt_of_le hγ with rfl | hγ
  · exact exists_threePoint_zero
  by_cases h : γ = 1
  · subst γ; exact exists_threePoint_one
  exact exists_threePoint_of_pos_ne_one hγ hγ2 h

end D5.S3.Quantum.Matrix.StolarskyMean.ThreePoint
