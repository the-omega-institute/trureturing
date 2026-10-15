/- GID: D5/S3/QuantumBounds/RebitExclusionDistance
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/RebitExclusionDistance
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The minimum average trace distance of a rebit exclusion strategy is exactly 1/12. -/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

noncomputable section

open scoped BigOperators

namespace D5.S3.QuantumBounds.RebitExclusionDistance

/-- The target distribution P(y|x) = (1 − δ_xy)/3. -/
def target (x y : Fin 4) : ℝ := if x = y then 0 else 1 / 3
/-- A rebit strategy: four real states and a four-outcome real POVM. -/
def IsRebitStrategy (ρ E : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  (∀ x, (ρ x).PosSemidef ∧ (ρ x).trace = 1) ∧ (∀ y, (E y).PosSemidef) ∧ ∑ y, E y = 1
/-- The source's average trace distance d = (1/|X|) Σ_x (1/2) Σ_y |P(y|x) − P̃(y|x)|,
    with P̃(y|x) = tr(ρ_x E_y). -/
def dist (ρ E : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (1 / 4) * ∑ x, (1 / 2) * ∑ y, |target x y - ((ρ x) * (E y)).trace|
def claim : Prop :=
  IsLeast {d : ℝ | ∃ ρ E, IsRebitStrategy ρ E ∧ d = dist ρ E} (1 / 12)

private theorem state_relation (ρ : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ)
    (hρ : ∀ x, (ρ x).PosSemidef ∧ (ρ x).trace = 1) :
    ∃ w : Fin 4 → ℝ, (∑ x, w x • ρ x = 0) ∧ (∑ x, w x = 0) ∧ ∃ x, w x ≠ 0 := by
  classical
  let v : Fin 4 → Fin 3 → ℝ := fun x => ![ρ x 0 0, ρ x 0 1, ρ x 1 1]
  have hdep : ¬ LinearIndependent ℝ v := by
    intro hi
    have hc := hi.fintype_card_le_finrank
    norm_num only [Fintype.card_fin, Module.finrank_fin_fun] at hc
  obtain ⟨w, hw, hn⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have h00 := congrFun hw (0 : Fin 3)
  have h01 := congrFun hw (1 : Fin 3)
  have h11 := congrFun hw (2 : Fin 3)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h00 h01 h11
  change (∑ x, w x * ρ x 0 0) = 0 at h00
  change (∑ x, w x * ρ x 0 1) = 0 at h01
  change (∑ x, w x * ρ x 1 1) = 0 at h11
  have hsym (x : Fin 4) : ρ x 1 0 = ρ x 0 1 := by
    simpa only [star_trivial] using (hρ x).1.isHermitian.apply 0 1
  have hmat : ∑ x, w x • ρ x = 0 := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    fin_cases i <;> fin_cases j
    · exact h00
    · exact h01
    · change (∑ x, w x * ρ x 1 0) = 0
      simpa only [hsym] using h01
    · exact h11
  have hsum : ∑ x, w x = 0 := by
    have ht := congrArg Matrix.trace hmat
    simpa only [Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul,
      (hρ _).2, mul_one, Matrix.trace_zero] using ht
  exact ⟨w, hmat, hsum, hn⟩

private theorem relation_readout (ρ E : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ)
    (w : Fin 4 → ℝ) (hw : ∑ x, w x • ρ x = 0) (y : Fin 4) :
    ∑ x, w x * ((ρ x) * (E y)).trace = 0 := by
  have ht := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => (A * E y).trace) hw
  simpa only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, Matrix.zero_mul, Matrix.trace_zero] using ht

private theorem target_relation (w : Fin 4 → ℝ) (hw : ∑ x, w x = 0) (y : Fin 4) :
    ∑ x, w x * target x y = -w y / 3 := by
  have ht (x : Fin 4) : target x y = (1 / 3 : ℝ) - if x = y then 1 / 3 else 0 := by
    change (if x = y then 0 else (1 / 3 : ℝ)) = _
    split_ifs <;> ring
  simp only [ht, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw,
    zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

private theorem twice_max_le_l1 (w : Fin 4 → ℝ) (hw : ∑ x, w x = 0) (j : Fin 4) :
    2 * |w j| ≤ ∑ x, |w x| := by
  have hs : ∑ x ∈ Finset.univ.erase j, w x = -w j := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j), hw, zero_sub]
  have hb := Finset.abs_sum_le_sum_abs w (Finset.univ.erase j)
  rw [hs, abs_neg, Finset.sum_erase_eq_sub (Finset.mem_univ j)] at hb
  linarith

private theorem lower_bound (ρ E : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ)
    (h : IsRebitStrategy ρ E) : (1 / 12 : ℝ) ≤ dist ρ E := by
  classical
  obtain ⟨w, hmat, hsum, k, hk⟩ := state_relation ρ h.1
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun x => |w x|)
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin 4)).Nonempty)
  have hmax (x : Fin 4) : |w x| ≤ |w j| := hj x (Finset.mem_univ x)
  have hm : 0 < |w j| := (abs_pos.mpr hk).trans_le (hmax k)
  have hcol (y : Fin 4) :
      |w y| / 3 ≤ |w j| * ∑ x, |target x y - ((ρ x) * (E y)).trace| := by
    have heq : ∑ x, w x * (target x y - ((ρ x) * (E y)).trace) = -w y / 3 := by
      simp only [mul_sub, Finset.sum_sub_distrib, target_relation w hsum y,
        relation_readout ρ E w hmat y, sub_zero]
    calc
      |w y| / 3 = |∑ x, w x * (target x y - ((ρ x) * (E y)).trace)| := by
        rw [heq, abs_div, abs_neg]
        norm_num
      _ ≤ ∑ x, |w x * (target x y - ((ρ x) * (E y)).trace)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, |w j| * |target x y - ((ρ x) * (E y)).trace| := by
        apply Finset.sum_le_sum
        intro x _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hmax x) (abs_nonneg _)
      _ = |w j| * ∑ x, |target x y - ((ρ x) * (E y)).trace| :=
        (Finset.mul_sum _ _ _).symm
  have htotal := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => hcol y)
  simp only [div_eq_mul_inv] at htotal
  rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_comm] at htotal
  have hmass := twice_max_le_l1 w hsum j
  have herror : (2 / 3 : ℝ) ≤ ∑ x, ∑ y, |target x y - ((ρ x) * (E y)).trace| := by
    nlinarith
  change (1 / 12 : ℝ) ≤ (1 / 4) * ∑ x, (1 / 2) *
    ∑ y, |target x y - ((ρ x) * (E y)).trace|
  rw [← Finset.mul_sum]
  linarith

private def exampleStates : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ :=
  ![!![1, 0; 0, 0],
    (1 / 4 : ℝ) • !![1, -Real.sqrt 3; -Real.sqrt 3, 3],
    (1 / 4 : ℝ) • !![1, Real.sqrt 3; Real.sqrt 3, 3],
    (1 / 4 : ℝ) • !![1, Real.sqrt 3; Real.sqrt 3, 3]]

private def exampleEffects : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ :=
  ![(1 / 9 : ℝ) • !![0, 0; 0, 4],
    (1 / 9 : ℝ) • !![3, Real.sqrt 3; Real.sqrt 3, 1],
    (1 / 9 : ℝ) • !![3, -Real.sqrt 3; -Real.sqrt 3, 1],
    (1 / 3 : ℝ) • 1]

private theorem states_eq (x : Fin 4) : exampleStates x =
    ![!![1, 0; 0, 0],
      (1 / 4 : ℝ) • !![1, -Real.sqrt 3; -Real.sqrt 3, 3],
      (1 / 4 : ℝ) • !![1, Real.sqrt 3; Real.sqrt 3, 3],
      (1 / 4 : ℝ) • !![1, Real.sqrt 3; Real.sqrt 3, 3]] x := rfl

private theorem effects_eq (y : Fin 4) : exampleEffects y =
    ![(1 / 9 : ℝ) • !![0, 0; 0, 4],
      (1 / 9 : ℝ) • !![3, Real.sqrt 3; Real.sqrt 3, 1],
      (1 / 9 : ℝ) • !![3, -Real.sqrt 3; -Real.sqrt 3, 1],
      (1 / 3 : ℝ) • 1] y := rfl

private theorem target_eq (x y : Fin 4) :
    target x y = if x = y then 0 else 1 / 3 := rfl

private theorem sqrt_three_mul_self : Real.sqrt 3 * Real.sqrt 3 = 3 :=
  Real.mul_self_sqrt (by norm_num)

private theorem scaled_outer_psd (a b c : ℝ) (hc : 0 ≤ c) :
    (c • (!![a * a, a * b; b * a, b * b] : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef := by
  convert (Matrix.posSemidef_vecMulVec_self_star (![a, b] : Fin 2 → ℝ)).smul hc using 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec]

private theorem explicit_strategy : IsRebitStrategy exampleStates exampleEffects := by
  change (∀ x, (exampleStates x).PosSemidef ∧ (exampleStates x).trace = 1) ∧
    (∀ y, (exampleEffects y).PosSemidef) ∧ ∑ y, exampleEffects y = 1
  refine ⟨?_, ?_, ?_⟩
  · intro x
    constructor
    · rw [states_eq]
      fin_cases x
      · change (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef
        simpa using scaled_outer_psd 1 0 1 (by norm_num)
      · change ((1 / 4 : ℝ) •
          (!![1, -Real.sqrt 3; -Real.sqrt 3, 3] : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef
        simpa only [one_mul, mul_one, neg_mul_neg, sqrt_three_mul_self] using
          scaled_outer_psd 1 (-Real.sqrt 3) (1 / 4) (by norm_num)
      · change ((1 / 4 : ℝ) •
          (!![1, Real.sqrt 3; Real.sqrt 3, 3] : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef
        simpa only [one_mul, mul_one, sqrt_three_mul_self] using
          scaled_outer_psd 1 (Real.sqrt 3) (1 / 4) (by norm_num)
      · change ((1 / 4 : ℝ) •
          (!![1, Real.sqrt 3; Real.sqrt 3, 3] : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef
        simpa only [one_mul, mul_one, sqrt_three_mul_self] using
          scaled_outer_psd 1 (Real.sqrt 3) (1 / 4) (by norm_num)
    · rw [states_eq]
      fin_cases x <;> norm_num [Matrix.trace_smul, Matrix.trace_fin_two]
  · intro y
    rw [effects_eq]
    fin_cases y
    · change ((1 / 9 : ℝ) • (!![0, 0; 0, 4] : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef
      simpa only [zero_mul, mul_zero, show (2 : ℝ) * 2 = 4 by norm_num] using
        scaled_outer_psd 0 2 (1 / 9) (by norm_num)
    · change ((1 / 9 : ℝ) •
        (!![3, Real.sqrt 3; Real.sqrt 3, 1] : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef
      simpa only [one_mul, mul_one, sqrt_three_mul_self] using
        scaled_outer_psd (Real.sqrt 3) 1 (1 / 9) (by norm_num)
    · change ((1 / 9 : ℝ) •
        (!![3, -Real.sqrt 3; -Real.sqrt 3, 1] : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef
      simpa only [neg_mul_neg, one_mul, mul_one, sqrt_three_mul_self] using
        scaled_outer_psd (-Real.sqrt 3) 1 (1 / 9) (by norm_num)
    · exact (Matrix.PosSemidef.one).smul (by norm_num : (0 : ℝ) ≤ 1 / 3)
  · simp only [effects_eq, Fin.sum_univ_succ, Fin.sum_univ_zero]
    change (1 / 9 : ℝ) • (!![0, 0; 0, 4] : Matrix (Fin 2) (Fin 2) ℝ) +
      ((1 / 9 : ℝ) • !![3, Real.sqrt 3; Real.sqrt 3, 1] +
        ((1 / 9 : ℝ) • !![3, -Real.sqrt 3; -Real.sqrt 3, 1] +
          ((1 / 3 : ℝ) • 1 + 0))) = 1
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]

private theorem explicit_readout (x y : Fin 4) :
    (exampleStates x * exampleEffects y).trace = target (if x = 3 then 2 else x) y := by
  rw [states_eq, effects_eq, target_eq]
  fin_cases x <;> fin_cases y <;>
    norm_num [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, Matrix.one_apply, Fin.ext_iff, Matrix.cons_val_succ',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one] <;>
    nlinarith [sqrt_three_mul_self]

private theorem explicit_distance : dist exampleStates exampleEffects = (1 / 12 : ℝ) := by
  change (1 / 4 : ℝ) * ∑ x, (1 / 2) *
    ∑ y, |target x y - (exampleStates x * exampleEffects y).trace| = 1 / 12
  simp only [explicit_readout, target_eq, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [Fin.ext_iff]

/-- The minimum average trace distance over all rebit strategies is exactly 1/12. -/
theorem result : claim := by
  change IsLeast {d : ℝ | ∃ ρ E, IsRebitStrategy ρ E ∧ d = dist ρ E} (1 / 12)
  refine ⟨?_, ?_⟩
  · exact ⟨exampleStates, exampleEffects, explicit_strategy, explicit_distance.symm⟩
  · rintro d ⟨ρ, E, h, rfl⟩
    exact lower_bound ρ E h

end D5.S3.QuantumBounds.RebitExclusionDistance
