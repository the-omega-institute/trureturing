/- GID: D5/S3/Geometry/Lorentz/PlebanskiSectors4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/PlebanskiSectors4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coframe normal forms, chiral Plebański sectors, and the simplicity Jacobian. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Geometry.Lorentz.Urbantke
import D5.S3.Geometry.Lorentz.PlebanskiCoframe
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Algebraic simplicity of triples in the oriented Urbantke pair basis. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Geometry.Lorentz.PlebanskiSectors4D

open Matrix Urbantke
open scoped Matrix
universe u

open Omega.Geometry.PlebanskiCoframe

open private W_symm W_sq urbantke_mul shear det_shear exterior_map exterior_smul
  exterior_det_ne pairLeft pairRight from D5.S3.Geometry.Lorentz.Urbantke

def gramScalar {K : Type u} [Field K] (B : FormTriple K) : K :=
  (wedgeGram B).trace / 3

def Simple {K : Type u} [Field K] (B : FormTriple K) : Prop :=
  wedgeGram B = gramScalar B • (1 : M3 K)

private def five {K : Type u} [Ring K] (S : M3 K) : Fin 5 → K :=
  ![S 0 1, S 0 2, S 1 2, S 0 0 - S 2 2, S 1 1 - S 2 2]

section Algebra

variable {K : Type u} [Field K] [CharZero K]

private theorem simple_of_gram (B : FormTriple K) (c : K)
    (h : wedgeGram B = c • (1 : M3 K)) : Simple B := by
  simp only [Simple, gramScalar, h, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
  congr 1
  ring

theorem simple_iff_five_eq_zero (B : FormTriple K) :
    Simple B ↔ five (wedgeGram B) = 0 := by
  constructor
  · intro h
    unfold Simple at h
    rw [h]
    funext i
    fin_cases i <;> simp [five]
  · intro h
    apply simple_of_gram B (wedgeGram B 2 2)
    have hs : (wedgeGram B)ᵀ = wedgeGram B := by
      simp [wedgeGram, transpose_mul, W_symm, Matrix.mul_assoc]
    have h01 : wedgeGram B 0 1 = 0 := congrFun h 0
    have h02 : wedgeGram B 0 2 = 0 := congrFun h 1
    have h12 : wedgeGram B 1 2 = 0 := congrFun h 2
    have h00 : wedgeGram B 0 0 = wedgeGram B 2 2 := sub_eq_zero.mp (congrFun h 3)
    have h11 : wedgeGram B 1 1 = wedgeGram B 2 2 := sub_eq_zero.mp (congrFun h 4)
    have h10 : wedgeGram B 1 0 = 0 := (congrFun (congrFun hs 0) 1).trans h01
    have h20 : wedgeGram B 2 0 = 0 := (congrFun (congrFun hs 0) 2).trans h02
    have h21 : wedgeGram B 2 1 = 0 := (congrFun (congrFun hs 1) 2).trans h12
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h11, h01, h02, h12, h10, h20, h21]

/-- The linear coefficient of the five simplicity equations at a triple. -/
def simplicityDeriv (B : FormTriple K) : FormTriple K →ₗ[K] (Fin 5 → K) where
  toFun X := five (Bᵀ * W K * X + Xᵀ * W K * B)
  map_add' X Y := by
    simp only [transpose_add, Matrix.mul_add, Matrix.add_mul]
    funext i
    fin_cases i <;> simp [five, Matrix.add_apply] <;> ring
  map_smul' a X := by
    simp only [transpose_smul, Matrix.mul_smul, Matrix.smul_mul, ← smul_add,
      RingHom.id_apply]
    funext i
    fin_cases i <;> simp [five, Matrix.smul_apply] <;> ring
omit [CharZero K] in
theorem simplicity_expansion (B X : FormTriple K) (t : K) :
    five (wedgeGram (B + t • X)) =
      five (wedgeGram B) + t • simplicityDeriv B X + t ^ 2 • five (wedgeGram X) := by
  simp only [wedgeGram, transpose_add, transpose_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul]
  funext i
  fin_cases i <;>
    simp [five, simplicityDeriv, Matrix.add_apply, Matrix.smul_apply] <;> ring

theorem simplicityDeriv_surjective (B : FormTriple K)
    (hB : LinearIndependent K B.col) : Function.Surjective (simplicityDeriv B) := by
  obtain ⟨L, hL⟩ := mulVec_surjective_iff_exists_right_inverse.mp
    (show Function.Surjective Bᵀ.mulVec from hB.mulVec_surjective)
  intro y
  let S : M3 K := !![y 3, y 0, y 1; y 0, y 4, y 2; y 1, y 2, 0]
  have hs : Sᵀ = S := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  let X := (1 / 2 : K) • (W K * L * S)
  have hx : Bᵀ * W K * X = (1 / 2 : K) • S := by
    simp only [X, Matrix.mul_smul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (W K) (W K), W_sq, Matrix.one_mul,
      ← Matrix.mul_assoc Bᵀ L, hL, Matrix.one_mul]
  have ht : Xᵀ * W K * B = (1 / 2 : K) • S := by
    simpa only [transpose_mul, W_symm, transpose_transpose, Matrix.mul_assoc,
      transpose_smul, hs] using congrArg Matrix.transpose hx
  refine ⟨X, ?_⟩
  change five (Bᵀ * W K * X + Xᵀ * W K * B) = y
  rw [hx, ht, ← add_smul]
  have htwo : (1 / 2 : K) + 1 / 2 = 1 := by ring
  rw [htwo, one_smul]
  funext i
  fin_cases i <;> simp [five, S]

theorem simplicity_jacobian_rank (B : FormTriple K) (hB : LinearIndependent K B.col) :
    Module.finrank K (simplicityDeriv B).range = 5 ∧
      Module.finrank K (simplicityDeriv B).ker = 13 := by
  have hr := LinearMap.range_eq_top.mpr (simplicityDeriv_surjective B hB)
  have hdim := (simplicityDeriv B).finrank_range_add_finrank_ker
  rw [hr] at hdim ⊢
  simp [Module.finrank_matrix, Fintype.card_sum] at hdim ⊢
  omega

omit [CharZero K] in
theorem wedgeGram_action (A : M4 K) (B : FormTriple K) :
    wedgeGram (action A B) = A.det • wedgeGram B := by
  simp only [wedgeGram, action, transpose_mul, ← Matrix.mul_assoc]
  rw [Matrix.mul_assoc Bᵀ _ (W K), Matrix.mul_assoc Bᵀ _ (exteriorSquare A),
    exterior_wedge_congruence, Matrix.mul_smul, Matrix.smul_mul]

omit [CharZero K] in
theorem urbantke_action (A : M4 K) (B : FormTriple K) :
    urbantke (action A B) = A.det • (A * urbantke B * Aᵀ) := by
  simp only [urbantke_cyclic, cyclicCubic, cubicTerm_action, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, ← smul_add, ← smul_sub]
  exact smul_comm _ _ _

omit [CharZero K] in
theorem simplicity_neg (B : FormTriple K) :
    wedgeGram (-B) = wedgeGram B ∧ urbantke (-B) = -urbantke B := by
  refine ⟨by simp [wedgeGram], ?_⟩
  have h : B * -(1 : M3 K) = -B := by simp
  rw [← h, urbantke_mul, det_neg, det_one]
  norm_num

theorem degenerate_simplicity_witnesses :
    wedgeGram (model (0 : K)) = 0 ∧ (urbantke (model (0 : K))).rank = 1 ∧
      (spatial : FormTriple K) ≠ 0 ∧ wedgeGram (spatial : FormTriple K) = 0 ∧
      urbantke (spatial : FormTriple K) = 0 := by
  refine ⟨by simp [wedgeGram_model], ?_, ?_, by simp [spatial, wedgeGram_graph], ?_⟩
  · classical
    rw [urbantke_model, modelMetric, Matrix.rank_diagonal]
    have hs (i : Fin 4) : (![1, (0 : K) ^ 2, 0 ^ 2, 0 ^ 2] : Fin 4 → K) i ≠ 0 ↔ i = 0 := by
      fin_cases i <;> simp
    let e : {i : Fin 4 // (![1, (0 : K) ^ 2, 0 ^ 2, 0 ^ 2] : Fin 4 → K) i ≠ 0} ≃ Fin 1 :=
      { toFun := fun _ => 0
        invFun := fun _ => ⟨0, (hs 0).2 rfl⟩
        left_inv := fun i => Subtype.ext ((hs i.1).1 i.2).symm
        right_inv := fun _ => Subsingleton.elim _ _ }
    simpa using Fintype.card_congr e
  · intro h
    have hentry : (1 : K) = 0 := congrFun (congrFun h (.inr 0)) 0
    exact one_ne_zero hentry
  · exact urbantke_spatial

private theorem simple_nondegenerate_iff (B : FormTriple K) :
    (Simple B ∧ (wedgeGram B).det ≠ 0) ↔ ∃ c : K, c ≠ 0 ∧ wedgeGram B = c • 1 := by
  constructor
  · rintro ⟨h, hd⟩
    exact ⟨gramScalar B, fun hc => hd (by rw [h, hc, zero_smul, det_zero]), h⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨simple_of_gram B c h, by simp [h, hc]⟩

private theorem electric_chart (B : FormTriple K) (hB : (urbantke B).det ≠ 0) :
    ∃ x y z : K, (electric (action (topShear x y z) B)).det ≠ 0 := by
  by_contra! h
  let U := urbantke B
  have hs : Uᵀ = U := (urbantke_polynomial_identities B).1
  have hz (x y z : K) : (topShear x y z * U * (topShear x y z)ᵀ) 0 0 = 0 := by
    have he := h x y z
    rw [← urbantke_electric, urbantke_action] at he
    simpa [topShear, det_coordinateShear] using he
  simp only [Matrix.mul_apply] at hz
  simp [topShear, coordinateShear, Fin.sum_univ_succ] at hz
  have h00 := hz 0 0 0
  have hxp := hz 1 0 0
  have hxm := hz (-1) 0 0
  have hyp := hz 0 1 0
  have hym := hz 0 (-1) 0
  have hzp := hz 0 0 1
  have hzm := hz 0 0 (-1)
  have sym (i j : Fin 4) : U j i = U i j := congrFun (congrFun hs i) j
  have e00 : U 0 0 = 0 := by linear_combination h00
  have e01 : U 0 1 = 0 := by linear_combination (hxp - hxm - 2 * sym 0 1) / 4
  have e02 : U 0 2 = 0 := by linear_combination (hyp - hym - 2 * sym 0 2) / 4
  have e03 : U 0 3 = 0 := by linear_combination (hzp - hzm - 2 * sym 0 3) / 4
  apply hB (det_eq_zero_of_row_eq_zero 0 ?_)
  intro j
  fin_cases j
  exacts [e00, e01, e02, e03]
private theorem chart_factor (B : FormTriple K) (c : K)
    (hQ : wedgeGram B = c • (1 : M3 K)) (hE : (electric B).det ≠ 0) :
    ∃ F : M4 K, F.det = (electric B).det ∧
      B = action F (model (c / (2 * (electric B).det))) := by
  let E := electric B
  let A := block 1 E
  let C := block 1 E⁻¹
  let T := action C B
  let z := c / (2 * E.det)
  have hA : A.det = E.det := by simp [A, det_block]
  have hC : C.det = E.det⁻¹ := by simp [C, det_block, det_nonsing_inv, Ring.inverse_eq_inv]
  have hu := isUnit_iff_ne_zero.mpr hE
  have hAC : A * C = 1 := by
    calc
      _ = block 1 (E * E⁻¹) := by
        ext i j
        simp only [Matrix.mul_apply]
        fin_cases i <;> fin_cases j <;> simp [A, C, block, Matrix.mul_apply, Fin.sum_univ_succ]
      _ = _ := by
        rw [Matrix.mul_nonsing_inv E hu]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [block]
  have hT : T = graph 1 (magnetic T) := by
    have hb : T = graph 1 ((E⁻¹).adjugateᵀ * magnetic B) := by
      dsimp [T, C]
      conv_lhs => rw [← graph_blocks B, act_block_graph, one_smul, nonsing_inv_mul _ hu]
    rw [hb]
    rfl
  have hGram : magnetic T + (magnetic T)ᵀ = (2 * z) • (1 : M3 K) := by
    calc
      _ = wedgeGram T := by conv_rhs => rw [hT, wedgeGram_graph, transpose_one, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by
        change wedgeGram (action C B) = _
        rw [wedgeGram_action, hQ, hC, smul_smul]
        congr 1
        dsimp [z]
        field_simp
  let L := (shear (magnetic T))ᵀ
  have hL : L.det = 1 := (det_transpose _).trans (det_shear _)
  refine ⟨A * L, by rw [det_mul, hL, mul_one, hA], ?_⟩
  rw [action_mul, show action L (model z) = T from (act_shear z _ hGram).trans hT.symm,
    show T = action C B from rfl, ← action_mul, hAC, action_one]

theorem exists_graph_model (B : FormTriple K) :
    (Simple B ∧ (wedgeGram B).det ≠ 0) ↔
      ∃ (A : M4 K) (z : K), A.det ≠ 0 ∧ z ≠ 0 ∧ B = action A (model z) := by
  rw [simple_nondegenerate_iff]
  constructor
  · rintro ⟨c, hc, hQ⟩
    have hU := (urbantke_nondegenerate_iff_and_chiral_star B).1.mpr
      (show (wedgeGram B).det ≠ 0 by simp [hQ, hc])
    obtain ⟨x, y, z, he⟩ := electric_chart B hU
    let F := topShear x y z
    have hf : F.det = 1 := by simp [F, topShear, det_coordinateShear]
    obtain ⟨C, hC, hB⟩ := chart_factor (action F B) c (by rw [wedgeGram_action, hf, one_smul, hQ]) he
    refine ⟨F⁻¹ * C, c / (2 * (electric (action F B)).det), ?_,
      div_ne_zero hc (mul_ne_zero (by norm_num) he), ?_⟩
    · rw [det_mul, det_nonsing_inv, hf, Ring.inverse_eq_inv, inv_one, one_mul, hC]
      exact he
    · rw [action_mul, ← hB, ← action_mul, nonsing_inv_mul _ (show IsUnit F.det by rw [hf]; exact isUnit_one), action_one]
  · rintro ⟨A, z, ha, hz, rfl⟩
    exact ⟨A.det * (2 * z), by simp [ha, hz], by rw [wedgeGram_action, wedgeGram_model, smul_smul]⟩

private theorem model_action_det (z z' : K) (hz : z ≠ 0) (A : M4 K)
    (h : action A (model z) = model z') : A.det = z' / z := by
  have hq := congrArg (fun B : FormTriple K => wedgeGram B 0 0) h
  simp only [wedgeGram_action, wedgeGram_model, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply_eq, mul_one] at hq
  apply (eq_div_iff hz).2
  linear_combination hq / 2

theorem model_orbit_iff (z z' : K) (hz : z ≠ 0) (hz' : z' ≠ 0) :
    (∃ A : M4 K, A.det ≠ 0 ∧ action A (model z) = model z') ↔
      ∃ q : Fin 4 → K, (∑ i, q i ^ 2) = z' / z := by
  constructor
  · rintro ⟨A, _, h⟩
    let r := z' / z
    have hu := congrArg (fun B : FormTriple K => urbantke B 0 0) h
    rw [urbantke_action, model_action_det z z' hz A h, urbantke_model, urbantke_model] at hu
    refine ⟨![r * A 0 0, r * z * A 0 1, r * z * A 0 2, r * z * A 0 3], ?_⟩
    change r • (A * modelMetric z * Aᵀ) 0 0 = 1 at hu
    simp [modelMetric, Matrix.mul_apply, Fin.sum_univ_succ] at hu
    change _ = r
    simp [Fin.sum_univ_succ]
    linear_combination r * hu
  · rintro ⟨q, hq⟩
    let r := z' / z
    have hr : r ≠ 0 := div_ne_zero hz' hz
    let A := dilate z' * (r⁻¹ • quaternionRight q) * dilate z⁻¹
    have h : action A (model z) = model z' := by
      change action (dilate z' * (r⁻¹ • quaternionRight q) * dilate z⁻¹) (model z) = _
      simp only [action_mul, dilate_model, inv_mul_cancel₀ hz, action_smul, action_scale,
        quaternion_model, hq, ← show r = z' / z from rfl, mul_one, smul_smul]
      have hs : z⁻¹ * (r⁻¹ ^ 2 * r * z') = 1 := by
        dsimp [r]
        field_simp
      rw [hs, one_smul]
    exact ⟨A, (model_action_det z z' hz A h).symm ▸ hr, h⟩

end Algebra

/-- The first Boolean records overall sign and the second records chirality. -/
def signValue {K : Type u} [Ring K] (p : Bool) : K := if p then 1 else -1

def sectorModel {K : Type u} [Field K] (z : K) (overall sd : Bool) : FormTriple K :=
  (signValue overall : K) • model (z * signValue sd)
private theorem sector_gram {K : Type u} [Field K] (z : K) (overall sd : Bool) :
    wedgeGram (sectorModel z overall sd) = (2 * (z * signValue sd)) • (1 : M3 K) := by
  cases overall <;> simp only [sectorModel, signValue, Bool.false_eq_true, ite_false, ite_true,
    neg_one_smul, one_smul, (simplicity_neg (model (z * (if sd = true then 1 else -1)))).1,
    wedgeGram_model]

theorem euclidean_model_iff (B : FormTriple ℝ) :
    (Simple B ∧ (wedgeGram B).det ≠ 0) ↔
      ∃ (A : M4 ℝ) (overall sd : Bool), 0 < A.det ∧
        B = action A (sectorModel 1 overall sd) := by
  constructor
  · intro h
    obtain ⟨A, z, hA, hz, hB⟩ := (exists_graph_model B).1 h
    have positive_rep (t : ℝ) (ht : t ≠ 0) :
        ∃ (C : M4 ℝ) (sd : Bool), 0 < C.det ∧
          action C (model (signValue sd : ℝ)) = model t := by
      let sd := decide (0 < t)
      have hs : (signValue sd : ℝ) ≠ 0 := by cases sd <;> norm_num [signValue]
      have hp : 0 < t / (signValue sd : ℝ) := by
        rcases lt_or_gt_of_ne ht with hn | hp
        · simp [sd, signValue, not_lt.mpr hn.le]
          simpa only [div_neg, div_one] using neg_pos.mpr hn
        · simp [sd, signValue, hp]
      have hq : ∃ q : Fin 4 → ℝ, (∑ i, q i ^ 2) = t / (signValue sd : ℝ) :=
        ⟨![Real.sqrt (t / signValue sd), 0, 0, 0], by
          simp [Fin.sum_univ_succ, Real.sq_sqrt hp.le]⟩
      obtain ⟨C, _, hC⟩ := (model_orbit_iff _ _ hs ht).2 hq
      exact ⟨C, sd, (model_action_det _ _ hs _ hC).symm ▸ hp, hC⟩
    rcases lt_or_gt_of_ne hA with hn | hp
    · obtain ⟨C, sd, hC, hc⟩ := positive_rep (-z) (neg_ne_zero.mpr hz)
      refine ⟨A * block (-1) 1 * C, false, sd, ?_, ?_⟩
      · simpa [det_mul, det_block] using mul_pos (neg_pos.mpr hn) hC
      · have hs : sectorModel (1 : ℝ) false sd = (-1 : ℝ) • model (signValue sd) := by
          rw [sectorModel, one_mul]; rfl
        rw [hB, action_mul, action_mul, hs, action_smul, hc, action_smul, reflected_model]
        simp
    · obtain ⟨C, sd, hC, hc⟩ := positive_rep z hz
      exact ⟨A * C, true, sd, by rw [det_mul]; exact mul_pos hp hC,
        by simpa [hB, sectorModel, signValue, action_mul] using congrArg (action A) hc.symm⟩
  · rintro ⟨A, overall, sd, hA, rfl⟩
    rw [simple_nondegenerate_iff, wedgeGram_action, sector_gram, smul_smul]
    have hs : (signValue sd : ℝ) ≠ 0 := by cases sd <;> norm_num [signValue]
    exact ⟨_, mul_ne_zero hA.ne' (mul_ne_zero (by norm_num) (by simpa using hs)), rfl⟩

def orientedIsometry (g A : M4 ℝ) : Prop := A.det = 1 ∧ A * g * Aᵀ = g
private theorem sector_cubic {K : Type u} [Field K] [CharZero K] (z : K) (overall sd : Bool) :
    urbantke (sectorModel z overall sd) = (signValue overall : K) • modelMetric z := by
  cases overall <;> cases sd <;>
    simp [sectorModel, signValue, modelMetric, urbantke_model, (simplicity_neg (model (-z))).2,
      (simplicity_neg (model z)).2]

/-- The labels classify the represented triples for a fixed metric and positive coframe orientation. -/
theorem fixed_metric_sector_orbit_iff {K : Type u} [Field K] [CharZero K] (f : ℝ →+* K)
    (z : K) (hz : z ≠ 0) (g₀ g A C : M4 ℝ) (hg₀ : f.mapMatrix g₀ = modelMetric z)
    (hg : g.det ≠ 0) (ha : 0 < A.det) (hc : 0 < C.det)
    (hA : A * g₀ * Aᵀ = g) (hC : C * g₀ * Cᵀ = g)
    (τ σ τ' σ' : Bool) :
    (∃ L : M4 ℝ, orientedIsometry g L ∧
      action (f.mapMatrix L) (action (f.mapMatrix A) (sectorModel z τ σ)) =
        action (f.mapMatrix C) (sectorModel z τ' σ')) ↔ τ = τ' ∧ σ = σ' := by
  have hd : A.det = C.det := by
    have h := congrArg Matrix.det (hA.trans hC.symm)
    simp only [det_mul, det_transpose] at h
    have h₀ : g₀.det ≠ 0 := by
      intro h₀
      exact hg (by rw [← hA, det_mul, det_mul, h₀, mul_zero, zero_mul])
    have hsq : A.det ^ 2 = C.det ^ 2 := by
      apply mul_right_cancel₀ h₀
      linear_combination h
    nlinarith
  have congruence (P : M4 ℝ) (hP : P * g₀ * Pᵀ = g) :
      f.mapMatrix P * modelMetric z * (f.mapMatrix P)ᵀ = f.mapMatrix g := by
    simpa only [map_mul, ← hg₀, RingHom.mapMatrix_apply, transpose_map]
      using congrArg f.mapMatrix hP
  constructor
  · rintro ⟨L, ⟨hL, hiso⟩, h⟩
    have hP : (L * A) * g₀ * (L * A)ᵀ = g := by
      calc
        _ = L * (A * g₀ * Aᵀ) * Lᵀ := by rw [transpose_mul]; simp [Matrix.mul_assoc]
        _ = g := hA ▸ hiso
    rw [← action_mul, ← map_mul] at h
    have he : (f.mapMatrix (L * A)).det = (f.mapMatrix C).det := by
      rw [← RingHom.map_det, ← RingHom.map_det, det_mul, hL, one_mul, hd]
    have hn : (f.mapMatrix C).det ≠ 0 := by
      rw [← RingHom.map_det]
      exact fun h => (ne_of_gt hc) (f.injective (h.trans f.map_zero.symm))
    have hq := congrArg (fun B : FormTriple K => wedgeGram B 0 0) h
    simp only [wedgeGram_action, sector_gram, he, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_eq, mul_one] at hq
    have hu := congrArg urbantke h
    simp only [urbantke_action, sector_cubic, Matrix.mul_smul, Matrix.smul_mul, he,
      congruence _ hP, congruence _ hC, smul_smul] at hu
    have hg' : f.mapMatrix g ≠ 0 := by
      intro hzero
      apply hg
      have hdet := congrArg Matrix.det hzero
      rw [det_zero, ← RingHom.map_det] at hdet
      exact f.injective (hdet.trans f.map_zero.symm)
    refine ⟨?_, ?_⟩
    · have hτ := mul_left_cancel₀ hn ((smul_left_injective K hg') hu)
      cases τ <;> cases τ' <;> first | rfl | exfalso; norm_num [signValue] at hτ
    · have hq' := mul_left_cancel₀ hn hq
      simp only [← mul_assoc] at hq'
      have hσ := mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : K) ≠ 0) hz) hq'
      cases σ <;> cases σ' <;> first | rfl | exfalso; norm_num [signValue] at hσ
  · rintro ⟨rfl, rfl⟩
    let L := C * A⁻¹
    have hLA : L * A = C := nonsing_inv_mul_cancel_right _ _ (isUnit_iff_ne_zero.mpr ha.ne')
    refine ⟨L, ⟨?_, ?_⟩, ?_⟩
    · have h := congrArg Matrix.det hLA
      rw [det_mul, ← hd] at h
      exact mul_right_cancel₀ ha.ne' (h.trans (one_mul A.det).symm)
    · calc
        L * g * Lᵀ = (L * A) * g₀ * (L * A)ᵀ := by rw [← hA]; simp only [transpose_mul, Matrix.mul_assoc]
        _ = g := by rw [hLA, hC]
    · rw [← action_mul, ← map_mul, hLA]

abbrev realCast := Complex.ofRealHom

private theorem lorentz_metric_data (B : FormTriple ℂ) (hQ : Simple B)
    (hnd : (wedgeGram B).det ≠ 0) (horth : Bᵀ * W ℂ * B.map star = 0)
    (hU : (urbantke B).map star = urbantke B) (hre : (gramScalar B).re = 0) :
    ∃ (A : M4 ℝ) (overall sd : Bool), 0 < A.det ∧
      gramScalar B = (A.det : ℂ) * (2 * (Complex.I * signValue sd)) ∧
      urbantke B = ((A.det : ℂ) * signValue overall) •
        (realCast.mapMatrix A * modelMetric Complex.I * (realCast.mapMatrix A)ᵀ) := by
  let c := gramScalar B
  change wedgeGram B = c • _ at hQ
  have him : c.im ≠ 0 := by
    intro h
    have hzero : c = 0 := Complex.ext hre h
    exact hnd (by simp [hQ, hzero])
  let v := |c.im| / 2
  let sd : Bool := decide (0 < c.im)
  have hv : 0 < v := by dsimp [v]; positivity
  have hphase : c = (v : ℂ) * (2 * (Complex.I * signValue sd)) := by
    rcases lt_or_gt_of_ne him with hn | hp
    · apply Complex.ext <;> simp [hre, c, sd, signValue, not_lt.mpr hn.le, v, abs_of_neg hn, Complex.mul_re, Complex.mul_im]
    · apply Complex.ext <;> simp [hre, c, sd, signValue, hp, v, abs_of_pos hp, Complex.mul_re, Complex.mul_im]
  obtain ⟨g₀, l, _, hsym, _, hrep, _⟩ := urbantke_lorentz_reality B hnd horth
  let g : M4 ℝ := (urbantke B).map Complex.re
  have hg : realCast.mapMatrix g = urbantke B :=
    Matrix.ext fun i j => Complex.conj_eq_iff_re.mp (congrArg (fun M : M4 ℂ => M i j) hU)
  have hgs : gᵀ = g := by
    have h : (urbantke B)ᵀ = urbantke B := by
      rw [hrep, transpose_smul]
      exact congrArg (fun M => l • realCast.mapMatrix M) hsym
    exact congrArg (fun M : M4 ℂ => M.map Complex.re) h
  have hpow : (Complex.I * (signValue sd : ℂ)) ^ 6 = -1 := by
    rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul]
    cases sd <;> norm_num [signValue, neg_sq, Complex.I_sq]
  have hdet : g.det = -v ^ 6 := by
    have h := (urbantke_polynomial_identities B).2.1
    rw [← hg, ← realCast.map_det, hQ, det_smul, det_one, Fintype.card_fin, mul_one, hphase,
      ← pow_mul, show (3 : ℕ) * 2 = 6 by decide, mul_pow, mul_pow, hpow] at h
    change (g.det : ℂ) = _ at h
    exact_mod_cast (show (g.det : ℂ) = -(v : ℂ) ^ 6 by rw [h]; ring)
  have hd : (v⁻¹ • g).det = -v ^ 2 := by rw [det_smul, Fintype.card_fin, hdet]; field_simp
  obtain ⟨A, overall, ha, hA⟩ := signed_lorentz_factor (v⁻¹ • g)
    (by rw [transpose_smul, hgs]) (by rw [hd]; exact neg_neg_of_pos (pow_pos hv 2))
  have hA_det : A.det = v := by
    have h := congrArg Matrix.det hA
    cases overall <;> norm_num [hd, lorentzMetric, det_neg, det_diagonal, Fin.prod_univ_four,
      det_mul, det_transpose] at h <;> nlinarith
  have h := congrArg (fun M : M4 ℝ => v • M) hA
  have hscaled : g = ((v * (signValue overall : ℝ)) : ℝ) • (A * lorentzMetric * Aᵀ) := by
    simpa [smul_smul, hv.ne', signValue] using h
  refine ⟨A, overall, sd, ha, hA_det.symm ▸ hphase, ?_⟩
  rw [← hg, hscaled, hA_det]
  have hm := Matrix.map_smul' realCast (v * (signValue overall : ℝ))
    (A * lorentzMetric * Aᵀ) (map_mul realCast)
  have ht : realCast.mapMatrix Aᵀ = (realCast.mapMatrix A)ᵀ := rfl
  simpa [← RingHom.mapMatrix_apply, map_mul, lorentzMetric_model, ht, signValue] using hm

private theorem lorentz_lift (z : ℂ) (hz : z = Complex.I ∨ z = -Complex.I)
    (R : M3 ℂ) (ho : Rᵀ * R = 1) (hd : R.det = 1) :
    ∃ A : M4 ℝ, A.det = 1 ∧ action (Complex.ofRealHom.mapMatrix A) (model z) = model z * R := by
  obtain ⟨A, hAct⟩ := exists_real_coframe_rotation z hz R ho hd
  refine ⟨A, ?_, hAct⟩
  have hz₀ : z ≠ 0 := by rcases hz with rfl | rfl <;> simp
  have hgram : wedgeGram (model z * R) = wedgeGram (model z) := by
    calc
      _ = Rᵀ * wedgeGram (model z) * R := by simp [wedgeGram, transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [wedgeGram_model, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ho]
  have h := congrArg (fun B : FormTriple ℂ => wedgeGram B 0 0) hAct
  simp only [wedgeGram_action, hgram, wedgeGram_model, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply_eq, mul_one, ← RingHom.map_det] at h
  exact Complex.ofReal_injective (mul_right_cancel₀ (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hz₀)
    (h.trans (one_mul _).symm))

def lorentzianReal (B : FormTriple ℂ) : Prop :=
  Bᵀ * W ℂ * B.map star = 0 ∧ (urbantke B).map star = urbantke B ∧ (gramScalar B).re = 0

private theorem lorentz_sector_mixed (overall sd : Bool) :
    let S := sectorModel Complex.I overall sd
    Sᵀ * W ℂ * S.map star = 0 := by
  cases overall <;> cases sd <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [sectorModel, signValue, model, graph, W, Matrix.mul_apply, Matrix.one_apply,
      Fintype.sum_sum_type, smul_eq_mul]

private theorem phase_of_lorentz_model (A : M4 ℝ) (overall sd : Bool) (hA : 0 < A.det) :
    let B := action (realCast.mapMatrix A) (sectorModel Complex.I overall sd)
    Simple B ∧ (wedgeGram B).det ≠ 0 ∧ Bᵀ * W ℂ * B.map star = 0 ∧
      (urbantke B).map star = urbantke B ∧ (gramScalar B).re = 0 := by
  dsimp only
  let F := realCast.mapMatrix A
  let S := sectorModel Complex.I overall sd
  let B := action F S
  let c : ℂ := (A.det : ℂ) * (2 * (Complex.I * signValue sd))
  have hc : c ≠ 0 := by cases sd <;> simp [c, signValue, hA.ne']
  have hg : wedgeGram B = c • (1 : M3 ℂ) := by
    change wedgeGram (action _ _) = _
    rw [wedgeGram_action, sector_gram, smul_smul, ← realCast.map_det]
    rfl
  refine ⟨simple_of_gram B c hg, ?_, ?_, ?_, ?_⟩
  · change (wedgeGram B).det ≠ 0
    simp [hg, hc]
  · let f := starRingEnd ℂ
    have hF : F.map f = F := by
      ext i j
      exact Complex.conj_ofReal _
    have hb : B.map star = action F (S.map star) := by
      change (exteriorSquare F * S).map f = exteriorSquare F * S.map f
      rw [Matrix.map_mul, ← exterior_map f, hF]
    change Bᵀ * W ℂ * B.map star = 0
    rw [hb]
    simp only [B, action, transpose_mul, ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc Sᵀ _ (W ℂ), Matrix.mul_assoc Sᵀ _ (exteriorSquare F),
      exterior_wedge_congruence, Matrix.mul_smul, Matrix.smul_mul, lorentz_sector_mixed, smul_zero]
  · have hreal : urbantke B = realCast.mapMatrix
        (((A.det * (signValue overall : ℝ)) : ℝ) • (A * lorentzMetric * Aᵀ)) := by
      change urbantke (action F S) = _
      rw [urbantke_action, sector_cubic, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
        show F.det = realCast A.det from (realCast.map_det A).symm, ← lorentzMetric_model]
      have hmap : F * realCast.mapMatrix lorentzMetric * Fᵀ =
          realCast.mapMatrix (A * lorentzMetric * Aᵀ) := by
        rw [map_mul, map_mul]
        rfl
      rw [hmap]
      ext i j
      let x := (A * lorentzMetric * Aᵀ : M4 ℝ) i j
      change ((A.det : ℂ) * signValue overall) * (x : ℂ) =
        (((A.det * signValue overall) * x : ℝ) : ℂ)
      cases overall <;> simp [signValue]
    change (urbantke B).map star = urbantke B
    rw [hreal]
    ext i j
    exact Complex.conj_ofReal _
  · change (gramScalar B).re = 0
    have hcg : gramScalar B = c := by
      rw [gramScalar, hg, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
      ring
    rw [hcg]
    cases sd <;> simp [c, signValue, Complex.mul_re, Complex.mul_im]

theorem lorentzian_model_iff (B : FormTriple ℂ) :
    (Simple B ∧ (wedgeGram B).det ≠ 0 ∧ lorentzianReal B) ↔
      ∃ (A : M4 ℝ) (overall sd : Bool), 0 < A.det ∧
        B = action (realCast.mapMatrix A) (sectorModel Complex.I overall sd) := by
  constructor
  · rintro ⟨hQ, hnd, horth, hU, hre⟩
    obtain ⟨A, overall, sd, ha, hs, hu⟩ := lorentz_metric_data B hQ hnd horth hU hre
    let C := action (realCast.mapMatrix A) (sectorModel Complex.I overall sd)
    have hC : wedgeGram C = gramScalar B • (1 : M3 ℂ) := by
      dsimp only [C]
      rw [wedgeGram_action, sector_gram, smul_smul, ← realCast.map_det]
      exact congrArg (fun c : ℂ => c • (1 : M3 ℂ)) hs.symm
    have hCU : urbantke B = urbantke C := by
      rw [show C = action (realCast.mapMatrix A) (sectorModel Complex.I overall sd) from rfl,
        urbantke_action, sector_cubic, ← realCast.map_det,
        Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      exact hu
    have hc : gramScalar B ≠ 0 := fun h => hnd (by rw [hQ, h, zero_smul, det_zero])
    obtain ⟨R, hR, hdR, hB⟩ := internal_frame _ _ _ hc hQ hC hCU
    have hz : Complex.I * (signValue sd : ℂ) = Complex.I ∨
        Complex.I * (signValue sd : ℂ) = -Complex.I := by
      cases sd <;> simp [signValue]
    obtain ⟨L, hL, hact⟩ := lorentz_lift _ hz R hR hdR
    refine ⟨A * L, overall, sd, by rw [det_mul, hL, mul_one]; exact ha, ?_⟩
    rw [hB, map_mul, action_mul]
    dsimp only [C, sectorModel]
    rw [action_smul (realCast.mapMatrix L), hact, action_smul]
    rw [action_smul (realCast.mapMatrix A), action_right_complex, Matrix.smul_mul]
  · rintro ⟨A, overall, sd, ha, rfl⟩
    exact phase_of_lorentz_model A overall sd ha

/-- With the coframe volume, the second sign determines the Hodge eigenvalue. -/
theorem oriented_sector_hodge {K : Type*} [Field K] [CharZero K] (z : K) (hz : z ^ 4 = 1)
    (A : M4 K) (ha : A.det ≠ 0) (overall sd : Bool) :
    hodge (A * modelMetric z * Aᵀ) A.det * action A (sectorModel z overall sd) =
      (z * signValue sd) • action A (sectorModel z overall sd) := by
  let d := A.det
  let a := z * (signValue sd : K)
  let g := A * modelMetric z * Aᵀ
  let B := action A (sectorModel z overall sd)
  change hodge g d * B = a • B
  have ha4 : a ^ 4 = 1 := by
    cases sd <;> convert hz using 1 <;> simp [a, signValue]
    ring
  have han : a ≠ 0 := by intro h; simp [h] at ha4
  have hQ : wedgeGram B = (2 * (d * a)) • (1 : M3 K) := by
    simp only [B, wedgeGram_action, sector_gram, smul_smul, d, a, mul_left_comm]
  have hnd : (wedgeGram B).det ≠ 0 := by simp [hQ, d, ha, han]
  have hU : urbantke B = (d * (signValue overall : K)) • g := by
    simp [B, urbantke_action, sector_cubic, g, d, smul_smul]
  have hscale : (d * signValue overall : K) ^ 2 = d ^ 2 := by
    cases overall <;> simp [signValue]
  have hD : density B = (d * a) ^ 3 := by
    rw [density, hQ, det_smul]; norm_num; ring
  have hg : g.det ≠ 0 := by
    have h := (urbantke_nondegenerate_iff_and_chiral_star B).1.mpr hnd
    rw [hU, det_smul] at h
    exact right_ne_zero_of_mul h
  let := invertibleOfNonzero (pow_ne_zero 2 ha : d ^ 2 ≠ 0)
  have hfix := ((urbantke_nondegenerate_iff_and_chiral_star B).2 hnd).2.2.2.1
  rw [hU, hD, hodge, exterior_smul, hscale,
    Matrix.inv_smul (exteriorSquare g) (d ^ 2) (isUnit_iff_ne_zero.mpr (exterior_det_ne _ hg)), invOf_eq_inv] at hfix
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul] at hfix
  rw [show (d ^ 2)⁻¹ * (d * a) ^ 3 = a ^ 3 * d by
    field_simp [show d ≠ 0 from ha]] at hfix
  have hscaled : a ^ 3 • (hodge g d * B) = B := by
    simpa only [hodge, Matrix.smul_mul, smul_smul] using hfix
  simpa only [smul_smul, ← pow_succ', ha4, one_smul] using
    (congrArg (fun C : FormTriple K => a • C) hscaled)

end D5.S3.Geometry.Lorentz.PlebanskiSectors4D
