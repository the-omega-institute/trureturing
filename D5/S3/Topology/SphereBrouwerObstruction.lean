/- GID: D5/S3/Topology/SphereBrouwerObstruction
   generality: G
   mirror-B: D5/B/S3/Topology/SphereBrouwerObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.Homotopy.Contractible]
   utility: none
   digest: A contraction of a Euclidean sphere gives a ball retraction contradicting Brouwer. -/

import D5.S3.Geometry.FixedPoint.Brouwer
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.Ball.Action
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Tactic

/-! # The sphere obstruction from the simplex fixed point theorem -/

set_option autoImplicit false

open Set Metric Function
open scoped Topology

noncomputable section

namespace D5.S3.Topology.SphereBrouwerObstruction

private theorem sphere_retraction_of_contractible {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (h : ContractibleSpace (sphere (0 : E) 1)) :
    ∃ R : C(closedBall (0 : E) 1, sphere (0 : E) 1),
      ∀ x : sphere (0 : E) 1,
        R ⟨x.val, mem_closedBall_zero_iff.mpr
          (mem_sphere_zero_iff_norm.mp x.property).le⟩ = x := by
  let := h
  obtain ⟨p, ⟨H⟩⟩ := id_nullhomotopic (sphere (0 : E) 1)
  let G := H.symm
  let q : unitInterval × sphere (0 : E) 1 → closedBall (0 : E) 1 := fun z =>
    ⟨(z.1 : ℝ) • (z.2 : E), by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg z.1.property.1, mem_sphere_zero_iff_norm.mp z.2.property, mul_one]
      exact z.1.property.2⟩
  have hq : Continuous q := by fun_prop
  have hsurj : Surjective q := by
    intro y
    by_cases hy : (y : E) = 0
    · exact ⟨(0, p), Subtype.ext (by simpa [q] using hy.symm)⟩
    · refine ⟨(⟨‖(y : E)‖, norm_nonneg _, mem_closedBall_zero_iff.mp y.property⟩,
        ⟨NormedSpace.normalize (y : E),
          mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hy)⟩), ?_⟩
      exact Subtype.ext (NormedSpace.norm_smul_normalize _)
  have hfiber : ∀ a b, q a = q b → G a = G b := by
    rintro ⟨t, x⟩ ⟨u, y⟩ heq
    have htu : (t : ℝ) = (u : ℝ) := by
      have hh := congrArg (fun z : closedBall (0 : E) 1 => ‖(z : E)‖) heq
      simpa only [q, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg t.property.1, abs_of_nonneg u.property.1,
        mem_sphere_zero_iff_norm.mp x.property,
        mem_sphere_zero_iff_norm.mp y.property, mul_one] using hh
    have htu' : t = u := Subtype.ext htu
    subst u
    by_cases ht : (t : ℝ) = 0
    · have ht' : t = 0 := Subtype.ext ht
      subst t
      exact (G.map_zero_left x).trans (G.map_zero_left y).symm
    · have hxy : x = y := by
        apply Subtype.ext
        have hh := congrArg (fun z : closedBall (0 : E) 1 => (t : ℝ)⁻¹ • (z : E)) heq
        simpa only [q, smul_smul, inv_mul_cancel₀ ht, one_smul] using hh
      subst y
      rfl
  let R : closedBall (0 : E) 1 → sphere (0 : E) 1 := fun y => G (invFun q y)
  have hRq : ∀ z, R (q z) = G z := by
    intro z
    exact hfiber _ _ (Function.rightInverse_invFun hsurj (q z))
  have hR : Continuous R := by
    apply (Topology.IsQuotientMap.of_surjective_continuous hsurj hq).continuous_iff.mpr
    convert G.continuous using 1
    exact funext hRq
  refine ⟨⟨R, hR⟩, ?_⟩
  intro x
  have hh := hRq (1, x)
  have hhx := hh.trans (G.map_one_left x)
  simpa [q] using hhx

/-- A positive-dimensional Euclidean unit sphere cannot be contractible: a contraction
would yield a ball retraction and hence a fixed-point-free simplex self-map. -/
theorem not_contractible_unit_sphere (n : ℕ) (hn : 0 < n) :
    ¬ ContractibleSpace (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  intro h
  let E := EuclideanSpace ℝ (Fin n)
  let S := sphere (0 : E) 1
  obtain ⟨R, hR⟩ := sphere_retraction_of_contractible h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  let a : S → Fin n → ℝ := fun x i => ((x.val i) + 1) / (2 * n)
  have hcoord : ∀ x : S, ∀ i, -1 ≤ x.val i ∧ x.val i ≤ 1 := by
    intro x i
    have hh := PiLp.norm_apply_le (p := 2) x.val i
    rw [Real.norm_eq_abs, mem_sphere_zero_iff_norm.mp x.property] at hh
    exact abs_le.mp hh
  have ha0 : ∀ x i, 0 ≤ a x i := by
    intro x i
    exact div_nonneg (by linarith [(hcoord x i).1]) (by positivity)
  have hasum : ∀ x, ∑ i, a x i ≤ 1 := by
    intro x
    calc
      ∑ i, a x i ≤ ∑ _i : Fin n, (1 : ℝ) / n := by
        apply Finset.sum_le_sum
        intro i _
        dsimp [a]
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
        have hh : (1 / (n : ℝ)) * (2 * n) = 2 := by field_simp
        rw [hh]
        linarith [(hcoord x i).2]
      _ = 1 := by simp [hn0]
  let A : S → stdSimplex ℝ (Fin (n + 1)) := fun x =>
    ⟨Fin.cons (1 - ∑ i, a x i) (a x), by
      constructor
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact sub_nonneg.mpr (hasum x)
        · exact ha0 x j
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        ring⟩
  have hac : ∀ j, Continuous (fun x : S => a x j) := by
    intro j
    exact (((PiLp.continuous_apply 2 _ j).comp continuous_subtype_val).add
      continuous_const).div_const _
  have hA : Continuous A := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Continuous fun x : S => 1 - ∑ j, a x j
      exact continuous_const.sub (continuous_finsetSum _ fun j _ => hac j)
    · change Continuous fun x : S => a x _
      exact hac _
  let B : stdSimplex ℝ (Fin (n + 1)) → E := fun z =>
    WithLp.toLp 2 (fun i => (2 * n : ℝ) * z.val i.succ - 1)
  have hB : Continuous B := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    exact (continuous_const.mul ((continuous_apply i.succ).comp continuous_subtype_val)).sub
      continuous_const
  have hBA : ∀ x, B (A x) = (x : E) := by
    intro x
    ext i
    change (2 * n : ℝ) * (((x.val i) + 1) / (2 * n)) - 1 = x.val i
    field_simp
    <;> ring
  let r : E → closedBall (0 : E) 1 := fun y =>
    ⟨(max 1 ‖y‖)⁻¹ • y, by
      have hm : 0 < max 1 ‖y‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hm)]
      calc
        (max 1 ‖y‖)⁻¹ * ‖y‖ = ‖y‖ / max 1 ‖y‖ := by ring
        _ ≤ 1 := (div_le_one hm).mpr (le_max_right _ _)⟩
  have hr : Continuous r := by
    apply Continuous.subtype_mk
    exact ((continuous_const.max continuous_norm).inv₀
      (fun y => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖y‖)))).smul
        continuous_id
  have hrS : ∀ x : S, r x.val = ⟨x.val,
      mem_closedBall_zero_iff.mpr (mem_sphere_zero_iff_norm.mp x.property).le⟩ := by
    intro x
    apply Subtype.ext
    simp [r, mem_sphere_zero_iff_norm.mp x.property]
  let f : stdSimplex ℝ (Fin (n + 1)) → stdSimplex ℝ (Fin (n + 1)) :=
    fun z => A (-R (r (B z)))
  have hf : Continuous f := by
    apply hA.comp
    exact (continuous_neg.comp R.continuous).comp (hr.comp hB)
  obtain ⟨z, hz⟩ := D5.S3.Geometry.FixedPoint.Brouwer ⟨n + 1, by omega⟩ f hf
  let y : S := R (r (B z))
  have hy : B z = (-y : S).val := by
    have hh := congrArg B hz
    simpa only [f, hBA] using hh.symm
  have hRy : y = -y := by
    change R (r (B z)) = -y
    rw [hy, hrS, hR]
  have hy0 : (y : E) = 0 := by
    have hh := congrArg Subtype.val hRy
    change (y : E) = -(y : E) at hh
    have ht : (2 : ℝ) • (y : E) = 0 := by
      calc
        (2 : ℝ) • (y : E) = (y : E) + (y : E) := two_smul _ _
        _ = (y : E) + -(y : E) := congrArg (fun z : E => (y : E) + z) hh
        _ = 0 := add_neg_cancel _
    exact (smul_eq_zero.mp ht).resolve_left (by norm_num)
  have hnorm := mem_sphere_zero_iff_norm.mp y.property
  simp [hy0] at hnorm

end D5.S3.Topology.SphereBrouwerObstruction
