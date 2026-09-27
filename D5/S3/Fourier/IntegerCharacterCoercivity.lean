/- GID: D5/S3/Fourier/IntegerCharacterCoercivity
   generality: G
   mirror-B: D5/B/S3/Fourier/IntegerCharacterCoercivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer character defects control distance to their full periodic zero set. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Algebra.Order.ToIntervalMod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.IntegerCharacterCoercivity

open scoped BigOperators
open Metric Set

/-- Global Euclidean coercivity for a finite family of integer characters,
with distance to every simultaneous integral-phase fiber. -/
theorem integer_character_global_coercivity (q : ℕ) {I : Type*} [Fintype I]
    (lam : I → Fin q → ℤ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : EuclideanSpace ℝ (Fin q),
      c * (infDist x {y : EuclideanSpace ℝ (Fin q) |
        ∀ a, ∃ k : ℤ, (∑ i, (lam a i : ℝ) * y i) = 2 * Real.pi * k}) ^ 2 ≤
      ∑ a, (1 - Real.cos (∑ i, (lam a i : ℝ) * x i)) := by
  classical
  let E := EuclideanSpace ℝ (Fin q)
  let F := EuclideanSpace ℝ I
  let A : E →ₗ[ℝ] F :=
    { toFun := fun x => WithLp.toLp 2 (fun a => ∑ i, (lam a i : ℝ) * x i)
      map_add' := by
        intro x y
        ext a
        change (∑ i, (lam a i : ℝ) * (x i + y i)) =
          (∑ i, (lam a i : ℝ) * x i) + ∑ i, (lam a i : ℝ) * y i
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r x
        ext a
        change (∑ i, (lam a i : ℝ) * (r * x i)) = r * ∑ i, (lam a i : ℝ) * x i
        simp [Finset.mul_sum, mul_left_comm] }
  let U : Set E := {x | ∀ a, ∃ k : ℤ, A x a = 2 * Real.pi * k}
  let D : E → ℝ := fun x => ∑ a, (1 - Real.cos (A x a))
  change ∃ c : ℝ, 0 < c ∧ ∀ x : E, c * (infDist x U) ^ 2 ≤ D x
  have hDnonneg (x : E) : 0 ≤ D x :=
    Finset.sum_nonneg fun a _ => sub_nonneg.mpr (Real.cos_le_one _)
  have hDcont : Continuous D := by
    unfold D
    apply continuous_finsetSum
    intro a _
    exact continuous_const.sub (Real.continuous_cos.comp
      ((PiLp.continuous_apply 2 (fun _ : I => ℝ) a).comp A.continuous_of_finiteDimensional))
  have hDzero (x : E) : D x = 0 ↔ x ∈ U := by
    dsimp only [D]
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
      sub_nonneg.mpr (Real.cos_le_one (A x a)))]
    constructor
    · intro h a
      obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff (A x a)).mp
        (by linarith [h a (Finset.mem_univ a)])
      exact ⟨k, by linarith⟩
    · intro h a _
      obtain ⟨k, hk⟩ := h a
      rw [hk, mul_comm (2 * Real.pi), Real.cos_int_mul_two_pi]
      exact sub_self _
  have hU0 : (0 : E) ∈ U := by
    intro a
    exact ⟨0, by simp⟩
  have hUadd {x y : E} (hx : x ∈ U) (hy : y ∈ U) : x + y ∈ U := by
    intro a
    obtain ⟨k, hk⟩ := hx a
    obtain ⟨l, hl⟩ := hy a
    refine ⟨k + l, ?_⟩
    rw [map_add]
    change A x a + A y a = _
    rw [hk, hl, Int.cast_add]
    ring
  have hUsub {x y : E} (hx : x ∈ U) (hy : y ∈ U) : x - y ∈ U := by
    intro a
    obtain ⟨k, hk⟩ := hx a
    obtain ⟨l, hl⟩ := hy a
    refine ⟨k - l, ?_⟩
    rw [map_sub]
    change A x a - A y a = _
    rw [hk, hl, Int.cast_sub]
    ring
  have hperiod (y : E) (hy : y ∈ U) (x : E) :
      D (x + y) = D x ∧ infDist (x + y) U = infDist x U := by
    constructor
    · apply Finset.sum_congr rfl
      intro a _
      obtain ⟨k, hk⟩ := hy a
      rw [map_add]
      change 1 - Real.cos (A x a + A y a) = _
      rw [hk]
      rw [mul_comm (2 * Real.pi), Real.cos_add_int_mul_two_pi]
    · have himage : (fun z : E => z + y) '' U = U := by
        ext z
        constructor
        · rintro ⟨w, hw, rfl⟩
          exact hUadd hw hy
        · intro hz
          exact ⟨z - y, hUsub hz hy, sub_add_cancel z y⟩
      simpa only [himage] using
        (Metric.infDist_image (x := x) (t := U) (isometry_add_right y))
  -- A bounded preimage of the phase vector controls distance to each kernel coset.
  let Ar : E →L[ℝ] A.range := A.rangeRestrict.toContinuousLinearMap
  obtain ⟨C, hCpos, hC⟩ := Ar.exists_preimage_norm_le A.surjective_rangeRestrict
  let Ac : E →L[ℝ] F := A.toContinuousLinearMap
  let δ : ℝ := Real.pi / (‖Ac‖ + 1)
  have hδ : 0 < δ := div_pos Real.pi_pos (by positivity)
  let α : ℝ := 2 / Real.pi ^ 2
  have hα : 0 < α := by dsimp [α]; positivity
  have hlocal (x : E) (hx : infDist x U < δ) :
      (α / C ^ 2) * (infDist x U) ^ 2 ≤ D x := by
    obtain ⟨y, hy, hxy⟩ := (infDist_lt_iff ⟨0, hU0⟩).mp hx
    let v := x - y
    have hv : ‖v‖ < δ := by
      rw [@dist_eq_norm E _ x y] at hxy
      exact hxy
    have hphase (a : I) : |A v a| ≤ Real.pi := by
      have h1 := PiLp.norm_apply_le (A v) a
      have h2 := Ac.le_opNorm v
      have h3 : (‖Ac‖ + 1) * ‖v‖ < Real.pi := by
        apply (lt_div_iff₀ (by positivity : 0 < ‖Ac‖ + 1)).mp at hv
        nlinarith
      change ‖A v‖ ≤ ‖Ac‖ * ‖v‖ at h2
      rw [Real.norm_eq_abs] at h1
      nlinarith [norm_nonneg v]
    have hsum : α * ‖A v‖ ^ 2 ≤ D x := by
      have heq : D x = D v := by
        simpa only [v, sub_add_cancel] using (hperiod y hy (x - y)).1
      rw [heq, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a _
      have ht := Real.cos_le_one_sub_mul_cos_sq (hphase a)
      dsimp [α]
      linarith
    obtain ⟨w, hw, hwnorm⟩ := hC (Ar v)
    have hwA : A w = A v := congrArg Subtype.val hw
    have hz : x - w ∈ U := by
      have heq : A (x - w) = A y := by
        rw [map_sub, hwA]
        dsimp [v]
        rw [map_sub]
        abel
      intro a
      simpa only [heq] using hy a
    have hdist : infDist x U ≤ C * ‖A v‖ := by
      have hd := infDist_le_dist_of_mem (x := x) hz
      have heq : dist x (x - w) = ‖w‖ := by rw [dist_eq_norm]; congr 1; abel
      rw [heq] at hd
      exact hd.trans hwnorm
    have hsq : (infDist x U) ^ 2 ≤ C ^ 2 * ‖A v‖ ^ 2 := by
      nlinarith [infDist_nonneg (x := x) (s := U), norm_nonneg (A v)]
    calc
      α / C ^ 2 * (infDist x U) ^ 2 ≤ α / C ^ 2 * (C ^ 2 * ‖A v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = α * ‖A v‖ ^ 2 := by field_simp
      _ ≤ D x := hsum
  -- Compactness supplies the lower bound away from all periodic zeros.
  let K : Set E := WithLp.toLp 2 '' (Set.pi Set.univ
    (fun _ : Fin q => Set.Icc (0 : ℝ) (2 * Real.pi)))
  have hK : IsCompact K :=
    (isCompact_univ_pi (fun _ => isCompact_Icc)).image (PiLp.continuous_toLp 2 _)
  have hdcont : Continuous (fun x : E => (infDist x U) ^ 2) :=
    (continuous_infDist_pt U).pow 2
  obtain ⟨B, hB⟩ := hK.bddAbove_image hdcont.continuousOn
  let S := K ∩ {x : E | δ ≤ infDist x U}
  have hS : IsCompact S := hK.inter_right
    (isClosed_le continuous_const (continuous_infDist_pt U))
  obtain ⟨m, hmpos, hm⟩ := hS.exists_forall_le' hDcont.continuousOn (a := 0) (by
    intro x hx
    apply lt_of_le_of_ne (hDnonneg x)
    intro heq
    have hxU := (hDzero x).mp heq.symm
    have hd := infDist_zero_of_mem hxU
    have hh : δ ≤ infDist x U := hx.2
    rw [hd] at hh
    linarith)
  let c : ℝ := min (α / C ^ 2) (m / (max B 0 + 1))
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hKbound (x : E) (hx : x ∈ K) : c * (infDist x U) ^ 2 ≤ D x := by
    by_cases hd : infDist x U < δ
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans (hlocal x hd)
    · have hmx := hm x ⟨hx, le_of_not_gt hd⟩
      have hBx : (infDist x U) ^ 2 ≤ max B 0 + 1 := by
        have hb := hB (Set.mem_image_of_mem (fun x : E => (infDist x U) ^ 2) hx)
        exact hb.trans (by linarith [le_max_left B 0])
      calc
        c * (infDist x U) ^ 2 ≤ (m / (max B 0 + 1)) * (infDist x U) ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
        _ ≤ (m / (max B 0 + 1)) * (max B 0 + 1) :=
          mul_le_mul_of_nonneg_left hBx (by positivity)
        _ = m := by field_simp
        _ ≤ D x := hmx
  -- Every point is a lattice translate of a point in the compact cube.
  refine ⟨c, hc, fun x => ?_⟩
  have hp : 0 < 2 * Real.pi := by positivity
  let n : Fin q → ℤ := fun i => toIcoDiv hp 0 (x i)
  let z : E := WithLp.toLp 2 (fun i => (n i : ℝ) * (2 * Real.pi))
  let r : E := WithLp.toLp 2 (fun i => toIcoMod hp 0 (x i))
  have hr : r ∈ K := by
    refine ⟨fun i => toIcoMod hp 0 (x i), ?_, rfl⟩
    intro i _
    exact ⟨(toIcoMod_mem_Ico' hp (x i)).1, (toIcoMod_mem_Ico' hp (x i)).2.le⟩
  have hx : x = r + z := by
    ext i
    change x i = toIcoMod hp 0 (x i) + (toIcoDiv hp 0 (x i) : ℝ) * (2 * Real.pi)
    simpa only [zsmul_eq_mul] using (toIcoMod_add_toIcoDiv_zsmul hp 0 (x i)).symm
  have hz : z ∈ U := by
    intro a
    refine ⟨∑ i, lam a i * n i, ?_⟩
    change (∑ i, (lam a i : ℝ) * ((n i : ℝ) * (2 * Real.pi))) = _
    simp only [Int.cast_sum, Int.cast_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hx, (hperiod z hz r).1, (hperiod z hz r).2]
  exact hKbound r hr

end D5.S3.Fourier.IntegerCharacterCoercivity
