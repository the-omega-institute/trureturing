import OmegaMath.Analysis.PlanarSublevelSandwich
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Topology.Order.Compact

import OmegaBuild.Commands

/-!
Omega original.

Whole periodic sublevels of a planar map admit smooth bounds assembled from a finite family
of regular zeros in the interior of a fundamental cell.
-/

compile_only_with_mathlib

namespace Omega.Analysis.PeriodicSublevelSandwich

noncomputable section

open Filter Metric Set WithLp
open scoped Topology

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The closed unit square with lower corner q. -/
def closedCell (q : Plane) : Set Plane :=
  {x | ∀ i, x i ∈ Icc (q i) (q i + 1)}

/-- The interior of the unit square with lower corner q. -/
def openCell (q : Plane) : Set Plane :=
  {x | ∀ i, x i ∈ Ioo (q i) (q i + 1)}

private def halfOpenCell (q : Plane) : Set Plane :=
  {x | ∀ i, x i ∈ Ico (q i) (q i + 1)}

/-- An integer translation in Euclidean coordinates. -/
def latticeVector (a : Fin 2 → ℤ) : Plane :=
  toLp 2 fun i => (a i : ℝ)

private theorem isCompact_closedCell (q : Plane) : IsCompact (closedCell q) := by
  let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm
  have h := (isCompact_univ_pi (fun i : Fin 2 =>
    isCompact_Icc (a := q i) (b := q i + 1))).image E.continuous
  convert h using 1
  ext x
  constructor
  · intro hx
    refine ⟨fun i => x i, ?_, ?_⟩
    · exact fun i _ => hx i
    · ext i
      rfl
  · rintro ⟨y, hy, rfl⟩ i
    exact hy i (mem_univ i)

private theorem existsUnique_lattice_representative (q x : Plane) :
    ∃! a : Fin 2 → ℤ, latticeVector a + x ∈ halfOpenCell q := by
  have h (i : Fin 2) : ∃! a : ℤ, (a : ℝ) + x i ∈ Ico (q i) (q i + 1) := by
    simpa [add_comm] using
      existsUnique_add_zsmul_mem_Ico (show (0 : ℝ) < 1 by norm_num) (x i) (q i)
  choose a ha hu using h
  refine ⟨a, ha, fun b hb => ?_⟩
  exact funext fun i => hu i (b i) (hb i)

private theorem gap_on_compact_complement {F : Plane → Plane} {K U : Set Plane}
    (hF : Continuous F) (hK : IsCompact K) (hU : IsOpen U)
    (hz : ∀ x ∈ K, F x = 0 → x ∈ U) :
    ∃ δ > 0, ∀ x ∈ K \ U, δ ≤ ‖F x‖ := by
  by_cases hne : (K \ U).Nonempty
  · obtain ⟨z, hzK, hzMin⟩ :=
      (hK.diff hU).exists_isMinOn hne hF.norm.continuousOn
    have hnz : F z ≠ 0 := fun h => hzK.2 (hz z hzK.1 h)
    exact ⟨‖F z‖, norm_pos_iff.mpr hnz, fun _ hx => hzMin hx⟩
  · exact ⟨1, zero_lt_one, fun x hx => (hne ⟨x, hx⟩).elim⟩

private theorem isOpen_openCell (q : Plane) : IsOpen (openCell q) := by
  have heq : openCell q = ⋂ i : Fin 2, {x : Plane | x i ∈ Ioo (q i) (q i + 1)} := by
    ext x
    simp [openCell]
  rw [heq]
  refine isOpen_iInter_of_finite (fun i => ?_)
  have h : Continuous (fun x : Plane => x i) :=
    (continuous_apply i).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).continuous
  exact isOpen_Ioo.preimage h

private def isolatedNeighborhood {ι : Type*} (q : Plane) (z : ι → Plane)
    (r : ι → ℝ) (i : ι) : Set Plane :=
  (ball (z i) (r i) ∩ openCell q) ∩
    ⋂ j : {j : ι // j ≠ i}, {x | dist x (z i) < dist x (z j)}

private theorem isOpen_isolatedNeighborhood {ι : Type*} [Fintype ι]
    (q : Plane) (z : ι → Plane) (r : ι → ℝ) (i : ι) :
    IsOpen (isolatedNeighborhood q z r i) := by
  classical
  apply (isOpen_ball.inter (isOpen_openCell q)).inter
  exact isOpen_iInter_of_finite fun j => isOpen_lt
    (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)

private theorem mem_isolatedNeighborhood {ι : Type*}
    (q : Plane) (z : ι → Plane) (r : ι → ℝ) (hz : Function.Injective z)
    (hcell : ∀ i, z i ∈ openCell q) (hr : ∀ i, 0 < r i) (i : ι) :
    z i ∈ isolatedNeighborhood q z r i := by
  refine ⟨⟨mem_ball_self (hr i), hcell i⟩, mem_iInter.mpr fun j => ?_⟩
  change dist (z i) (z i) < dist (z i) (z j.val)
  rw [dist_self]
  exact dist_pos.mpr (fun h => j.property (hz h.symm))

private theorem pairwiseDisjoint_isolatedNeighborhood {ι : Type*}
    (q : Plane) (z : ι → Plane) (r : ι → ℝ) :
    Pairwise (fun i j => Disjoint (isolatedNeighborhood q z r i) (isolatedNeighborhood q z r j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  have h₁ : dist x (z i) < dist x (z j) := mem_iInter.mp hxi.2 ⟨j, hij.symm⟩
  have h₂ : dist x (z j) < dist x (z i) := mem_iInter.mp hxj.2 ⟨i, hij⟩
  exact (not_lt_of_ge h₂.le) h₁

private theorem eventually_mul_lt (m : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ε * m < δ := by
  have hc : ContinuousAt (fun ε : ℝ => ε * m) 0 :=
    (continuous_id.mul continuous_const).continuousAt
  exact (hc.eventually (eventually_lt_nhds (show (0 : ℝ) * m < δ by
    simpa using hδ))).filter_mono nhdsWithin_le_nhds

private theorem eventually_scaled_support {g : Plane → ℝ}
    (hg : HasCompactSupport g) {U : Set Plane} (hU : IsOpen U)
    {z : Plane} (hz : z ∈ U) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ x, g (ε⁻¹ • (x - z)) ≠ 0 → x ∈ U := by
  obtain ⟨m, hm⟩ := hg.isCompact.isBounded.subset_closedBall 0
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU z hz
  have hεm := eventually_mul_lt m hδ
  filter_upwards [self_mem_nhdsWithin, hεm] with ε hε hmε x hx
  have hε' : 0 < ε := hε
  have hscaled : ‖ε⁻¹ • (x - z)‖ ≤ m := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hm (subset_tsupport g hx)
  have hxm : ‖x - z‖ ≤ ε * m := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε')] at hscaled
    have hh := mul_le_mul_of_nonneg_left hscaled hε'.le
    rwa [← mul_assoc, mul_inv_cancel₀ hε'.ne', one_mul] at hh
  exact hδU (by simpa [Metric.mem_ball, dist_eq_norm] using hxm.trans_lt hmε)

private theorem halfOpenCell_subset_closed (q : Plane) :
    halfOpenCell q ⊆ closedCell q :=
  fun _ hx i => Ico_subset_Icc_self (hx i)

private theorem openCell_subset_halfOpen (q : Plane) :
    openCell q ⊆ halfOpenCell q :=
  fun _ hx i => Ioo_subset_Ico_self (hx i)

private theorem periodization_eq_single_representative {q x : Plane}
    (g : Plane → ℝ) (hg : ∀ x, g x ≠ 0 → x ∈ halfOpenCell q)
    {a₀ : Fin 2 → ℤ} (ha₀ : latticeVector a₀ + x ∈ halfOpenCell q) :
    (∑' a : Fin 2 → ℤ, g (latticeVector a + x)) = g (latticeVector a₀ + x) := by
  obtain ⟨a₁, _, ha₁⟩ := existsUnique_lattice_representative q x
  apply tsum_eq_single a₀
  intro a hne
  by_contra hnz
  exact hne ((ha₁ a (hg _ hnz)).trans (ha₁ a₀ ha₀).symm)

private theorem lower_sum_le {ι : Type*} [Fintype ι] {L : ι → ℝ} {b : ℝ}
    (hb : 0 ≤ b) (hL : ∀ i, L i ≤ b)
    (hunique : ∀ i j, L i ≠ 0 → L j ≠ 0 → i = j) :
    (∑ i, L i) ≤ b := by
  classical
  by_cases h : ∃ i, L i ≠ 0
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i (fun j _ hji => by
      by_contra hj
      exact hji (hunique j i hj hi)) (by simp)]
    exact hL i
  · have hzero (i : ι) : L i = 0 := not_ne_iff.mp (not_exists.mp h i)
    simpa only [hzero, Finset.sum_const_zero] using hb

open MeasureTheory
open scoped ContDiff

/-- Fixed compact windows give pointwise bounds for the entire periodic sublevel. -/
theorem periodic_test_sandwich {ι : Type*} [Fintype ι]
    (q : Plane) {F : Plane → Plane} (hF : Continuous F)
    (hperiod : ∀ (a : Fin 2 → ℤ) (x : Plane), F (latticeVector a + x) = F x)
    (z : ι → Plane) (hz : Function.Injective z)
    (hcell : ∀ i, z i ∈ openCell q)
    (hzero : ∀ x ∈ closedCell q, F x = 0 ↔ ∃ i, x = z i)
    (A : ι → Plane ≃L[ℝ] Plane) (hA : ∀ i, HasFDerivAt F (A i : Plane →L[ℝ] Plane) (z i))
    {η ρ σ : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hρ : 0 < ρ) (hρ' : ρ < (1 + η)⁻¹) (hσ : (1 - η)⁻¹ < σ) :
    let D := ∑ i, |LinearMap.det ((A i).toLinearEquiv : Plane →ₗ[ℝ] Plane)|⁻¹
    ∃ (lower upper : ι → Plane → ℝ) (δ : ℝ),
      0 < δ ∧
      (∀ i, ContDiff ℝ ∞ (lower i) ∧ ContDiff ℝ ∞ (upper i) ∧
        HasCompactSupport (lower i) ∧ HasCompactSupport (upper i)) ∧
      Real.pi * ρ ^ 2 * D ≤ ∑ i, ∫ u, lower i u ∧
      (∑ i, ∫ u, upper i u) ≤ Real.pi * σ ^ 2 * D ∧
      ∀ ε ∈ Ioo 0 δ, ∀ x,
        (∑ i, ∑' a : Fin 2 → ℤ, lower i (ε⁻¹ • (latticeVector a + x - z i))) ≤
          (if ‖F x‖ < ε then 1 else 0) ∧
        (if ‖F x‖ < ε then 1 else 0) ≤
          (∑ i, ∑' a : Fin 2 → ℤ, upper i (ε⁻¹ • (latticeVector a + x - z i))) := by
  classical
  have hz₀ (i : ι) : F (z i) = 0 :=
    (hzero (z i) (halfOpenCell_subset_closed q (openCell_subset_halfOpen q (hcell i)))).mpr ⟨i, rfl⟩
  choose r lower upper hr hlSmooth huSmooth hlSupport huSupport hlIntegral huIntegral hLocal using fun i =>
    Omega.Analysis.PlanarSublevelSandwich.smooth_local_ellipse_sandwich
      (A i) (hA i) (hz₀ i) hη hη1 hρ hρ' hσ
  have hsmooth (i : ι) : ContDiff ℝ ∞ (lower i) ∧ ContDiff ℝ ∞ (upper i) ∧
      HasCompactSupport (lower i) ∧ HasCompactSupport (upper i) :=
    ⟨hlSmooth i, huSmooth i, hlSupport i, huSupport i⟩
  let U : ι → Set Plane := isolatedNeighborhood q z r
  have hU_open (i : ι) : IsOpen (U i) := isOpen_isolatedNeighborhood q z r i
  have hU_mem (i : ι) : z i ∈ U i := mem_isolatedNeighborhood q z r hz hcell hr i
  have hU_disjoint : Pairwise (fun i j => Disjoint (U i) (U j)) :=
    pairwiseDisjoint_isolatedNeighborhood q z r
  have hUi_openCell (i : ι) : U i ⊆ openCell q := fun _ hx => hx.1.2
  have hgap : ∃ d > 0, ∀ x ∈ closedCell q \ ⋃ i, U i, d ≤ ‖F x‖ := by
    apply gap_on_compact_complement hF (isCompact_closedCell q) (isOpen_iUnion hU_open)
    intro x hx hx₀
    obtain ⟨i, rfl⟩ := (hzero x hx).mp hx₀
    exact mem_iUnion.mpr ⟨i, hU_mem i⟩
  obtain ⟨d, hd, hdgap⟩ := hgap
  have hεcut : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ i,
      ε * (‖((A i).symm : Plane →L[ℝ] Plane)‖ * (1 + η)⁻¹) < r i := by
    apply Filter.eventually_all.mpr
    intro i
    exact eventually_mul_lt _ (hr i)
  have hL : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ i x, lower i (ε⁻¹ • (x - z i)) ≠ 0 → x ∈ U i :=
    Filter.eventually_all.mpr fun i => eventually_scaled_support (hsmooth i).2.2.1 (hU_open i) (hU_mem i)
  have hH : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ i x, upper i (ε⁻¹ • (x - z i)) ≠ 0 → x ∈ U i :=
    Filter.eventually_all.mpr fun i => eventually_scaled_support (hsmooth i).2.2.2 (hU_open i) (hU_mem i)
  have hall := hεcut.and (hL.and hH)
  obtain ⟨δ, hδ, hδall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hall
  dsimp
  refine ⟨lower, upper, min δ d, lt_min hδ hd, hsmooth, ?_, ?_, ?_⟩
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => by
      simpa only [div_eq_mul_inv] using hlIntegral i)
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => by
      simpa only [div_eq_mul_inv] using huIntegral i)
  · intro ε hε x
    obtain ⟨hcut, hls, hus⟩ := hδall ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
    obtain ⟨a₀, ha₀, _⟩ := existsUnique_lattice_representative q x
    let p := latticeVector a₀ + x
    let u (i : ι) := ε⁻¹ • (p - z i)
    have hp : p ∈ halfOpenCell q := ha₀
    have hFx : F p = F x := hperiod a₀ x
    have hscaled (i : ι) : ε • u i = p - z i := by
      dsimp [u]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hε.1), one_smul]
    have hdist (i : ι) : ε * ‖u i‖ = dist p (z i) := by
      rw [← abs_of_pos hε.1, ← Real.norm_eq_abs, ← norm_smul, hscaled, dist_eq_norm]
    have hshift (i : ι) : z i + ε • u i = p := by
      rw [hscaled, add_sub_cancel]
    have hlocal (i : ι) :
        lower i (u i) ≤ (if dist p (z i) < r i ∧ ‖F x‖ < ε then 1 else 0) ∧
        (if dist p (z i) < r i ∧ ‖F x‖ < ε then 1 else 0) ≤ upper i (u i) := by
      simpa only [hdist i, hshift i, hFx] using
        hLocal i ε hε.1 (hcut i) (u i)
    have hlo (i : ι) : lower i (u i) ≤ (if ‖F x‖ < ε then 1 else 0) := by
      refine (hlocal i).1.trans ?_
      by_cases hq : ‖F x‖ < ε <;> by_cases hr' : dist p (z i) < r i <;> simp [hq, hr']
    have hup (i : ι) : 0 ≤ upper i (u i) := by
      apply le_trans _ (hlocal i).2
      split_ifs <;> norm_num
    have hsumL :
        (∑ i, ∑' a : Fin 2 → ℤ, lower i (ε⁻¹ • (latticeVector a + x - z i))) =
          ∑ i, lower i (u i) := Finset.sum_congr rfl fun i _ =>
      periodization_eq_single_representative (fun y => lower i (ε⁻¹ • (y - z i)))
        (fun y hy => openCell_subset_halfOpen _ (hUi_openCell i (hls i y hy))) hp
    have hsumU :
        (∑ i, ∑' a : Fin 2 → ℤ, upper i (ε⁻¹ • (latticeVector a + x - z i))) =
          ∑ i, upper i (u i) := Finset.sum_congr rfl fun i _ =>
      periodization_eq_single_representative (fun y => upper i (ε⁻¹ • (y - z i)))
        (fun y hy => openCell_subset_halfOpen _ (hUi_openCell i (hus i y hy))) hp
    rw [hsumL, hsumU]
    constructor
    · apply lower_sum_le (by split_ifs <;> norm_num) hlo
      intro i j hi hj
      by_contra hij
      exact (Set.disjoint_left.mp (hU_disjoint hij)) (hls i p hi) (hls j p hj)
    · by_cases hsmall : ‖F x‖ < ε
      · have hpU : p ∈ ⋃ i, U i := by
          by_contra hn
          have hle := hdgap p ⟨halfOpenCell_subset_closed q hp, hn⟩
          have hεd := hε.2.trans_le (min_le_right δ d)
          exact (not_lt_of_ge hle) (hFx ▸ hsmall.trans hεd)
        obtain ⟨i, hi⟩ := mem_iUnion.mp hpU
        have hnear : dist p (z i) < r i := hi.1.1
        simp only [hsmall, ite_true]
        apply le_trans _ (Finset.single_le_sum (fun j _ => hup j) (Finset.mem_univ i))
        simpa only [hnear, hsmall, and_self, ite_true] using (hlocal i).2
      · simpa only [hsmall, ite_false] using Finset.sum_nonneg (fun i _ => hup i)

end

end Omega.Analysis.PeriodicSublevelSandwich
