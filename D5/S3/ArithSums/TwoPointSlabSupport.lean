/- GID: D5/S3/ArithSums/TwoPointSlabSupport
   generality: G
   mirror-B: D5/B/S3/ArithSums/TwoPointSlabSupport
   mirror-E: none(waiver:universal-real-support-theorem)
   anchors: []
   utility: none
   digest: Two-point corners give slab support and strictly positive zero-shape offsets. -/

import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ArithSums.TwoPointSlabSupport

open Set
open scoped BigOperators

/-- Distance from a set to an actual pair of points. The next theorem identifies
this minimum with an attained set-to-set distance whenever the set is compact. -/
def pairDistance {α : Type*} [PseudoMetricSpace α] (s : Set α) (c d : α) : ℝ :=
  min (Metric.infDist c s) (Metric.infDist d s)

/-- Each coordinate is an actual endpoint, including coincident endpoints. -/
def IsCorner {ι α : Type*} (c d x : ι → α) : Prop :=
  ∀ i, x i ∈ ({c i, d i} : Set α)

/-- A closed slab contains two distinct actual corner budget values. -/
def WideSlab {ι : Type*} [Fintype ι] (c d : ι → ℝ) (M₀ M₁ : ℝ) : Prop :=
  M₀ < M₁ ∧ ∃ x y, IsCorner c d x ∧ IsCorner c d y ∧
    (∑ i, x i) ∈ Icc M₀ M₁ ∧ (∑ i, y i) ∈ Icc M₀ M₁ ∧
    (∑ i, x i) ≠ ∑ i, y i

/-- Natural logarithmic coordinate widths for the ordered primes 2, 3, 7. -/
def logWidths : Fin 3 → ℝ := ![Real.log 2, Real.log 3, Real.log 7]

/-- Nonnegativity, attainment, and comparison with every pair of actual points
characterize the genuine minimum distance between a compact set and a pair. -/
theorem pair_distance_spec {α : Type*} [PseudoMetricSpace α]
    (s : Set α) (hs : IsCompact s) (hne : s.Nonempty) (c d : α) :
    0 ≤ pairDistance s c d ∧
    (∃ y ∈ s, ∃ z ∈ ({c, d} : Set α), pairDistance s c d = dist y z) ∧
    (∀ y ∈ s, ∀ z ∈ ({c, d} : Set α), pairDistance s c d ≤ dist y z) := by
  refine ⟨le_min Metric.infDist_nonneg Metric.infDist_nonneg, ?_, ?_⟩
  · rcases le_total (Metric.infDist c s) (Metric.infDist d s) with h | h
    · obtain ⟨y, hy, he⟩ := hs.exists_infDist_eq_dist hne c
      exact ⟨y, hy, c, by simp, by simpa [pairDistance, min_eq_left h, dist_comm] using he⟩
    · obtain ⟨y, hy, he⟩ := hs.exists_infDist_eq_dist hne d
      exact ⟨y, hy, d, by simp, by simpa [pairDistance, min_eq_right h, dist_comm] using he⟩
  · intro y hy z hz
    rcases mem_insert_iff.mp hz with hz | hz
    · subst z
      exact (min_le_left _ _).trans (by simpa [dist_comm] using
        (Metric.infDist_le_dist_of_mem (x := c) hy))
    · have hz : z = d := mem_singleton_iff.mp hz
      subst z
      exact (min_le_right _ _).trans (by simpa [dist_comm] using
        (Metric.infDist_le_dist_of_mem (x := d) hy))

private theorem corner_iff_choice {ι : Type*} (c h x : ι → ℝ) :
    IsCorner c (fun i => c i + h i) x ↔
      ∃ e : ι → Bool, x = fun i => c i + if e i then h i else 0 := by
  classical
  constructor
  · intro hx
    have he (i : ι) : ∃ b : Bool, x i = c i + if b then h i else 0 := by
      rcases mem_insert_iff.mp (hx i) with hi | hi
      · exact ⟨false, by simpa using hi⟩
      · exact ⟨true, by simpa using mem_singleton_iff.mp hi⟩
    choose e he using he
    exact ⟨e, funext he⟩
  · rintro ⟨e, rfl⟩ i
    cases hi : e i <;> simp [hi]

private theorem centered_square_identity {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (m T : ℝ) (hm : ∑ i, x i = Fintype.card ι * m) :
    (∑ i, (x i - m) ^ 2) = (∑ i, (x i - T) ^ 2) -
      Fintype.card ι * (m - T) ^ 2 := by
  have hpoint (i : ι) : (x i - m) ^ 2 = (x i - T) ^ 2 +
      (2 * (T - m)) * x i + (m ^ 2 - T ^ 2) := by ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hm]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

private theorem centered_square_bound {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (m T : ℝ) (hm : ∑ i, x i = Fintype.card ι * m)
    (hx : ∀ i, T ≤ x i) :
    (∑ i, (x i - m) ^ 2) ≤
      (Fintype.card ι : ℝ) * (Fintype.card ι - 1) * (m - T) ^ 2 := by
  have hsum : (∑ i, (x i - T)) = Fintype.card ι * (m - T) := by
    rw [Finset.sum_sub_distrib, hm]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i => x i - T) (fun i _ => sub_nonneg.mpr (hx i))
  rw [hsum] at hsq
  rw [centered_square_identity x m T hm]
  nlinarith

private theorem log_widths_bounds :
    0 < Real.log 2 ∧ ∀ i, Real.log 2 ≤ logWidths i := by
  refine ⟨Real.log_pos (by norm_num), ?_⟩
  intro i
  fin_cases i
  · exact le_rfl
  · exact Real.log_le_log (by norm_num) (by norm_num)
  · exact Real.log_le_log (by norm_num) (by norm_num)

private theorem offset_nonneg (e : Fin 3 → Bool) :
    0 ≤ ∑ i, if e i then logWidths i else 0 := by
  apply Finset.sum_nonneg
  intro i _
  split <;> first | exact (log_widths_bounds.1.le.trans (log_widths_bounds.2 i)) | rfl

private theorem offset_ge_log_two (e : Fin 3 → Bool)
    (he : 0 < ∑ i, if e i then logWidths i else 0) :
    Real.log 2 ≤ ∑ i, if e i then logWidths i else 0 := by
  classical
  have hex : ∃ i, e i = true := by
    by_contra! hn
    have hz : (∑ i, if e i then logWidths i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp [hn i]
    linarith
  obtain ⟨i, hi⟩ := hex
  calc
    Real.log 2 ≤ logWidths i := log_widths_bounds.2 i
    _ = (if e i then logWidths i else 0) := by simp [hi]
    _ ≤ ∑ j, if e j then logWidths j else 0 :=
      Finset.single_le_sum (f := fun j => if e j then logWidths j else 0) (fun j _ => by
        split <;> first | exact log_widths_bounds.1.le.trans (log_widths_bounds.2 j) | rfl)
        (Finset.mem_univ i)

private theorem corner_estimate (T M₀ M₁ : ℝ) (c d x : Fin 3 → ℝ)
    (hc : ∀ i, T ≤ c i) (hd : ∀ i, T ≤ d i)
    (hx : IsCorner c d x) (hb : (∑ i, x i) ∈ Icc M₀ M₁) :
    let m := (∑ i, x i) / 3
    let δ := fun i => pairDistance (Icc (M₀ / 3) (M₁ / 3)) (c i) (d i)
    let V := ∑ i, δ i ^ 2
    let ρ := Real.sqrt (V / 6)
    m ∈ Icc (M₀ / 3) (M₁ / 3) ∧
    (∀ i, 0 ≤ x i - T) ∧
    V ≤ ∑ i, (x i - m) ^ 2 ∧
    (∑ i, (x i - m) ^ 2) = (∑ i, (x i - T) ^ 2) - 3 * (m - T) ^ 2 ∧
    (∑ i, (x i - T) ^ 2) - 3 * (m - T) ^ 2 ≤ 6 * (m - T) ^ 2 ∧
    0 ≤ ρ ∧ ρ ≤ m - T ∧ m - T ≤ M₁ / 3 - T := by
  dsimp only
  let m := (∑ i, x i) / 3
  let δ := fun i => pairDistance (Icc (M₀ / 3) (M₁ / 3)) (c i) (d i)
  have hm : ∑ i, x i = 3 * m := by dsimp [m]; ring
  have hmem : m ∈ Icc (M₀ / 3) (M₁ / 3) := by
    constructor <;> dsimp [m] <;> linarith [hb.1, hb.2]
  have hTx (i) : T ≤ x i := by
    rcases mem_insert_iff.mp (hx i) with hi | hi
    · rw [hi]; exact hc i
    · rw [mem_singleton_iff.mp hi]; exact hd i
  have hmean : 0 ≤ m - T := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hTx i)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using (show 0 ≤ m - T by
        norm_num at h
        linarith)
  have hdist (i) := pair_distance_spec _ isCompact_Icc ⟨m, hmem⟩ (c i) (d i)
  have hδ (i) : δ i ≤ |x i - m| := by
    simpa only [δ, Real.dist_eq, abs_sub_comm] using (hdist i).2.2 m hmem (x i) (hx i)
  have hV : (∑ i, δ i ^ 2) ≤ ∑ i, (x i - m) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    have hnonneg : 0 ≤ δ i := (hdist i).1
    have hsq := (sq_le_sq₀ hnonneg (abs_nonneg (x i - m))).mpr (hδ i)
    simpa only [sq_abs] using hsq
  have hid : (∑ i, (x i - m) ^ 2) =
      (∑ i, (x i - T) ^ 2) - 3 * (m - T) ^ 2 :=
    centered_square_identity x m T (by simpa using hm)
  have hbound : (∑ i, (x i - m) ^ 2) ≤ 6 * (m - T) ^ 2 := by
    convert centered_square_bound x m T (by simpa using hm) hTx using 1; norm_num
  have hr : Real.sqrt ((∑ i, δ i ^ 2) / 6) ≤ m - T :=
    Real.sqrt_le_iff.mpr ⟨hmean, by nlinarith⟩
  exact ⟨hmem, fun i => sub_nonneg.mpr (hTx i), hV, hid,
    by change (∑ i, (x i - T) ^ 2) - 3 * (m - T) ^ 2 ≤ 6 * (m - T) ^ 2
       linarith, Real.sqrt_nonneg _, hr, by linarith [hmem.2]⟩

private theorem zero_shape_upper_budget (T M₀ M₁ : ℝ)
    (hW : WideSlab (fun _ : Fin 3 => T) (fun i => T + logWidths i) M₀ M₁) :
    Real.log 2 ≤ M₁ - 3 * T := by
  obtain ⟨_, x, y, hx, hy, hbx, hby, hne⟩ := hW
  obtain ⟨e, he⟩ := (corner_iff_choice (fun _ => T) logWidths x).mp hx
  obtain ⟨f, hf⟩ := (corner_iff_choice (fun _ => T) logWidths y).mp hy
  have hsum (g : Fin 3 → Bool) :
      (∑ i, (T + if g i then logWidths i else 0)) =
        3 * T + ∑ i, if g i then logWidths i else 0 := by
    rw [Finset.sum_add_distrib]
    simp
  subst x
  subst y
  simp only [hsum] at hbx hby hne
  have he0 := offset_nonneg e
  have hf0 := offset_nonneg f
  by_cases hp : 0 < ∑ i, if e i then logWidths i else 0
  · have ha := offset_ge_log_two e hp
    linarith [hbx.2]
  · have hq : 0 < ∑ i, if f i then logWidths i else 0 := by
      by_contra hq
      have : (∑ i, if e i then logWidths i else 0) = 0 := by linarith
      have : (∑ i, if f i then logWidths i else 0) = 0 := by linarith
      apply hne
      linarith
    have ha := offset_ge_log_two f hq
    linarith [hby.2]

private theorem zero_shape_support (T M₀ M₁ : ℝ)
    (hW : WideSlab (fun _ : Fin 3 => T) (fun i => T + logWidths i) M₀ M₁) :
    let δ := fun i => pairDistance (Icc (M₀ / 3) (M₁ / 3)) T (T + logWidths i)
    let ρ := Real.sqrt ((∑ i, δ i ^ 2) / 6)
    let L := M₁ / 3 - ρ
    let H := M₁ / 3 + 2 * ρ
    let u := M₀ - 3 * T
    let v := M₁ - 3 * T
    Real.log 2 ≤ v ∧ u < v ∧
    (u ≤ 0 → (∀ i, δ i = 0) ∧ ρ = 0 ∧ L = T + v / 3 ∧ T < L) ∧
    (0 < u → (∀ i, δ i ≤ u / 3) ∧ ρ ≤ u / (3 * Real.sqrt 2) ∧
      T + (v - u / Real.sqrt 2) / 3 ≤ L ∧ T < T + (v - u / Real.sqrt 2) / 3) ∧
    0 < L - T ∧ L - T ≤ H - T := by
  dsimp only
  let δ := fun i => pairDistance (Icc (M₀ / 3) (M₁ / 3)) T (T + logWidths i)
  let ρ := Real.sqrt ((∑ i, δ i ^ 2) / 6)
  let u := M₀ - 3 * T
  let v := M₁ - 3 * T
  have hv : Real.log 2 ≤ v := zero_shape_upper_budget T M₀ M₁ hW
  have hvp : 0 < v := log_widths_bounds.1.trans_le hv
  have huv : u < v := by dsimp [u, v]; linarith [hW.1]
  have hρ : 0 ≤ ρ := Real.sqrt_nonneg _
  have hδnonneg (i) : 0 ≤ δ i := le_min Metric.infDist_nonneg Metric.infDist_nonneg
  have hzero (hu : u ≤ 0) : (∀ i, δ i = 0) ∧ ρ = 0 ∧
      M₁ / 3 - ρ = T + v / 3 ∧ T < M₁ / 3 - ρ := by
    have hT : T ∈ Icc (M₀ / 3) (M₁ / 3) := by
      constructor <;> dsimp [u, v] at * <;> linarith
    have hδzero (i) : δ i = 0 := by
      apply le_antisymm _ (hδnonneg i)
      exact (min_le_left _ _).trans_eq (Metric.infDist_zero_of_mem hT)
    have hrzero : ρ = 0 := by simp [ρ, hδzero]
    refine ⟨hδzero, hrzero, ?_, ?_⟩
    · rw [hrzero]; dsimp [v]; ring
    · rw [hrzero]; dsimp [v] at hvp; linarith
  have hpositive (hu : 0 < u) : (∀ i, δ i ≤ u / 3) ∧
      ρ ≤ u / (3 * Real.sqrt 2) ∧
      T + (v - u / Real.sqrt 2) / 3 ≤ M₁ / 3 - ρ ∧
      T < T + (v - u / Real.sqrt 2) / 3 := by
    have hleft : M₀ / 3 ∈ Icc (M₀ / 3) (M₁ / 3) :=
      ⟨le_rfl, by linarith [hW.1]⟩
    have hd (i) : δ i ≤ u / 3 := by
      calc
        δ i ≤ Metric.infDist T (Icc (M₀ / 3) (M₁ / 3)) := min_le_left _ _
        _ ≤ dist T (M₀ / 3) := Metric.infDist_le_dist_of_mem hleft
        _ = u / 3 := by
          have hsign : T - M₀ / 3 ≤ 0 := by dsimp [u] at hu; linarith
          rw [Real.dist_eq, abs_of_nonpos hsign]
          dsimp [u]
          ring
    have hV : (∑ i, δ i ^ 2) ≤ 3 * (u / 3) ^ 2 := by
      calc
        _ ≤ ∑ _ : Fin 3, (u / 3) ^ 2 := Finset.sum_le_sum (fun i _ =>
          (sq_le_sq₀ (hδnonneg i) (by positivity)).mpr (hd i))
        _ = _ := by simp
    have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hquot : (u / (3 * Real.sqrt 2)) ^ 2 = (u / 3) ^ 2 / 2 := by
      rw [div_pow, mul_pow, hs2]
      ring
    have hr : ρ ≤ u / (3 * Real.sqrt 2) := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      rw [hquot]
      nlinarith
    have hless : u / Real.sqrt 2 < u :=
      (div_lt_self hu Real.one_lt_sqrt_two)
    refine ⟨hd, hr, ?_, by linarith⟩
    dsimp [v]
    have hdiv : u / (3 * Real.sqrt 2) = (u / Real.sqrt 2) / 3 := by ring
    rw [hdiv] at hr
    linarith
  refine ⟨hv, huv, hzero, hpositive, ?_, ?_⟩
  · rcases le_or_gt u 0 with hu | hu
    · linarith [(hzero hu).2.2.2]
    · linarith [(hpositive hu).2.2.1, (hpositive hu).2.2.2]
  · linarith

/-- Complete three-coordinate support for the logarithmic (2,3,7) box.
All budgets and shapes are real. The strict zero-shape conclusion is derived
from two distinct included budget values, and both lower-budget branches are
retained. No positive-variance, integer-exponent, or cutoff condition is used. -/
theorem wide_slab_support_237 (T M₀ M₁ : ℝ) (ξ : Fin 3 → ℝ)
    (hT : Real.log 2 ≤ T) (hξ : ∀ i, 0 ≤ ξ i) (_hmin : ∃ i, ξ i = 0)
    (hW : WideSlab (fun i => T + ξ i) (fun i => T + ξ i + logWidths i) M₀ M₁) :
    let c := fun i => T + ξ i
    let d := fun i => c i + logWidths i
    let A := 3 * T + ∑ i, ξ i
    let I := Icc (M₀ / 3) (M₁ / 3)
    let δ := fun i => pairDistance I (c i) (d i)
    let V₀ := ∑ i, δ i ^ 2
    let μ := M₁ / 3
    let ρ := Real.sqrt (V₀ / 6)
    let L := μ - ρ
    let H := μ + 2 * ρ
    let offset := fun e : Fin 3 → Bool => ∑ i, if e i then logWidths i else 0
    (∀ x, IsCorner c d x ↔ ∃ e : Fin 3 → Bool,
      x = fun i => c i + if e i then logWidths i else 0) ∧
    (∀ e : Fin 3 → Bool, (∑ i, (c i + if e i then logWidths i else 0)) = A + offset e) ∧
    (∀ i, 0 ≤ δ i ∧ (∃ y ∈ I, ∃ z ∈ ({c i, d i} : Set ℝ), δ i = dist y z) ∧
      (∀ y ∈ I, ∀ z ∈ ({c i, d i} : Set ℝ), δ i ≤ dist y z)) ∧
    (∀ x, IsCorner c d x → (∑ i, x i) ∈ Icc M₀ M₁ →
      let m := (∑ i, x i) / 3
      m ∈ I ∧ (∀ i, 0 ≤ x i - T) ∧ V₀ ≤ ∑ i, (x i - m) ^ 2 ∧
      (∑ i, (x i - m) ^ 2) = (∑ i, (x i - T) ^ 2) - 3 * (m - T) ^ 2 ∧
      (∑ i, (x i - T) ^ 2) - 3 * (m - T) ^ 2 ≤ 6 * (m - T) ^ 2 ∧
      0 ≤ ρ ∧ ρ ≤ m - T ∧ m - T ≤ μ - T) ∧
    L ≤ H ∧ T ≤ L ∧ 0 < T ∧
    IsLeast (range offset) 0 ∧ IsLeast {r | r ∈ range offset ∧ 0 < r} (Real.log 2) ∧
    (ξ = 0 →
      let u := M₀ - 3 * T
      let v := M₁ - 3 * T
      Real.log 2 ≤ v ∧ u < v ∧
      (u ≤ 0 → (∀ i, δ i = 0) ∧ ρ = 0 ∧ L = T + v / 3 ∧ T < L) ∧
      (0 < u → (∀ i, δ i ≤ u / 3) ∧ ρ ≤ u / (3 * Real.sqrt 2) ∧
        T + (v - u / Real.sqrt 2) / 3 ≤ L ∧ T < T + (v - u / Real.sqrt 2) / 3) ∧
      0 < L - T ∧ L - T ≤ H - T) := by
  dsimp only
  let c := fun i => T + ξ i
  let d := fun i => c i + logWidths i
  let I := Icc (M₀ / 3) (M₁ / 3)
  let δ := fun i => pairDistance I (c i) (d i)
  let ρ := Real.sqrt ((∑ i, δ i ^ 2) / 6)
  have hc (i) : T ≤ c i := by dsimp [c]; linarith [hξ i]
  have hd (i) : T ≤ d i := by
    dsimp [d]
    linarith [hc i, log_widths_bounds.1, log_widths_bounds.2 i]
  have hcorner := corner_estimate T M₀ M₁ c d
  obtain ⟨x, y, hx, _, hbx, _, _⟩ := hW.2
  obtain ⟨_, _, _, _, _, _, hr, hm⟩ := hcorner x hc hd hx hbx
  have hL : T ≤ M₁ / 3 - ρ := by change ρ ≤ _ at hr; linarith
  refine ⟨fun x => corner_iff_choice c logWidths x, ?_, ?_,
    fun x hx hb => hcorner x hc hd hx hb, ?_, hL, log_widths_bounds.1.trans_le hT,
    ?_, ?_, ?_⟩
  · intro e
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  · intro i
    exact pair_distance_spec I isCompact_Icc
      ⟨M₀ / 3, le_rfl, by linarith [hW.1]⟩ (c i) (d i)
  · have := Real.sqrt_nonneg ((∑ i, δ i ^ 2) / 6)
    change M₁ / 3 - ρ ≤ M₁ / 3 + 2 * ρ
    change 0 ≤ ρ at this
    linarith
  · constructor
    · exact ⟨fun _ => false, by simp⟩
    · rintro r ⟨e, rfl⟩
      exact offset_nonneg e
  · constructor
    · refine ⟨⟨![true, false, false], ?_⟩, log_widths_bounds.1⟩
      simp [Fin.sum_univ_succ, logWidths]
    · rintro r ⟨⟨e, rfl⟩, he⟩
      exact offset_ge_log_two e he
  · intro hzero
    have hWzero : WideSlab (fun _ : Fin 3 => T)
        (fun i => T + logWidths i) M₀ M₁ := by simpa [hzero] using hW
    simpa only [hzero, Pi.zero_apply, add_zero] using zero_shape_support T M₀ M₁ hWzero

#print axioms pair_distance_spec
#print axioms wide_slab_support_237

end D5.S3.ArithSums.TwoPointSlabSupport
