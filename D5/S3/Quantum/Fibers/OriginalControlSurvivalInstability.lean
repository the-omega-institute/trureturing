/- GID: D5/S3/Quantum/Fibers/OriginalControlSurvivalInstability
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/OriginalControlSurvivalInstability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Triangular original controls preserve survival loss under uniform height convergence. -/

import D5.S3.Quantum.Fibers.OriginalControlComposition
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Scalar original controls with uniformly small heights and fixed survival loss. -/

noncomputable section
namespace D5.S3.Quantum.Fibers.OriginalControlSurvivalInstability
open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval
open D5.S3.Quantum.Fibers.FiniteRectangleTransport
open D5.S3.Quantum.Fibers.OriginalControlComposition
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option relaxedAutoImplicit false

def doubleWall (c : ℝ) : Base := (c, c, 1 - 2 * c)

def tent (n j : ℕ) (t : ℝ) : ℝ :=
  max 0 (min (t - (j : ℝ) / n) (((j : ℝ) + 1) / n - t))

def triangle (c : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  c / 2 * ∑ j ∈ Finset.range n, tent n j t

def height (c : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  c / 2 - triangle c n t / (2 - t)

def hazard (c : ℝ) (k : ℝ → ℝ) (t : ℝ) : ℝ :=
  max (deriv k t) 0 / k t + max (-deriv k t) 0 / (c - k t)

def survival (c : ℝ) (k : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(∫ u in (0 : ℝ)..t, hazard c k u))

def coordinateLength (k chi : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, Real.sqrt ((deriv k t)^2 + (deriv chi t)^2)

def quadraticCost (k chi : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (deriv k t)^2 + (deriv chi t)^2

private theorem triangle_continuous (c : ℝ) (n : ℕ) : Continuous (triangle c n) := by
  unfold triangle
  fun_prop [tent]

private theorem triangle_cycle (c : ℝ) (n j : ℕ) (hn : 0 < n) (hj : j < n)
    (t : ℝ) (ht : t ∈ Icc ((j : ℝ) / n) (((j : ℝ) + 1) / n)) :
    triangle c n t = c / 2 * min (t - (j : ℝ) / n) (((j : ℝ) + 1) / n - t) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  unfold triangle
  congr 1
  rw [Finset.sum_eq_single j]
  · simp only [tent]
    exact max_eq_right (le_min (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2))
  · intro i hi hij
    dsimp [tent]
    apply max_eq_left
    rcases lt_or_gt_of_ne hij with h | h
    · apply (min_le_right _ _).trans
      have hle : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      have := (div_le_div_of_nonneg_right hle hn'.le).trans ht.1
      linarith
    · apply (min_le_left _ _).trans
      have hle : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      have := ht.2.trans (div_le_div_of_nonneg_right hle hn'.le)
      linarith
  · intro h; exact (h (Finset.mem_range.mpr hj)).elim

private theorem cycle_cover (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ j < n, t ∈ Icc ((j : ℝ) / n) (((j : ℝ) + 1) / n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  by_cases he : t = 1
  · subst t
    refine ⟨n - 1, by omega, ?_, ?_⟩
    · apply (div_le_iff₀ hn').mpr
      simp
    · have he : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast (Nat.sub_add_cancel hn)
      rw [he, div_self hn'.ne']
  · have ht' : t < 1 := lt_of_le_of_ne ht.2 he
    refine ⟨⌊(n : ℝ) * t⌋₊, ?_, ?_, ?_⟩
    · apply (Nat.floor_lt (mul_nonneg hn'.le ht.1)).mpr
      nlinarith
    · apply (div_le_iff₀ hn').mpr
      simpa [mul_comm] using Nat.floor_le (mul_nonneg hn'.le ht.1)
    · apply (le_div_iff₀ hn').mpr
      simpa [mul_comm] using (Nat.lt_floor_add_one ((n : ℝ) * t)).le

private theorem triangle_bounds (c : ℝ) (n : ℕ) (hc : 0 < c) (hn : 0 < n)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ triangle c n t ∧ triangle c n t ≤ c / (4 * n) := by
  obtain ⟨j, hj, hjt⟩ := cycle_cover n hn t ht
  rw [triangle_cycle c n j hn hj t hjt]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsum : (t - (j : ℝ) / n) + (((j : ℝ) + 1) / n - t) = 1 / (n : ℝ) := by ring
  have hmin : min (t - (j : ℝ) / n) (((j : ℝ) + 1) / n - t) ≤ 1 / (2 * n) := by
    have h1 := min_le_left (t - (j : ℝ) / n) (((j : ℝ) + 1) / n - t)
    have h2 := min_le_right (t - (j : ℝ) / n) (((j : ℝ) + 1) / n - t)
    have he : 1 / (2 * (n : ℝ))= (1 / (n : ℝ)) / 2 := by ring
    rw [he]; linarith
  constructor
  · exact mul_nonneg (by positivity) (le_min (by linarith [hjt.1]) (by linarith [hjt.2]))
  · calc
      _ ≤ c / 2 * (1 / (2 * n)) := mul_le_mul_of_nonneg_left hmin (by positivity)
      _ = _ := by ring

private theorem height_bounds (c : ℝ) (n : ℕ) (hc : 0 < c) (hn : 0 < n)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    c / 4 ≤ height c n t ∧ height c n t ≤ c / 2 ∧ |height c n t - c / 2| ≤ c / (4 * n) := by
  obtain ⟨h0, h1⟩ := triangle_bounds c n hc hn t ht
  have hd : 1 ≤ 2 - t := by linarith [ht.2]
  have hdiv : 0 ≤ triangle c n t / (2 - t) := div_nonneg h0 (by linarith)
  have hdiv' : triangle c n t / (2 - t) ≤ c / (4 * n) :=
    (div_le_self h0 hd).trans h1
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hquarter : c / (4 * (n : ℝ)) ≤ c / 4 := by
    apply div_le_div_of_nonneg_left hc.le (by norm_num) (by nlinarith)
  dsimp [height]
  rw [show c / 2 - triangle c n t / (2 - t) - c / 2 = -(triangle c n t / (2 - t)) by ring,
    abs_neg, abs_of_nonneg hdiv]
  exact ⟨by linarith, by linarith, hdiv'⟩

private theorem triangle_legs (c : ℝ) (n j : ℕ) (hn : 0 < n) (hj : j < n) :
    (∀ t ∈ Icc ((j : ℝ) / n) (((j : ℝ) + 1 / 2) / n),
      triangle c n t = c / 2 * (t - (j : ℝ) / n)) ∧
    (∀ t ∈ Icc (((j : ℝ) + 1 / 2) / n) (((j : ℝ) + 1) / n),
      triangle c n t = c / 2 * (((j : ℝ) + 1) / n - t)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hm : (j : ℝ) / n ≤ ((j : ℝ) + 1 / 2) / n :=
    div_le_div_of_nonneg_right (by linarith) hn'.le
  have hm' : ((j : ℝ) + 1 / 2) / n ≤ ((j : ℝ) + 1) / n :=
    div_le_div_of_nonneg_right (by linarith) hn'.le
  have he : (j : ℝ) / n + ((j : ℝ) + 1) / n = 2 * (((j : ℝ) + 1 / 2) / n) := by ring
  constructor
  · intro t ht
    rw [triangle_cycle c n j hn hj t ⟨ht.1, ht.2.trans hm'⟩,
      min_eq_left (by linarith [ht.2])]
  · intro t ht
    rw [triangle_cycle c n j hn hj t ⟨hm.trans ht.1, ht.2⟩,
      min_eq_right (by linarith [ht.1])]

private theorem triangle_leg_derivs (c : ℝ) (n j : ℕ) (hn : 0 < n) (hj : j < n) :
    (∀ t ∈ Ioo ((j : ℝ) / n) (((j : ℝ) + 1 / 2) / n), HasDerivAt (triangle c n) (c / 2) t) ∧
    (∀ t ∈ Ioo (((j : ℝ) + 1 / 2) / n) (((j : ℝ) + 1) / n), HasDerivAt (triangle c n) (-c / 2) t) := by
  obtain ⟨hr, hf⟩ := triangle_legs c n j hn hj
  constructor
  · intro t ht
    have hd := ((hasDerivAt_id t).sub_const ((j : ℝ) / n)).const_mul (c / 2)
    simp only [mul_one] at hd
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    exact hr x ⟨hx.1.le, hx.2.le⟩
  · intro t ht
    have hd := ((hasDerivAt_const t (((j : ℝ) + 1) / n)).sub (hasDerivAt_id t)).const_mul (c / 2)
    change HasDerivAt (fun x : ℝ => c / 2 * (((j : ℝ) + 1) / n - x)) (c / 2 * (0 - 1)) t at hd
    have hd' : HasDerivAt (fun x : ℝ => c / 2 * (((j : ℝ) + 1) / n - x)) (-c / 2) t := by
      convert hd using 1 <;> ring
    apply hd'.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    exact hf x ⟨hx.1.le, hx.2.le⟩

private def rate (c : ℝ) (n : ℕ) (s t : ℝ) : ℝ :=
  -s / (2 - t) - triangle c n t / (2 - t)^2

private theorem height_deriv (c : ℝ) (n : ℕ) (s t : ℝ) (ht : t < 2)
    (hd : HasDerivAt (triangle c n) s t) : HasDerivAt (height c n) (rate c n s t) t := by
  have hne : (2 : ℝ) - t ≠ 0 := by linarith
  have hd' : HasDerivAt (height c n)
      (0 - (s * (2 - t) - triangle c n t * (0 - 1)) / (2 - t)^2) t :=
    (hasDerivAt_const t (c / 2)).sub
      (hd.div ((hasDerivAt_const t 2).sub (hasDerivAt_id t)) hne)
  convert hd' using 1
  dsimp [rate]
  field_simp [hne]
  ring

private theorem height_continuous (c : ℝ) (n : ℕ) :
    ContinuousOn (height c n) (Icc (0 : ℝ) 1) := by
  exact continuousOn_const.sub ((triangle_continuous c n).continuousOn.div
    (continuous_const.sub continuous_id).continuousOn (fun t ht => by linarith [ht.2]))

private theorem rate_continuous (c : ℝ) (n : ℕ) (s : ℝ) :
    ContinuousOn (rate c n s) (Icc (0 : ℝ) 1) := by
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, (2 : ℝ) - t ≠ 0 := fun t ht => by linarith [ht.2]
  exact (continuousOn_const.div (continuous_const.sub continuous_id).continuousOn hd).sub
    ((triangle_continuous c n).continuousOn.div
      ((continuous_const.sub continuous_id).pow 2).continuousOn
      (fun t ht => pow_ne_zero 2 (hd t ht)))

private def mesh (n j : ℕ) : ℝ := (j : ℝ) / (2 * n)

private theorem mesh_mono (n : ℕ) : Monotone (mesh n) := by
  intro i j hij
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (by positivity)

private theorem mesh_pair (n j : ℕ) :
    mesh n (2 * j) = (j : ℝ) / n ∧ mesh n (2 * j + 1) = ((j : ℝ) + 1 / 2) / n ∧
    mesh n (2 * j + 2) = ((j : ℝ) + 1) / n := by
  simp only [mesh, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  constructor
  · ring
  constructor <;> ring

private theorem mesh_inside (n j : ℕ) (hn : 0 < n) (hj : j < 2 * n) :
    uIcc (mesh n j) (mesh n (j + 1)) ⊆ Icc (0 : ℝ) 1 := by
  rw [uIcc_of_le (mesh_mono n (Nat.le_succ j))]
  intro t ht
  refine ⟨(by dsimp [mesh]; positivity : 0 ≤ mesh n j).trans ht.1, ht.2.trans ?_⟩
  dsimp [mesh]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
  norm_num only [one_mul]
  exact_mod_cast (show j + 1 ≤ 2 * n by omega)

private theorem height_finite_c1 (c phase : ℝ) (n : ℕ) (hn : 0 < n) :
    FiniteC1Control 1 (height c n) (fun _ => phase) := by
  refine ⟨2 * n, mesh n, mesh_mono n, by simp [mesh], ?_, ?_⟩
  · dsimp [mesh]; push_cast; exact div_self (by positivity)
  · intro m hm
    have hi := mesh_inside n m hn hm
    have hd (s : ℝ) := (rate_continuous c n s).mono hi
    have hj : m / 2 < n := by omega
    have he : m = 2 * (m / 2) ∨ m = 2 * (m / 2) + 1 := by omega
    rcases he with he | he
    · refine ⟨rate c n (c / 2), fun _ => 0, hd _, continuousOn_const, ?_⟩
      intro t ht
      have ht' := hi (by rw [uIcc_of_le (mesh_mono n (Nat.le_succ m))]; exact ⟨ht.1.le, ht.2.le⟩)
      have hleg : t ∈ Ioo (((m / 2 : ℕ) : ℝ) / n) ((((m / 2 : ℕ) : ℝ) + 1 / 2) / n) := by
        rw [he] at ht
        simpa only [(mesh_pair n (m / 2)).1, (mesh_pair n (m / 2)).2.1] using ht
      exact ⟨height_deriv c n (c / 2) t (by linarith [ht'.2])
        ((triangle_leg_derivs c n (m / 2) hn hj).1 t hleg), hasDerivAt_const t phase⟩
    · refine ⟨rate c n (-c / 2), fun _ => 0, hd _, continuousOn_const, ?_⟩
      intro t ht
      have ht' := hi (by rw [uIcc_of_le (mesh_mono n (Nat.le_succ m))]; exact ⟨ht.1.le, ht.2.le⟩)
      have hleg : t ∈ Ioo ((((m / 2 : ℕ) : ℝ) + 1 / 2) / n) ((((m / 2 : ℕ) : ℝ) + 1) / n) := by
        rw [he, show 2 * (m / 2) + 1 + 1 = 2 * (m / 2) + 2 by omega] at ht
        simpa only [(mesh_pair n (m / 2)).2.1, (mesh_pair n (m / 2)).2.2] using ht
      exact ⟨height_deriv c n (-c / 2) t (by linarith [ht'.2])
        ((triangle_leg_derivs c n (m / 2) hn hj).2 t hleg), hasDerivAt_const t phase⟩

private theorem family_original (c phase : ℝ) (n : ℕ) (hc : 0 < c) (hn : 0 < n) :
    OriginalControl (doubleWall c) 1 (height c n) (fun _ => phase) := by
  refine ⟨by norm_num, ?_, continuousOn_const, ?_, ?_, Or.inr (height_finite_c1 c phase n hn)⟩
  · simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using height_continuous c n
  · intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    obtain ⟨hl, hu, -⟩ := height_bounds c n hc hn t ht
    have hlo : lower (doubleWall c) = 0 := by simp [lower, doubleWall]; ring_nf; norm_num
    have hhi : upper (doubleWall c) = c := by simp [upper, doubleWall]
    rw [hlo, hhi]
    exact ⟨by linarith, by linarith⟩
  · exact (LipschitzWith.const phase).lipschitzOnWith.absolutelyContinuousOnInterval.boundedVariationOn

private theorem ae_signed_deriv (c : ℝ) (n : ℕ) (hn : 0 < n) :
    ∀ᵐ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      deriv (height c n) t = -(c - height c n t) / (2 - t) ∨
      deriv (height c n) t = height c n t / (2 - t) := by
  filter_upwards [(Set.countable_range (mesh n)).ae_notMem volume] with t ht htI
  obtain ⟨j, hj, hjt⟩ := cycle_cover n hn t htI
  have hne (m : ℕ) : t ≠ mesh n m := fun h => ht ⟨m, h.symm⟩
  have hstart : (j : ℝ) / n < t := lt_of_le_of_ne hjt.1 (by
    simpa only [(mesh_pair n j).1] using (hne (2 * j)).symm)
  have hend : t < ((j : ℝ) + 1) / n := lt_of_le_of_ne hjt.2 (by
    simpa only [(mesh_pair n j).2.2] using hne (2 * j + 2))
  have hmid : t ≠ ((j : ℝ) + 1 / 2) / n := by
    simpa only [(mesh_pair n j).2.1] using hne (2 * j + 1)
  have hd : (2 : ℝ) - t ≠ 0 := by linarith [htI.2]
  by_cases hu : t < ((j : ℝ) + 1 / 2) / n
  · left
    rw [(height_deriv c n (c / 2) t (by linarith [htI.2])
      ((triangle_leg_derivs c n j hn hj).1 t ⟨hstart, hu⟩)).deriv]
    dsimp [rate, height]
    field_simp [hd] <;> ring
  · right
    have hu' : ((j : ℝ) + 1 / 2) / n < t := lt_of_le_of_ne (le_of_not_gt hu) hmid.symm
    rw [(height_deriv c n (-c / 2) t (by linarith [htI.2])
      ((triangle_leg_derivs c n j hn hj).2 t ⟨hu', hend⟩)).deriv]
    dsimp [rate, height]
    field_simp [hd] <;> ring

private theorem ae_hazard_speed (c : ℝ) (n : ℕ) (hc : 0 < c) (hn : 0 < n) :
    ∀ᵐ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      hazard c (height c n) t = 1 / (2 - t) ∧ |deriv (height c n) t| ≤ 3 * c / 4 := by
  filter_upwards [ae_signed_deriv c n hn] with t ht htI
  obtain ⟨hl, hu, -⟩ := height_bounds c n hc hn t htI
  have hk : 0 < height c n t := by linarith
  have hck : 0 < c - height c n t := by linarith
  have hd : 0 < 2 - t := by linarith [htI.2]
  have hd1 : 1 ≤ 2 - t := by linarith [htI.2]
  rcases ht htI with he | he
  · have hneg : -(c - height c n t) / (2 - t) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
    constructor
    · dsimp [hazard]
      rw [he, max_eq_right hneg, max_eq_left (neg_nonneg.mpr hneg)]
      field_simp [hd.ne', hck.ne']
      ring
    · rw [he, abs_of_nonpos hneg]
      have hb : (c - height c n t) / (2 - t) ≤ 3 * c / 4 :=
        (div_le_iff₀ hd).mpr (by nlinarith)
      simpa only [neg_div, neg_neg] using hb
  · have hpos : 0 ≤ height c n t / (2 - t) := div_nonneg hk.le hd.le
    constructor
    · dsimp [hazard]
      rw [he, max_eq_left hpos, max_eq_right (neg_nonpos.mpr hpos)]
      field_simp [hd.ne', hk.ne'] <;> ring
    · rw [he, abs_of_nonneg hpos]
      apply (div_le_iff₀ hd).mpr
      nlinarith

private theorem inverse_integrable (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun u : ℝ => 1 / (2 - u)) volume 0 t := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le ht.1]
  exact continuousOn_const.div (continuous_const.sub continuous_id).continuousOn
    (fun u hu => by linarith [hu.2, ht.2])

private theorem actual_survival (c : ℝ) (n : ℕ) (hc : 0 < c) (hn : 0 < n)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (hazard c (height c n)) volume 0 t ∧
    survival c (height c n) t = 1 - t / 2 := by
  have he : ∀ᵐ u : ℝ, u ∈ Ι (0 : ℝ) t → hazard c (height c n) u = 1 / (2 - u) := by
    filter_upwards [ae_hazard_speed c n hc hn] with u hu huI
    rw [uIoc_of_le ht.1] at huI
    exact (hu ⟨huI.1.le, huI.2.trans ht.2⟩).1
  have hi := inverse_integrable t ht
  have hh : IntervalIntegrable (hazard c (height c n)) volume 0 t := by
    apply hi.congr_ae
    change ∀ᵐ u : ℝ ∂volume.restrict (Ι (0 : ℝ) t), 1 / (2 - u) = hazard c (height c n) u
    rw [ae_restrict_iff' measurableSet_uIoc]
    exact he.mono (fun u hu huI => (hu huI).symm)
  refine ⟨hh, ?_⟩
  have hint : (∫ u in (0 : ℝ)..t, 1 / (2 - u)) = -Real.log (1 - t / 2) := by
    have hprim : ∀ u ∈ uIcc (0 : ℝ) t,
        HasDerivAt (fun x : ℝ => -Real.log (1 - x / 2)) (1 / (2 - u)) u := by
      intro u hu
      rw [uIcc_of_le ht.1] at hu
      have hne : 1 - u / 2 ≠ 0 := by linarith [hu.2, ht.2]
      have hd := (((hasDerivAt_const u 1).sub ((hasDerivAt_id u).div_const 2)).log hne).neg
      change HasDerivAt (fun x : ℝ => -Real.log (1 - x / 2)) (-((0 - 1 / 2) / (1 - u / 2))) u at hd
      convert hd using 1
      field_simp [hne, (show (2 : ℝ) - u≠0 by linarith [hu.2, ht.2])]
      ring
    simpa using integral_eq_sub_of_hasDerivAt hprim hi
  unfold survival
  rw [integral_congr_ae he, hint, neg_neg, Real.exp_log (by linarith [ht.2])]

private theorem family_lipschitz (c : ℝ) (n : ℕ) (hc : 0 < c) (hn : 0 < n) :
    LipschitzOnWith (Real.toNNReal (3 * c / 4)) (height c n) (Icc (0 : ℝ) 1) := by
  have hac := (original_ac (doubleWall c) 1 (height c n) (fun _ => (0 : ℝ))
    (family_original c 0 n hc hn)).1
  apply LipschitzOnWith.of_dist_le'
  intro x hx y hy
  have hsub : uIcc y x ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact uIcc_subset_Icc hy hx
  have he := (hac.mono hsub).integral_deriv_eq_sub
  have hb : ∀ᵐ t : ℝ, t ∈ Ι y x → ‖deriv (height c n) t‖ ≤ 3 * c / 4 := by
    filter_upwards [ae_hazard_speed c n hc hn] with t ht htI
    apply (ht ?_).2
    exact (uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)) ▸ hsub (uIoc_subset_uIcc htI)
  have hnorm := norm_integral_le_of_norm_le_const_ae hb
  rw [he] at hnorm
  simpa only [Real.dist_eq, Real.norm_eq_abs] using hnorm

private theorem family_variation (c : ℝ) (n : ℕ) (hc : 0 < c) (hn : 0 < n) :
    eVariationOn (height c n) (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (3 * c / 4) := by
  have h := (family_lipschitz c n hc hn).comp_eVariationOn_le (mapsTo_id (Icc (0 : ℝ) 1))
  simpa [eVariationOn_id_Icc, ENNReal.ofReal] using h

private theorem family_costs (c phase : ℝ) (n : ℕ) (hc : 0 < c) (hn : 0 < n) :
    IntervalIntegrable (fun t : ℝ => Real.sqrt
      ((deriv (height c n) t)^2 + (deriv (fun _ : ℝ => phase) t)^2)) volume 0 1 ∧
    IntervalIntegrable (fun t : ℝ =>
      (deriv (height c n) t)^2 + (deriv (fun _ : ℝ => phase) t)^2) volume 0 1 ∧
    coordinateLength (height c n) (fun _ => phase) ≤ 3 * c / 4 ∧
    quadraticCost (height c n) (fun _ => phase) ≤ 9 * c^2 / 16 := by
  have hac := (original_ac (doubleWall c) 1 (height c n) (fun _ => phase)
    (family_original c phase n hc hn)).1
  have hiL := hac.intervalIntegrable_deriv.abs
  have hL : ∀ᵐ t : ℝ ∂volume.restrict (Icc (0 : ℝ) 1), |deriv (height c n) t| ≤ 3 * c / 4 := by
    rw [ae_restrict_iff' measurableSet_Icc]
    exact (ae_hazard_speed c n hc hn).mono (fun t ht htI => (ht htI).2)
  have hQ : ∀ᵐ t : ℝ ∂volume.restrict (Icc (0 : ℝ) 1),
      (deriv (height c n) t)^2 ≤ 9 * c^2 / 16 := by
    filter_upwards [hL] with t ht
    have hs := pow_le_pow_left₀ (abs_nonneg (deriv (height c n) t)) ht 2
    nlinarith [sq_abs (deriv (height c n) t)]
  have hiQ : IntervalIntegrable (fun t : ℝ => (deriv (height c n) t)^2) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    have hconst : IntegrableOn (fun _ : ℝ => 9 * c^2 / 16) (Icc (0 : ℝ) 1) volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
        intervalIntegrable_const
    apply hconst.mono' ((aestronglyMeasurable_deriv (height c n) _).pow 2)
    filter_upwards [hQ] with t ht
    change ‖(deriv (height c n) t)^2‖ ≤ 9 * c^2 / 16
    rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hbL := integral_mono_ae_restrict (by norm_num : (0 : ℝ) ≤ 1)
    hiL (intervalIntegrable_const (c:=3 * c / 4)) hL
  have hbQ := integral_mono_ae_restrict (by norm_num : (0 : ℝ) ≤ 1)
    hiQ (intervalIntegrable_const (c:=9 * c^2 / 16)) hQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [deriv_const, zero_pow (by decide : 2 ≠ 0), add_zero, Real.sqrt_sq_eq_abs] using hiL
  · simpa only [deriv_const, zero_pow (by decide : 2 ≠ 0), add_zero] using hiQ
  · simpa [coordinateLength, Real.sqrt_sq_eq_abs] using hbL
  · simpa [quadraticCost] using hbQ

private theorem family_endpoints (c : ℝ) (n : ℕ) (hn : 0 < n) :
    height c n 0 = c / 2 ∧ height c n 1 = c / 2 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h0 := (triangle_legs c n 0 hn hn).1 0
    (by constructor <;> norm_num <;> positivity)
  have he : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast (Nat.sub_add_cancel hn)
  have hmid : (((n - 1 : ℕ) : ℝ) + 1 / 2) / n ≤ 1 := by
    apply (div_le_iff₀ hn').mpr
    linarith
  have hend : (((n - 1 : ℕ) : ℝ) + 1) / n = 1 := by rw [he, div_self hn'.ne']
  have h1 := (triangle_legs c n (n - 1) hn (by omega)).2 1 ⟨hmid, hend.ge⟩
  constructor
  · simp [height, h0]
  · simp [height, h1, hend]

/-- One explicit family has all the common scalar resource bounds and its original hazard law. -/
theorem oscillatory_original_controls (c phase : ℝ) (n : ℕ)
    (hc : 0 < c) (hc' : c < 1 / 2) (hn : 1 ≤ n) :
    ValidBase (doubleWall c) ∧
    OriginalControl (doubleWall c) 1 (height c n) (fun _ => phase) ∧
    FiniteC1Control 1 (height c n) (fun _ => phase) ∧
    (AbsolutelyContinuousOnInterval (height c n) 0 1 ∧
      AbsolutelyContinuousOnInterval (fun _ : ℝ => phase) 0 1) ∧
    (height c n 0 = c / 2 ∧ height c n 1 = c / 2) ∧
    (∀ j < n,
      (∀ t ∈ Icc ((j : ℝ) / n) (((j : ℝ) + 1 / 2) / n), triangle c n t = c / 2 * (t - (j : ℝ) / n)) ∧
      (∀ t ∈ Icc (((j : ℝ) + 1 / 2) / n) (((j : ℝ) + 1) / n), triangle c n t = c / 2 * (((j : ℝ) + 1) / n - t))) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, c / 4 ≤ height c n t ∧ height c n t ≤ c / 2 ∧
      |height c n t - c / 2| ≤ c / (4 * n)) ∧
    (0 < min (c / 4) (1 - 2 * c) ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ i : Fin 5,
      min (c / 4) (1 - 2 * c) ≤ probability (doubleWall c) (height c n t) i) ∧
    LipschitzOnWith (Real.toNNReal (3 * c / 4)) (height c n) (Icc (0 : ℝ) 1) ∧
    eVariationOn (fun _ : ℝ => phase) (Icc (0 : ℝ) 1) = 0 ∧
    eVariationOn (height c n) (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (3 * c / 4) ∧
    (∀ t : ℝ, deriv (fun _ : ℝ => phase) t = 0) ∧
    (IntervalIntegrable (fun t : ℝ => Real.sqrt
      ((deriv (height c n) t)^2 + (deriv (fun _ : ℝ => phase) t)^2)) volume 0 1 ∧
      IntervalIntegrable (fun t : ℝ =>
        (deriv (height c n) t)^2 + (deriv (fun _ : ℝ => phase) t)^2) volume 0 1 ∧
      coordinateLength (height c n) (fun _ => phase) ≤ 3 * c / 4 ∧
      quadraticCost (height c n) (fun _ => phase) ≤ 9 * c^2 / 16) ∧
    (∀ᵐ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      hazard c (height c n) t = 1 / (2 - t) ∧ |deriv (height c n) t| ≤ 3 * c / 4) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, IntervalIntegrable (hazard c (height c n)) volume 0 t ∧
      survival c (height c n) t = 1 - t / 2) ∧
    OriginalControl (doubleWall c) 1 (fun _ => c / 2) (fun _ => phase) ∧
    (∀ t : ℝ, hazard c (fun _ => c / 2) t = 0 ∧ survival c (fun _ => c / 2) t = 1) := by
  have hn0 : 0 < n := hn
  have hOC := family_original c phase n hc hn0
  have hAC := original_ac (doubleWall c) 1 (height c n) (fun _ => phase) hOC
  refine ⟨?_, hOC, height_finite_c1 c phase n hn0, hAC, family_endpoints c n hn0,
    fun j hj => triangle_legs c n j hn0 hj, height_bounds c n hc hn0, ?_,
    family_lipschitz c n hc hn0, ?_, family_variation c n hc hn0, fun t => deriv_const t phase,
    family_costs c phase n hc hn0, ae_hazard_speed c n hc hn0,
    actual_survival c n hc hn0, ?_, ?_⟩
  · dsimp [ValidBase, doubleWall]
    exact ⟨by linarith, by linarith, hc, by linarith, hc, by linarith⟩
  · refine ⟨lt_min (by positivity) (by linarith), ?_⟩
    intro t ht i
    obtain ⟨hl, hu, -⟩ := height_bounds c n hc hn0 t ht
    have hmin := min_le_left (c / 4) (1 - 2 * c)
    have hmin' := min_le_right (c / 4) (1 - 2 * c)
    fin_cases i
    · change min (c / 4) (1 - 2 * c) ≤ 1 - (1 - 2 * c) - c - c + height c n t
      linarith
    · change min (c / 4) (1 - 2 * c) ≤ c - height c n t
      linarith
    · exact hmin'
    · change min (c / 4) (1 - 2 * c) ≤ c - height c n t
      linarith
    · exact hmin.trans hl
  · apply (eVariationOn.eq_zero_iff _).mpr
    intro x hx y hy
    exact edist_self phase
  · refine ⟨by norm_num, continuousOn_const, continuousOn_const, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
    · intro t ht
      have hlo : lower (doubleWall c) = 0 := by simp [lower, doubleWall]; ring_nf; norm_num
      have hhi : upper (doubleWall c) = c := by simp [upper, doubleWall]
      rw [hlo, hhi]
      exact ⟨by linarith, by linarith⟩
    · exact (LipschitzWith.const phase).lipschitzOnWith.absolutelyContinuousOnInterval.boundedVariationOn
    · exact (LipschitzWith.const (c / 2)).lipschitzOnWith.absolutelyContinuousOnInterval
    · exact (LipschitzWith.const phase).lipschitzOnWith.absolutelyContinuousOnInterval
  · intro t
    simp [hazard, survival]

/-- Uniform convergence of these actual heights coexists with a fixed terminal survival gap. -/
theorem uniform_height_survival_discontinuity (c phase : ℝ) (hc : 0 < c) (hc' : c < 1 / 2) :
    (∀ e : ℝ, 0 < e → ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N,
      OriginalControl (doubleWall c) 1 (height c n) (fun _ => phase) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, |height c n t - c / 2| < e) ∧
    (∀ n : ℕ, 1 ≤ n →
      |survival c (height c n) 1 - survival c (fun _ => c / 2) 1|=1 / 2) ∧
    ¬ Tendsto (fun n : ℕ => survival c (height c (n + 1)) 1) atTop
      (𝓝 (survival c (fun _ => c / 2) 1)) := by
  have hfamily (n : ℕ) (hn : 1 ≤ n) := oscillatory_original_controls c phase n hc hc' hn
  have hbound (n : ℕ) (hn : 1 ≤ n) :
      ∀ t ∈ Icc (0 : ℝ) 1, |height c n t - c / 2| ≤ c / (4 * n) := by
    rcases hfamily n hn with ⟨-, -, -, -, -, -, hb, -⟩
    exact fun t ht => (hb t ht).2.2
  have hterminal (n : ℕ) (hn : 1 ≤ n) : survival c (height c n) 1 = 1 / 2 := by
    rcases hfamily n hn with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hs, -⟩
    have := (hs 1 ⟨by norm_num, le_rfl⟩).2
    linarith
  have hwait : survival c (fun _ => c / 2) 1 = 1 := by simp [survival, hazard]
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨N, hN⟩ := exists_nat_gt (c / (4 * e))
    refine ⟨N + 1, by omega, ?_⟩
    intro n hn
    have hn1 : 1 ≤ n := by omega
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
    have hne : c / (4 * (n : ℝ)) < e := by
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * n)).mpr
      have hlarge : c < (N : ℝ) * (4 * e) := (div_lt_iff₀ (by positivity)).mp hN
      have hcast : (N : ℝ) < n := by exact_mod_cast (show N < n by omega)
      nlinarith
    refine ⟨(hfamily n hn1).2.1, fun t ht => (hbound n hn1 t ht).trans_lt hne⟩
  · intro n hn
    rw [hterminal n hn, hwait]
    norm_num
  · intro hlim
    have hlim' : Tendsto (fun n : ℕ => survival c (height c (n + 1)) 1) atTop (𝓝 (1 / 2 : ℝ)) := by
      have he : (fun n : ℕ => survival c (height c (n + 1)) 1) = fun _ : ℕ => (1 / 2 : ℝ) :=
        funext (fun n => hterminal (n + 1) (by omega))
      rw [he]
      exact tendsto_const_nhds
    have heq := tendsto_nhds_unique hlim hlim'
    rw [hwait] at heq
    norm_num at heq

#print axioms oscillatory_original_controls
#print axioms uniform_height_survival_discontinuity

end D5.S3.Quantum.Fibers.OriginalControlSurvivalInstability
