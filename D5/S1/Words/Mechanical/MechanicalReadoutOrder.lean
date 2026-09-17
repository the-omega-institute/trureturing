/- GID: D5/S1/Words/Mechanical/MechanicalReadoutOrder
   generality: G
   mirror-B: D5/B/S1/Words/Mechanical/MechanicalReadoutOrder
   mirror-E: none(waiver:actual-dynamics-weight-cone-classification)
   anchors: []
   utility: none
   digest: Actual mechanical letters determine the order cone, geometric L1 completion, and exact one-sided finite-precision cost. -/

import D5.S1.Words.Mechanical.MechanicalSlopeSensitivity
import D5.S1.Words.Mechanical.FloorFractShift
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The order cone of numerical mechanical-bit readouts

For a fixed irrational slope and a finite nonempty observation horizon,
local monotonicity for every phase forces every successive weight drop and
the terminal weight to be nonnegative. The necessity proof realizes each
constraint on an actual swept interval of the rotation, rather than on an
arbitrary binary vector. The converse derives summation by parts from the
actual cumulative floors. The same identity drives the geometric completion.
Its bit means are calculated by integrating the actual shifted floors.
Summability, uniform tails, integrability, dominated convergence, and L1
distance are proved for every ratio in [0,1).
Summation by parts and dominated convergence are classical prerequisites.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S1.Words.Mechanical.MechanicalReadoutOrder

open Set Finset Filter MeasureTheory
open scoped BigOperators Topology
open D5.S1.Words.Mechanical
open D5.S1.Words.Mechanical.MechanicalSlopeSensitivity

/-- Finite additive numerical readout of the actual integer-valued letters.
For slopes in [0,1), these letters are the actual binary observations. -/
def weightedPrefix (weights : ℕ → ℝ) (alpha x : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ range n, weights j * (lowerMechanicalLetter alpha x j : ℝ)

/-- The actual-floor Abel identity is shared by the weight classification
and the analytic completion below. -/
private theorem weightedPrefix_order (weights : ℕ → ℝ) (m : ℕ)
    (hlast : 0 ≤ weights m) (hweights : ∀ k < m, weights (k + 1) ≤ weights k)
    (alpha beta x : ℝ) (hab : alpha ≤ beta) :
    weightedPrefix weights alpha x (m + 1) ≤ weightedPrefix weights beta x (m + 1) := by
  let D : ℕ → ℝ := fun k =>
    (⌊x + (k : ℝ) * beta⌋ : ℝ) - (⌊x + (k : ℝ) * alpha⌋ : ℝ)
  have hD0 : D 0 = 0 := by simp [D]
  have hD (k : ℕ) : 0 ≤ D k := by
    apply sub_nonneg.mpr
    exact_mod_cast (Int.floor_mono (add_le_add_left
      (mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg (R := ℝ) k)) x))
  have hparts : ∀ N : ℕ,
      (∑ j ∈ range N, weights j * (D (j + 1) - D j)) =
        weights N * D N + ∑ j ∈ range N, (weights j - weights (j + 1)) * D (j + 1) := by
    intro N
    induction N with
    | zero => simp [hD0]
    | succ N ih =>
        rw [sum_range_succ, ih, sum_range_succ]
        ring
  have heq : weightedPrefix weights beta x (m + 1) -
      weightedPrefix weights alpha x (m + 1) =
      weights m * D (m + 1) +
        ∑ j ∈ range m, (weights j - weights (j + 1)) * D (j + 1) := by
    unfold weightedPrefix
    rw [← sum_sub_distrib]
    calc
      (∑ j ∈ range (m + 1),
          (weights j * (lowerMechanicalLetter beta x j : ℝ) -
            weights j * (lowerMechanicalLetter alpha x j : ℝ))) =
          ∑ j ∈ range (m + 1), weights j * (D (j + 1) - D j) := by
        apply sum_congr rfl
        intro j hj
        dsimp [D, lowerMechanicalLetter]
        push_cast
        ring
      _ = _ := by rw [sum_range_succ, hparts m]; ring
  apply sub_nonneg.mp
  rw [heq]
  exact add_nonneg (mul_nonneg hlast (hD (m + 1)))
    (sum_nonneg fun j hj => mul_nonneg
      (sub_nonneg.mpr (hweights j (mem_range.mp hj))) (hD (j + 1)))

/-- A finite additive readout preserves all sufficiently small upward slope
changes at every phase exactly when its weights decrease to a nonnegative
last weight. Arbitrary real weights are allowed in the statement. -/
theorem local_order_iff_decreasing_weights
    (alpha : ℝ) (halpha : Irrational alpha) (h0 : 0 < alpha) (h1 : alpha < 1)
    (weights : ℕ → ℝ) (m : ℕ) :
    (∃ radius : ℝ, 0 < radius ∧ alpha + radius < 1 ∧
      ∀ delta : ℝ, 0 ≤ delta → delta ≤ radius → ∀ x ∈ Ico (0 : ℝ) 1,
        weightedPrefix weights alpha x (m + 1) ≤
          weightedPrefix weights (alpha + delta) x (m + 1)) ↔
      0 ≤ weights m ∧ ∀ k < m, weights (k + 1) ≤ weights k := by
  classical
  constructor
  · rintro ⟨r, hr, _, hmono⟩
    obtain ⟨s, hs, _, hlaw⟩ := local_slope_disagreement_law alpha halpha h0 h1 (m + 1)
    let delta := min r s / 2
    have hd : 0 < delta := div_pos (lt_min hr hs) (by norm_num)
    have hdr : delta ≤ r := by dsimp [delta]; linarith [min_le_left r s, lt_min hr hs]
    have hds : delta ≤ s := by dsimp [delta]; linarith [min_le_right r s, lt_min hr hs]
    obtain ⟨hset, _, _, hpattern⟩ := hlaw delta hd.le hds
    have hdrop (k : ℕ) (hk : k < m + 1) :
        0 ≤ weights k - if k + 1 < m + 1 then weights (k + 1) else 0 := by
      let i : Fin (m + 1) := ⟨k, hk⟩
      let c : ℝ := 1 - Int.fract (((k + 1 : ℕ) : ℝ) * alpha)
      let x := c - ((k + 1 : ℕ) : ℝ) * delta / 2
      have hlen : 0 < ((k + 1 : ℕ) : ℝ) * delta := mul_pos (by positivity) hd
      have hx : x ∈ Ico (c - ((k + 1 : ℕ) : ℝ) * delta) c := by
        dsimp [x]
        constructor <;> linarith
      have hxdis : x ∈ slopeDisagreement alpha (alpha + delta) (m + 1) := by
        rw [hset]
        exact Set.mem_iUnion.mpr ⟨i, hx⟩
      have hx01 : x ∈ Ico (0 : ℝ) 1 := hxdis.1
      have heq : weightedPrefix weights (alpha + delta) x (m + 1) -
          weightedPrefix weights alpha x (m + 1) =
          weights k - if k + 1 < m + 1 then weights (k + 1) else 0 := by
        unfold weightedPrefix
        rw [← sum_sub_distrib]
        calc
          (∑ j ∈ range (m + 1),
              (weights j * (lowerMechanicalLetter (alpha + delta) x j : ℝ) -
                weights j * (lowerMechanicalLetter alpha x j : ℝ))) =
              ∑ j ∈ range (m + 1), weights j *
                ((if j = k then (1 : ℝ) else 0) -
                  (if j = k + 1 then (1 : ℝ) else 0)) := by
            apply sum_congr rfl
            intro j hj
            have hp := hpattern i x hx ⟨j, mem_range.mp hj⟩
            have hpR := congrArg (fun z : ℤ => (z : ℝ)) hp
            simp only [Int.cast_sub, apply_ite, Int.cast_one, Int.cast_zero] at hpR
            rw [← mul_sub]
            exact congrArg (weights j * ·) hpR
          _ = weights k - if k + 1 < m + 1 then weights (k + 1) else 0 := by
            simp [mul_sub, mul_ite, sum_sub_distrib, hk]
      rw [← heq]
      exact sub_nonneg.mpr (hmono delta hd.le hdr x hx01)
    constructor
    · simpa using hdrop m (Nat.lt_succ_self m)
    · intro k hk
      have h := hdrop k (Nat.lt_succ_of_lt hk)
      rw [if_pos (by omega)] at h
      exact sub_nonneg.mp h
  · rintro ⟨hlast, hweights⟩
    refine ⟨(1 - alpha) / 2, by linarith, by linarith, ?_⟩
    intro delta hd _ x _
    exact weightedPrefix_order weights m hlast hweights alpha (alpha + delta) x (by linarith)

/- The concrete source measure, with its normalization proved here. -/
local notation "μ₀" => (volume.restrict (Ico (0 : ℝ) 1))
local instance : IsProbabilityMeasure μ₀ := ⟨by simp⟩

/-- Integrate the actual shifted floor by deriving its single carry interval.
No expectation of a bit, invariant-measure assertion, or readout integral is
assumed. This also handles shifts that are integers or negative. -/
private theorem shifted_floor_mean (t : ℝ) :
    Integrable (fun x : ℝ => (⌊x + t⌋ : ℝ)) μ₀ ∧
      (∫ x : ℝ, (⌊x + t⌋ : ℝ) ∂μ₀) = t := by
  classical
  let c : ℝ := 1 - Int.fract t
  let f : ℝ → ℝ := fun x => (⌊t⌋ : ℝ) + (Ico c 1).indicator (fun _ => (1 : ℝ)) x
  have hc0 : 0 ≤ c := by dsimp [c]; linarith [Int.fract_lt_one t]
  have hc1 : c ≤ 1 := by dsimp [c]; linarith [Int.fract_nonneg t]
  have hs : Ico c 1 ⊆ Ico (0 : ℝ) 1 :=
    fun _ hx => ⟨hc0.trans hx.1, hx.2⟩
  have hi : Integrable f μ₀ := (integrable_const (⌊t⌋ : ℝ)).add
    ((integrable_const (1 : ℝ)).indicator measurableSet_Ico)
  have heq : (fun x : ℝ => (⌊x + t⌋ : ℝ)) =ᵐ[μ₀] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    have hxfract : Int.fract x = x := by
      simp [Int.fract, Int.floor_eq_zero_iff.mpr hx]
    have hfloor : ⌊x + t⌋ = ⌊t⌋ + if c ≤ x then (1 : ℤ) else 0 := by
      simpa only [hxfract] using FloorFractShift.floor_fract_add_indicator x t
    dsimp [f]
    rw [hfloor, Int.cast_add]
    by_cases hcx : c ≤ x
    · simp [Set.indicator, hcx, hx.2]
    · simp [Set.indicator, hcx]
  have hind : (∫ x : ℝ, (Ico c 1).indicator (fun _ => (1 : ℝ)) x ∂μ₀) =
      Int.fract t := by
    change (∫ x : ℝ, (Ico c 1).indicator (1 : ℝ → ℝ) x ∂μ₀) = _
    rw [integral_indicator_one measurableSet_Ico, measureReal_def,
      Measure.restrict_apply measurableSet_Ico, inter_eq_left.mpr hs,
      Real.volume_Ico, ENNReal.toReal_ofReal (sub_nonneg.mpr hc1)]
    dsimp [c]
    ring
  refine ⟨hi.congr heq.symm, ?_⟩
  calc
    (∫ x : ℝ, (⌊x + t⌋ : ℝ) ∂μ₀) = ∫ x : ℝ, f x ∂μ₀ := integral_congr_ae heq
    _ = (⌊t⌋ : ℝ) + Int.fract t := by
      rw [show (∫ x : ℝ, f x ∂μ₀) =
        (∫ x : ℝ, (⌊t⌋ : ℝ) ∂μ₀) +
          ∫ x : ℝ, (Ico c 1).indicator (fun _ => (1 : ℝ)) x ∂μ₀ from
        integral_add (integrable_const _) ((integrable_const _).indicator measurableSet_Ico)]
      simp [hind]
    _ = t := Int.floor_add_fract t

private theorem actual_letter_mean (alpha : ℝ) (k : ℕ) :
    Integrable (fun x : ℝ => (lowerMechanicalLetter alpha x k : ℝ)) μ₀ ∧
      (∫ x : ℝ, (lowerMechanicalLetter alpha x k : ℝ) ∂μ₀) = alpha := by
  have hnext := shifted_floor_mean (((k + 1 : ℕ) : ℝ) * alpha)
  have hprev := shifted_floor_mean ((k : ℝ) * alpha)
  constructor
  · simpa only [lowerMechanicalLetter, Int.cast_sub] using hnext.1.sub hprev.1
  · simp only [lowerMechanicalLetter, Int.cast_sub]
    rw [integral_sub hnext.1 hprev.1, hnext.2, hprev.2]
    push_cast
    ring

/-- The completed geometric readout of the actual mechanical letters.
The usual binary numerical readout is obtained at r=1/2. -/
def geometricReadout (r alpha x : ℝ) : ℝ :=
  ∑' k : ℕ, ((1 - r) * r ^ k) * (lowerMechanicalLetter alpha x k : ℝ)

/-- Actual geometric readouts have uniform finite tails and exact finite and
infinite L1 distances. The last clause is a matching mixed-error formula:
a downward parameter approximation and output truncation contribute exactly
alpha - beta*(1-r^n). Every integral and convergence property is proved from
the real floor readout; none is supplied as a premise. -/
theorem geometric_readout_isometric_completion
    (r alpha beta : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : alpha ∈ Ico (0 : ℝ) 1) (hb : beta ∈ Ico (0 : ℝ) 1) :
    let q : ℕ → ℝ := fun k => (1 - r) * r ^ k
    IntegrableOn (geometricReadout r alpha) (Ico (0 : ℝ) 1) ∧
    IntegrableOn (geometricReadout r beta) (Ico (0 : ℝ) 1) ∧
    (∀ x : ℝ, ∀ n : ℕ,
      0 ≤ geometricReadout r alpha x - weightedPrefix q alpha x n ∧
      geometricReadout r alpha x - weightedPrefix q alpha x n ≤ r ^ n) ∧
    (∀ n : ℕ, (∫ x : ℝ in Ico (0 : ℝ) 1,
      |weightedPrefix q beta x n - weightedPrefix q alpha x n|) =
        (1 - r ^ n) * |beta - alpha|) ∧
    ((∫ x : ℝ in Ico (0 : ℝ) 1,
      |geometricReadout r beta x - geometricReadout r alpha x|) = |beta - alpha|) ∧
    (beta ≤ alpha → ∀ n : ℕ, (∫ x : ℝ in Ico (0 : ℝ) 1,
      |geometricReadout r alpha x - weightedPrefix q beta x n|) =
        alpha - beta * (1 - r ^ n)) := by
  classical
  let q : ℕ → ℝ := fun k => (1 - r) * r ^ k
  let P : ℝ → ℕ → ℝ → ℝ := fun a n x => weightedPrefix q a x n
  let G : ℝ → ℝ → ℝ := geometricReadout r
  have hq0 (k : ℕ) : 0 ≤ q k := mul_nonneg (sub_nonneg.mpr hr1.le) (pow_nonneg hr0 k)
  have hqstep (k : ℕ) : q (k + 1) ≤ q k := by
    calc
      q (k + 1) = q k * r := by dsimp [q]; rw [pow_succ]; ring
      _ ≤ q k * 1 := mul_le_mul_of_nonneg_left hr1.le (hq0 k)
      _ = q k := mul_one _
  have hqs : Summable q := (summable_geometric_of_lt_one hr0 hr1).mul_left (1 - r)
  have hqt : (∑' k, q k) = 1 := by
    dsimp [q]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    simpa only [one_div] using mul_inv_cancel₀ (sub_ne_zero.mpr hr1.ne')
  have hqn : ∀ n : ℕ, (∑ k ∈ range n, q k) = 1 - r ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih, pow_succ]; dsimp [q]; ring
  have hterm (a : ℝ) (ha' : a ∈ Ico (0 : ℝ) 1) (x : ℝ) (k : ℕ) :
      0 ≤ q k * (lowerMechanicalLetter a x k : ℝ) ∧
        q k * (lowerMechanicalLetter a x k : ℝ) ≤ q k := by
    rcases lowerMechanicalLetter_eq_zero_or_one (rho := x) ha'.1 ha'.2 k with hz | ho
    · simp [hz, hq0 k]
    · simp [ho, hq0 k]
  have hsum (a : ℝ) (ha' : a ∈ Ico (0 : ℝ) 1) (x : ℝ) :
      Summable (fun k : ℕ => q k * (lowerMechanicalLetter a x k : ℝ)) :=
    Summable.of_nonneg_of_le (fun k => (hterm a ha' x k).1)
      (fun k => (hterm a ha' x k).2) hqs
  have hPint (a : ℝ) (n : ℕ) : Integrable (P a n) μ₀ := by
    induction n with
    | zero => simp [P, weightedPrefix]
    | succ n ih =>
        simpa only [P, weightedPrefix, sum_range_succ] using
          ih.add ((actual_letter_mean a n).1.const_mul (q n))
  have hPmean (a : ℝ) (n : ℕ) : (∫ x : ℝ, P a n x ∂μ₀) = a * (1 - r ^ n) := by
    dsimp [P, weightedPrefix]
    rw [integral_finsetSum (range n) (fun k _ => (actual_letter_mean a k).1.const_mul (q k))]
    simp_rw [integral_const_mul]
    calc
      (∑ k ∈ range n, q k * ∫ x : ℝ, (lowerMechanicalLetter a x k : ℝ) ∂μ₀) =
          ∑ k ∈ range n, q k * a := by
        apply sum_congr rfl
        intro k hk
        rw [(actual_letter_mean a k).2]
      _ = a * (1 - r ^ n) := by rw [← sum_mul, hqn n]; ring
  have hPbound (a : ℝ) (ha' : a ∈ Ico (0 : ℝ) 1) (n : ℕ) (x : ℝ) :
      0 ≤ P a n x ∧ P a n x ≤ 1 := by
    have h0' : 0 ≤ P a n x := sum_nonneg fun k _ => (hterm a ha' x k).1
    have hle : P a n x ≤ ∑ k ∈ range n, q k :=
      sum_le_sum fun k _ => (hterm a ha' x k).2
    rw [hqn n] at hle
    exact ⟨h0', le_trans hle (by linarith [pow_nonneg hr0 n])⟩
  have hPmono (a b : ℝ) (hab : a ≤ b) (n : ℕ) (x : ℝ) : P a n x ≤ P b n x := by
    cases n with
    | zero => simp [P, weightedPrefix]
    | succ m => exact weightedPrefix_order q m (hq0 m) (fun k _ => hqstep k) a b x hab
  have hlim (a : ℝ) (ha' : a ∈ Ico (0 : ℝ) 1) (x : ℝ) :
      Tendsto (fun n : ℕ => P a n x) atTop (𝓝 (G a x)) :=
    (hsum a ha' x).hasSum.tendsto_sum_nat
  have htail (a : ℝ) (ha' : a ∈ Ico (0 : ℝ) 1) (x : ℝ) (n : ℕ) :
      0 ≤ G a x - P a n x ∧ G a x - P a n x ≤ r ^ n := by
    have hs := hsum a ha' x
    have hlo := hs.sum_le_tsum (range n) (fun k _ => (hterm a ha' x k).1)
    have hhi := (hqs.sub hs).sum_le_tsum (range n)
      (fun k _ => sub_nonneg.mpr (hterm a ha' x k).2)
    rw [sum_sub_distrib, hqn n, hqs.tsum_sub hs, hqt] at hhi
    change P a n x ≤ G a x at hlo
    change (1 - r ^ n) - P a n x ≤ 1 - G a x at hhi
    constructor <;> linarith
  have hGbound (a : ℝ) (ha' : a ∈ Ico (0 : ℝ) 1) (x : ℝ) :
      0 ≤ G a x ∧ G a x ≤ 1 := by
    simpa [P, weightedPrefix] using htail a ha' x 0
  have hGint (a : ℝ) (ha' : a ∈ Ico (0 : ℝ) 1) : Integrable (G a) μ₀ := by
    have hmeas : AEStronglyMeasurable (G a) μ₀ :=
      aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hPint a n).aestronglyMeasurable)
        (ae_of_all _ (fun x => hlim a ha' x))
    apply (integrable_const (1 : ℝ)).mono' hmeas
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hGbound a ha' x).1]
      exact (hGbound a ha' x).2)
  have hGmean (a : ℝ) (ha' : a ∈ Ico (0 : ℝ) 1) : (∫ x : ℝ, G a x ∂μ₀) = a := by
    have hDCT := tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1 : ℝ))
      (fun n => (hPint a n).aestronglyMeasurable) (integrable_const (1 : ℝ))
      (fun n => ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hPbound a ha' n x).1]
        exact (hPbound a ha' n x).2))
      (ae_of_all _ (fun x => hlim a ha' x))
    have hp : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have hm : Tendsto (fun n : ℕ => ∫ x : ℝ, P a n x ∂μ₀) atTop (𝓝 a) := by
      simp_rw [hPmean]
      simpa using (tendsto_const_nhds.mul (tendsto_const_nhds.sub hp) :
        Tendsto (fun n : ℕ => a * (1 - r ^ n)) atTop (𝓝 (a * (1 - 0))))
    exact tendsto_nhds_unique hDCT hm
  have hGmono (a b : ℝ) (ha' : a ∈ Ico (0 : ℝ) 1) (hb' : b ∈ Ico (0 : ℝ) 1)
      (hab : a ≤ b) (x : ℝ) : G a x ≤ G b x :=
    le_of_tendsto_of_tendsto (hlim a ha' x) (hlim b hb' x)
      (Eventually.of_forall fun n => hPmono a b hab n x)
  have hfinite (a b : ℝ) (hab : a ≤ b) (n : ℕ) :
      (∫ x : ℝ, |P b n x - P a n x| ∂μ₀) = (1 - r ^ n) * (b - a) := by
    calc
      _ = ∫ x : ℝ, P b n x - P a n x ∂μ₀ := integral_congr_ae
        (ae_of_all _ fun x => abs_of_nonneg (sub_nonneg.mpr (hPmono a b hab n x)))
      _ = (1 - r ^ n) * (b - a) := by
        rw [integral_sub (hPint b n) (hPint a n), hPmean b n, hPmean a n]
        ring
  have hinfinite (a b : ℝ) (ha' : a ∈ Ico (0 : ℝ) 1) (hb' : b ∈ Ico (0 : ℝ) 1)
      (hab : a ≤ b) : (∫ x : ℝ, |G b x - G a x| ∂μ₀) = b - a := by
    calc
      _ = ∫ x : ℝ, G b x - G a x ∂μ₀ := integral_congr_ae
        (ae_of_all _ fun x => abs_of_nonneg (sub_nonneg.mpr (hGmono a b ha' hb' hab x)))
      _ = b - a := by rw [integral_sub (hGint b hb') (hGint a ha'), hGmean b hb', hGmean a ha']
  refine ⟨hGint alpha ha, hGint beta hb, htail alpha ha, ?_, ?_, ?_⟩
  · intro n
    change (∫ x : ℝ, |P beta n x - P alpha n x| ∂μ₀) = (1 - r ^ n) * |beta - alpha|
    rcases le_total alpha beta with hab | hba
    · rw [hfinite alpha beta hab n, abs_of_nonneg (sub_nonneg.mpr hab)]
    · calc
        _ = ∫ x : ℝ, |P alpha n x - P beta n x| ∂μ₀ :=
          integral_congr_ae (ae_of_all _ fun x => abs_sub_comm _ _)
        _ = (1 - r ^ n) * |beta - alpha| := by
          rw [hfinite beta alpha hba n, abs_sub_comm beta alpha,
            abs_of_nonneg (sub_nonneg.mpr hba)]
  · change (∫ x : ℝ, |G beta x - G alpha x| ∂μ₀) = |beta - alpha|
    rcases le_total alpha beta with hab | hba
    · rw [hinfinite alpha beta ha hb hab, abs_of_nonneg (sub_nonneg.mpr hab)]
    · calc
        _ = ∫ x : ℝ, |G alpha x - G beta x| ∂μ₀ :=
          integral_congr_ae (ae_of_all _ fun x => abs_sub_comm _ _)
        _ = |beta - alpha| := by
          rw [hinfinite beta alpha hb ha hba, abs_sub_comm beta alpha,
            abs_of_nonneg (sub_nonneg.mpr hba)]
  · intro hba n
    change (∫ x : ℝ, |G alpha x - P beta n x| ∂μ₀) = alpha - beta * (1 - r ^ n)
    calc
      _ = ∫ x : ℝ, G alpha x - P beta n x ∂μ₀ := integral_congr_ae
        (ae_of_all _ fun x => abs_of_nonneg (sub_nonneg.mpr
          ((sub_nonneg.mp (htail beta hb x n).1).trans (hGmono beta alpha hb ha hba x))))
      _ = alpha - beta * (1 - r ^ n) := by
        rw [integral_sub (hGint alpha ha) (hPint beta n), hGmean alpha ha, hPmean beta n]

#print axioms weightedPrefix
#print axioms local_order_iff_decreasing_weights
#print axioms geometricReadout
#print axioms geometric_readout_isometric_completion

end D5.S1.Words.Mechanical.MechanicalReadoutOrder
