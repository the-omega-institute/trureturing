/- GID: D5/S3/ArithSums/ThreeCoordinateSpan
   generality: G
   mirror-B: D5/B/S3/ArithSums/ThreeCoordinateSpan
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An explicit remote-coordinate threshold gives a uniform negative grid-envelope margin. -/

import D5.S3.ArithSums.ThreeCoordinateSlabGap
import D5.S3.Analytic.Knapsack.GridDualStructure
import D5.S3.Analytic.Interpolation.EnvelopeKMonotone
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Set
open scoped BigOperators

namespace D5.S3.ArithSums.ThreeCoordinateSpan

open TwoPointSlabSupport ThreeCoordinateSlabGap
open D5.S3.Analytic.Knapsack.GridDualStructure
open D5.S3.Analytic.Interpolation.TwoPointGridDominance (logValue logValue_strictMono
  logValue_strictConcave)
open D5.S3.Analytic.Interpolation.EnvelopeKMonotone (radius_envelope_strictAnti)

/-- A corner's budget increment over the lower corner. -/
def offset (h : Fin 3 → ℝ) (e : Fin 3 → Bool) : ℝ :=
  ∑ i, if e i then h i else 0

/-- The eight subset sums, before imposing distinctness. -/
def subsetSums (h : Fin 3 → ℝ) : Finset ℝ := Finset.univ.image (offset h)

private theorem subset_sums_card (h : Fin 3 → ℝ) (hi : Function.Injective (offset h)) :
    (subsetSums h).card = 8 := by
  classical
  rw [subsetSums, Finset.card_image_of_injective _ hi]
  norm_num

/-- Increasing enumeration of the eight distinct subset sums. -/
def sortedOffsets (h : Fin 3 → ℝ) (hi : Function.Injective (offset h)) : Fin 8 ↪o ℝ :=
  (subsetSums h).orderEmbOfFin (subset_sums_card h hi)

/-- The least adjacent gap in the increasing enumeration. -/
def minimumGap (h : Fin 3 → ℝ) (hi : Function.Injective (offset h)) : ℝ :=
  (Finset.univ.image (fun i : Fin 7 =>
    sortedOffsets h hi i.succ - sortedOffsets h hi i.castSucc)).min'
      (Finset.univ_nonempty.image _)

/-- The uniform exponential margin. -/
def margin (S Q δ : ℝ) : ℝ := Real.exp (-(S + Q) / 2) * (1 - Real.exp (-(δ / 18)))

/-- The threshold includes a strict unit of slack, even when the remote coordinate equals it. -/
def threshold (S Q δ : ℝ) : ℝ := 1 +
  max (max (2 * S + 3 * Q) (Real.sqrt (6 * errorBound S Q)))
    (max (9 * errorBound S Q / δ)
      (3 / 2 * (S + Q) + 3 * Real.log (2 / (1 - Real.exp (-(δ / 18))))))

/-- The envelope computed on the original closed slab. -/
def slabEnvelope (c h : Fin 3 → ℝ) (M₀ M₁ : ℝ) : ℝ :=
  logValue (M₁ / 3 + 2 * slabRadius c h M₀ M₁) +
    2 * logValue (slabLower c h M₀ M₁)

private theorem minimum_gap_pos (h : Fin 3 → ℝ) (hi : Function.Injective (offset h)) :
    0 < minimumGap h hi := by
  classical
  obtain ⟨i, _, he⟩ := Finset.mem_image.mp
    (Finset.min'_mem _ (Finset.univ_nonempty.image
      (fun i : Fin 7 => sortedOffsets h hi i.succ - sortedOffsets h hi i.castSucc)))
  rw [minimumGap, ← he]
  exact sub_pos.mpr ((sortedOffsets h hi).strictMono (by simp))

private theorem minimum_gap_le (h : Fin 3 → ℝ) (hi : Function.Injective (offset h))
    (e f : Fin 3 → Bool) (hef : offset h e < offset h f) :
    minimumGap h hi ≤ offset h f - offset h e := by
  classical
  have hmem (g : Fin 3 → Bool) : offset h g ∈ subsetSums h :=
    Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩
  have hrange := (subsetSums h).range_orderEmbOfFin (subset_sums_card h hi)
  obtain ⟨i, hie⟩ : ∃ i, sortedOffsets h hi i = offset h e := by
    apply Set.mem_range.mp
    rw [show Set.range (sortedOffsets h hi) = (subsetSums h : Set ℝ) from hrange]
    exact hmem e
  obtain ⟨j, hjf⟩ : ∃ j, sortedOffsets h hi j = offset h f := by
    apply Set.mem_range.mp
    rw [show Set.range (sortedOffsets h hi) = (subsetSums h : Set ℝ) from hrange]
    exact hmem f
  have hij : i < j := (sortedOffsets h hi).lt_iff_lt.mp (by simpa [hie, hjf] using hef)
  let k : Fin 7 := ⟨i.val, by omega⟩
  have hk : k.castSucc = i := by ext; rfl
  have hkj : k.succ ≤ j := by
    change i.val + 1 ≤ j.val
    exact Nat.succ_le_iff.mpr hij
  have hstep : minimumGap h hi ≤
      sortedOffsets h hi k.succ - sortedOffsets h hi k.castSucc :=
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  have hmono := (sortedOffsets h hi).monotone hkj
  rw [hk, hie] at hstep
  rw [hjf] at hmono
  linarith

private theorem offset_bounds (h : Fin 3 → ℝ) (hh : ∀ i, 0 < h i)
    (e : Fin 3 → Bool) : 0 ≤ offset h e ∧ offset h e ≤ totalWidth h := by
  have hpoint (i) : 0 ≤ (if e i then h i else 0) ∧ (if e i then h i else 0) ≤ h i := by
    cases e i <;> simp [le_of_lt (hh i)]
  constructor
  · exact Finset.sum_nonneg (fun i _ => (hpoint i).1)
  · have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hpoint i).2)
    simpa [offset, totalWidth, Fin.sum_univ_succ, add_assoc] using he

private theorem corner_budget (h : Fin 3 → ℝ) (T s t : ℝ) (x : Fin 3 → ℝ)
    (hx : IsCorner (base T s t) (fun i => base T s t i + h i) x) :
    ∃ e : Fin 3 → Bool, ∑ i, x i = 3 * T + s + t + offset h e := by
  obtain ⟨e, he⟩ := (corner_iff_choice (base T s t) h x).mp hx
  refine ⟨e, ?_⟩
  rw [he]
  rw [Finset.sum_add_distrib]
  simp [base, offset, Fin.sum_univ_succ]
  ring

private theorem log_increment (m ε : ℝ) (hm : 0 < m) (hε : 0 ≤ ε) :
    Real.exp (-m) * (1 - Real.exp (-ε)) ≤ logValue (m + ε) - logValue m := by
  let u := Real.exp (-m)
  let v := Real.exp (-(m + ε))
  have hu : 0 < u := Real.exp_pos _
  have hv : 0 < v := Real.exp_pos _
  have hu1 : u < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hm)
  have hvu : v ≤ u := Real.exp_le_exp.mpr (by linarith)
  have hv1 : v < 1 := hvu.trans_lt hu1
  have hratio : 0 < (1 - v) / (1 - u) := div_pos (by linarith) (by linarith)
  have he := Real.one_sub_inv_le_log_of_pos hratio
  rw [inv_div, Real.log_div (by linarith : 1 - v ≠ 0) (by linarith : 1 - u ≠ 0)] at he
  have hfrac : u - v ≤ 1 - (1 - u) / (1 - v) := by
    have hd : (1 - u) / (1 - v) ≤ 1 - (u - v) := by
      apply (div_le_iff₀ (by linarith : 0 < 1 - v)).mpr
      nlinarith [mul_nonneg hv.le (sub_nonneg.mpr hvu)]
    linarith
  have huv : Real.exp (-m) * (1 - Real.exp (-ε)) = u - v := by
    dsimp [u, v]
    rw [neg_add, Real.exp_add]
    ring
  rw [huv]
  exact hfrac.trans he

private theorem log_tail (x : ℝ) (hx : Real.log 2 ≤ x) :
    -2 * Real.exp (-x) ≤ logValue x := by
  have hx0 : 0 < x := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hx
  let u := Real.exp (-x)
  have hu : 0 < u := Real.exp_pos _
  have hu2 : u ≤ 1 / 2 := by
    have he := Real.exp_le_exp.mpr (neg_le_neg hx)
    simpa [u, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using he
  have h1 : 0 < 1 - u := by linarith
  have he := Real.one_sub_inv_le_log_of_pos h1
  have hfrac : -2 * u ≤ 1 - (1 - u)⁻¹ := by
    rw [inv_eq_one_div]
    have hd : 1 / (1 - u) ≤ 1 + 2 * u := by
      apply (div_le_iff₀ h1).mpr
      nlinarith [mul_nonneg hu.le (show 0 ≤ 1 - 2 * u by linarith)]
    linarith
  exact hfrac.trans he

private theorem row_bound (c h y : ℝ) (hc : 0 < c) (hh : 0 ≤ h) (hy : y ∈ Icc 0 1) :
    logValue c + y * (logValue (c + h) - logValue c) ≤ logValue (c + h * y) := by
  have he := logValue_strictConcave.concaveOn.2 hc (show 0 < c + h by linarith)
    (show 0 ≤ 1 - y by linarith [hy.2]) hy.1 (show 1 - y + y = 1 by ring)
  simp only [smul_eq_mul] at he
  convert he using 1 <;> (try ring_nf) <;> rfl

private theorem fill_resource_bound (h : Fin 3 → ℝ) (T s t q : ℝ)
    (hh : ∀ i, 0 < h i) (hT : 0 < T) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (y : Fin 3 → ℝ)
    (hy : FillFeasible (base T s t) (fun i => base T s t i + h i)
      (3 * T + s + t + q) y) :
    fillValue (base T s t) (fun i => base T s t i + h i) y <
      2 * logValue (lowMean T s q (h 0 + h 1)) := by
  have hy0 := hy.1 0
  have hy1 := hy.1 1
  have hy2 := hy.1 2
  have hw0 : 0 ≤ h 0 * y 0 := mul_nonneg (hh 0).le hy0.1
  have hw1 : 0 ≤ h 1 * y 1 := mul_nonneg (hh 1).le hy1.1
  have hw2 : 0 ≤ h 2 * y 2 := mul_nonneg (hh 2).le hy2.1
  have hb : h 0 * y 0 + h 1 * y 1 ≤ q := by
    have hp := hy.2
    simp [base, Fin.sum_univ_succ] at hp
    linarith
  have hB : h 0 * y 0 + h 1 * y 1 ≤ h 0 + h 1 :=
    add_le_add (mul_le_of_le_one_right (hh 0).le hy0.2)
      (mul_le_of_le_one_right (hh 1).le hy1.2)
  have hm : (T + h 0 * y 0 + (T + s + h 1 * y 1)) / 2 ≤
      lowMean T s q (h 0 + h 1) := by
    have hr := le_min hb hB
    dsimp [lowMean]; linarith
  have hmpos : 0 < (T + h 0 * y 0 + (T + s + h 1 * y 1)) / 2 := by linarith
  have hj := logValue_strictConcave.concaveOn.2
    (show 0 < T + h 0 * y 0 by linarith)
    (show 0 < T + s + h 1 * y 1 by linarith)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul] at hj
  have hj' : logValue (T + h 0 * y 0) + logValue (T + s + h 1 * y 1) ≤
      2 * logValue ((T + h 0 * y 0 + (T + s + h 1 * y 1)) / 2) := by
    convert (mul_le_mul_of_nonneg_left hj (by norm_num : (0 : ℝ) ≤ 2)) using 1 <;> (try ring_nf) <;> rfl
  have hmono := logValue_strictMono.monotoneOn hmpos (hmpos.trans_le hm) hm
  have hr0 := row_bound T (h 0) (y 0) hT (hh 0).le hy0
  have hr1 := row_bound (T + s) (h 1) (y 1) (by linarith) (hh 1).le hy1
  have hr2 := row_bound (T + t) (h 2) (y 2) (by linarith) (hh 2).le hy2
  have hneg : logValue (T + t + h 2 * y 2) < 0 := by
    apply Real.log_neg
    · exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
    · linarith [Real.exp_pos (-(T + t + h 2 * y 2))]
  simp [fillValue, base, Fin.sum_univ_succ]
  linarith

/-- The original fractional optimization value. -/
def maxValue (c h : Fin 3 → ℝ) (M : ℝ) : ℝ :=
  sSup (fillValue c (fun i => c i + h i) ''
    {y | FillFeasible c (fun i => c i + h i) M y})

/-- Admissibility uses actual corners in a closed budget interval. -/
def Admissible (h : Fin 3 → ℝ) (T s t M₀ M₁ : ℝ) : Prop :=
  totalWidth h + Real.log 5040 < M₀ ∧
    WideSlab (base T s t) (fun i => base T s t i + h i) M₀ M₁

private theorem slab_envelope_mono (c h : Fin 3 → ℝ) (M₀ M₁ N₀ N₁ : ℝ)
    (hlo : M₀ ≤ N₀) (hhi : N₁ ≤ M₁) (hN : N₀ ≤ N₁)
    (hL : 0 < slabLower c h N₀ N₁) :
    slabEnvelope c h N₀ N₁ ≤ slabEnvelope c h M₀ M₁ := by
  have hsub : Icc (N₀ / 3) (N₁ / 3) ⊆ Icc (M₀ / 3) (M₁ / 3) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hne : (Icc (N₀ / 3) (N₁ / 3)).Nonempty :=
    ⟨N₀ / 3, le_rfl, by linarith⟩
  have hdist (i) : pairDistance (Icc (M₀ / 3) (M₁ / 3)) (c i) (c i + h i) ≤
      pairDistance (Icc (N₀ / 3) (N₁ / 3)) (c i) (c i + h i) :=
    min_le_min (Metric.infDist_le_infDist_of_subset hsub hne)
      (Metric.infDist_le_infDist_of_subset hsub hne)
  have hr : slabRadius c h M₀ M₁ ≤ slabRadius c h N₀ N₁ := by
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply Finset.sum_le_sum
    intro i _
    exact (sq_le_sq₀ (le_min Metric.infDist_nonneg Metric.infDist_nonneg)
      (le_min Metric.infDist_nonneg Metric.infDist_nonneg)).mpr (hdist i)
  have hr0 : 0 ≤ slabRadius c h M₀ M₁ := Real.sqrt_nonneg _
  have hn0 : 0 ≤ slabRadius c h N₀ N₁ := Real.sqrt_nonneg _
  have hnl : slabRadius c h N₀ N₁ < N₁ / 3 := by
    change 0 < N₁ / 3 - slabRadius c h N₀ N₁ at hL
    linarith
  have hm : N₁ / 3 ≤ M₁ / 3 := by linarith
  have hrad := (radius_envelope_strictAnti (by norm_num : 2 ≤ 3) (N₁ / 3)).antitoneOn
    ⟨hr0, hr.trans_lt hnl⟩ ⟨hn0, hnl⟩ hr
  norm_num only [Nat.cast_ofNat, Nat.cast_sub, Nat.cast_one] at hrad
  have hlow := logValue_strictMono.monotoneOn
    (show 0 < N₁ / 3 - slabRadius c h M₀ M₁ by linarith)
    (show 0 < M₁ / 3 - slabRadius c h M₀ M₁ by linarith) (by linarith :
      N₁ / 3 - slabRadius c h M₀ M₁ ≤ M₁ / 3 - slabRadius c h M₀ M₁)
  have hhigh := logValue_strictMono.monotoneOn
    (show 0 < N₁ / 3 + 2 * slabRadius c h M₀ M₁ by linarith)
    (show 0 < M₁ / 3 + 2 * slabRadius c h M₀ M₁ by linarith) (by linarith :
      N₁ / 3 + 2 * slabRadius c h M₀ M₁ ≤ M₁ / 3 + 2 * slabRadius c h M₀ M₁)
  dsimp [slabEnvelope, slabLower]
  linarith

private theorem threshold_bounds (S Q δ t : ℝ) (ht : threshold S Q δ ≤ t) :
    2 * S + 3 * Q ≤ t ∧ Real.sqrt (6 * errorBound S Q) ≤ t ∧
    9 * errorBound S Q / δ ≤ t ∧
    3 / 2 * (S + Q) + 3 * Real.log (2 / (1 - Real.exp (-(δ / 18)))) < t := by
  dsimp [threshold] at ht
  have h1 := le_max_left (2 * S + 3 * Q) (Real.sqrt (6 * errorBound S Q))
  have h2 := le_max_right (2 * S + 3 * Q) (Real.sqrt (6 * errorBound S Q))
  have h3 := le_max_left (9 * errorBound S Q / δ)
    (3 / 2 * (S + Q) + 3 * Real.log (2 / (1 - Real.exp (-(δ / 18)))))
  have h4 := le_max_right (9 * errorBound S Q / δ)
    (3 / 2 * (S + Q) + 3 * Real.log (2 / (1 - Real.exp (-(δ / 18)))))
  have h5 := le_max_left
    (max (2 * S + 3 * Q) (Real.sqrt (6 * errorBound S Q)))
    (max (9 * errorBound S Q / δ)
      (3 / 2 * (S + Q) + 3 * Real.log (2 / (1 - Real.exp (-(δ / 18))))))
  have h6 := le_max_right
    (max (2 * S + 3 * Q) (Real.sqrt (6 * errorBound S Q)))
    (max (9 * errorBound S Q / δ)
      (3 / 2 * (S + Q) + 3 * Real.log (2 / (1 - Real.exp (-(δ / 18))))))
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private theorem tail_threshold (S Q δ t : ℝ) (hδ : 0 < δ)
    (ht : threshold S Q δ ≤ t) :
    0 < margin S Q δ ∧ Real.exp (-(t / 3)) < margin S Q δ / 2 := by
  have hd : 0 < 1 - Real.exp (-(δ / 18)) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have htail := (threshold_bounds S Q δ t ht).2.2.2
  have he := Real.exp_lt_exp.mpr (show -(t / 3) <
      -(S + Q) / 2 - Real.log (2 / (1 - Real.exp (-(δ / 18)))) by linarith)
  have heq : Real.exp (-(S + Q) / 2 - Real.log (2 / (1 - Real.exp (-(δ / 18))))) =
      margin S Q δ / 2 := by
    rw [Real.exp_sub, Real.exp_log (div_pos (by norm_num) hd)]
    unfold margin
    field_simp
  exact ⟨mul_pos (Real.exp_pos _) hd, he.trans_eq heq⟩

private theorem saturated_margin (h : Fin 3 → ℝ) (S T s t r q δ D : ℝ)
    (hh : ∀ i, 0 < h i) (hS : 0 ≤ S) (hT : Real.log 2 ≤ T)
    (hs : 0 ≤ s) (hsS : s ≤ S) (hr : 0 ≤ r) (hrq : r ≤ q)
    (hq : q ≤ totalWidth h) (hδ : 0 < δ) (hgap : δ ≤ q - r)
    (ht : threshold S (totalWidth h) δ ≤ t)
    (hD : D ≤ 2 * logValue (lowMean T s q (h 0 + h 1))) :
    Real.exp T * (D - slabEnvelope (base T s t) h
      (3 * T + s + t + r) (3 * T + s + t + q)) < -margin S (totalWidth h) δ := by
  have hb := threshold_bounds S (totalWidth h) δ t ht
  have hl := saturated_lower_gap h S T s t r q δ hh hS hs hsS hr hrq hq hδ hgap
    hb.1 hb.2.1 hb.2.2.1
  have hTp : 0 < T := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hT
  have ht0 : 0 ≤ t := (Real.sqrt_nonneg _).trans hb.2.1
  have hB : 0 ≤ h 0 + h 1 := by linarith [hh 0, hh 1]
  have hq0 : 0 ≤ q := hr.trans hrq
  have hm0 : 0 < lowMean T s q (h 0 + h 1) := by
    have := le_min hq0 hB
    dsimp [lowMean]; linarith
  have hmS : lowMean T s q (h 0 + h 1) ≤ T + (S + totalWidth h) / 2 := by
    have := min_le_left q (h 0 + h 1)
    dsimp [lowMean]; linarith
  have hmon := logValue_strictMono.monotoneOn
    (show 0 < lowMean T s q (h 0 + h 1) + δ / 18 by linarith)
    (show 0 < slabLower (base T s t) h (3 * T + s + t + r)
      (3 * T + s + t + q) by linarith) hl
  have hinc := log_increment (lowMean T s q (h 0 + h 1)) (δ / 18) hm0 (by linarith)
  have hρ : 0 ≤ slabRadius (base T s t) h (3 * T + s + t + r)
      (3 * T + s + t + q) := Real.sqrt_nonneg _
  have hH : T + t / 3 ≤ (3 * T + s + t + q) / 3 +
      2 * slabRadius (base T s t) h (3 * T + s + t + r) (3 * T + s + t + q) := by
    linarith
  have hlog := log_tail ((3 * T + s + t + q) / 3 +
    2 * slabRadius (base T s t) h (3 * T + s + t + r) (3 * T + s + t + q))
    (by linarith)
  have hEH := Real.exp_le_exp.mpr (neg_le_neg hH)
  have hEm := Real.exp_le_exp.mpr (neg_le_neg hmS)
  have hd0 : 0 ≤ 1 - Real.exp (-(δ / 18)) := by
    have := Real.exp_le_one_iff.mpr (show -(δ / 18) ≤ 0 by linarith)
    linarith
  have hmul := mul_le_mul_of_nonneg_right hEm hd0
  have htrans : Real.exp (-(T + (S + totalWidth h) / 2)) *
      (1 - Real.exp (-(δ / 18))) = Real.exp (-T) * margin S (totalWidth h) δ := by
    unfold margin
    rw [neg_add, Real.exp_add]
    ring
  rw [htrans] at hmul
  have htail := tail_threshold S (totalWidth h) δ t hδ ht
  have hE : Real.exp (-(T + t / 3)) = Real.exp (-T) * Real.exp (-(t / 3)) := by
    rw [neg_add, Real.exp_add]
  rw [hE] at hEH
  have hpre : D - slabEnvelope (base T s t) h
      (3 * T + s + t + r) (3 * T + s + t + q) ≤
      -2 * Real.exp (-T) * (margin S (totalWidth h) δ - Real.exp (-(t / 3))) := by
    dsimp [slabEnvelope]
    nlinarith
  have hscale := mul_le_mul_of_nonneg_left hpre (Real.exp_pos T).le
  have hexp : Real.exp T * Real.exp (-T) = 1 := by rw [← Real.exp_add]; simp
  have hscale' : Real.exp T * (D - slabEnvelope (base T s t) h
      (3 * T + s + t + r) (3 * T + s + t + q)) ≤
      -2 * (margin S (totalWidth h) δ - Real.exp (-(t / 3))) := by
    apply hscale.trans_eq
    calc
      Real.exp T * (-2 * Real.exp (-T) *
          (margin S (totalWidth h) δ - Real.exp (-(t / 3)))) =
          -2 * (Real.exp T * Real.exp (-T)) *
            (margin S (totalWidth h) δ - Real.exp (-(t / 3))) := by ring
      _ = _ := by rw [hexp]; ring
  linarith [htail.2]

end D5.S3.ArithSums.ThreeCoordinateSpan
