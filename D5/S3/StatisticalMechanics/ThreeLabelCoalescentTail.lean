/- GID: D5/S3/StatisticalMechanics/ThreeLabelCoalescentTail
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/ThreeLabelCoalescentTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An open seven-rate region containing the entire coalescent family has a uniform positive association tail. -/

import D5.S3.StatisticalMechanics.ThreeLabelCoalescent

/-! # Uniform tail control under seven-rate perturbations -/

noncomputable section
namespace D5.S3.StatisticalMechanics.ThreeLabelCoalescentTail
open ThreeLabelCoalescent Set Filter
open scoped Topology

def margin (r : Fin 7 → ℝ) : ℝ :=
  min (r 4) (outgoing r) + min (r 5) (outgoing r) - outgoing r

/-- The region is specified by rate bounds, independently of trajectory roots. -/
def tailRegion : Set (Fin 7 → ℝ) := {r | (∀ i, 0 < r i) ∧
  max (r 0) (max (r 1) (r 2)) < 4 ∧
  1 / 8 < min (outgoing r) (min (r 4) (min (r 5) (r 6))) ∧ 1 / 8 < margin r}

private lemma region_open : IsOpen tailRegion := by
  have hmax : Continuous (fun r : Fin 7 → ℝ => max (r 0) (max (r 1) (r 2))) := by fun_prop
  have hmin : Continuous (fun r : Fin 7 → ℝ =>
      min (outgoing r) (min (r 4) (min (r 5) (r 6)))) := by dsimp [outgoing]; fun_prop
  have hm : Continuous margin := by
    change Continuous (fun r : Fin 7 → ℝ =>
      min (r 4) (r 0 + r 1 + r 2 + r 3) +
      min (r 5) (r 0 + r 1 + r 2 + r 3) - (r 0 + r 1 + r 2 + r 3))
    fun_prop
  simpa only [tailRegion, setOf_and, setOf_forall] using
    (isOpen_iInter_of_finite fun i : Fin 7 =>
      isOpen_lt continuous_const (continuous_apply i)).inter
      ((isOpen_lt hmax continuous_const).inter
        ((isOpen_lt continuous_const hmin).inter (isOpen_lt continuous_const hm)))

private lemma base_mem (h : ℝ) (hh : 0 < h) : baseRates h ∈ tailRegion := by
  have hL : outgoing (baseRates h) = ell h := by dsimp [outgoing, baseRates, ell]; ring
  have hl : 1 / 8 < ell h := by dsimp [ell]; linarith
  have hquarter : (1 : ℝ) / 4 ≤ ell h := by dsimp [ell]; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num [baseRates, ell] <;> linarith
  · norm_num [baseRates]
  · rw [hL]
    change (1 : ℝ) / 8 < min (ell h) (min (1 / 4) (min (ell h) (1 / 4)))
    exact lt_min hl (lt_min (by norm_num) (lt_min hl (by norm_num)))
  · rw [margin, hL]
    change (1 : ℝ) / 8 < min (1 / 4) (ell h) + min (ell h) (ell h) - ell h
    rw [min_eq_left hquarter, min_self]
    linarith

/-- One open rate region contains every positive-h base vector and has a common
finite time after which every probability solution has strictly positive association. -/
theorem uniform_positive_tail :
    ∃ U : Set (Fin 7 → ℝ), IsOpen U ∧ (∀ h, 0 < h → baseRates h ∈ U) ∧
      ∃ T : ℝ, 0 ≤ T ∧ ∀ r ∈ U, ∀ p : ℝ → Fin 5 → ℝ, GeneralForwardLaw r p →
        ∀ t, T ≤ t → 0 < delta (p t) := by
  have hlim (n : ℝ) : Tendsto (fun t : ℝ => t ^ n * Real.exp (-(1 / 8 : ℝ) * t))
      atTop (𝓝 0) := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero n (1 / 8) (by norm_num)
  have hzero : Tendsto (fun t : ℝ => Real.exp (-(1 / 8 : ℝ) * t)) atTop (𝓝 0) := by
    simpa using hlim 0
  have hone : Tendsto (fun t : ℝ => t * Real.exp (-(1 / 8 : ℝ) * t)) atTop (𝓝 0) := by
    simpa using hlim 1
  have htwo : Tendsto (fun t : ℝ => t ^ 2 * Real.exp (-(1 / 8 : ℝ) * t)) atTop (𝓝 0) := by
    simpa using hlim 2
  have hall := (hzero.add (hone.const_mul 12)).add (htwo.const_mul 16)
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (hall.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) + 12 * 0 + 16 * 0 < 1)))
  refine ⟨tailRegion, region_open, base_mem, max T 0, le_max_right _ _, ?_⟩
  intro r hr p hp t ht
  rcases hr with ⟨hr, hu, hl, hm⟩
  have ht0 : 0 ≤ t := (le_max_right T 0).trans ht
  have htT : T ≤ t := (le_max_left T 0).trans ht
  rcases lt_min_iff.mp hl with ⟨hL, hrest⟩
  rcases lt_min_iff.mp hrest with ⟨hd, hrest⟩
  rcases lt_min_iff.mp hrest with ⟨he, hf⟩
  rcases max_lt_iff.mp hu with ⟨hα, hu⟩
  rcases max_lt_iff.mp hu with ⟨hβ, hγ⟩
  obtain ⟨hN, hAB, hbranches, _, _⟩ := seven_rate_endpoint_certificates r hr p hp
  have hE (c : ℝ) (hc : 1 / 8 ≤ c) :
      Real.exp (-c * t) ≤ Real.exp (-(1 / 8 : ℝ) * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hbranch (a d : ℝ) (ha : 0 ≤ a) (ha4 : a ≤ 4) (hd : 1 / 8 ≤ d) :
      a * t * Real.exp (-min d (outgoing r) * t) ≤
        4 * t * Real.exp (-(1 / 8 : ℝ) * t) := by
    have hexp := hE (min d (outgoing r)) (le_min hd hL.le)
    exact mul_le_mul (mul_le_mul_of_nonneg_right ha4 ht0) hexp
      (Real.exp_pos _).le (by positivity)
  have hA := (hbranches t ht0).1.trans (hbranch (r 0) (r 4) (hr 0).le hα.le hd.le)
  have hB := (hbranches t ht0).2.1.trans (hbranch (r 1) (r 5) (hr 1).le hβ.le he.le)
  have hC := (hbranches t ht0).2.2.trans (hbranch (r 2) (r 6) (hr 2).le hγ.le hf.le)
  have hNbound : p t 0 ≤ Real.exp (-(1 / 8 : ℝ) * t) := by
    rw [hN t ht0]; exact hE (outgoing r) hL.le
  have hprod : r 0 * r 1 ≤ 16 := by nlinarith [hr 0, hr 1]
  have hratio : p t 1 * p t 2 / p t 0 ≤
      16 * t ^ 2 * Real.exp (-(1 / 8 : ℝ) * t) := by
    apply (hAB t ht0).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_right hprod (sq_nonneg t)) (hE (margin r) hm.le)
      (Real.exp_pos _).le (by positivity)
  have hsum := hp.normalized t ht0
  rw [Fin.sum_univ_five] at hsum
  have htail := hT t htT
  have hgap : 0 < p t 3 - p t 1 * p t 2 / p t 0 := by
    nlinarith
  have hNpos : 0 < p t 0 := by rw [hN t ht0]; exact Real.exp_pos _
  have hid : delta (p t) = p t 0 * (p t 3 - p t 1 * p t 2 / p t 0) := by
    dsimp [delta]; field_simp [ne_of_gt hNpos]
  rw [hid]
  exact mul_pos hNpos hgap

private lemma positive_in_small_box (r : Fin 7 → ℝ) (hr : ∀ i, 0 < r i)
    (p : ℝ → Fin 5 → ℝ) (hp : GeneralForwardLaw r p)
    (R a : ℝ) (hR : 0 < R) (ha : 0 < a) (hupper : ∀ i, r i ≤ R) (hζ : a ≤ r 3)
    (t : ℝ) (ht : 0 < t) (htR : t < 1 / (8 * R)) (hta : t < a / (8 * R ^ 2)) :
    0 < delta (p t) := by
  obtain ⟨hN, _, hbranches, _, _⟩ := seven_rate_endpoint_certificates r hr p hp
  have hL : 0 < outgoing r := by dsimp [outgoing]; linarith [hr 0, hr 1, hr 2, hr 3]
  have hLR : outgoing r ≤ 4 * R := by
    dsimp [outgoing]; linarith [hupper 0, hupper 1, hupper 2, hupper 3]
  have htR' : 8 * R * t < 1 := by
    have := (lt_div_iff₀ (by positivity : 0 < 8 * R)).mp htR
    nlinarith
  have hhalf (s : ℝ) (hs : s ∈ Icc 0 t) : 1 / 2 ≤ p s 0 := by
    rw [hN s hs.1]
    have hexp := Real.add_one_le_exp (-outgoing r * s)
    have hst := mul_le_mul_of_nonneg_left hs.2 hL.le
    have hLt := mul_le_mul_of_nonneg_right hLR ht.le
    linarith
  have hTder (s : ℝ) (hs : s ∈ Icc 0 t) : a / 2 ≤ deriv (fun u => p u 3) s := by
    rw [(hp.equation s hs.1 3).deriv]
    change a / 2 ≤ r 3 * p s 0 + r 4 * p s 1 + r 5 * p s 2 + r 6 * p s 4
    have hdirect := mul_le_mul hζ (hhalf s hs) (by norm_num : (0 : ℝ) ≤ 1 / 2) (hr 3).le
    have hA := mul_nonneg (hr 4).le (hp.nonneg s hs.1 1)
    have hB := mul_nonneg (hr 5).le (hp.nonneg s hs.1 2)
    have hC := mul_nonneg (hr 6).le (hp.nonneg s hs.1 4)
    linarith
  have hT := (convex_Icc (0 : ℝ) t).mul_sub_le_image_sub_of_le_deriv
    (fun s hs => (hp.equation s hs.1 3).continuousAt.continuousWithinAt)
    (fun s hs => (hp.equation s (interior_subset hs).1 3).differentiableAt.differentiableWithinAt)
    (fun s hs => hTder s (interior_subset hs))
    0 ⟨le_rfl, ht.le⟩ t ⟨ht.le, le_rfl⟩ ht.le
  have hzT : p 0 3 = 0 := by simpa [initial] using congrFun hp.start 3
  rw [hzT, sub_zero, sub_zero] at hT
  have hbranch (i d : Fin 7) : r i * t * Real.exp (-min (r d) (outgoing r) * t) ≤ R * t := by
    have he : Real.exp (-min (r d) (outgoing r) * t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (le_min (hr d).le hL.le)) ht.le)
    have hb := mul_le_mul (mul_le_mul_of_nonneg_right (hupper i) ht.le) he
      (Real.exp_pos _).le (by positivity : 0 ≤ R * t)
    simpa using hb
  have hA := (hbranches t ht.le).1.trans (hbranch 0 4)
  have hB := (hbranches t ht.le).2.1.trans (hbranch 1 5)
  have hAB := mul_le_mul hA hB (hp.nonneg t ht.le 2) (by positivity : 0 ≤ R * t)
  have hNT := mul_le_mul (hhalf t ⟨ht.le, le_rfl⟩) hT
    (by positivity : 0 ≤ a / 2 * t) (hp.nonneg t ht.le 0)
  have hsmall := (lt_div_iff₀ (by positivity : 0 < 8 * R ^ 2)).mp hta
  have hsmall' := mul_lt_mul_of_pos_right hsmall ht
  dsimp [delta]
  nlinarith

/-- Each base rate vector has an open neighborhood and a common positive time
interval on which every probability solution has strictly positive association. -/
theorem uniform_positive_near_zero (h : ℝ) (hh : 0 < h) :
    ∃ U : Set (Fin 7 → ℝ), IsOpen U ∧ baseRates h ∈ U ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ U, ∀ p : ℝ → Fin 5 → ℝ, GeneralForwardLaw r p →
        ∀ t, 0 < t → t < ε → 0 < delta (p t) := by
  let R := ell h + 4
  let a := h / 2
  have hR : 0 < R := by dsimp [R, ell]; linarith
  have ha : 0 < a := by dsimp [a]; positivity
  let U : Set (Fin 7 → ℝ) := {r | (∀ i, 0 < r i) ∧ (∀ i, r i < R) ∧ a < r 3}
  have hU : IsOpen U := by
    simpa only [U, setOf_and, setOf_forall] using
      (isOpen_iInter_of_finite fun i : Fin 7 =>
        isOpen_lt continuous_const (continuous_apply i)).inter
        ((isOpen_iInter_of_finite fun i : Fin 7 =>
          isOpen_lt (continuous_apply i) continuous_const).inter
          (isOpen_lt continuous_const (continuous_apply (3 : Fin 7))))
  have hbase : baseRates h ∈ U := by
    refine ⟨?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num [baseRates, ell] <;> linarith
    · intro i; fin_cases i <;> norm_num [baseRates, R, ell] <;> linarith
    · change h / 2 < h; linarith
  refine ⟨U, hU, hbase, min (1 / (8 * R)) (a / (8 * R ^ 2)), by positivity, ?_⟩
  intro r hr p hp t ht hε
  exact positive_in_small_box r hr.1 p hp R a hR ha (fun i => (hr.2.1 i).le) hr.2.2.le
    t ht (lt_of_lt_of_le hε (min_le_left _ _)) (lt_of_lt_of_le hε (min_le_right _ _))

#print axioms uniform_positive_near_zero
#print axioms uniform_positive_tail
end D5.S3.StatisticalMechanics.ThreeLabelCoalescentTail
