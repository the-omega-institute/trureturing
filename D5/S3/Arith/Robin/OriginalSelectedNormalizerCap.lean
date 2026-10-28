/- GID: D5/S3/Arith/Robin/OriginalSelectedNormalizerCap
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/OriginalSelectedNormalizerCap
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Complete label budgets cap the literal selected volume and original kernel mass. -/

import D5.S3.Arith.Robin.OriginalFirstClockTransport
import D5.S3.Arith.Robin.OriginalMovingCutRow

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Classical Set MeasureTheory
open scoped BigOperators

namespace D5.S3.Arith.Robin.OriginalSelectedNormalizerCap

open D5.S3.Arith.Robin.OriginalFirstClockTransport
open D5.S3.Arith.Robin.OriginalMovingWindowMoment
open D5.S3.Arith.Robin.OriginalMovingCutRow
open D5.S3.Arith.Robin.MellinWeightedVariation (weight)
open D5.S3.Arith.Robin.ActualRobinClockCovariance (g)

private theorem label_log_bounds (X : OriginalWindow) {p : ℕ} (hp : p ∈ X.labels) :
    Real.log (p : ℝ) ∈ Icc X.labelStart (2 * X.labelStart) := by
  rw [X.complete_labels] at hp
  obtain ⟨hp, hlo⟩ := Finset.mem_filter.mp hp
  have hhi : (p : ℝ) ≤ Real.exp (2 * X.labelStart) :=
    (Nat.cast_le.mpr (Nat.mem_primesLE.mp hp).1).trans
      (Nat.floor_le (Real.exp_pos _).le)
  constructor
  · simpa using Real.log_le_log (Real.exp_pos X.labelStart) hlo
  · simpa using Real.log_le_log (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos) hhi

private theorem edge_length (X : OriginalWindow) {p r : ℕ} (he : GoodEdge X p r) :
    Real.log (canonicalSource r : ℝ) - Real.log (canonicalSource p : ℝ) =
      Real.log (r : ℝ) - Real.log (p : ℝ) := by
  obtain ⟨U, hU, _, hpU, hrU, _⟩ := he.2.2.2.2
  rw [hpU, hrU, Nat.cast_mul, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast (X.prime_labels r he.2.1).ne_zero)
      (by exact_mod_cast hU.ne'),
    Real.log_mul (by exact_mod_cast (X.prime_labels p he.1).ne_zero)
      (by exact_mod_cast hU.ne')]
  ring

private theorem edge_clock_four (X : OriginalWindow) {p r : ℕ} (he : GoodEdge X p r) :
    4 ≤ Real.log (canonicalSource p : ℝ) := by
  obtain ⟨U, hU, hcore, hpU, _⟩ := he.2.2.2.2
  have hcorele := Nat.le_of_dvd hU hcore
  have hN : (64 : ℝ) ≤ canonicalSource p := by
    rw [hpU]
    exact_mod_cast (show 64 ≤ p * U by nlinarith [(X.prime_labels p he.1).two_le])
  have hlog : 4 ≤ Real.log (64 : ℝ) := by
    have h := Real.log_pow (2 : ℝ) 6
    norm_num at h
    linarith [Real.log_two_gt_d9]
  exact hlog.trans (Real.log_le_log (by norm_num) hN)

private theorem kernel_density_cap {t x : ℝ} (ht : 4 ≤ t) (hx : 4 ≤ x) :
    kernel t x ≤ x ^ (-3 / 10 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hx0 : 0 < x := by linarith
  by_cases hactive : t < x ∧ x ≤ endpoint t
  · have hw : 0 < weight t := weight_pos (by linarith)
    have htden : 0 < t ^ (11 / 10 : ℝ) := Real.rpow_pos_of_pos ht0 _
    have hwidth : width t ≤ t := by
      simpa [width] using Real.rpow_le_rpow_of_exponent_le
        (show 1 ≤ t by linarith) (show (4 / 5 : ℝ) ≤ 1 by norm_num)
    have hq : 1 ≤ x / t := (one_le_div ht0).mpr hactive.1.le
    have hpow : x ^ (3 / 10 : ℝ) ≤ t ^ (3 / 10 : ℝ) * (x / t) := by
      calc
        _ = t ^ (3 / 10 : ℝ) * (x / t) ^ (3 / 10 : ℝ) := by
          rw [← Real.mul_rpow ht0.le (div_pos hx0 ht0).le]
          congr 1
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (by simpa using (Real.rpow_le_rpow_of_exponent_le hq
            (show (3 / 10 : ℝ) ≤ 1 by norm_num))) (Real.rpow_nonneg ht0.le _)
    have htriangle : (endpoint t - x) * (x / t) ≤ width t := by
      apply (mul_le_mul_iff_right₀ ht0).mp
      have heq : (endpoint t - x) * (x / t) * t = (t + width t - x) * x := by
        dsimp [endpoint]
        field_simp
      rw [mul_comm t ((endpoint t - x) * (x / t)), heq]
      nlinarith [mul_nonneg (sub_nonneg.mpr hactive.1.le) (sub_nonneg.mpr hwidth)]
    have hproduct : (endpoint t - x) * x ^ (3 / 10 : ℝ) ≤ t ^ (11 / 10 : ℝ) := by
      calc
        _ ≤ (endpoint t - x) * (t ^ (3 / 10 : ℝ) * (x / t)) :=
          mul_le_mul_of_nonneg_left hpow (sub_nonneg.mpr hactive.2)
        _ = t ^ (3 / 10 : ℝ) * ((endpoint t - x) * (x / t)) := by ring
        _ ≤ t ^ (3 / 10 : ℝ) * width t :=
          mul_le_mul_of_nonneg_left htriangle (Real.rpow_nonneg ht0.le _)
        _ = t ^ (11 / 10 : ℝ) := by
          rw [width, ← Real.rpow_add ht0]
          norm_num
    have htriangleCap : (endpoint t - x) / t ^ (11 / 10 : ℝ) ≤ x ^ (-3 / 10 : ℝ) := by
      rw [show (-3 / 10 : ℝ) = -(3 / 10 : ℝ) by ring, Real.rpow_neg hx0.le]
      apply (div_le_iff₀ htden).mpr
      rw [inv_mul_eq_div]
      exact (le_div_iff₀ (Real.rpow_pos_of_pos hx0 (3 / 10 : ℝ))).mpr hproduct
    calc
      kernel t x = (g x - g (endpoint t)) / (weight t * t ^ (11 / 10 : ℝ)) :=
        if_pos hactive
      _ ≤ (weight t * (endpoint t - x)) / (weight t * t ^ (11 / 10 : ℝ)) :=
        div_le_div_of_nonneg_right (price_drop ht hactive.1.le hactive.2).2
          (mul_pos hw htden).le
      _ = (endpoint t - x) / t ^ (11 / 10 : ℝ) := by field_simp
      _ ≤ _ := htriangleCap
  · rw [kernel, if_neg hactive]
    exact Real.rpow_nonneg hx0.le _

private theorem label_cells_disjoint (X : OriginalWindow) :
    Set.PairwiseDisjoint (↑(goodEdges X))
      (fun e : ℕ × ℕ => Ioc (Real.log (e.1 : ℝ)) (Real.log (e.2 : ℝ))) := by
  intro e he f hf hef
  have he := (Finset.mem_filter.mp he).2
  have hf := (Finset.mem_filter.mp hf).2
  have horder : e.2 ≤ f.1 ∨ f.2 ≤ e.1 := by
    have ha := he.2.2.2.1 f.1 hf.1
    have hb := hf.2.2.2.1 e.1 he.1
    have hc := he.2.2.2.1 f.2 hf.2.1
    have hd := hf.2.2.2.1 e.2 he.2.1
    have hne : e.1 ≠ f.1 ∨ e.2 ≠ f.2 := by
      by_contra h
      push_neg at h
      exact hef (Prod.ext h.1 h.2)
    have := he.2.2.1
    have := hf.2.2.1
    omega
  rcases horder with h | h
  · exact Ioc_disjoint_Ioc_of_le (Real.log_le_log
      (by exact_mod_cast (X.prime_labels _ he.2.1).pos) (by exact_mod_cast h))
  · exact Disjoint.symm (Ioc_disjoint_Ioc_of_le (Real.log_le_log
      (by exact_mod_cast (X.prime_labels _ hf.2.1).pos) (by exact_mod_cast h)))

private theorem selected_volume_cap (X : OriginalWindow) (hL : 0 ≤ X.labelStart) :
    volume.real (selectedDomain X) ≤ X.labelStart := by
  let J : ℕ × ℕ → Set ℝ := fun e => Ioc (Real.log (e.1 : ℝ)) (Real.log (e.2 : ℝ))
  have hgood (e : ℕ × ℕ) (he : e ∈ goodEdges X) : GoodEdge X e.1 e.2 :=
    (Finset.mem_filter.mp he).2
  have hsum : (∑ e ∈ goodEdges X, volume.real (Icc
      (Real.log (canonicalSource e.1 : ℝ)) (Real.log (canonicalSource e.2 : ℝ)))) =
      ∑ e ∈ goodEdges X, volume.real (J e) := by
    apply Finset.sum_congr rfl
    intro e he
    have hedge := hgood e he
    rw [Real.volume_real_Icc_of_le hedge.2.2.2.2.choose_spec.2.2.2.2.1.le]
    rw [edge_length X hedge]
    dsimp only [J]
    rw [Real.volume_real_Ioc_of_le
      (Real.log_le_log (by exact_mod_cast (X.prime_labels _ hedge.1).pos)
        (by exact_mod_cast hedge.2.2.1.le))]
  have hsub : (⋃ e ∈ goodEdges X, J e) ⊆ Ioc X.labelStart (2 * X.labelStart) := by
    intro t ht
    obtain ⟨e, he, ht⟩ := mem_iUnion₂.mp ht
    have hedge := hgood e he
    exact ⟨(label_log_bounds X hedge.1).1.trans_lt ht.1,
      ht.2.trans (label_log_bounds X hedge.2.1).2⟩
  calc
    _ ≤ ∑ e ∈ goodEdges X, volume.real (Icc
        (Real.log (canonicalSource e.1 : ℝ)) (Real.log (canonicalSource e.2 : ℝ))) :=
      measureReal_biUnion_finset_le _ _
    _ = ∑ e ∈ goodEdges X, volume.real (J e) := hsum
    _ = volume.real (⋃ e ∈ goodEdges X, J e) :=
      (measureReal_biUnion_finset (label_cells_disjoint X)
        (fun _ _ => measurableSet_Ioc) (fun _ _ => by
          rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).symm
    _ ≤ volume.real (Ioc X.labelStart (2 * X.labelStart)) :=
      measureReal_mono hsub (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    _ = X.labelStart := by
      rw [Real.volume_real_Ioc_of_le (by linarith)]
      ring

/-- All actual good-edge source intervals are paid by the complete label-log
window. The mass cap uses the original price kernel and permits empty selection. -/
theorem original_selected_normalizer_cap (X : OriginalWindow) (hL : 0 ≤ X.labelStart) :
    volume.real (selectedDomain X) ≤ X.labelStart ∧
      ∀ x : ℝ, 4 ≤ x →
        0 ≤ (∫ t in selectedDomain X, kernel t x) ∧
        (∫ t in selectedDomain X, kernel t x) ≤ x ^ (-3 / 10 : ℝ) * X.labelStart := by
  have hvolume := selected_volume_cap X hL
  have hmeas : MeasurableSet (selectedDomain X) :=
    (goodEdges X).measurableSet_biUnion (fun _ _ => measurableSet_Icc)
  have hfour : ∀ t ∈ selectedDomain X, 4 ≤ t := by
    intro t ht
    obtain ⟨e, he, ht⟩ := mem_iUnion₂.mp ht
    exact (edge_clock_four X (Finset.mem_filter.mp he).2).trans ht.1
  have hfinite : volume (selectedDomain X) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (measure_biUnion_finset_le (goodEdges X) _)
    exact ENNReal.sum_ne_top.mpr (fun _ _ => isCompact_Icc.measure_ne_top)
  refine ⟨hvolume, ?_⟩
  intro x hx
  have hint : IntegrableOn (fun t => kernel t x) (selectedDomain X) := by
    apply integrableOn_finset_iUnion.mpr
    intro e he
    exact kernel_integrableOn (edge_clock_four X (Finset.mem_filter.mp he).2)
  refine ⟨setIntegral_nonneg hmeas (fun t ht => kernel_nonneg (hfour t ht)), ?_⟩
  calc
    _ ≤ ∫ _t in selectedDomain X, x ^ (-3 / 10 : ℝ) :=
      setIntegral_mono_on hint (integrableOn_const hfinite) hmeas
        (fun t ht => kernel_density_cap (hfour t ht) hx)
    _ = x ^ (-3 / 10 : ℝ) * volume.real (selectedDomain X) := by
      rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hvolume (Real.rpow_nonneg (by linarith) _)

#print axioms original_selected_normalizer_cap

end D5.S3.Arith.Robin.OriginalSelectedNormalizerCap
