/- GID: D5/S3/Topology/Measures/IntervalLpCompactness
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/IntervalLpCompactness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Whole-interval equal-mesh averages are controlled by internal positive translations. -/

import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal

namespace D5.S3.Topology.Measures.IntervalLpCompactness

private def upperBand (T d : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 < z.1 ∧ z.1 < z.2 ∧ z.2 ≤ T ∧ z.2 - z.1 ≤ d}

private def symmetricBand (T d : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Ioc 0 T ∧ z.2 ∈ Ioc 0 T ∧ |z.2 - z.1| ≤ d}

private lemma measurable_upperBand (T d : ℝ) : MeasurableSet (upperBand T d) := by
  unfold upperBand
  have hf : Measurable (fun z : ℝ × ℝ => z.1) := measurable_fst
  have hg : Measurable (fun z : ℝ × ℝ => z.2) := measurable_snd
  exact (measurableSet_lt measurable_const hf).inter
    ((measurableSet_lt hf hg).inter ((measurableSet_le hg measurable_const).inter
      (measurableSet_le (hg.sub hf) measurable_const)))

private lemma band_integral_eq (T d : ℝ) (K : ℝ × ℝ → ℝ≥0∞)
    (hK : Measurable K) (hsym : ∀ x y, K (y,x) = K (x,y))
    (hdiag : ∀ x, K (x,x) = 0) :
    ∫⁻ z in symmetricBand T d, K z ∂(volume.prod volume) =
      2 * ∫⁻ h in Ioc 0 d, ∫⁻ t in Ioc 0 (T-h), K (t,t+h) := by
  classical
  let P := upperBand T d
  have hP : MeasurableSet P := measurable_upperBand T d
  have hsplit : (symmetricBand T d).indicator K =
      fun z => P.indicator K z + P.indicator K z.swap := by
    funext z
    rcases z with ⟨x,y⟩
    rcases lt_trichotomy x y with h | h | h
    · have hn : (y,x) ∉ P := by simp [P, upperBand, not_lt_of_gt h]
      have heq : (x,y) ∈ symmetricBand T d ↔ (x,y) ∈ P := by
        simp only [symmetricBand, P, upperBand, mem_ofPred, mem_Ioc]
        rw [abs_of_pos (sub_pos.mpr h)]
        constructor
        · rintro ⟨hx,hy,hd⟩; exact ⟨hx.1,h,hy.2,hd⟩
        · rintro ⟨hx,_,hy,hd⟩; exact ⟨⟨hx,le_trans h.le hy⟩,⟨lt_trans hx h,hy⟩,hd⟩
      simp only [Prod.swap_prod_mk, indicator_of_notMem hn, add_zero]
      by_cases hm : (x,y) ∈ P
      · rw [indicator_of_mem hm, indicator_of_mem (heq.mpr hm)]
      · rw [indicator_of_notMem hm, indicator_of_notMem (fun hb => hm (heq.mp hb))]
    · subst y
      simp [hdiag, indicator_apply]
    · have hn : (x,y) ∉ P := by simp [P, upperBand, not_lt_of_gt h]
      have heq : (x,y) ∈ symmetricBand T d ↔ (y,x) ∈ P := by
        simp only [symmetricBand, P, upperBand, mem_ofPred, mem_Ioc]
        rw [abs_of_neg (sub_neg.mpr h)]
        constructor
        · rintro ⟨hx,hy,hd⟩; exact ⟨hy.1,h,hx.2,by linarith⟩
        · rintro ⟨hy,_,hx,hd⟩; exact ⟨⟨lt_trans hy h,hx⟩,⟨hy,le_trans h.le hx⟩,by linarith⟩
      simp only [Prod.swap_prod_mk, indicator_of_notMem hn, zero_add]
      by_cases hm : (y,x) ∈ P
      · rw [indicator_of_mem hm, indicator_of_mem (heq.mpr hm), hsym]
      · rw [indicator_of_notMem hm, indicator_of_notMem (fun hb => hm (heq.mp hb))]
  have htwo : ∫⁻ z in symmetricBand T d, K z ∂(volume.prod volume) =
      2 * ∫⁻ z in P, K z ∂(volume.prod volume) := by
    rw [← lintegral_indicator (by
      unfold symmetricBand
      have hf : Measurable (fun z : ℝ × ℝ => z.1) := measurable_fst
      have hg : Measurable (fun z : ℝ × ℝ => z.2) := measurable_snd
      exact (measurableSet_Ioc.preimage hf).inter
        ((measurableSet_Ioc.preimage hg).inter
          (measurableSet_le (continuous_abs.measurable.comp (hg.sub hf)) measurable_const))),
      hsplit, lintegral_add_left (hK.indicator hP), lintegral_prod_swap,
      lintegral_indicator hP, two_mul]
  rw [htwo]
  congr 1
  have hchange := (measurePreserving_prod_add (volume : Measure ℝ) volume).lintegral_comp_emb
    (MeasurableEquiv.shearAddRight ℝ).measurableEmbedding (P.indicator K)
  rw [lintegral_indicator hP] at hchange
  rw [← hchange]
  have hmeas : Measurable (fun z : ℝ × ℝ => P.indicator K (z.1,z.1+z.2)) :=
    (hK.indicator hP).comp (measurable_fst.prodMk (measurable_fst.add measurable_snd))
  rw [lintegral_prod_symm' _ hmeas]
  have heq : ∀ t h, P.indicator K (t,t+h) =
      (Ioc 0 d).indicator (fun h => (Ioc 0 (T-h)).indicator
        (fun t => K (t,t+h)) t) h := by
    intro t h
    have hm : (t,t+h) ∈ P ↔ h ∈ Ioc 0 d ∧ t ∈ Ioc 0 (T-h) := by
      simp only [P, upperBand, mem_ofPred, mem_Ioc]
      constructor
      · rintro ⟨ht,hh,hT,hd⟩
        exact ⟨⟨by linarith,by linarith⟩,⟨ht,by linarith⟩⟩
      · rintro ⟨⟨hh,hd⟩,⟨ht,hT⟩⟩
        exact ⟨ht,by linarith,by linarith,by linarith⟩
    by_cases hh : h ∈ Ioc 0 d
    · rw [indicator_of_mem hh]
      by_cases ht : t ∈ Ioc 0 (T-h)
      · rw [indicator_of_mem ht, indicator_of_mem (hm.mpr ⟨hh,ht⟩)]
      · rw [indicator_of_notMem ht, indicator_of_notMem (fun hz => ht (hm.mp hz).2)]
    · rw [indicator_of_notMem hh, indicator_of_notMem (fun hz => hh (hm.mp hz).1)]
  simp_rw [heq]
  calc
    _ = ∫⁻ h, (Ioc 0 d).indicator (fun h => ∫⁻ t in Ioc 0 (T-h), K (t,t+h)) h := by
      apply lintegral_congr_ae
      refine Filter.Eventually.of_forall fun h => ?_
      by_cases hh : h ∈ Ioc 0 d
      · simp only [indicator_of_mem hh]
        exact lintegral_indicator measurableSet_Ioc _
      · simp [indicator_of_notMem hh]
    _ = _ := lintegral_indicator measurableSet_Ioc _

private lemma cell_pair_integral_le {ι : Type*} [Fintype ι]
    (T d : ℝ) (s : ι → Set ℝ) (hs : ∀ i, MeasurableSet (s i))
    (hdisj : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hsub : ∀ i, s i ⊆ Ioc 0 T)
    (hdiam : ∀ i, ∀ x ∈ s i, ∀ y ∈ s i, |y-x| ≤ d)
    (K : ℝ × ℝ → ℝ≥0∞) (hK : Measurable K)
    (hsym : ∀ x y, K (y,x) = K (x,y)) (hdiag : ∀ x, K (x,x) = 0) :
    ∑ i, ∫⁻ x in s i, ∫⁻ y in s i, K (x,y) ≤
      2 * ∫⁻ h in Ioc 0 d, ∫⁻ t in Ioc 0 (T-h), K (t,t+h) := by
  classical
  calc
    _ = ∑ i, ∫⁻ z, (s i ×ˢ s i).indicator K z ∂(volume.prod volume) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [lintegral_indicator ((hs i).prod (hs i))]
      exact (setLIntegral_prod K hK.aemeasurable.restrict).symm
    _ = ∫⁻ z, ∑ i, (s i ×ˢ s i).indicator K z ∂(volume.prod volume) :=
      (lintegral_finsetSum _ (fun i _ => hK.indicator ((hs i).prod (hs i)))).symm
    _ ≤ ∫⁻ z, (symmetricBand T d).indicator K z ∂(volume.prod volume) := by
      apply lintegral_mono
      intro z
      by_cases hz : ∃ i, z.1 ∈ s i ∧ z.2 ∈ s i
      · obtain ⟨i,hx,hy⟩ := hz
        have hb : z ∈ symmetricBand T d := ⟨hsub i hx,hsub i hy,hdiam i z.1 hx z.2 hy⟩
        rw [indicator_of_mem hb]
        apply le_of_eq
        change (∑ j, (s j ×ˢ s j).indicator K z) = K z
        rw [Finset.sum_eq_single i]
        · exact indicator_of_mem (show z ∈ s i ×ˢ s i from ⟨hx,hy⟩) K
        · intro j _ hji
          exact indicator_of_notMem (fun hj => Set.disjoint_left.mp (hdisj hji) hj.1 hx) K
        · simp
      · have hzero : ∀ i, (s i ×ˢ s i).indicator K z = 0 := by
          intro i
          exact indicator_of_notMem (fun hm : z ∈ s i ×ˢ s i => hz ⟨i,hm⟩) K
        simp only [hzero, Finset.sum_const_zero, zero_le]
    _ = _ := by
      rw [lintegral_indicator (by
        have hf : Measurable (fun z : ℝ × ℝ => z.1) := measurable_fst
        have hg : Measurable (fun z : ℝ × ℝ => z.2) := measurable_snd
        exact (measurableSet_Ioc.preimage hf).inter
          ((measurableSet_Ioc.preimage hg).inter
            (measurableSet_le (continuous_abs.measurable.comp (hg.sub hf)) measurable_const)))]
      exact band_integral_eq T d K hK hsym hdiag

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in
`docs/reports/licenses/tauceti-sphere-port-LICENSE.txt`.
Authors: The Tau Ceti contributors

Selective source port from TauCetiProject/TauCeti revision
`ef2b35da80dbe9f123fd200fcf160a036fe69813`:
`TauCeti/MeasureTheory/Function/Lp/LIntegralRpow.lean`, SHA256
`6954ce124fb51025e4afe01c0992d2afedfb83740ee5f2835471f09f6f9c4c77`,
and `TauCeti/MeasureTheory/Integral/Average.lean`, SHA256
`cd2ede6573aaf1c5c80fd56e048f70859a5fb94c97b9a944e33b292374af2c67`.
The selected Hölder and average-norm declarations are private consumed helpers.
Adaptation: imports and private visibility for the receiving Mathlib pin.
Retire each port when the Mathlib revision adopted by this repository supplies
an equivalent declaration, replacing its uses by the adopted Mathlib declaration.
-/
private theorem rpow_lintegral_le_measure_univ_rpow_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {u : α → ℝ≥0∞} (hu : AEMeasurable u μ) {r : ℝ} (hr : 1 ≤ r) :
    (∫⁻ x, u x ∂μ) ^ r ≤ μ Set.univ ^ (r - 1) * ∫⁻ x, u x ^ r ∂μ := by
  have hf : AEStronglyMeasurable u μ := hu.aestronglyMeasurable
  have hr0 : (0 : ℝ) < r := one_pos.trans_le hr
  have hCr : eLpNorm u (ENNReal.ofReal r) μ = (∫⁻ x, u x ^ r ∂μ) ^ (1 / r) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr0) ENNReal.ofReal_ne_top hf,
      ENNReal.toReal_ofReal hr0.le]
    simp only [enorm_eq_self]
  have holder : ∫⁻ x, u x ∂μ
      ≤ (∫⁻ x, u x ^ r ∂μ) ^ (1 / r) * μ Set.univ ^ (1 - 1 / r) := by
    have hle : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr
    have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (f := u) (μ := μ) hle hf
    rw [eLpNorm_one_eq_lintegral_enorm hf, hCr, ENNReal.toReal_one,
      ENNReal.toReal_ofReal hr0.le, div_one] at this
    simpa only [enorm_eq_self] using this
  have hinv : 1 / r * r = 1 := by field_simp
  have hexp : (1 - 1 / r) * r = r - 1 := by field_simp
  calc (∫⁻ x, u x ∂μ) ^ r
      ≤ ((∫⁻ x, u x ^ r ∂μ) ^ (1 / r) * μ Set.univ ^ (1 - 1 / r)) ^ r :=
        ENNReal.rpow_le_rpow holder hr0.le
    _ = ((∫⁻ x, u x ^ r ∂μ) ^ (1 / r)) ^ r * (μ Set.univ ^ (1 - 1 / r)) ^ r :=
        ENNReal.mul_rpow_of_nonneg _ _ hr0.le
    _ = (∫⁻ x, u x ^ r ∂μ) * μ Set.univ ^ (r - 1) := by
        rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hinv, hexp, ENNReal.rpow_one]
    _ = μ Set.univ ^ (r - 1) * ∫⁻ x, u x ^ r ∂μ := mul_comm _ _


section AveragePort
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem enorm_average_le_laverage (μ : Measure α) (f : α → E) :
    ‖⨍ x, f x ∂μ‖ₑ ≤ ⨍⁻ x, ‖f x‖ₑ ∂μ := by
  rw [average_eq', laverage_eq']
  exact enorm_integral_le_lintegral_enorm _

/-- The extended norm of an average over a set is at most the average of the extended norm over
the set. -/
private theorem enorm_setAverage_le_setLAverage (μ : Measure α) (f : α → E) (s : Set α) :
    ‖⨍ x in s, f x ∂μ‖ₑ ≤ ⨍⁻ x in s, ‖f x‖ₑ ∂μ :=
  enorm_average_le_laverage _ _


end AveragePort
section HolderPort
variable {α F : Type*} [MeasurableSpace α] {mu : Measure α} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {f : α → F} {p : ℝ≥0∞} {s : Set α}
private theorem enorm_setAverage_rpow_le {q : ℝ} (hq : 1 ≤ q) :
    ‖⨍ y in s, f y ∂mu‖ₑ ^ q ≤ (mu s)⁻¹ * ∫⁻ y in s, ‖f y‖ₑ ^ q ∂mu := by
  have hq0 : (0 : ℝ) < q := one_pos.trans_le hq
  by_cases hs0 : mu s = 0
  · simp [setAverage_eq, measureReal_def, hs0, ENNReal.zero_rpow_of_pos hq0]
  by_cases hs : mu s = ∞
  · simp [setAverage_eq, measureReal_def, hs, ENNReal.zero_rpow_of_pos hq0]
  by_cases hf : IntegrableOn f s mu
  swap
  · simp [setAverage_eq, integral_undef hf, ENNReal.zero_rpow_of_pos hq0]
  have h0 : ‖⨍ y in s, f y ∂mu‖ₑ ≤ (mu s)⁻¹ * ∫⁻ y in s, ‖f y‖ₑ ∂mu := by
    simpa only [setLAverage_eq, ENNReal.div_eq_inv_mul] using
      enorm_setAverage_le_setLAverage mu f s
  have hholder : (∫⁻ y in s, ‖f y‖ₑ ∂mu) ^ q ≤ mu s ^ (q - 1) * ∫⁻ y in s, ‖f y‖ₑ ^ q ∂mu := by
    have := rpow_lintegral_le_measure_univ_rpow_mul (μ := mu.restrict s)
      (u := fun y => ‖f y‖ₑ) hf.aestronglyMeasurable.enorm hq
    rwa [Measure.restrict_apply_univ] at this
  have hexp : -q + (q - 1) = (-1 : ℝ) := by ring
  calc ‖⨍ y in s, f y ∂mu‖ₑ ^ q
      ≤ ((mu s)⁻¹ * ∫⁻ y in s, ‖f y‖ₑ ∂mu) ^ q := ENNReal.rpow_le_rpow h0 hq0.le
    _ = (mu s)⁻¹ ^ q * (∫⁻ y in s, ‖f y‖ₑ ∂mu) ^ q := ENNReal.mul_rpow_of_nonneg _ _ hq0.le
    _ ≤ (mu s)⁻¹ ^ q * (mu s ^ (q - 1) * ∫⁻ y in s, ‖f y‖ₑ ^ q ∂mu) := mul_le_mul' le_rfl hholder
    _ = (mu s)⁻¹ * ∫⁻ y in s, ‖f y‖ₑ ^ q ∂mu := by
        rw [← mul_assoc, ENNReal.inv_rpow, ← ENNReal.rpow_neg, ← ENNReal.rpow_add _ _ hs0 hs,
          hexp, ENNReal.rpow_neg_one]


end HolderPort


private lemma cell_error_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {μ : Measure ℝ} {s : Set ℝ} {f : ℝ → E}
    (hf : IntegrableOn f s μ) (hs0 : μ s ≠ 0) (hs : μ s ≠ ∞)
    {q : ℝ} (hq : 1 ≤ q) :
    ∫⁻ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ₑ ^ q ∂μ ≤
      (μ s)⁻¹ * ∫⁻ x in s, ∫⁻ y in s, ‖f x - f y‖ₑ ^ q ∂μ ∂μ := by
  calc
    _ ≤ ∫⁻ x in s, (μ s)⁻¹ * ∫⁻ y in s, ‖f x - f y‖ₑ ^ q ∂μ ∂μ := by
      apply lintegral_mono
      intro x
      have hav : (⨍ y in s, f x - f y ∂μ) = f x - ⨍ y in s, f y ∂μ := by
        rw [setAverage_fun_sub (integrableOn_const hs) hf, setAverage_const hs0 hs]
      dsimp only
      rw [← hav]
      exact enorm_setAverage_rpow_le hq
    _ = _ := lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hs0)

/-- The right-closed mesh cell with width `d` and index `i`. -/
def meshCell (d : ℝ) (i : ℕ) : Set ℝ := Ioc (i*d) ((i+1)*d)

/-- The equal-mesh averaging function, including the first and last cells. -/
noncomputable def meshAverage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℝ) (N : ℕ) (f : ℝ → E) : ℝ → E :=
  fun t => ∑ i : Fin N, (meshCell d i).indicator (fun _ => ⨍ y in meshCell d i, f y) t

private lemma mesh_monotone {d : ℝ} (hd : 0 ≤ d) : Monotone (fun i : ℕ => (i:ℝ)*d) :=
  fun _ _ hij => mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hd

private lemma mesh_disjoint {d : ℝ} (hd : 0 ≤ d) :
    Pairwise (fun i j : ℕ => Disjoint (meshCell d i) (meshCell d j)) := by
  simpa only [meshCell, Order.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
    (mesh_monotone hd).pairwise_disjoint_on_Ioc_succ

private lemma mesh_union {d : ℝ} (hd : 0 ≤ d) (N : ℕ) :
    ⋃ i : Fin N, meshCell d i = Ioc 0 (N*d) := by
  have hh := (mesh_monotone hd).biUnion_Ico_Ioc_map_succ 0 N
  have heq : (⋃ i : Fin N, meshCell d i) = ⋃ i ∈ Ico 0 N, meshCell d i := by
    ext x
    simp only [mem_iUnion, mem_Ico, Nat.zero_le, true_and]
    constructor
    · rintro ⟨i,hi⟩; exact ⟨i,i.isLt,hi⟩
    · rintro ⟨i,hi,hx⟩; exact ⟨⟨i,hi⟩,hx⟩
  rw [heq]
  simpa only [meshCell, Order.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
    Nat.cast_zero, zero_mul] using hh

private lemma mesh_subset {d : ℝ} (hd : 0 ≤ d) {N : ℕ} (i : Fin N) :
    meshCell d i ⊆ Ioc 0 (N*d) := by
  rw [← mesh_union hd N]
  exact subset_iUnion (fun j : Fin N => meshCell d j) i

private lemma mesh_diameter {d : ℝ} (_hd : 0 ≤ d) (i : ℕ) :
    ∀ x ∈ meshCell d i, ∀ y ∈ meshCell d i, |y-x| ≤ d := by
  intro x hx y hy
  change (i:ℝ)*d < x ∧ x ≤ (i+1)*d at hx
  change (i:ℝ)*d < y ∧ y ≤ (i+1)*d at hy
  rw [abs_le]
  constructor <;> linarith

private lemma meshAverage_on {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℝ} (hd : 0 ≤ d) (N : ℕ) (f : ℝ → E) (i : Fin N) {t : ℝ}
    (ht : t ∈ meshCell d i) :
    meshAverage d N f t = ⨍ y in meshCell d i, f y := by
  classical
  unfold meshAverage
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem ht _
  · intro j _ hji
    exact indicator_of_notMem
      (fun hj => Set.disjoint_left.mp (mesh_disjoint hd (Fin.val_injective.ne hji)) hj ht) _
  · simp

/-- The whole-interval mesh error is controlled by internal positive translations.
The constant is a convenient bound, with no optimality assertion. -/
theorem mesh_error_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {d : ℝ} (hd : 0 < d) (N : ℕ) {f : ℝ → E}
    (hf : IntegrableOn f (Ioc 0 (N*d))) (hm : StronglyMeasurable f)
    {q : ℝ} (hq : 1 ≤ q) :
    ∫⁻ t in Ioc 0 (N*d), ‖f t - meshAverage d N f t‖ₑ ^ q ≤
      (ENNReal.ofReal d)⁻¹ * (2 *
        ∫⁻ h in Ioc 0 d, ∫⁻ t in Ioc 0 (N*d-h), ‖f (t+h) - f t‖ₑ ^ q) := by
  classical
  let K : ℝ × ℝ → ℝ≥0∞ := fun z => ‖f z.1 - f z.2‖ₑ ^ q
  have hK : Measurable K :=
    ((hm.comp_measurable measurable_fst).sub (hm.comp_measurable measurable_snd)).enorm.pow_const q
  have hs : ∀ i : Fin N, MeasurableSet (meshCell d i) := fun _ => measurableSet_Ioc
  have hdisj : Pairwise (fun i j : Fin N => Disjoint (meshCell d i) (meshCell d j)) :=
    fun _ _ hij => mesh_disjoint hd.le (Fin.val_injective.ne hij)
  have hvol : ∀ i : Fin N, volume (meshCell d i) = ENNReal.ofReal d := by
    intro i
    rw [meshCell, Real.volume_Ioc]
    congr 1
    ring
  calc
    _ = ∑ i : Fin N, ∫⁻ x in meshCell d i, ‖f x - ⨍ y in meshCell d i, f y‖ₑ ^ q := by
      rw [← mesh_union hd.le N, lintegral_iUnion hs hdisj]
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro i _
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro x hx
      dsimp only
      rw [meshAverage_on hd.le N f i hx]
    _ ≤ ∑ i : Fin N, (ENNReal.ofReal d)⁻¹ *
        ∫⁻ x in meshCell d i, ∫⁻ y in meshCell d i, K (x,y) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [← hvol i] using
        cell_error_le (hf.mono_set (mesh_subset hd.le i))
          (by rw [hvol i]; exact (ENNReal.ofReal_pos.mpr hd).ne')
          (by rw [hvol i]; exact ENNReal.ofReal_ne_top) hq
    _ = (ENNReal.ofReal d)⁻¹ * ∑ i : Fin N,
        ∫⁻ x in meshCell d i, ∫⁻ y in meshCell d i, K (x,y) := (Finset.mul_sum ..).symm
    _ ≤ (ENNReal.ofReal d)⁻¹ * (2 *
        ∫⁻ h in Ioc 0 d, ∫⁻ t in Ioc 0 (N*d-h), K (t,t+h)) := by
      gcongr
      exact cell_pair_integral_le (N*d) d (fun i : Fin N => meshCell d i) hs hdisj
        (mesh_subset hd.le) (fun i => mesh_diameter hd.le i) K hK
        (fun x y => by simp [K,enorm_sub_rev])
        (fun x => by simp [K,ENNReal.zero_rpow_of_pos (lt_of_lt_of_le zero_lt_one hq)])
    _ = _ := by
      simp only [K,enorm_sub_rev]

end D5.S3.Topology.Measures.IntervalLpCompactness
