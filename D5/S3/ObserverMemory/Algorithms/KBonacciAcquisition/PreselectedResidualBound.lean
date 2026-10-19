/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PreselectedResidualBound
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PreselectedResidualBound
   mirror-E: none(waiver:symbolic-probability-and-counting)
   anchors: []
   utility: none
   digest: One preselected hard-two catalog law bounds the residual from the third amplitude. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound

/-- The chain word has exactly t initial true replies. -/
def chainWord (L t : ℕ) : Fin L → Bool := fun i => decide (i.val < t)
/-- The terminal base event shares zero only with the independent pair event. -/
def chainEvent (L t r : ℕ) : Prop :=
  if t = L then r = 0 else if t = 1 then r = 0 ∨ r = 2 else r = t + 1

instance (L t r : ℕ) : Decidable (chainEvent L t r) := by
  unfold chainEvent
  infer_instance

private def rank (Q : Finset ℕ) (t : ℕ) : ℕ := (Q.filter (· < t)).card

private theorem rank_output {L : ℕ} (f : Catalog false L)
    (xs : List ℕ) (low : ∀ i ∈ xs, i < L)
    (factor : ∀ b c, view false xs (lowReply b) = view false xs (lowReply c) →
      f.val b = f.val c) (s t : ℕ) (same : rank xs.toFinset s = rank xs.toFinset t) :
    f.val (chainWord L s) = f.val (chainWord L t) := by
  have sets : xs.toFinset.filter (· < s) = xs.toFinset.filter (· < t) := by
    rcases le_total s t with h | h
    · apply Finset.eq_of_subset_of_card_le
      · intro i hi
        obtain ⟨hi, hs⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr ⟨hi, lt_of_lt_of_le hs h⟩
      · exact same.ge
    · symm
      apply Finset.eq_of_subset_of_card_le
      · intro i hi
        obtain ⟨hi, ht⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr ⟨hi, lt_of_lt_of_le ht h⟩
      · exact same.le
  apply factor
  apply view_congr
  intro i hi
  have hm : i ∈ xs.toFinset := List.mem_toFinset.mpr hi
  have eq : (i < s) ↔ (i < t) := by
    have := Finset.ext_iff.mp sets i
    simpa only [Finset.mem_filter, hm, true_and] using this
  simp only [lowReply, dif_pos (low i hi), chainWord]
  simp only [eq]

private theorem chain_score_le_three (L : ℕ) (f : Catalog false L) :
    (Finset.univ.filter (fun t : Fin (L+1) =>
      chainEvent L t.val (f.val (chainWord L t.val)).val)).card ≤ 3 := by
  classical
  obtain ⟨xs, length, low, _, factor⟩ := f.property
  let Q := xs.toFinset
  have cardQ : Q.card ≤ 2 := (List.toFinset_card_le xs).trans length
  have rank_le (t) : rank Q t ≤ Q.card := Finset.card_filter_le _ _
  have endpoint : rank Q L = Q.card := by
    unfold rank
    congr 1
    exact Finset.filter_eq_self.mpr (fun i hi => low i (List.mem_toFinset.mp hi))
  have rank_one : rank Q 1 ≤ 1 := by
    apply (Finset.card_le_card (show Q.filter (· < 1) ⊆ {0} from ?_)).trans
      (by simp)
    intro i hi
    have := (Finset.mem_filter.mp hi).2
    simp only [Finset.mem_singleton]
    omega
  let S := Finset.univ.filter (fun t : Fin (L+1) =>
    chainEvent L t.val (f.val (chainWord L t.val)).val)
  let slot := fun t : Fin (L+1) => if t.val = L then 2 else rank Q t.val
  have hit (t) (ht : t ∈ S) : chainEvent L t.val (f.val (chainWord L t.val)).val :=
    (Finset.mem_filter.mp ht).2
  have nonterminal (s t : Fin (L+1)) (hs : s.val ≠ L) (ht : t.val ≠ L)
      (hS : s ∈ S) (hT : t ∈ S) (eq : rank Q s.val = rank Q t.val) : s = t := by
    have out := rank_output f xs low factor s.val t.val eq
    have hv := congrArg Fin.val out
    have sh := hit s hS
    have th := hit t hT
    simp only [chainEvent, if_neg hs, if_neg ht] at sh th
    split_ifs at sh th <;> omega
  have no_collision (s : Fin (L+1)) (hs : s.val ≠ L) (hS : s ∈ S)
      (hEnd : (⟨L, by omega⟩ : Fin (L+1)) ∈ S) : rank Q s.val ≠ 2 := by
    intro hr
    have req : rank Q s.val = rank Q L := by
      have h := rank_le s.val
      omega
    have out := rank_output f xs low factor s.val L req
    have eh := hit ⟨L, by omega⟩ hEnd
    have sh := hit s hS
    have hv := congrArg Fin.val out
    simp [chainEvent] at eh
    simp only [chainEvent, if_neg hs] at sh
    have eo : (f.val (chainWord L L)).val = 0 := by
      exact congrArg Fin.val eh
    have sone : s.val = 1 := by split_ifs at sh <;> omega
    rw [sone] at hr
    omega
  have bound := Finset.card_le_card_of_injOn slot (s := S) (t := Finset.range 3)
    (by
      intro t ht
      apply Finset.mem_range.mpr
      dsimp only [slot]
      split_ifs
      · omega
      · have := (rank_le t.val).trans cardQ
        omega)
    (by
      intro s hs t ht heq
      by_cases se : s.val = L <;> by_cases te : t.val = L
      · exact Fin.ext (se.trans te.symm)
      · have endeq : s = ⟨L, by omega⟩ := Fin.ext se
        have hr : rank Q t.val = 2 := by simpa [slot, se, te] using heq.symm
        exact False.elim (no_collision t te ht (endeq ▸ hs) hr)
      · have endeq : t = ⟨L, by omega⟩ := Fin.ext te
        have hr : rank Q s.val = 2 := by simpa [slot, se, te] using heq
        exact False.elim (no_collision s se hs (endeq ▸ ht) hr)
      · apply nonterminal s t se te hs ht
        simpa [slot, se, te] using heq)
  simpa only [Finset.card_range] using bound


/-- First false low reply, with L as the all-positive sentinel. -/
def firstFalse {L : ℕ} (b : Fin L → Bool) : ℕ :=
  Nat.find (show ∃ i, lowReply b i = false from ⟨L, by simp [lowReply]⟩)

/-- The original projected selected target on every low word. -/
def finiteTarget (L : ℕ) (a : ℕ → ℝ) (b : Fin L → Bool) : Measure (Fin (L+1)) :=
  if h : firstFalse b < L then
    ENNReal.ofReal (1-a (firstFalse b)) • Measure.dirac 0 +
    ENNReal.ofReal (a (firstFalse b)) • Measure.dirac ⟨firstFalse b+1, by omega⟩
  else Measure.dirac 0

/-- Zero-based a(k) denotes original a_(k+1); this sum starts at original index 3. -/
def residual (a : ℕ → ℝ) (eps : ℝ) : ℝ := ∑' k : ℕ, max (a (k+2)-eps) 0

private theorem firstFalse_chain (L t : ℕ) (ht : t ≤ L) :
    firstFalse (chainWord L t) = t := by
  apply (Nat.find_eq_iff _).mpr
  constructor
  · by_cases h : t < L <;> simp [lowReply, h, chainWord]
  · intro i hi
    have hL : i < L := lt_of_lt_of_le hi ht
    simp [lowReply, hL, chainWord, hi]

private def eventMass {L : ℕ} (w : PMF (Catalog false L)) (t : ℕ) : ℝ :=
  (w.toMeasure.map (fun f => f.val (chainWord L t))
    {r | chainEvent L t r.val}).toReal

private theorem common_score_bound (L : ℕ)
    (w : PMF (Catalog false L)) : ∑ t : Fin (L+1), eventMass w t.val ≤ 3 := by
  classical
  letI : Fintype (Catalog false L) := Fintype.ofFinite _
  have expansion (t : Fin (L+1)) : eventMass w t.val =
      ∑ f : Catalog false L, (w f).toReal *
        (if chainEvent L t.val (f.val (chainWord L t.val)).val then 1 else 0) := by
    unfold eventMass
    rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
      PMF.toMeasure_apply w (Set.to_countable _).measurableSet, tsum_fintype,
      ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro f _
      by_cases h : chainEvent L t.val (f.val (chainWord L t.val)).val <;>
        simp [Set.indicator, h]
    · intro f _
      by_cases h : chainEvent L t.val (f.val (chainWord L t.val)).val <;>
        simp [Set.indicator, h, w.apply_ne_top]
  have weights : ∑ f : Catalog false L, (w f).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun f _ => w.apply_ne_top f)]
    have hs : (∑ f : Catalog false L, w f) = 1 :=
      (tsum_fintype _).symm.trans w.tsum_coe
    rw [hs]; norm_num
  simp_rw [expansion]
  rw [Finset.sum_comm]
  calc
    ∑ f : Catalog false L, ∑ t : Fin (L+1), (w f).toReal *
        (if chainEvent L t.val (f.val (chainWord L t.val)).val then 1 else 0)
      = ∑ f : Catalog false L, (w f).toReal *
          ((Finset.univ.filter (fun t : Fin (L+1) =>
            chainEvent L t.val (f.val (chainWord L t.val)).val)).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro f _
        rw [← Finset.mul_sum]
        congr 1
        simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ f : Catalog false L, (w f).toReal * 3 := by
      apply Finset.sum_le_sum
      intro f _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      exact_mod_cast chain_score_le_three L f
    _ = 3 := by rw [← Finset.sum_mul, weights]; norm_num

private def lower (L : ℕ) (a : ℕ → ℝ) (eps : ℝ) (t : ℕ) : ℝ :=
  if t = L then 1-eps else if t = 0 then a 0-eps else
    if t = 1 then 1-eps else max (a t-eps) 0

private theorem cap_chain_lower (L : ℕ) (hL : 3 ≤ L) (a : ℕ → ℝ)
    (upper : ∀ i, a i ≤ 1) (eps : ℝ) (heps : 0 ≤ eps)
    (cut : ∀ i, i < L ↔ eps < a i) (w : PMF (Catalog false L))
    (cap : ∀ b, measurableTotalVariation (w.toMeasure.map (fun f => f.val b))
      (finiteTarget L a b) ≤ ENNReal.ofReal eps) (t : Fin (L+1)) :
    lower L a eps t.val ≤ eventMass w t.val := by
  classical
  let b := chainWord L t.val
  let E : Set (Fin (L+1)) := {r | chainEvent L t.val r.val}
  let law := w.toMeasure.map (fun f => f.val b)
  have hlaw : IsProbabilityMeasure law :=
    inferInstance
  have event : (finiteTarget L a b E).toReal ≤ eps + (law E).toReal := by
    have h := (le_iSup (fun E : {E : Set (Fin (L+1)) // MeasurableSet E} =>
      max (law E.1 - finiteTarget L a b E.1) (finiteTarget L a b E.1 - law E.1))
      ⟨E, (Set.to_countable E).measurableSet⟩).trans (cap b)
    have hb := tsub_le_iff_right.mp ((le_max_right _ _).trans h)
    have hc := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, measure_ne_top law E⟩) hb
    simpa only [ENNReal.toReal_add ENNReal.ofReal_ne_top (measure_ne_top law E),
      ENNReal.toReal_ofReal heps] using hc
  have first : firstFalse b = t.val := firstFalse_chain L t.val (by omega)
  change lower L a eps t.val ≤ (law E).toReal
  by_cases endpt : t.val = L
  · have value : finiteTarget L a b E = 1 := by
      simp [finiteTarget, first, endpt, E, chainEvent]
    rw [value] at event
    simp only [lower, if_pos endpt]
    norm_num at event
    linarith
  · have ht : t.val < L := by omega
    have pos : 0 ≤ a t.val := heps.trans (le_of_lt ((cut t.val).mp ht))
    have weights : ENNReal.ofReal (1-a t.val) + ENNReal.ofReal (a t.val) = 1 := by
      rw [← ENNReal.ofReal_add (sub_nonneg.mpr (upper t.val)) pos]
      simp
    by_cases zero : t.val = 0
    · have value : finiteTarget L a b E = ENNReal.ofReal (a 0) := by
        simp [finiteTarget, first, zero, E, chainEvent, show 0 < L by omega,
          show 0 ≠ L by omega]
      rw [value, ENNReal.toReal_ofReal (zero ▸ pos)] at event
      simp only [lower, if_neg endpt, if_pos zero]
      linarith
    · by_cases one : t.val = 1
      · have value : finiteTarget L a b E = 1 := by
          simpa [finiteTarget, first, one, E, chainEvent, show 1 < L by omega,
            show 1 ≠ L by omega]
            using weights
        rw [value] at event
        simp only [lower, if_neg endpt, if_neg zero, if_pos one]
        norm_num at event
        linarith
      · have value : finiteTarget L a b E = ENNReal.ofReal (a t.val) := by
          simp [finiteTarget, first, ht, E, chainEvent, endpt, one]
        rw [value, ENNReal.toReal_ofReal pos] at event
        have active : 0 ≤ a t.val-eps := sub_nonneg.mpr (le_of_lt ((cut t.val).mp ht))
        simp only [lower, if_neg endpt, if_neg zero, if_neg one, max_eq_left active]
        linarith

private theorem residual_finite (L : ℕ) (a : ℕ → ℝ) (eps : ℝ)
    (cut : ∀ i, i < L ↔ eps < a i) :
    residual a eps = ∑ k ∈ Finset.range (L-2), max (a (k+2)-eps) 0 := by
  apply tsum_eq_sum
  intro k hk
  have h : L ≤ k+2 := by have := Finset.mem_range.not.mp hk; omega
  have inactive : a (k+2) ≤ eps := le_of_not_gt (fun ha =>
    (Nat.not_lt_of_ge h) ((cut (k+2)).mpr ha))
  exact max_eq_right (sub_nonpos.mpr inactive)

private theorem lower_sum (L : ℕ) (hL : 3 ≤ L) (a : ℕ → ℝ) (eps : ℝ) :
    (∑ t : Fin (L+1), lower L a eps t.val) =
      a 0 + 2 - 3*eps + ∑ k ∈ Finset.range (L-2), max (a (k+2)-eps) 0 := by
  rw [Fin.sum_univ_eq_sum_range, Finset.sum_range_succ]
  have split : 2 + (L-2) = L := by omega
  have hs := Finset.sum_range_add (lower L a eps) 2 (L-2)
  rw [split] at hs
  rw [hs]
  have init : (∑ t ∈ Finset.range 2, lower L a eps t) = a 0 + 1 - 2*eps := by
    simp [Finset.sum_range_succ, lower, show 0 ≠ L by omega, show 1 ≠ L by omega]
    ring
  have rest : (∑ k ∈ Finset.range (L-2), lower L a eps (2+k)) =
      ∑ k ∈ Finset.range (L-2), max (a (k+2)-eps) 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    have := Finset.mem_range.mp hk
    rw [Nat.add_comm 2 k]
    simp only [lower, if_neg (show k+2 ≠ L by omega), if_neg (show k+2 ≠ 0 by omega),
      if_neg (show k+2 ≠ 1 by omega)]
  rw [init, rest]
  have endlower : lower L a eps L = 1-eps := by
    unfold lower
    rw [if_pos rfl]
  rw [endlower]
  ring

/-- The all-word closed cap under one actual preselected law bounds the entire residual. -/
theorem preselected_residual_bound (L : ℕ) (a : ℕ → ℝ)
    (upper : ∀ i, a i ≤ 1) (eps : ℝ) (heps : 0 ≤ eps)
    (cut : ∀ i, i < L ↔ eps < a i) (w : PMF (Catalog false L))
    (cap : ∀ b, measurableTotalVariation (w.toMeasure.map (fun f => f.val b))
      (finiteTarget L a b) ≤ ENNReal.ofReal eps) :
    residual a eps ≤ 3*eps + 1-a 0 := by
  by_cases hL : 3 ≤ L
  · have lowerBound := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) =>
      cap_chain_lower L hL a upper eps heps cut w cap t)
    have score := common_score_bound L w
    rw [lower_sum L hL a eps, ← residual_finite L a eps cut] at lowerBound
    linarith
  · have finite := residual_finite L a eps cut
    have small : L-2 = 0 := by omega
    rw [small, Finset.range_zero, Finset.sum_empty] at finite
    rw [finite]
    have := upper 0
    linarith

#print axioms preselected_residual_bound

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound
