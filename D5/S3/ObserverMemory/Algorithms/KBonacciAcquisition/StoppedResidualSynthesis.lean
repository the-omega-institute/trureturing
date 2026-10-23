/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedResidualSynthesis
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedResidualSynthesis
   mirror-E: none(waiver:symbolic-execution-and-measure)
   anchors: []
   utility: none
   digest: One chronological stopped table law synthesizes arbitrary residual amplitudes. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedCoefficientRealization
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Classical ENNReal
open MeasureTheory
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedCoefficientRealization
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedResidualSynthesis

/-- Numerical addresses 0,...,m-1 followed by the base sentinel m. -/
abbrev triples (m : ℕ) : Finset (Finset ℕ) := (Finset.range (m+1)).powersetCard 3

private def uniformSubset (s : Finset (Finset ℕ)) (hs : s.Nonempty) :
    PMF (Finset ℕ) :=
  PMF.ofFinset (fun a => if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0) s (by
    have hsum : (∑ a ∈ s, if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0) =
        ∑ _a ∈ s, (s.card : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [ha]
    rw [hsum, Finset.sum_const, nsmul_eq_mul]
    have hcard : s.card ≠ 0 := Nat.ne_of_gt (Finset.card_pos.mpr hs)
    exact ENNReal.mul_inv_cancel (by exact_mod_cast hcard)
      (ENNReal.natCast_ne_top _)) (by
    intro a ha
    simp [ha])

private def baseTable (L : ℕ) : Catalog true L :=
  ⟨fun _ => 0, [], by simp, by simp, by simp, by simp⟩

/-- The two least selected labels are queried; the largest is a terminal output. -/
def subsetTable (L m : ℕ) (hmL : m ≤ L) (s : Finset ℕ) : Catalog true L := by
  classical
  by_cases hs : s ∈ triples m
  · have hc : s.card = 3 := (Finset.mem_powersetCard.mp hs).2
    let e := s.orderEmbOfFin hc
    have inc : StrictMono e := e.strictMono
    have e02 := inc (show (0 : Fin 3) < 2 by decide)
    have e12 := inc (show (1 : Fin 3) < 2 by decide)
    have e2 : e 2 < m+1 := Finset.mem_range.mp
      ((Finset.mem_powersetCard.mp hs).1 (s.orderEmbOfFin_mem hc 2))
    let i : Fin L := ⟨e 0, by omega⟩
    let j : Fin L := ⟨e 1, by omega⟩
    let out : ℕ → Fin (L+1) := fun k => if h : k < m then ⟨k+1,by omega⟩ else 0
    exact table (.inr (.inr ⟨(i,j), inc (by decide)⟩)) (out (e 0),out (e 1),out (e 2))
  · exact baseTable L

private theorem subset_eval {L m : ℕ} (hmL : m ≤ L) {s : Finset ℕ}
    (hs : s ∈ triples m) (b : Fin L → Bool) :
    (subsetTable L m hmL s).val b =
      let e := s.orderEmbOfFin (Finset.mem_powersetCard.mp hs).2
      let out := fun k : ℕ => if h : k < m then (⟨k+1,by omega⟩ : Fin (L+1)) else 0
      if lowReply b (e 0) then
        (if lowReply b (e 1) then out (e 2) else out (e 1)) else out (e 0) := by
  have h0 := (s.orderEmbOfFin (Finset.mem_powersetCard.mp hs).2).strictMono
    (show (0 : Fin 3) < 2 by decide)
  have h1 := (s.orderEmbOfFin (Finset.mem_powersetCard.mp hs).2).strictMono
    (show (1 : Fin 3) < 2 by decide)
  have h2 := Finset.mem_range.mp ((Finset.mem_powersetCard.mp hs).1
    (s.orderEmbOfFin_mem (Finset.mem_powersetCard.mp hs).2 2))
  have h0L : s.orderEmbOfFin (Finset.mem_powersetCard.mp hs).2 (0 : Fin 3) < L := by omega
  have h1L : s.orderEmbOfFin (Finset.mem_powersetCard.mp hs).2 (1 : Fin 3) < L := by omega
  cases hb0 : lowReply b (s.orderEmbOfFin (Finset.mem_powersetCard.mp hs).2 (0 : Fin 3)) <;>
    cases hb1 : lowReply b (s.orderEmbOfFin (Finset.mem_powersetCard.mp hs).2 (1 : Fin 3)) <;>
    simp_all [subsetTable,table,label,cell,lowReply]


/-- The first absent coordinate is emitted exactly when it was selected, even
when it is the unqueried third label and later coordinates are also absent. -/
private theorem chronological_inclusion {L m : ℕ} (hmL : m ≤ L) {s : Finset ℕ}
    (hs : s ∈ triples m) (b : Fin L → Bool) (n : ℕ) (hn : n < m)
    (hz : lowReply b n = false) (hp : ∀ i < n, lowReply b i = true) :
    (subsetTable L m hmL s).val b = ⟨n+1,by omega⟩ ↔ n ∈ s := by
  let e := s.orderEmbOfFin (Finset.mem_powersetCard.mp hs).2
  have inc := e.strictMono
  have e01 := inc (show (0 : Fin 3) < 1 by decide)
  have e12 := inc (show (1 : Fin 3) < 2 by decide)
  have hmem : n ∈ s ↔ ∃ k : Fin 3, e k = n := by
    exact Iff.symm (Set.ext_iff.mp (s.range_orderEmbOfFin (Finset.mem_powersetCard.mp hs).2) n)
  have out_eq (k : ℕ) :
      (if h : k < m then (⟨k+1,by omega⟩ : Fin (L+1)) else 0) =
        ⟨n+1,by omega⟩ ↔ k = n := by
    split_ifs with h
    · simp only [Fin.mk.injEq]; omega
    · simp only [Fin.ext_iff,Fin.val_zero]; omega
  rw [subset_eval hmL hs]
  change (if lowReply b (e 0) then
    (if lowReply b (e 1) then (if h : e 2 < m then (⟨e 2+1,by omega⟩ : Fin (L+1)) else 0)
      else (if h : e 1 < m then (⟨e 1+1,by omega⟩ : Fin (L+1)) else 0))
    else (if h : e 0 < m then (⟨e 0+1,by omega⟩ : Fin (L+1)) else 0)) = _ ↔ _
  constructor
  · intro h
    apply hmem.mpr
    by_cases h0 : lowReply b (e 0) = true
    · rw [if_pos h0] at h
      by_cases h1 : lowReply b (e 1) = true
      · rw [if_pos h1] at h
        exact ⟨2,(out_eq _).mp h⟩
      · rw [if_neg h1] at h
        exact ⟨1,(out_eq _).mp h⟩
    · rw [if_neg h0] at h
      exact ⟨0,(out_eq _).mp h⟩
  · intro h
    obtain ⟨k,hk⟩ := hmem.mp h
    fin_cases k
    · change e 0 = n at hk
      simp [hk,hz,hn]
    · change e 1 = n at hk
      have h0 : lowReply b (e 0) = true := hp _ (by omega)
      simp [h0,hk,hz,hn]
    · change e 2 = n at hk
      have h0 : lowReply b (e 0) = true := hp _ (by omega)
      have h1 : lowReply b (e 1) = true := hp _ (by omega)
      simp [h0,h1,hk,hn]

private theorem chronological_base {L m : ℕ} (hmL : m ≤ L) {s : Finset ℕ}
    (hs : s ∈ triples m) (b : Fin L → Bool) :
    (subsetTable L m hmL s).val b = 0 ↔
      m ∈ s ∧ ∀ i ∈ s, i < m → lowReply b i = true := by
  let e := s.orderEmbOfFin (Finset.mem_powersetCard.mp hs).2
  have inc := e.strictMono
  have e01 := inc (show (0 : Fin 3) < 1 by decide)
  have e12 := inc (show (1 : Fin 3) < 2 by decide)
  have e2 : e 2 ≤ m := by
    have := Finset.mem_range.mp ((Finset.mem_powersetCard.mp hs).1
      (s.orderEmbOfFin_mem (Finset.mem_powersetCard.mp hs).2 2))
    change e 2 < m+1 at this
    omega
  have hmem (n) : n ∈ s ↔ ∃ k : Fin 3, e k = n := by
    exact Iff.symm (Set.ext_iff.mp (s.range_orderEmbOfFin (Finset.mem_powersetCard.mp hs).2) n)
  rw [subset_eval hmL hs]
  change (if lowReply b (e 0) then
    (if lowReply b (e 1) then (if h : e 2 < m then (⟨e 2+1,by omega⟩ : Fin (L+1)) else 0)
      else (if h : e 1 < m then (⟨e 1+1,by omega⟩ : Fin (L+1)) else 0))
    else (if h : e 0 < m then (⟨e 0+1,by omega⟩ : Fin (L+1)) else 0)) = 0 ↔ _
  have out0 (k) : (if h : k < m then (⟨k+1,by omega⟩ : Fin (L+1)) else 0) = 0 ↔ m ≤ k := by
    split_ifs with h <;> simp [Fin.ext_iff] <;> omega
  constructor
  · intro h
    have h0 : lowReply b (e 0) = true := by
      by_contra hn; simp [hn,out0,show e 0 < m by omega] at h
    have h1 : lowReply b (e 1) = true := by
      by_contra hn; simp [h0,hn,out0,show e 1 < m by omega] at h
    have he : e 2 = m := by
      have := (out0 _).mp (by simpa [h0,h1] using h)
      omega
    refine ⟨(hmem _).mpr ⟨2,he⟩,?_⟩
    intro i hi him
    obtain ⟨k,rfl⟩ := (hmem _).mp hi
    fin_cases k <;> dsimp only [Fin.reduceFinMk] at *
    · exact h0
    · exact h1
    · omega
  · rintro ⟨hm,hp⟩
    have he : e 2 = m := by
      obtain ⟨k,hk⟩ := (hmem _).mp hm
      fin_cases k <;> dsimp at hk <;> omega
    have h0 : lowReply b (e 0) = true := hp _ (s.orderEmbOfFin_mem (Finset.mem_powersetCard.mp hs).2 (0 : Fin 3)) (by omega)
    have h1 : lowReply b (e 1) = true := hp _ (s.orderEmbOfFin_mem (Finset.mem_powersetCard.mp hs).2 (1 : Fin 3)) (by omega)
    simp [h0,h1,out0,he]

private theorem chronological_support {L m : ℕ} (hmL : m ≤ L) {s : Finset ℕ}
    (hs : s ∈ triples m) (b : Fin L → Bool) :
    (subsetTable L m hmL s).val b = 0 ∨ ((subsetTable L m hmL s).val b).val ≤ m := by
  rw [subset_eval hmL hs]
  dsimp
  split_ifs <;> simp_all [Fin.le_iff_val_le_val] <;> omega

#print axioms chronological_inclusion
#print axioms chronological_base
/-- A single source-independent draw chooses an actual entire stopped table. -/
def subsetLaw (L m : ℕ) (hmL : m ≤ L) (hm : 3 ≤ m) : PMF (Catalog true L) :=
  (uniformSubset (triples m)
    (Finset.powersetCard_nonempty.mpr (by simpa using (show 3 ≤ m+1 by omega)))).map
      (subsetTable L m hmL)

private theorem subset_mass {L m : ℕ} (hmL : m ≤ L) (hm : 3 ≤ m)
    (b : Fin L → Bool) (r : Fin (L+1)) :
    ((subsetLaw L m hmL hm).map (fun f => f.val b) r).toReal =
      (((triples m).filter (fun s => (subsetTable L m hmL s).val b = r)).card : ℝ) /
        (Nat.choose (m+1) 3 : ℝ) := by
  have he : ((subsetLaw L m hmL hm).map (fun f => f.val b)) r =
      (((triples m).filter (fun s => (subsetTable L m hmL s).val b = r)).card : ENNReal) /
        ((triples m).card : ENNReal) := by
    rw [subsetLaw,PMF.map_comp,PMF.map_apply]
    rw [tsum_eq_sum (s := triples m) (fun s hs => by
      simp only [uniformSubset, PMF.ofFinset_apply, hs, if_false]
      simp)]
    simp only [Function.comp_apply]
    calc
      _ = ∑ s ∈ triples m, if (subsetTable L m hmL s).val b = r then
          ((triples m).card : ENNReal)⁻¹ else 0 := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [uniformSubset, PMF.ofFinset_apply]
        simp only [hs, if_true, eq_comm]
      _ = _ := by
        rw [← Finset.sum_filter]
        simp [div_eq_mul_inv]
  rw [he,ENNReal.toReal_div]
  simp [triples]

def positives {L : ℕ} (m : ℕ) (b : Fin L → Bool) : Finset ℕ :=
  (Finset.range m).filter (fun i => lowReply b i = true)

private theorem base_filter {L m : ℕ} (hmL : m ≤ L) (b : Fin L → Bool) :
    (triples m).filter (fun s => (subsetTable L m hmL s).val b = 0) =
      ((insert m (positives m b)).powersetCard 3).filter (fun s => {m} ⊆ s) := by
  ext s
  simp only [Finset.mem_filter,Finset.mem_powersetCard,Finset.singleton_subset_iff]
  constructor
  · rintro ⟨hs,hb⟩
    have hs' : s ∈ triples m := Finset.mem_powersetCard.mpr hs
    obtain ⟨hm,hp⟩ := (chronological_base hmL hs' b).mp hb
    refine ⟨⟨?_,(Finset.mem_powersetCard.mp hs').2⟩,hm⟩
    intro i hi
    by_cases him : i = m
    · simp [him]
    · have bound := Finset.mem_range.mp ((Finset.mem_powersetCard.mp hs').1 hi)
      have ilt : i < m := by omega
      simp [positives,him,ilt,hp i hi ilt]
  · rintro ⟨⟨hs,hcard⟩,hm⟩
    have hs' : s ∈ triples m := by
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_,hcard⟩
      intro i hi
      rcases Finset.mem_insert.mp (hs hi) with rfl | hi
      · simp
      · have ilt := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
        exact Finset.mem_range.mpr (by omega)
    refine ⟨Finset.mem_powersetCard.mp hs',(chronological_base hmL hs' b).mpr ⟨hm,?_⟩⟩
    intro i hi him
    have hne : i ≠ m := by omega
    exact (Finset.mem_filter.mp ((Finset.mem_insert.mp (hs hi)).resolve_left hne)).2

private theorem choose_ratio (m : ℕ) (hm : 3 ≤ m) :
    (Nat.choose m 2 : ℝ) / (Nat.choose (m+1) 3 : ℝ) = 3/(m+1:ℝ) := by
  have hc := Nat.add_one_mul_choose_eq m 2
  have hcp : (0 : ℝ) < Nat.choose (m+1) 3 := by
    exact_mod_cast Nat.choose_pos (by omega : 3 ≤ m+1)
  have hcr : (m+1 : ℝ) * Nat.choose m 2 = (Nat.choose (m+1) 3 : ℝ)*3 := by
    exact_mod_cast hc
  apply (div_eq_div_iff (ne_of_gt hcp) (by positivity : (m+1 : ℝ) ≠ 0)).mpr
  nlinarith

/-- Simultaneous first-zero inclusion, base probability and output support under
one law on whole chronological tables. -/
theorem stopped_subset_law (L m : ℕ) (hmL : m ≤ L) (hm : 3 ≤ m) :
    let w := subsetLaw L m hmL hm
    ∀ b : Fin L → Bool,
      (∀ n (hn : n < m), lowReply b n = false →
        (∀ i < n, lowReply b i = true) →
        (w.map (fun f => f.val b) ⟨n+1,by omega⟩).toReal = 3 / (m+1 : ℝ)) ∧
      (w.map (fun f => f.val b) 0).toReal =
        (Nat.choose (positives m b).card 2 : ℝ) / (Nat.choose (m+1) 3 : ℝ) ∧
      (∀ r : Fin (L+1), m < r.val → w.map (fun f => f.val b) r = 0) ∧
      ((∀ i < m, lowReply b i = true) →
        (w.map (fun f => f.val b) 0).toReal = 3/(m+1:ℝ)) := by
  dsimp only
  intro b
  refine ⟨?_,?_,?_,?_⟩
  · intro n hn hz hp
    rw [subset_mass]
    have filters : (triples m).filter (fun s =>
        (subsetTable L m hmL s).val b = ⟨n+1,by omega⟩) =
        (triples m).filter (fun s => {n} ⊆ s) := by
      apply Finset.filter_congr
      intro s hs
      simpa only [Finset.singleton_subset_iff] using chronological_inclusion hmL hs b n hn hz hp
    rw [filters]
    unfold triples
    rw [Finset.card_filter_powersetCard_subset]
    · simp only [Finset.card_range,Finset.card_singleton,Nat.add_sub_cancel,Nat.reduceSub]
      exact choose_ratio m hm
    · simp [Finset.singleton_subset_iff,Finset.mem_range]; omega
    · simp
  · rw [subset_mass,base_filter,Finset.card_filter_powersetCard_subset]
    · have hn : m ∉ positives m b := by simp [positives]
      simp [Finset.card_insert_of_notMem hn]
    · simp
    · simp
  · intro r hr
    have hfilter : (triples m).filter (fun s => (subsetTable L m hmL s).val b = r) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro s hs he
      have bound := chronological_support hmL hs b
      rw [he] at bound
      rcases bound with h | h
      · have rz : r.val = 0 := congrArg (fun x : Fin (L+1) => x.val) h
        omega
      · omega
    have hz : ((subsetLaw L m hmL hm).map (fun f => f.val b) r).toReal = 0 := by
      rw [subset_mass,hfilter]; simp
    exact (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right (PMF.apply_ne_top _ _)

  · intro hp
    rw [subset_mass,base_filter,Finset.card_filter_powersetCard_subset]
    · have hpos : positives m b = Finset.range m := by
        ext i
        simp only [positives,Finset.mem_filter,Finset.mem_range]
        exact ⟨And.left,fun hi => ⟨hi,hp i hi⟩⟩
      rw [hpos,Finset.card_insert_of_notMem (by simp),Finset.card_range]
      simp only [Finset.card_singleton,Nat.add_sub_cancel,Nat.reduceSub]
      exact choose_ratio m hm
    · simp
    · simp

#print axioms stopped_subset_law

open private residual_finite from
  D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound

/-- Truncated residual demand, with zero value at the strict cutoff. -/
def demand (a : ℕ → ℝ) (eps : ℝ) (k : ℕ) : ℝ := max (a (k+2)-eps) 0

/-- Prefix-uniform component indexed by original length k+3. -/
def weight (a : ℕ → ℝ) (eps : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ)+4)/3 * (demand a eps k-demand a eps (k+1))

private theorem weight_mass (a : ℕ → ℝ) (eps : ℝ) (N : ℕ)
    (hend : demand a eps N = 0) :
    (∑ k ∈ Finset.range N, weight a eps k) =
      demand a eps 0 + (∑ k ∈ Finset.range N, demand a eps k)/3 := by
  let d := demand a eps
  have hterm (k : ℕ) : weight a eps k = d k/3 +
      (((k : ℝ)+3)*d k-((k+1 : ℕ):ℝ)*d (k+1)-3*d (k+1))/3 := by
    simp [weight,d] <;> ring
  have hterm' (k : ℕ) : weight a eps k = d k/3 +
      (((k : ℝ)+3)*d k-(((k+1 : ℕ):ℝ)+3)*d (k+1))/3 := by
    rw [hterm]; push_cast <;> ring
  simp_rw [hterm']
  rw [Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_div,Finset.sum_range_sub']
  simp [d,hend]
  all_goals ring

private theorem weight_tail (a : ℕ → ℝ) (eps : ℝ) (N n : ℕ) (hn : n ≤ N)
    (hend : demand a eps N = 0) :
    (∑ k ∈ Finset.Ico n N, weight a eps k * (3 / ((k:ℝ)+4))) = demand a eps n := by
  have hterm (k : ℕ) : weight a eps k * (3 / ((k:ℝ)+4)) =
      demand a eps k-demand a eps (k+1) := by
    dsimp [weight]
    field_simp
  simp_rw [hterm]
  have h := Finset.sum_Ico_sub (fun k => -demand a eps k) hn
  simpa only [neg_sub_neg,hend,sub_zero] using h

private def prefixTable (L : ℕ) (hL : 3 ≤ L) (j : Fin 3) : Catalog true L :=
  table (.inr (.inr ⟨(⟨0,by omega⟩,⟨1,by omega⟩),by change (0:ℕ) < 1; omega⟩))
    (if j = 2 then 0 else 1, if j = 0 then 2 else 0, 0)

/-- The closed residual condition produces one common stopped law. The returned
identities retain all low words and the exact all-positive base probability. -/
theorem stopped_residual_synthesis (L : ℕ) (hL : 3 ≤ L)
    (a : ℕ → ℝ) (ha : Antitone a) (bound : a 0 ≤ 1)
    (eps : ℝ) (heps : 0 < eps) (cut : ∀ i, i < L ↔ eps < a i)
    (cap : residual a eps ≤ 3*eps) :
    ∃ w : PMF (Catalog true L),
      (∀ b : Fin L → Bool, ∀ hn : firstFalse b < L,
        (w.map (fun f => f.val b) ⟨firstFalse b+1,by omega⟩).toReal =
          a (firstFalse b)-eps ∧
        1-residual a eps/3 ≤ (w.map (fun f => f.val b) 0).toReal +
          (w.map (fun f => f.val b) ⟨firstFalse b+1,by omega⟩).toReal) ∧
      (w.map (fun f => f.val (fun _ => true)) 0).toReal = 1-residual a eps/3 := by
  classical
  have fin1 : (⟨1,by omega⟩ : Fin (L+1)) = 1 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (show 1 < L+1 by omega)]
  have fin2 : (⟨2,by omega⟩ : Fin (L+1)) = 2 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (show 2 < L+1 by omega)]
  have fin01 : (0 : Fin (L+1)) ≠ 1 := by
    intro h
    have h' := congrArg (fun z : Fin (L+1) => z.val) (h.trans fin1.symm)
    change (0:ℕ) = 1 at h'
    omega
  have fin02 : (0 : Fin (L+1)) ≠ 2 := by
    intro h
    have h' := congrArg (fun z : Fin (L+1) => z.val) (h.trans fin2.symm)
    change (0:ℕ) = 2 at h'
    omega
  let N := L-2
  let d := demand a eps
  have endzero : d N = 0 := by
    dsimp [d,demand,N]
    apply max_eq_right
    have h : L-2+2 = L := by omega
    rw [h]
    exact sub_nonpos.mpr (le_of_not_gt (fun ht => (Nat.lt_irrefl L) ((cut L).mpr ht)))
  have D : residual a eps = ∑ k ∈ Finset.range N, d k := residual_finite L a eps cut
  have d0 : d 0 = a 2-eps := max_eq_left (by
    have := ((cut 2).mp (by omega : 2 < L)).le
    dsimp [d,demand]; simp; linarith)
  have mono : Antitone d := by
    intro i j hij
    exact max_le_max (sub_le_sub_right (ha (by omega : i+2 ≤ j+2)) eps) le_rfl
  have wn (k : Fin N) : 0 ≤ weight a eps k :=
    mul_nonneg (by positivity) (sub_nonneg.mpr (mono (by omega)))
  let W := ∑ k : Fin N, weight a eps k
  have Wvalue : W = a 2-eps+residual a eps/3 := by
    dsimp [W]
    rw [Fin.sum_univ_eq_sum_range,weight_mass a eps N endzero,← D]
    change d 0+_ = _
    rw [d0]
  have Wle : W ≤ a 2 := by rw [Wvalue]; linarith
  have Wn : 0 ≤ W := Finset.sum_nonneg (fun k _ => wn k)
  let R := 1-W
  let t0 := a 0-a 2
  let t1 := a 1-a 2
  have ht1 : 0 ≤ t1 := sub_nonneg.mpr (ha (by decide : 1 ≤ 2))
  have ht01 : t1 ≤ t0 := sub_le_sub_right (ha (by decide : 0 ≤ 1)) _
  have hRt : t0 ≤ R := by dsimp [t0,R]; linarith
  let branchMass : Fin 3 ⊕ Fin N → ℝ := fun j => match j with
    | .inl j => if j = 0 then t1 else if j = 1 then t0-t1 else R-t0
    | .inr k => weight a eps k
  have bn (j) : 0 ≤ branchMass j := by
    cases j with
    | inl j => fin_cases j <;> simp [branchMass] <;> linarith
    | inr k => exact wn k
  have bt : (∑ j, branchMass j) = 1 := by
    simp [branchMass,Fintype.sum_sum_type,Fin.sum_univ_three,W,R]
    all_goals ring
  let branchPMF := PMF.ofFintype (fun j => ENNReal.ofReal (branchMass j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => bn j),bt]; simp)
  have kmL (k : Fin N) : k.val+3 ≤ L := by
    have := k.isLt
    dsimp [N] at *
    omega
  let choices : Fin 3 ⊕ Fin N → PMF (Catalog true L) := fun j => match j with
    | .inl j => PMF.pure (prefixTable L hL j)
    | .inr k => subsetLaw L (k.val+3) (kmL k) (by omega)
  let w := branchPMF.bind choices
  have rows (b : Fin L → Bool) (r : Fin (L+1)) :
      (w.map (fun f => f.val b) r).toReal =
      ∑ j, branchMass j * ((choices j).map (fun f => f.val b) r).toReal := by
    rw [show w = branchPMF.bind choices from rfl,PMF.map_bind,PMF.bind_apply,tsum_fintype,
      ENNReal.toReal_sum (fun j _ => ENNReal.mul_ne_top (branchPMF.apply_ne_top j)
        ((choices j).map _ |>.apply_ne_top r))]
    apply Finset.sum_congr rfl
    intro j _
    rw [ENNReal.toReal_mul]
    simp [branchPMF,ENNReal.toReal_ofReal (bn j)]
  have inclusion (k : Fin N) (b : Fin L → Bool) (n : ℕ) (hn : n < k.val+3)
      (hz : lowReply b n = false) (hp : ∀ i < n, lowReply b i = true) :
      ((choices (.inr k)).map (fun f => f.val b) ⟨n+1,by have := k.isLt; dsimp [N] at *; omega⟩).toReal =
        3 / ((k:ℝ)+4) := by
    simpa only [choices,Nat.cast_add,Nat.cast_ofNat,add_assoc,show (3:ℝ)+1=4 by norm_num] using
      (stopped_subset_law L (k.val+3) (kmL k) (by omega) b).1 n hn hz hp
  refine ⟨w,?_,?_⟩
  · intro b hn
    let n := firstFalse b
    have hnL : n < L := hn
    have hz : lowReply b n = false := by
      change lowReply b (firstFalse b) = false
      unfold firstFalse
      exact Nat.find_spec (show ∃ i, lowReply b i = false from ⟨L,by simp [lowReply]⟩)
    have hp : ∀ i < n, lowReply b i = true := by
      intro i hi
      exact Bool.eq_true_of_not_eq_false (Nat.find_min _ hi)
    let pref (r : Fin (L+1)) := ∑ j : Fin 3,
      branchMass (.inl j) * ((choices (.inl j)).map (fun f => f.val b) r).toReal
    have row (r) : (w.map (fun f => f.val b) r).toReal = pref r +
        ∑ k : Fin N, weight a eps k * ((choices (.inr k)).map (fun f => f.val b) r).toReal := by
      rw [rows,Fintype.sum_sum_type]
    let r : Fin (L+1) := ⟨n+1,by omega⟩
    have pn : pref r = if n = 0 then t0 else if n = 1 then t1 else 0 := by
      by_cases h0 : n = 0
      · have hb0 : b ⟨0,by omega⟩ = false := by simpa [h0,lowReply,show 0 < L by omega] using hz
        simp [pref,branchMass,choices,PMF.pure_map,Fin.sum_univ_three,prefixTable,table,label,cell,fin1,fin2,fin01,fin02,Ne.symm fin01,Ne.symm fin02,show L ≠ 0 by omega,hb0,r,h0]
        all_goals ring
      · by_cases h1 : n = 1
        · have hb0 : b ⟨0,by omega⟩ = true := by simpa [lowReply,show 0 < L by omega] using hp 0 (by omega)
          have hb1 : b ⟨1,by omega⟩ = false := by simpa [h1,lowReply,show 1 < L by omega] using hz
          simp [pref,branchMass,choices,PMF.pure_map,Fin.sum_univ_three,prefixTable,table,label,cell,fin1,fin2,fin01,fin02,Ne.symm fin01,Ne.symm fin02,show L ≠ 0 by omega,hb0,hb1,r,h1]
        · have hb0 : b ⟨0,by omega⟩ = true := by simpa [lowReply,show 0 < L by omega] using hp 0 (by omega)
          have hb1 : b ⟨1,by omega⟩ = true := by simpa [lowReply,show 1 < L by omega] using hp 1 (by omega)
          have hr : r ≠ 0 := by intro h; have := congrArg Fin.val h; dsimp [r] at this; omega
          simp [pref,branchMass,choices,PMF.pure_map,Fin.sum_univ_three,prefixTable,table,label,cell,fin1,fin2,fin01,fin02,Ne.symm fin01,Ne.symm fin02,show L ≠ 0 by omega,hb0,hb1,hr,h0,h1]
    have ppair : pref 0 + pref r = R := by
      by_cases h0 : n = 0
      · have hb0 : b ⟨0,by omega⟩ = false := by simpa [h0,lowReply,show 0 < L by omega] using hz
        rw [pn]
        simp [pref,branchMass,choices,PMF.pure_map,Fin.sum_univ_three,prefixTable,table,label,cell,fin1,fin2,fin01,fin02,Ne.symm fin01,Ne.symm fin02,show L ≠ 0 by omega,hb0,h0]
        all_goals ring
      · by_cases h1 : n = 1
        · have hb0 : b ⟨0,by omega⟩ = true := by simpa [lowReply,show 0 < L by omega] using hp 0 (by omega)
          have hb1 : b ⟨1,by omega⟩ = false := by simpa [h1,lowReply,show 1 < L by omega] using hz
          rw [pn]
          simp [pref,branchMass,choices,PMF.pure_map,Fin.sum_univ_three,prefixTable,table,label,cell,fin1,fin2,fin01,fin02,Ne.symm fin01,Ne.symm fin02,show L ≠ 0 by omega,hb0,hb1,h0,h1]
          all_goals ring
        · have hb0 : b ⟨0,by omega⟩ = true := by simpa [lowReply,show 0 < L by omega] using hp 0 (by omega)
          have hb1 : b ⟨1,by omega⟩ = true := by simpa [lowReply,show 1 < L by omega] using hp 1 (by omega)
          rw [pn]
          simp [pref,branchMass,choices,PMF.pure_map,Fin.sum_univ_three,prefixTable,table,label,cell,fin1,fin2,fin01,fin02,Ne.symm fin01,Ne.symm fin02,show L ≠ 0 by omega,hb0,hb1,h0,h1]
          all_goals ring
    have pkn (k : Fin N) :
        ((choices (.inr k)).map (fun f => f.val b) r).toReal =
          if n < k.val+3 then 3/((k:ℝ)+4) else 0 := by
      by_cases hkn : n < k.val+3
      · exact (inclusion k b n hkn hz hp).trans (if_pos hkn).symm
      · have support := (stopped_subset_law L (k.val+3) (kmL k) (by omega) b).2.2.1 r (by dsimp [r]; omega)
        simp only [choices,support,ENNReal.toReal_zero,if_neg hkn]
    have telesc : (∑ k : Fin N, weight a eps k * (if n < k.val+3 then 3/((k:ℝ)+4) else 0)) = d (n-2) := by
      simp_rw [mul_ite,mul_zero]
      rw [Fin.sum_univ_eq_sum_range (fun k => if n < k+3 then weight a eps k * (3/((k:ℝ)+4)) else 0) N,← Finset.sum_filter]
      have filter : (Finset.range N).filter (fun k => n < k+3) = Finset.Ico (n-2) N := by
        ext k; simp; omega
      rw [filter,weight_tail a eps N (n-2) (by dsimp [N]; omega) endzero]
    have active : (w.map (fun f => f.val b) r).toReal = a n-eps := by
      rw [row,pn]
      simp_rw [pkn]
      rw [telesc]
      by_cases h0 : n = 0
      · simp [h0,t0,d0] <;> ring
      · by_cases h1 : n = 1
        · simp [h0,h1,t1,d0] <;> ring
        · have hn2 : n-2+2 = n := by omega
          have han : 0 ≤ a n-eps := sub_nonneg.mpr ((cut n).mp hnL).le
          simp [h0,h1,d,demand,hn2,max_eq_left han]
    have pairk (k : Fin N) : 3/((k:ℝ)+4) ≤
        ((choices (.inr k)).map (fun f => f.val b) 0).toReal +
        ((choices (.inr k)).map (fun f => f.val b) r).toReal := by
      by_cases hkn : n < k.val+3
      · rw [inclusion k b n hkn hz hp]
        exact le_add_of_nonneg_left ENNReal.toReal_nonneg
      · have hpos : ∀ i < k.val+3, lowReply b i = true := fun i hi => hp i (by omega)
        have base := (stopped_subset_law L (k.val+3) (kmL k) (by omega) b).2.2.2 hpos
        have base' : ((choices (.inr k)).map (fun f => f.val b) 0).toReal = 3/((k:ℝ)+4) := by
          simpa only [choices,Nat.cast_add,Nat.cast_ofNat,add_assoc,show (3:ℝ)+1=4 by norm_num] using base
        rw [base']
        exact le_add_of_nonneg_right ENNReal.toReal_nonneg
    have sumreturn : (∑ k : Fin N, weight a eps k * (3/((k:ℝ)+4))) = d 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun k => weight a eps k * (3/((k:ℝ)+4))) N]
      simpa using weight_tail a eps N 0 (Nat.zero_le _) endzero
    refine ⟨active,?_⟩
    change 1-residual a eps/3 ≤ (w.map (fun f => f.val b) 0).toReal + (w.map (fun f => f.val b) r).toReal
    rw [row,row]
    have regroup : pref 0 + (∑ k : Fin N, weight a eps k * ((choices (.inr k)).map (fun f => f.val b) 0).toReal) +
        (pref r + ∑ k : Fin N, weight a eps k * ((choices (.inr k)).map (fun f => f.val b) r).toReal) =
        R + ∑ k : Fin N, weight a eps k *
          (((choices (.inr k)).map (fun f => f.val b) 0).toReal + ((choices (.inr k)).map (fun f => f.val b) r).toReal) := by
      simp_rw [mul_add,Finset.sum_add_distrib]
      linarith [ppair]
    rw [regroup]
    have lower := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => mul_le_mul_of_nonneg_left (pairk k) (wn k))
    rw [sumreturn,d0] at lower
    dsimp [R]
    rw [Wvalue]
    linarith
  · rw [rows,Fintype.sum_sum_type]
    have pref : (∑ j : Fin 3, branchMass (.inl j) * ((choices (.inl j)).map (fun f => f.val (fun _ => true)) 0).toReal) = R := by
      simp [branchMass,choices,PMF.pure_map,Fin.sum_univ_three,prefixTable,table,label,cell]
      all_goals ring
    rw [pref]
    have base (k : Fin N) : ((choices (.inr k)).map (fun f => f.val (fun _ => true)) 0).toReal = 3/((k:ℝ)+4) := by
      have h := (stopped_subset_law L (k.val+3) (kmL k) (by omega) (fun _ => true)).2.2.2
        (by intro i hi; simp [lowReply,show i < L by have := k.isLt; dsimp [N] at *; omega])
      simpa only [choices,Nat.cast_add,Nat.cast_ofNat,add_assoc,show (3:ℝ)+1=4 by norm_num] using h
    simp only [branchMass]
    simp_rw [base]
    change R + (∑ k : Fin N, weight a eps k.val * (3/((k.val:ℝ)+4))) = _
    rw [Fin.sum_univ_eq_sum_range (fun k => weight a eps k * (3/((k:ℝ)+4))) N]
    have sumreturn := weight_tail a eps N 0 (Nat.zero_le _) endzero
    have eqset : Finset.Ico 0 N = Finset.range N := by ext k; simp
    rw [eqset] at sumreturn
    rw [sumreturn]
    change R+d 0 = _
    rw [d0]
    dsimp [R]
    rw [Wvalue]
    all_goals ring

#print axioms stopped_residual_synthesis

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedResidualSynthesis
