/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain
   mirror-E: none(waiver:symbolic-finite-measures)
   anchors: []
   utility: none
   digest: Stopped tables collect arbitrary first-zero classes with terminal mass. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.JointRewardFiberObstruction
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound

/-! Weighted rewards on the original full Boolean carrier and complete catalogs. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedCoefficientRealization
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.JointRewardFiberObstruction
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound
open private firstZero_unique firstZero_exists firstZero_not_terminal from
  D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.JointRewardFiberObstruction
namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain

/-- The actual reward for every original label, including zero. -/
def reward {L : ℕ} (y : FullScore L) (b : Word L) (r : Fin (L + 1)) : ℝ :=
  Fin.cases (baseline y b) (fun i => numerical y i b) r

/-- An arbitrary legal whole output function is evaluated on every word. -/
def score {L : ℕ} (y : FullScore L) (f : Word L → Fin (L + 1)) : ℝ :=
  ∑ b, reward y b (f b)

private def constantTable (stop : Bool) (L : ℕ) (r : Fin (L + 1)) : Catalog stop L :=
  ⟨fun _ => r, ⟨[], by simp, by simp, by simp, by intros; rfl⟩⟩

/-- Maximum over the original complete catalog, not a normalized law. -/
def support {L : ℕ} (stop : Bool) (y : FullScore L) : ℝ := by
  classical
  exact Finset.univ.sup' ⟨constantTable stop L 0, Finset.mem_univ _⟩
    (fun f => score y f.val)

open Classical in
/-- Correct mass at the original first-zero address. -/
def gamma {L : ℕ} (y : FullScore L) (i : Fin L) : ℝ :=
  ∑ b, if FirstZero b i then y.C b else 0

open Classical in
/-- Pair mass at the original first-zero address. -/
def pairMass {L : ℕ} (y : FullScore L) (i : Fin L) : ℝ :=
  ∑ b, if FirstZero b i then y.P b else 0

private theorem reward_nonneg {L : ℕ} (y : FullScore L) (b : Word L)
    (r : Fin (L + 1)) : 0 ≤ reward y b r := by
  refine Fin.cases ?_ (fun i => ?_) r
  · simp only [reward, Fin.cases_zero, baseline]
    have := y.nonnegA b; have := y.nonnegP b; have := y.nonnegT
    split <;> linarith
  · simp only [reward, Fin.cases_succ, numerical]
    split
    · exact add_nonneg (y.nonnegC b) (y.nonnegP b)
    · exact le_rfl

private theorem gamma_nonneg {L : ℕ} (y : FullScore L) (i : Fin L) :
    0 ≤ gamma y i := by
  classical
  exact Finset.sum_nonneg (fun b _ => by split <;> simp_all [FullScore.nonnegC])

private theorem pairMass_nonneg {L : ℕ} (y : FullScore L) (i : Fin L) :
    0 ≤ pairMass y i := by
  classical
  exact Finset.sum_nonneg (fun b _ => by split <;> simp_all [FullScore.nonnegP])

private theorem score_le_support {L : ℕ} (stop : Bool) (y : FullScore L)
    (f : Catalog stop L) : score y f.val ≤ support stop y := by
  classical
  unfold support
  exact Finset.le_sup' (fun f : Catalog stop L => score y f.val) (Finset.mem_univ f)

private theorem collect_classes {L : ℕ} (y : FullScore L)
    (f : Word L → Fin (L + 1)) (I : Finset (Fin L))
    (hits : ∀ i ∈ I, ∀ b, FirstZero b i → f b = i.succ)
    (terminal : f (fun _ => true) = 0) :
    (∑ i ∈ I, (gamma y i + pairMass y i)) + y.T ≤ score y f := by
  classical
  have expand : (∑ i ∈ I, (gamma y i + pairMass y i)) =
      ∑ b, ∑ i ∈ I, if FirstZero b i then y.C b + y.P b else 0 := by
    calc
      (∑ i ∈ I, (gamma y i + pairMass y i)) =
          ∑ i ∈ I, ∑ b, if FirstZero b i then y.C b + y.P b else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [gamma, pairMass, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro b _
        by_cases h : FirstZero b i <;> simp [h]
      _ = _ := Finset.sum_comm
  rw [expand]
  have ht : y.T = ∑ b : Word L, if b = (fun _ => true) then y.T else 0 := by simp
  rw [ht, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b _
  by_cases hb : b = (fun _ => true)
  · subst b
    simp [FirstZero, terminal, reward, baseline, y.terminalA, y.terminalP]
  · simp only [hb, ite_false, add_zero]
    by_cases hex : ∃ i ∈ I, FirstZero b i
    · obtain ⟨i,hi,hbi⟩ := hex
      rw [Finset.sum_eq_single i]
      · rw [ite_eq_left hbi, hits i hi b hbi]
        simp [reward, numerical, hbi]
      · intro j hj hji
        exact ite_eq_right (fun hbj => hji (firstZero_unique hbj hbi))
      · exact fun h => False.elim (h hi)
    · have hz : ∀ i ∈ I, ¬FirstZero b i := by
        intro i hi hbi; exact hex ⟨i,hi,hbi⟩
      simp only [Finset.sum_eq_zero (fun i hi => ite_eq_right (hz i hi))]
      exact reward_nonneg y b (f b)

private theorem pair_collect {L : ℕ} (y : FullScore L) (i j : Fin L) (hij : i < j) :
    gamma y i + pairMass y i + gamma y j + pairMass y j + y.T ≤ support true y := by
  classical
  let f := table (.inr (.inr ⟨(i,j),hij⟩)) (i.succ,j.succ,0)
  have h := collect_classes y f.val {i,j} (by
    intro k hk b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · simp [f, table, cell, label, hb.1]
    · have hbi := hb.2 i hij
      simp [f, table, cell, label, hbi, hb.1]) (by simp [f,table,cell,label])
  have hs := score_le_support true y f
  simp only [Finset.sum_pair (ne_of_lt hij)] at h
  linarith

private theorem single_collect {L : ℕ} (y : FullScore L) (i : Fin L) :
    gamma y i + pairMass y i + y.T ≤ support true y := by
  classical
  let f := table (.inr (.inl i)) (i.succ,0,0)
  have h := collect_classes y f.val {i} (by
    intro k hk b hb
    have : k = i := Finset.mem_singleton.mp hk
    subst k
    simp [f,table,cell,label,hb.1]) (by simp [f,table,cell,label])
  have hs := score_le_support true y f
  simp only [Finset.sum_singleton] at h
  linarith

/-- Any two distinct first-zero classes can be collected together with the
terminal coefficient, regardless of the joint placement of the full score. -/
private theorem collect_two_classes {L : ℕ} (y : FullScore L) (I : Finset (Fin L))
    (hI : I.card ≤ 2) : (∑ i ∈ I, gamma y i) + y.T ≤ support true y := by
  classical
  have casesI : I = ∅ ∨ (∃ i, I = {i}) ∨ (∃ i j, I = {i,j}) := by
    by_cases h0 : I.card = 0
    · exact Or.inl (Finset.card_eq_zero.mp h0)
    · by_cases h1 : I.card = 1
      · exact Or.inr (Or.inl (Finset.card_eq_one.mp h1))
      · obtain ⟨i,j,_,h⟩ := Finset.card_eq_two.mp (show I.card = 2 by omega)
        exact Or.inr (Or.inr ⟨i,j,h⟩)
  rcases casesI with h | ⟨i,h⟩ | ⟨i,j,h⟩
  · subst I
    have h := collect_classes y (constantTable true L 0).val ∅ (by simp) rfl
    have hs := score_le_support true y (constantTable true L 0)
    simpa using h.trans hs
  · subst I
    simp only [Finset.sum_singleton]
    have := single_collect y i
    have := pairMass_nonneg y i
    linarith
  · subst I
    by_cases he : i = j
    · subst j
      simp only [Finset.insert_eq_of_mem (Finset.mem_singleton_self _), Finset.sum_singleton]
      have := single_collect y i
      have := pairMass_nonneg y i
      linarith
    · rw [Finset.sum_pair he]
      rcases lt_or_gt_of_ne he with hlt | hgt
      · have := pair_collect y i j hlt
        have := pairMass_nonneg y i; have := pairMass_nonneg y j
        linarith
      · have := pair_collect y j i hgt
        have := pairMass_nonneg y i; have := pairMass_nonneg y j
        linarith


/-- Pair coefficients vanish outside the first two original first-zero classes. -/
def EarlyPair {L : ℕ} (y : FullScore L) : Prop :=
  ∀ b i, FirstZero b i → 2 ≤ i.val → y.P b = 0

/-- The total pair coefficient on the entire Boolean cube. -/
def pairTotal {L : ℕ} (y : FullScore L) : ℝ := ∑ b, y.P b

/-- Total early correct coefficient, with original labels 1 and 2. -/
def early {L : ℕ} (hL : 3 ≤ L) (y : FullScore L) : ℝ :=
  gamma y ⟨0, by omega⟩ + gamma y ⟨1, by omega⟩

/-- The original anchor on the A=0 early-pair family. -/
def inputAnchor {L : ℕ} (hL : 3 ≤ L) (y : FullScore L) : ℝ :=
  early hL y + pairTotal y + y.T

/-- Complete excess relative to that same input anchor. -/
def delta {L : ℕ} (hL : 3 ≤ L) (stop : Bool) (y : FullScore L) : ℝ :=
  support stop y - inputAnchor hL y

open Classical in
/-- Maximum late correct total, with zero included. Addresses retain their order. -/
def latePeak {L : ℕ} (y : FullScore L) : ℝ :=
  Finset.univ.sup' ⟨none, Finset.mem_univ _⟩
    (fun o : Option (Fin L) => o.elim 0 (fun i => if 2 ≤ i.val then gamma y i else 0))

open Classical in
/-- Maximum sum of at most two distinct late class totals, including the empty set. -/
def twoLate {L : ℕ} (y : FullScore L) : ℝ :=
  ((Finset.univ : Finset (Finset (Fin L))).filter
    (fun I => I.card ≤ 2 ∧ ∀ i ∈ I, 2 ≤ i.val)).sup'
      ⟨∅, by simp⟩ (fun I => ∑ i ∈ I, gamma y i)

/-- Optimal smaller early C+P total. -/
def earlyCapacity {L : ℕ} (hL : 3 ≤ L) (y : FullScore L) : ℝ :=
  min ((early hL y + pairTotal y) / 2)
    (pairTotal y + min (gamma y ⟨0, by omega⟩) (gamma y ⟨1, by omega⟩))

/-- The high-terminal lower bound of the optimized chain supplier. -/
def highLower {L : ℕ} (hL : 3 ≤ L) (y : FullScore L) : ℝ :=
  max (max 0 (twoLate y - early hL y - pairTotal y))
    (latePeak y - earlyCapacity hL y)

private theorem pair_partition {L : ℕ} (hL : 3 ≤ L) (y : FullScore L)
    (hy : EarlyPair y) :
    pairMass y ⟨0, by omega⟩ + pairMass y ⟨1, by omega⟩ = pairTotal y := by
  classical
  unfold pairMass pairTotal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hp : y.P b = 0
  · simp [hp]
  · have hb : b ≠ (fun _ => true) := by
      intro hb; exact hp (hb ▸ y.terminalP)
    obtain ⟨i,hi⟩ := firstZero_exists b hb
    have he : i.val < 2 := by
      by_contra h
      exact hp (hy b i hi (by omega))
    have hc : i = (⟨0, by omega⟩ : Fin L) ∨ i = ⟨1, by omega⟩ := by
      by_cases h0 : i.val = 0
      · exact Or.inl (Fin.ext h0)
      · exact Or.inr (Fin.ext (show i.val = 1 by omega))
    rcases hc with hc | hc
    · have hfirst : FirstZero b (⟨0, by omega⟩ : Fin L) := hc ▸ hi
      have hn : ¬FirstZero b (⟨1, by omega⟩ : Fin L) := by
        intro hj
        have hh := congrArg Fin.val (firstZero_unique hfirst hj)
        norm_num at hh
      simp [hfirst,hn]
    · have hfirst : FirstZero b (⟨1, by omega⟩ : Fin L) := hc ▸ hi
      have hn : ¬FirstZero b (⟨0, by omega⟩ : Fin L) := by
        intro hj
        have hh := congrArg Fin.val (firstZero_unique hfirst hj)
        norm_num at hh
      simp [hfirst,hn]

private theorem anchor_le_support {L : ℕ} (hL : 3 ≤ L) (y : FullScore L)
    (hy : EarlyPair y) : inputAnchor hL y ≤ support true y := by
  have h := pair_collect y (⟨0, by omega⟩ : Fin L) ⟨1, by omega⟩ (by change (0 : ℕ) < 1; omega)
  have hp := pair_partition hL y hy
  unfold inputAnchor early
  linarith

private theorem capacity_nonneg {L : ℕ} (hL : 3 ≤ L) (y : FullScore L) :
    0 ≤ earlyCapacity hL y := by
  have h0 := gamma_nonneg y (⟨0, by omega⟩ : Fin L)
  have h1 := gamma_nonneg y (⟨1, by omega⟩ : Fin L)
  have hS : 0 ≤ pairTotal y := Finset.sum_nonneg (fun b _ => y.nonnegP b)
  simp only [earlyCapacity, early, le_min_iff]
  constructor
  · linarith
  · exact add_nonneg hS (le_min h0 h1)

private theorem smaller_early_le_capacity {L : ℕ} (hL : 3 ≤ L)
    (y : FullScore L) (hy : EarlyPair y) :
    min (gamma y ⟨0, by omega⟩ + pairMass y ⟨0, by omega⟩)
      (gamma y ⟨1, by omega⟩ + pairMass y ⟨1, by omega⟩) ≤ earlyCapacity hL y := by
  have hp := pair_partition hL y hy
  have h0 := pairMass_nonneg y (⟨0, by omega⟩ : Fin L)
  have h1 := pairMass_nonneg y (⟨1, by omega⟩ : Fin L)
  have hm0 := min_le_left
    (gamma y ⟨0, by omega⟩ + pairMass y ⟨0, by omega⟩)
    (gamma y ⟨1, by omega⟩ + pairMass y ⟨1, by omega⟩)
  have hm1 := min_le_right
    (gamma y ⟨0, by omega⟩ + pairMass y ⟨0, by omega⟩)
    (gamma y ⟨1, by omega⟩ + pairMass y ⟨1, by omega⟩)
  unfold earlyCapacity early
  apply le_min
  · linarith
  · rcases le_total (gamma y (⟨0, by omega⟩ : Fin L)) (gamma y ⟨1, by omega⟩) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith

private theorem late_le_capacity_add_delta {L : ℕ} (hL : 3 ≤ L)
    (y : FullScore L) (hy : EarlyPair y) (j : Fin L) (hj : 2 ≤ j.val) :
    gamma y j ≤ earlyCapacity hL y + delta hL true y := by
  have h0 := pair_collect y (⟨0, by omega⟩ : Fin L) j (by change 0 < j.val; omega)
  have h1 := pair_collect y (⟨1, by omega⟩ : Fin L) j (by change 1 < j.val; omega)
  have hp := pair_partition hL y hy
  have hjP := pairMass_nonneg y j
  have hc := smaller_early_le_capacity hL y hy
  have hsum : inputAnchor hL y =
      (gamma y ⟨0, by omega⟩ + pairMass y ⟨0, by omega⟩) +
      (gamma y ⟨1, by omega⟩ + pairMass y ⟨1, by omega⟩) + y.T := by
    unfold inputAnchor early; linarith
  unfold delta
  rcases le_total
      (gamma y (⟨0, by omega⟩ : Fin L) + pairMass y ⟨0, by omega⟩)
      (gamma y (⟨1, by omega⟩ : Fin L) + pairMass y ⟨1, by omega⟩) with h | h
  · rw [min_eq_left h] at hc; linarith
  · rw [min_eq_right h] at hc; linarith

/-- The bound applies to every arbitrary legal placement on the original cube.
No same-fiber, normalization, sorted-profile or chain-support premise is used. -/
theorem arbitrary_input_lower_bound {L : ℕ} (hL : 3 ≤ L)
    (y : FullScore L) (hy : EarlyPair y) : highLower hL y ≤ delta hL true y := by
  have ha := anchor_le_support hL y hy
  have hd : 0 ≤ delta hL true y := by unfold delta; linarith
  have h2 : twoLate y - early hL y - pairTotal y ≤ delta hL true y := by
    have hb : twoLate y ≤ support true y - y.T := by
      unfold twoLate
      apply Finset.sup'_le
      intro I hI
      have h := collect_two_classes y I (Finset.mem_filter.mp hI).2.1
      linarith
    unfold delta inputAnchor
    linarith
  have hm : latePeak y - earlyCapacity hL y ≤ delta hL true y := by
    have hc := capacity_nonneg hL y
    have hb : latePeak y ≤ earlyCapacity hL y + delta hL true y := by
      unfold latePeak
      apply Finset.sup'_le
      intro o _
      cases o with
      | none => simp only [Option.elim_none]; linarith
      | some i =>
        simp only [Option.elim_some]
        split_ifs with hi
        · exact late_le_capacity_add_delta hL y hy i hi
        · linarith
    linarith
  exact max_le (max_le hd h2) hm

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain
