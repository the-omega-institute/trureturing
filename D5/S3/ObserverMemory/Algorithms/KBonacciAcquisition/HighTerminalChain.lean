/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain
   mirror-E: none(waiver:symbolic-finite-measures)
   anchors: []
   utility: none
   digest: Native balanced chains realize exact complete high-terminal catalog excess. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.JointRewardFiberObstruction
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound

/-! Weighted rewards on the original full Boolean carrier and complete catalogs. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedCoefficientRealization
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.JointRewardFiberObstruction
open private point_integral firstZero_exists firstZero_not_terminal numerical_total from
  D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.JointRewardFiberCatalog
namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain

/-- The actual reward for every original label, including zero. -/
def reward {L : ℕ} (y : FullScore L) (b : Word L) (r : Fin (L + 1)) : ℝ := Fin.cases (baseline y b) (fun i => numerical y i b) r

/-- An arbitrary legal whole output function is evaluated on every word. -/
def score {L : ℕ} (y : FullScore L) (f : Word L → Fin (L + 1)) : ℝ := ∑ b, reward y b (f b)
private def constantTable (stop : Bool) (L : ℕ) (r : Fin (L + 1)) : Catalog stop L := ⟨fun _ => r, ⟨[], by simp, by simp, by simp, by intros; rfl⟩⟩

/-- Maximum over the original complete catalog, not a normalized law. -/
def support {L : ℕ} (stop : Bool) (y : FullScore L) : ℝ := by
  classical
  exact Finset.univ.sup' ⟨constantTable stop L 0, Finset.mem_univ _⟩ (fun f => score y f.val)

open Classical in
/-- Correct mass at the original first-zero address. -/
def gamma {L : ℕ} (y : FullScore L) (i : Fin L) : ℝ := ∑ b, if FirstZero b i then y.C b else 0

open Classical in
/-- Pair mass at the original first-zero address. -/
def pairMass {L : ℕ} (y : FullScore L) (i : Fin L) : ℝ := ∑ b, if FirstZero b i then y.P b else 0
private theorem reward_nonneg {L : ℕ} (y : FullScore L) (b : Word L) (r : Fin (L + 1)) : 0 ≤ reward y b r := by
  refine Fin.cases ?_ (fun i => ?_) r
  · simp only [reward, Fin.cases_zero, baseline]
    have := y.nonnegA b; have := y.nonnegP b; have := y.nonnegT
    split <;> linarith
  · simp only [reward, Fin.cases_succ, numerical]
    split
    · exact add_nonneg (y.nonnegC b) (y.nonnegP b)
    · exact le_rfl
private theorem gamma_nonneg {L : ℕ} (y : FullScore L) (i : Fin L) : 0 ≤ gamma y i := by
  classical
  exact Finset.sum_nonneg (fun b _ => by split <;> simp_all [FullScore.nonnegC])
private theorem pairMass_nonneg {L : ℕ} (y : FullScore L) (i : Fin L) : 0 ≤ pairMass y i := by
  classical
  exact Finset.sum_nonneg (fun b _ => by split <;> simp_all [FullScore.nonnegP])
private theorem score_le_support {L : ℕ} (stop : Bool) (y : FullScore L) (f : Catalog stop L) : score y f.val ≤ support stop y := by
  classical
  unfold support
  exact Finset.le_sup' (fun f : Catalog stop L => score y f.val) (Finset.mem_univ f)
private theorem collect_classes {L : ℕ} (y : FullScore L) (f : Word L → Fin (L + 1)) (I : Finset (Fin L))
    (hits : ∀ i ∈ I, ∀ b, FirstZero b i → f b = i.succ) (terminal : f (fun _ => true) = 0) :
    (∑ i ∈ I, (gamma y i + pairMass y i)) + y.T ≤ score y f := by
  classical
  have expand : (∑ i ∈ I, (gamma y i + pairMass y i)) = ∑ b, ∑ i ∈ I, if FirstZero b i then y.C b + y.P b else 0 := by
    calc
      (∑ i ∈ I, (gamma y i + pairMass y i)) = ∑ i ∈ I, ∑ b, if FirstZero b i then y.C b + y.P b else 0 := by
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
private theorem single_collect {L : ℕ} (y : FullScore L) (i : Fin L) : gamma y i + pairMass y i + y.T ≤ support true y := by
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
def EarlyPair {L : ℕ} (y : FullScore L) : Prop := ∀ b i, FirstZero b i → 2 ≤ i.val → y.P b = 0

/-- The total pair coefficient on the entire Boolean cube. -/
def pairTotal {L : ℕ} (y : FullScore L) : ℝ := ∑ b, y.P b

/-- Total early correct coefficient, with original labels 1 and 2. -/
def early {L : ℕ} (hL : 3 ≤ L) (y : FullScore L) : ℝ := gamma y ⟨0, by omega⟩ + gamma y ⟨1, by omega⟩

/-- The original anchor on the A=0 early-pair family. -/
def inputAnchor {L : ℕ} (hL : 3 ≤ L) (y : FullScore L) : ℝ := early hL y + pairTotal y + y.T

/-- Complete excess relative to that same input anchor. -/
def delta {L : ℕ} (hL : 3 ≤ L) (stop : Bool) (y : FullScore L) : ℝ := support stop y - inputAnchor hL y

open Classical in
/-- Maximum late correct total, with zero included. Addresses retain their order. -/
def latePeak {L : ℕ} (y : FullScore L) : ℝ := Finset.univ.sup' ⟨none, Finset.mem_univ _⟩
    (fun o : Option (Fin L) => o.elim 0 (fun i => if 2 ≤ i.val then gamma y i else 0))

open Classical in
/-- Maximum sum of at most two distinct late class totals, including the empty set. -/
def twoLate {L : ℕ} (y : FullScore L) : ℝ := ((Finset.univ : Finset (Finset (Fin L))).filter (fun I => I.card ≤ 2 ∧ ∀ i ∈ I, 2 ≤ i.val)).sup'
      ⟨∅, by simp⟩ (fun I => ∑ i ∈ I, gamma y i)

/-- Optimal smaller early C+P total. -/
def earlyCapacity {L : ℕ} (hL : 3 ≤ L) (y : FullScore L) : ℝ := min ((early hL y + pairTotal y) / 2)
    (pairTotal y + min (gamma y ⟨0, by omega⟩) (gamma y ⟨1, by omega⟩))

/-- The high-terminal lower bound of the optimized chain supplier. -/
def highLower {L : ℕ} (hL : 3 ≤ L) (y : FullScore L) : ℝ := max (max 0 (twoLate y - early hL y - pairTotal y)) (latePeak y - earlyCapacity hL y)
private theorem pair_partition {L : ℕ} (hL : 3 ≤ L) (y : FullScore L) (hy : EarlyPair y) :
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
private theorem anchor_le_support {L : ℕ} (hL : 3 ≤ L) (y : FullScore L) (hy : EarlyPair y) : inputAnchor hL y ≤ support true y := by
  have h := pair_collect y (⟨0, by omega⟩ : Fin L) ⟨1, by omega⟩ (by change (0 : ℕ) < 1; omega)
  have hp := pair_partition hL y hy
  unfold inputAnchor early
  linarith
private theorem capacity_nonneg {L : ℕ} (hL : 3 ≤ L) (y : FullScore L) : 0 ≤ earlyCapacity hL y := by
  have h0 := gamma_nonneg y (⟨0, by omega⟩ : Fin L)
  have h1 := gamma_nonneg y (⟨1, by omega⟩ : Fin L)
  have hS : 0 ≤ pairTotal y := Finset.sum_nonneg (fun b _ => y.nonnegP b)
  simp only [earlyCapacity, early, le_min_iff]
  constructor
  · linarith
  · exact add_nonneg hS (le_min h0 h1)
private theorem smaller_early_le_capacity {L : ℕ} (hL : 3 ≤ L) (y : FullScore L) (hy : EarlyPair y) :
    min (gamma y ⟨0, by omega⟩ + pairMass y ⟨0, by omega⟩) (gamma y ⟨1, by omega⟩ + pairMass y ⟨1, by omega⟩) ≤ earlyCapacity hL y := by
  have hp := pair_partition hL y hy
  have h0 := pairMass_nonneg y (⟨0, by omega⟩ : Fin L)
  have h1 := pairMass_nonneg y (⟨1, by omega⟩ : Fin L)
  have hm0 := min_le_left (gamma y ⟨0, by omega⟩ + pairMass y ⟨0, by omega⟩) (gamma y ⟨1, by omega⟩ + pairMass y ⟨1, by omega⟩)
  have hm1 := min_le_right (gamma y ⟨0, by omega⟩ + pairMass y ⟨0, by omega⟩) (gamma y ⟨1, by omega⟩ + pairMass y ⟨1, by omega⟩)
  unfold earlyCapacity early
  apply le_min
  · linarith
  · rcases le_total (gamma y (⟨0, by omega⟩ : Fin L)) (gamma y ⟨1, by omega⟩) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
private theorem late_le_capacity_add_delta {L : ℕ} (hL : 3 ≤ L) (y : FullScore L) (hy : EarlyPair y) (j : Fin L) (hj : 2 ≤ j.val) :
    gamma y j ≤ earlyCapacity hL y + delta hL true y := by
  have h0 := pair_collect y (⟨0, by omega⟩ : Fin L) j (by change 0 < j.val; omega)
  have h1 := pair_collect y (⟨1, by omega⟩ : Fin L) j (by change 1 < j.val; omega)
  have hp := pair_partition hL y hy
  have hjP := pairMass_nonneg y j
  have hc := smaller_early_le_capacity hL y hy
  have hsum : inputAnchor hL y = (gamma y ⟨0, by omega⟩ + pairMass y ⟨0, by omega⟩) + (gamma y ⟨1, by omega⟩ + pairMass y ⟨1, by omega⟩) + y.T := by
    unfold inputAnchor early; linarith
  unfold delta
  rcases le_total (gamma y (⟨0, by omega⟩ : Fin L) + pairMass y ⟨0, by omega⟩) (gamma y (⟨1, by omega⟩ : Fin L) + pairMass y ⟨1, by omega⟩) with h | h
  · rw [min_eq_left h] at hc; linarith
  · rw [min_eq_right h] at hc; linarith

/-- The bound applies to every arbitrary legal placement on the original cube.
No same-fiber, normalization, sorted-profile or chain-support premise is used. -/
theorem arbitrary_input_lower_bound {L : ℕ} (hL : 3 ≤ L) (y : FullScore L) (hy : EarlyPair y) :
    highLower hL y ≤ support true y - inputAnchor hL y := by
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

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound
open Classical

/-- The source's clamped allocation of pair mass to the first chain word. -/
def balancedSplit (a b S : ℝ) : ℝ := min S (max 0 ((b + S - a) / 2))
private theorem balanced_split_spec (a b S : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hS : 0 ≤ S) : 0 ≤ balancedSplit a b S ∧ balancedSplit a b S ≤ S ∧
    min (a + balancedSplit a b S) (b + (S - balancedSplit a b S)) = min ((a+b+S)/2) (S + min a b) := by
  unfold balancedSplit
  constructor
  · exact le_min hS (le_max_left _ _)
  constructor
  · exact min_le_left _ _
  · rcases le_total 0 ((b+S-a)/2) with h | h
    · rw [max_eq_right h]
      rcases le_total S ((b+S-a)/2) with k | k
      · rw [min_eq_left k]
        have hab : a+S ≤ b := by linarith
        rw [min_eq_left (by linarith : a+S ≤ b+(S-S)), min_eq_left (by linarith : a ≤ b), min_eq_right (by linarith : S+a ≤ (a+b+S)/2)]
        ring
      · rw [min_eq_right k]
        have heq : a+(b+S-a)/2 = b+(S-(b+S-a)/2) := by ring
        rw [min_eq_left heq.le]
        have hm : (a+b+S)/2 ≤ S+min a b := by
          rcases le_total a b with hab | hab
          · rw [min_eq_left hab]; linarith
          · rw [min_eq_right hab]; linarith
        rw [min_eq_left hm]
        ring
    · rw [max_eq_left h, min_eq_right hS]
      rw [add_zero, sub_zero, min_eq_right (by linarith : b+S ≤ a), min_eq_right (by linarith : b ≤ a), min_eq_right (by linarith : S+b ≤ (a+b+S)/2)]
      ring
private theorem chain_firstZero {L : ℕ} (i j : Fin L) : FirstZero (chainWord L i.val) j ↔ j = i := by
  have self : FirstZero (chainWord L i.val) i := by
    constructor
    · simp [chainWord]
    · intro k hk
      simpa [chainWord] using hk
  constructor
  · intro h
    exact firstZero_unique h self
  · rintro rfl
    exact self
private theorem chain_not_terminal {L : ℕ} (i : Fin L) : chainWord L i.val ≠ (fun _ => true) := by
  exact firstZero_not_terminal ((chain_firstZero i i).2 rfl)

/-- The actual A-free FullScore of 206.7; every unspecified cube row is zero. -/
def balancedChain {L : ℕ} (hL : 3 ≤ L) (g : Fin L → ℝ) (S t : ℝ) (hg : ∀ i, 0 ≤ g i) (hS : 0 ≤ S) (ht : 0 ≤ t) : FullScore L where
  A := fun _ => 0
  C := fun b => ∑ i, point (chainWord L i.val) (g i) b
  P := fun b => point (chainWord L 0) (balancedSplit (g ⟨0,by omega⟩) (g ⟨1,by omega⟩) S) b +
    point (chainWord L 1) (S-balancedSplit (g ⟨0,by omega⟩) (g ⟨1,by omega⟩) S) b
  T := t
  nonnegA := by simp
  nonnegC := by intro b; apply Finset.sum_nonneg; intro i _; unfold point; split <;> simp [hg]
  nonnegP := by
    intro b
    have h := balanced_split_spec _ _ S (hg ⟨0,by omega⟩) (hg ⟨1,by omega⟩) hS
    apply add_nonneg <;> unfold point <;> split
    · exact h.1
    · rfl
    · exact sub_nonneg.mpr h.2.1
    · rfl
  nonnegT := ht
  terminalA := rfl
  terminalC := by
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (Ne.symm (chain_not_terminal i))
  terminalP := by
    have h0 := chain_not_terminal (⟨0,by omega⟩ : Fin L)
    have h1 := chain_not_terminal (⟨1,by omega⟩ : Fin L)
    simp only [point, ite_eq_right (Ne.symm h0), ite_eq_right (Ne.symm h1), add_zero]
private theorem ite_sum_zero {I : Type*} [Fintype I] (p : Prop) [Decidable p]
    (f : I → ℝ) : (if p then ∑ i, f i else 0) = ∑ i, if p then f i else 0 := by
  exact Finset.ite_sum_zero p Finset.univ f
private theorem chain_gamma {L : ℕ} (hL : 3 ≤ L) (g : Fin L → ℝ) (S t : ℝ) (hg : ∀ i, 0 ≤ g i) (hS : 0 ≤ S) (ht : 0 ≤ t) (j : Fin L) :
    gamma (balancedChain hL g S t hg hS ht) j = g j := by
  classical
  unfold gamma
  change (∑ b, if FirstZero b j then ∑ i, point (chainWord L i.val) (g i) b else 0) = _
  simp_rw [ite_sum_zero]
  rw [Finset.sum_comm]
  have hp (i : Fin L) : (∑ b, if FirstZero b j then point (chainWord L i.val) (g i) b else 0) = if j = i then g i else 0 := by
    have := point_integral (chainWord L i.val) (g i) (fun b => if FirstZero b j then 1 else 0)
    simpa only [mul_ite,mul_one,mul_zero,chain_firstZero,ite_mul,one_mul,zero_mul] using this
  simp_rw [hp]
  simp
private theorem chain_pair_total {L : ℕ} (hL : 3 ≤ L) (g : Fin L → ℝ) (S t : ℝ) (hg : ∀ i, 0 ≤ g i) (hS : 0 ≤ S) (ht : 0 ≤ t) :
    pairTotal (balancedChain hL g S t hg hS ht) = S := by
  classical
  simp [pairTotal,balancedChain,Finset.sum_add_distrib,point]
private theorem chain_early_pair {L : ℕ} (hL : 3 ≤ L) (g : Fin L → ℝ) (S t : ℝ) (hg : ∀ i, 0 ≤ g i) (hS : 0 ≤ S) (ht : 0 ≤ t) :
    EarlyPair (balancedChain hL g S t hg hS ht) := by
  classical
  intro b i hi hlate
  have off (k : Fin L) (hk : k.val < 2) : b ≠ chainWord L k.val := by
    intro hb
    rw [hb,chain_firstZero] at hi
    subst i
    omega
  simp [balancedChain,point,off ⟨0,by omega⟩ (by simp),off ⟨1,by omega⟩ (by simp)]
private def hit {L : ℕ} (b : Word L) (r : Fin (L + 1)) : Prop := ∃ i, FirstZero b i ∧ r = i.succ
private theorem hit_chain {L : ℕ} (i : Fin L) (r : Fin (L + 1)) : hit (chainWord L i.val) r ↔ r = i.succ := by
  simp [hit,chain_firstZero]
private theorem reward_linear {L : ℕ} (y : FullScore L) (b : Word L) (r : Fin (L + 1)) : reward y b r = (if r = 0 then y.A b else 0) +
      (if hit b r then y.C b else 0) + (if r = 0 ∨ hit b r then y.P b else 0) + (if b = (fun _ => true) ∧ r = 0 then y.T else 0) := by
  classical
  refine Fin.cases ?_ (fun i => ?_) r
  · have hn : ¬hit b (0 : Fin (L + 1)) := by
      rintro ⟨i,_,h⟩
      exact Fin.succ_ne_zero i h.symm
    simp [reward,baseline,hn]
  · have hh : hit b i.succ ↔ FirstZero b i := by simp [hit]
    by_cases h : FirstZero b i <;>
      simp [reward,numerical,hh,h,Fin.succ_ne_zero]
private theorem succ_zero_label {L : ℕ} (hL : 3 ≤ L) : (⟨0,by omega⟩ : Fin L).succ = (1 : Fin (L+1)) := by
  letI : NeZero L := ⟨by omega⟩
  exact Fin.succ_zero_eq_one' (n := L)
private theorem succ_one_label {L : ℕ} (hL : 3 ≤ L) : (⟨1,by omega⟩ : Fin L).succ = (2 : Fin (L+1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 2 := ⟨L - 2, by omega⟩
  simpa only [Fin.one_eq_mk_of_lt (by omega : 1 < n + 2)] using (Fin.succ_one_eq_two (n := n))
private theorem succ_eq_one {L : ℕ} (hL : 3 ≤ L) (n : Fin L) : n.succ = (1 : Fin (L+1)) ↔ n.val = 0 := by
  rw [← succ_zero_label hL,Fin.succ_inj,Fin.ext_iff]
private theorem succ_eq_two {L : ℕ} (hL : 3 ≤ L) (n : Fin L) : n.succ = (2 : Fin (L+1)) ↔ n.val = 1 := by
  rw [← succ_one_label hL,Fin.succ_inj,Fin.ext_iff]
private theorem early_labels_distinct {L : ℕ} (hL : 3 ≤ L) : (1 : Fin (L+1)) ≠ 2 := by
  intro h
  have hh := congrArg Fin.val h
  change 1 % (L+1) = 2 % (L+1) at hh
  rw [Nat.mod_eq_of_lt (by omega : 1 < L+1),Nat.mod_eq_of_lt (by omega : 2 < L+1)] at hh
  omega
private theorem early_one_ne_zero {L : ℕ} (hL : 3 ≤ L) : (1 : Fin (L+1)) ≠ 0 := by
  rw [←succ_zero_label hL]
  exact Fin.succ_ne_zero _
private theorem early_two_ne_zero {L : ℕ} (hL : 3 ≤ L) : (2 : Fin (L+1)) ≠ 0 := by
  rw [←succ_one_label hL]
  exact Fin.succ_ne_zero _
private theorem chain_score {L : ℕ} (hL : 3 ≤ L) (g : Fin L → ℝ) (S t : ℝ) (hg : ∀ i, 0 ≤ g i) (hS : 0 ≤ S) (ht : 0 ≤ t) (f : Word L → Fin (L + 1)) :
    score (balancedChain hL g S t hg hS ht) f = (∑ i, if f (chainWord L i.val) = i.succ then g i else 0) +
      (if f (chainWord L 0) = 0 ∨ f (chainWord L 0) = 1 then
        balancedSplit (g ⟨0,by omega⟩) (g ⟨1,by omega⟩) S else 0) +
      (if f (chainWord L 1) = 0 ∨ f (chainWord L 1) = 2 then
        S-balancedSplit (g ⟨0,by omega⟩) (g ⟨1,by omega⟩) S else 0) +
      (if f (fun _ => true) = 0 then t else 0) := by
  classical
  unfold score
  simp_rw [reward_linear,Finset.sum_add_distrib]
  have hc : (∑ b, if hit b (f b) then (balancedChain hL g S t hg hS ht).C b else 0) = ∑ i, if f (chainWord L i.val) = i.succ then g i else 0 := by
    change (∑ b, if hit b (f b) then ∑ i, point (chainWord L i.val) (g i) b else 0) = _
    simp_rw [ite_sum_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [mul_ite,mul_one,mul_zero,hit_chain] using
      point_integral (chainWord L i.val) (g i) (fun b => if hit b (f b) then 1 else 0)
  have hp : (∑ b, if f b = 0 ∨ hit b (f b) then
      (balancedChain hL g S t hg hS ht).P b else 0) = (if f (chainWord L 0) = 0 ∨ f (chainWord L 0) = 1 then
        balancedSplit (g ⟨0,by omega⟩) (g ⟨1,by omega⟩) S else 0) +
      (if f (chainWord L 1) = 0 ∨ f (chainWord L 1) = 2 then
        S-balancedSplit (g ⟨0,by omega⟩) (g ⟨1,by omega⟩) S else 0) := by
    change (∑ b, if f b = 0 ∨ hit b (f b) then
      point (chainWord L 0) _ b + point (chainWord L 1) _ b else 0) = _
    have hadd (p : Prop) [Decidable p] (a b : ℝ) : (if p then a+b else 0) = (if p then a else 0)+(if p then b else 0) := by
      split <;> simp
    simp_rw [hadd,Finset.sum_add_distrib]
    have h0 := point_integral (chainWord L 0) (balancedSplit (g ⟨0,by omega⟩) (g ⟨1,by omega⟩) S) (fun b => if f b = 0 ∨ hit b (f b) then 1 else 0)
    have h1 := point_integral (chainWord L 1) (S-balancedSplit (g ⟨0,by omega⟩) (g ⟨1,by omega⟩) S) (fun b => if f b = 0 ∨ hit b (f b) then 1 else 0)
    simp only [mul_ite,mul_one,mul_zero] at h0 h1
    rw [h0,h1]
    have hz : hit (chainWord L 0) (f (chainWord L 0)) ↔ f (chainWord L 0) = 1 :=
      (hit_chain (⟨0,by omega⟩ : Fin L) _).trans (by rw [succ_zero_label hL])
    have ho : hit (chainWord L 1) (f (chainWord L 1)) ↔ f (chainWord L 1) = 2 :=
      (hit_chain (⟨1,by omega⟩ : Fin L) _).trans (by rw [succ_one_label hL])
    simp only [hz,ho]

  rw [hc,hp]
  have hterm : (∑ b : Word L, if b = (fun _ => true) ∧ f b = 0 then t else 0) = if f (fun _ => true) = 0 then t else 0 := by
    rw [Finset.sum_eq_single (fun _ => true)]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  change (∑ x, if f x = 0 then (0 : ℝ) else 0) + (∑ i, if f (chainWord L i.val) = i.succ then g i else 0) + _ +
    (∑ x, if x = (fun _ => true) ∧ f x = 0 then t else 0) = _
  rw [hterm]
  simp only [ite_self,Finset.sum_const_zero,zero_add]
  ring
private theorem chain_coefficient_mass {L : ℕ} (hL : 3 ≤ L) (g : Fin L → ℝ) (S t : ℝ) (hg : ∀ i, 0 ≤ g i) (hS : 0 ≤ S) (ht : 0 ≤ t) :
    coefficientMass (balancedChain hL g S t hg hS ht) = (∑ i, g i) + S + t := by
  classical
  simp only [coefficientMass,balancedChain,zero_add,Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp [point]

private theorem chain_beta {L : ℕ} (hL : 3 ≤ L) (g : Fin L → ℝ) (S t : ℝ) (hg : ∀ i, 0 ≤ g i) (hS : 0 ≤ S) (ht : 0 ≤ t) :
    beta (balancedChain hL g S t hg hS ht) = g := by
  funext i
  simpa only [beta,balancedChain,sub_zero,gamma] using chain_gamma hL g S t hg hS ht i

private theorem catalog_two_factor {L : ℕ} (hL : 3 ≤ L) (stop : Bool) (f : Catalog stop L) : ∃ i j : Fin L, i < j ∧
      ∀ b c, b i = c i → b j = c j → f.val b = f.val c := by
  obtain ⟨xs,hlen,hlow,_,hfactor⟩ := f.property
  have single (i : Fin L) (hf : ∀ b c, b i = c i → f.val b = f.val c) : ∃ i j : Fin L, i < j ∧ ∀ b c, b i = c i → b j = c j → f.val b = f.val c := by
    by_cases hi : i.val = 0
    · refine ⟨⟨0,by omega⟩,⟨1,by omega⟩,by change (0:ℕ)<1; omega,?_⟩
      intro b c h _
      have he : i = (⟨0,by omega⟩ : Fin L) := Fin.ext hi
      exact hf b c (by simpa only [he] using h)
    · refine ⟨⟨0,by omega⟩,i,by change (0 : ℕ) < i.val; omega,?_⟩
      intro b c _ h
      exact hf b c h
  cases xs with
  | nil =>
      exact single ⟨0,by omega⟩ (fun b c _ => hfactor b c rfl)
  | cons i xs =>
      have hi : i < L := hlow i (by simp)
      cases xs with
      | nil =>
          apply single ⟨i,hi⟩
          intro b c h
          apply hfactor
          simp [view,lowReply,hi,h]
      | cons j xs =>
          have hj : j < L := hlow j (by simp)
          cases xs with
          | cons k xs => simp at hlen
          | nil =>
              have hf (b c : Word L) (hbi : b ⟨i,hi⟩ = c ⟨i,hi⟩) (hbj : b ⟨j,hj⟩ = c ⟨j,hj⟩) : f.val b = f.val c := by
                apply hfactor
                apply view_congr
                intro k hk
                simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
                rcases hk with rfl | rfl
                · simpa [lowReply,hi] using hbi
                · simpa [lowReply,hj] using hbj
              rcases lt_trichotomy i j with hij | hij | hij
              · exact ⟨⟨i,hi⟩,⟨j,hj⟩,hij,hf⟩
              · subst j
                exact single ⟨i,hi⟩ (fun b c h => hf b c h h)
              · exact ⟨⟨j,hj⟩,⟨i,hi⟩,hij,fun b c h₁ h₂ => hf b c h₂ h₁⟩

/-- Restriction of every complete native table to chain rows is an original
increasing stopped pair table; off-chain values are not identified. -/
private theorem chain_represented {L : ℕ} (hL : 3 ≤ L) (stop : Bool) (f : Catalog stop L) : ∃ a : Pair L, ∃ labels : Labels (Fin (L + 1)),
      (∀ n : Fin L, f.val (chainWord L n.val) = (table (.inr (.inr a)) labels).val (chainWord L n.val)) ∧
      f.val (fun _ => true) = (table (.inr (.inr a)) labels).val (fun _ => true) := by
  obtain ⟨i,j,hij,hf⟩ := catalog_two_factor hL stop f
  let a : Pair L := ⟨(i,j),hij⟩
  let labels : Labels (Fin (L + 1)) := (f.val (chainWord L 0), f.val (chainWord L (i.val+1)), f.val (fun _ => true))
  refine ⟨a,labels,?_,?_⟩
  · intro n
    by_cases hni : n.val ≤ i.val
    · have hnj : n.val ≤ j.val := by have := hij; change i.val < j.val at this; omega
      have hn : (chainWord L n.val) i = false := by simp [chainWord]; omega
      have hnj' : (chainWord L n.val) j = false := by simp [chainWord]; omega
      simpa [table,cell,label,a,labels,hn] using hf
        (chainWord L n.val) (chainWord L 0) (by rw [hn]; simp [chainWord]) (by rw [hnj']; simp [chainWord])
    · by_cases hnj : n.val ≤ j.val
      · have hn : (chainWord L n.val) i = true := by simp [chainWord]; omega
        have hn' : (chainWord L n.val) j = false := by simp [chainWord]; omega
        simpa [table,cell,label,a,labels,hn,hn'] using hf (chainWord L n.val) (chainWord L (i.val+1)) (by rw [hn]; simp [chainWord])
          (by rw [hn']; simp [chainWord]; have := hij; change i.val<j.val at this; omega)
      · have hn : (chainWord L n.val) i = true := by simp [chainWord]; omega
        have hn' : (chainWord L n.val) j = true := by simp [chainWord]; omega
        simpa [table,cell,label,a,labels,hn,hn'] using hf (chainWord L n.val) (fun _ => true) hn hn'
  · simp [table,cell,label,a,labels]

private def cellCorrect {L : ℕ} (g : Fin L → ℝ) (a : Pair L) (k : Fin 3) (r : Fin (L + 1)) : ℝ :=
  ∑ n, if cell (.inr (.inr a)) (chainWord L n.val) = k ∧ r = n.succ then g n else 0

private theorem cell_correct_label {L : ℕ} (g : Fin L → ℝ) (a : Pair L) (k : Fin 3) (n : Fin L) : cellCorrect g a k n.succ =
      if cell (.inr (.inr a)) (chainWord L n.val) = k then g n else 0 := by
  classical
  unfold cellCorrect
  rw [Finset.sum_eq_single n]
  · simp
  · intro j _ hj
    simp [show n.succ ≠ j.succ from fun h => hj (Fin.succ_injective _ h).symm]
  · simp

private def chainCell {L : ℕ} (hL : 3 ≤ L) (g : Fin L → ℝ) (S t : ℝ) (a : Pair L) (k : Fin 3) (r : Fin (L + 1)) : ℝ := cellCorrect g a k r +
    (if cell (.inr (.inr a)) (chainWord L 0) = k ∧ (r = 0 ∨ r = 1) then
      balancedSplit (g ⟨0,by omega⟩) (g ⟨1,by omega⟩) S else 0) +
    (if cell (.inr (.inr a)) (chainWord L 1) = k ∧ (r = 0 ∨ r = 2) then
      S-balancedSplit (g ⟨0,by omega⟩) (g ⟨1,by omega⟩) S else 0) +
    (if k = 2 ∧ r = 0 then t else 0)

private theorem table_score_cells {L : ℕ} (hL : 3 ≤ L) (g : Fin L → ℝ) (S t : ℝ) (hg : ∀ i, 0 ≤ g i) (hS : 0 ≤ S) (ht : 0 ≤ t)
    (a : Pair L) (labels : Labels (Fin (L + 1))) :
    score (balancedChain hL g S t hg hS ht) (table (.inr (.inr a)) labels).val = chainCell hL g S t a 0 labels.1 + chainCell hL g S t a 1 labels.2.1 +
      chainCell hL g S t a 2 labels.2.2 := by
  classical
  rw [chain_score]
  have hs : (∑ n, if label labels (cell (.inr (.inr a)) (chainWord L n.val)) = n.succ then
      g n else 0) = ∑ k : Fin 3, cellCorrect g a k (label labels k) := by
    unfold cellCorrect
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    symm
    rw [Finset.sum_eq_single (cell (.inr (.inr a)) (chainWord L n.val))]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · simp
  have hp (n : ℕ) (r : Fin (L + 1)) (w : ℝ) : (if label labels (cell (.inr (.inr a)) (chainWord L n)) = 0 ∨
          label labels (cell (.inr (.inr a)) (chainWord L n)) = r then w else 0) =
      ∑ k : Fin 3, if cell (.inr (.inr a)) (chainWord L n) = k ∧ (label labels k = 0 ∨ label labels k = r) then w else 0 := by
    symm
    rw [Finset.sum_eq_single (cell (.inr (.inr a)) (chainWord L n))]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · simp
  change (∑ n, if label labels (cell (.inr (.inr a)) (chainWord L n.val)) = n.succ then
      g n else 0) + _ + _ + _ = _
  rw [hs]
  change (∑ k : Fin 3, cellCorrect g a k (label labels k)) + (if label labels (cell (.inr (.inr a)) (chainWord L 0)) = 0 ∨
      label labels (cell (.inr (.inr a)) (chainWord L 0)) = 1 then _ else 0) +
    (if label labels (cell (.inr (.inr a)) (chainWord L 1)) = 0 ∨
      label labels (cell (.inr (.inr a)) (chainWord L 1)) = 2 then _ else 0) + _ = _
  rw [hp 0 1,hp 1 2]
  simp [Fin.sum_univ_succ,chainCell,label,table,cell]
  <;> ring

private theorem chain_cell_zero {L : ℕ} (a : Pair L) (n : ℕ) : cell (.inr (.inr a)) (chainWord L n) = 0 ↔ n ≤ a.val.1.val := by
  by_cases hi : a.val.1.val < n <;> by_cases hj : a.val.2.val < n <;>
    simp [cell,chainWord,hi,hj] <;> omega

private theorem chain_cell_one {L : ℕ} (a : Pair L) (n : ℕ) : cell (.inr (.inr a)) (chainWord L n) = 1 ↔ a.val.1.val < n ∧ n ≤ a.val.2.val := by
  by_cases hi : a.val.1.val < n <;> by_cases hj : a.val.2.val < n <;>
    simp [cell,chainWord,hi,hj] <;> omega

private theorem chain_cell_two {L : ℕ} (a : Pair L) (n : ℕ) : cell (.inr (.inr a)) (chainWord L n) = 2 ↔ a.val.2.val < n := by
  have ha := a.property
  change a.val.1.val < a.val.2.val at ha
  by_cases hi : a.val.1.val < n <;> by_cases hj : a.val.2.val < n <;>
    simp [cell,chainWord,hi,hj] <;> omega

private theorem cell_correct_zero {L : ℕ} (g : Fin L → ℝ) (a : Pair L) (k : Fin 3) : cellCorrect g a k 0 = 0 := by
  have hz (n : Fin L) : (0 : Fin (L+1)) ≠ n.succ := Ne.symm (Fin.succ_ne_zero n)
  simp [cellCorrect,hz]

private theorem late_peak_nonneg {L : ℕ} (y : FullScore L) : 0 ≤ latePeak y := by
  unfold latePeak
  exact Finset.le_sup' (fun o : Option (Fin L) => o.elim (0 : ℝ) (fun i => if 2 ≤ i.val then gamma y i else 0))
    (Finset.mem_univ (none : Option (Fin L)))

private theorem late_le_peak {L : ℕ} (y : FullScore L) (i : Fin L) (hi : 2 ≤ i.val) : gamma y i ≤ latePeak y := by
  unfold latePeak
  have h := Finset.le_sup' (fun o : Option (Fin L) => o.elim (0 : ℝ) (fun i => if 2 ≤ i.val then gamma y i else 0)) (Finset.mem_univ (some i))
  simpa [hi] using h

private theorem two_late_subset {L : ℕ} (y : FullScore L) (I : Finset (Fin L)) (hcard : I.card ≤ 2) (hlate : ∀ i ∈ I, 2 ≤ i.val) :
    (∑ i ∈ I, gamma y i) ≤ twoLate y := by
  unfold twoLate
  exact Finset.le_sup' (fun J : Finset (Fin L) => ∑ i ∈ J, gamma y i) (Finset.mem_filter.mpr ⟨Finset.mem_univ I,hcard,hlate⟩)

private theorem chain_late_le {L : ℕ} (hL : 3 ≤ L) (g : Fin L → ℝ) (S t : ℝ)
    (hg : ∀ i, 0 ≤ g i) (hS : 0 ≤ S) (ht : 0 ≤ t) (i : Fin L) (hi : 2 ≤ i.val) :
    g i ≤ latePeak (balancedChain hL g S t hg hS ht) := by
  rw [← chain_gamma hL g S t hg hS ht i]
  exact late_le_peak _ i hi

private theorem chain_two_late {L : ℕ} (hL : 3 ≤ L) (g : Fin L → ℝ) (S t : ℝ) (hg : ∀ i, 0 ≤ g i) (hS : 0 ≤ S) (ht : 0 ≤ t)
    (i j : Fin L) (hi : 2 ≤ i.val) (hj : 2 ≤ j.val) (hne : i ≠ j) :
    g i + g j ≤ twoLate (balancedChain hL g S t hg hS ht) := by
  have h := two_late_subset (balancedChain hL g S t hg hS ht) {i,j} (by simp [hne]) (by
      intro k hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> assumption)
  simpa [Finset.sum_pair hne,chain_gamma] using h

private theorem chain_single_late {L : ℕ} (hL : 3 ≤ L) (g : Fin L → ℝ) (S t : ℝ) (hg : ∀ i, 0 ≤ g i) (hS : 0 ≤ S) (ht : 0 ≤ t)
    (i : Fin L) (hi : 2 ≤ i.val) :
    g i ≤ twoLate (balancedChain hL g S t hg hS ht) := by
  have h := two_late_subset (balancedChain hL g S t hg hS ht) {i}
    (by simp) (by intro k hk; have : k=i := Finset.mem_singleton.mp hk; simpa [this] using hi)
  simpa [chain_gamma] using h

private theorem last_cell_le {L : ℕ} (hL : 3 ≤ L) (g : Fin L → ℝ) (S t : ℝ) (hg : ∀ i, 0 ≤ g i) (hS : 0 ≤ S) (ht : 0 ≤ t) (a : Pair L)
    (hhigh : latePeak (balancedChain hL g S t hg hS ht) ≤ t) (r : Fin (L + 1)) :
    chainCell hL g S t a 2 r ≤ t := by
  have ha := a.property
  change a.val.1.val < a.val.2.val at ha
  have hj : 1 ≤ a.val.2.val := by omega
  refine Fin.cases ?_ (fun n => ?_) r
  · simp [chainCell,cell_correct_zero,chain_cell_two,show ¬a.val.2.val<1 by omega]
  · simp only [chainCell,cell_correct_label,chain_cell_two,Fin.succ_ne_zero,and_false, ite_false,add_zero,show ¬a.val.2.val<0 by omega,
      show ¬a.val.2.val<1 by omega,false_and]
    split_ifs with hn
    · exact (chain_late_le hL g S t hg hS ht n (by omega)).trans hhigh
    · exact ht

private theorem middle_cell_le {L : ℕ} (hL : 3 ≤ L) (g : Fin L → ℝ) (S t : ℝ) (hg : ∀ i, 0 ≤ g i) (hS : 0 ≤ S) (ht : 0 ≤ t) (a : Pair L)
    (hi : 1 ≤ a.val.1.val) (r : Fin (L + 1)) :
    chainCell hL g S t a 1 r ≤ latePeak (balancedChain hL g S t hg hS ht) := by
  refine Fin.cases ?_ (fun n => ?_) r
  · simpa [chainCell,cell_correct_zero,chain_cell_one,show ¬a.val.1.val<0 by omega,
      show ¬a.val.1.val<1 by omega] using late_peak_nonneg (balancedChain hL g S t hg hS ht)
  · simp only [chainCell,cell_correct_label,chain_cell_one,Fin.succ_ne_zero,and_false, ite_false,add_zero,show ¬a.val.1.val<0 by omega,
      show ¬a.val.1.val<1 by omega,false_and,Fin.reduceEq]
    split_ifs with hn
    · exact chain_late_le hL g S t hg hS ht n (by omega)
    · exact late_peak_nonneg _
private theorem head_first_cell_le {L : ℕ} (hL : 3 ≤ L) (g : Fin L → ℝ) (S t : ℝ) (hg : ∀ i, 0 ≤ g i) (hS : 0 ≤ S) (a : Pair L) (hi : a.val.1.val = 0)
    (r : Fin (L + 1)) :
    chainCell hL g S t a 0 r ≤ g ⟨0,by omega⟩ + balancedSplit (g ⟨0,by omega⟩) (g ⟨1,by omega⟩) S := by
  have hs := balanced_split_spec _ _ S (hg ⟨0,by omega⟩) (hg ⟨1,by omega⟩) hS
  refine Fin.cases ?_ (fun n => ?_) r
  · simp [chainCell,cell_correct_zero,chain_cell_zero,hi]
    exact hg ⟨0,by omega⟩
  · by_cases hn : n.val = 0
    · have he : n = (⟨0,by omega⟩ : Fin L) := Fin.ext hn
      rw [chainCell,cell_correct_label]
      simp only [chain_cell_zero]
      rw [he]
      simp [chain_cell_zero,hi,succ_zero_label hL,early_labels_distinct hL,early_one_ne_zero hL]
    · have hn' : ¬n.val ≤ a.val.1.val := by omega
      have hne : n.succ ≠ (1 : Fin (L+1)) := (succ_eq_one hL n).not.mpr hn
      simp [chainCell,cell_correct_label,chain_cell_zero,hi,hn,hne]
      exact add_nonneg (hg ⟨0,by omega⟩) hs.1

private theorem head_middle_cell_le {L : ℕ} (hL : 3 ≤ L) (g : Fin L → ℝ) (S t : ℝ) (hg : ∀ i, 0 ≤ g i) (hS : 0 ≤ S) (ht : 0 ≤ t)
    (a : Pair L) (hi : a.val.1.val = 0) (r : Fin (L + 1)) :
    chainCell hL g S t a 1 r ≤ g ⟨1,by omega⟩ + (S-balancedSplit (g ⟨0,by omega⟩) (g ⟨1,by omega⟩) S) ∨
    chainCell hL g S t a 1 r ≤ latePeak (balancedChain hL g S t hg hS ht) := by
  have ha := a.property
  change a.val.1.val < a.val.2.val at ha
  have hj : 1 ≤ a.val.2.val := by omega
  have hs := balanced_split_spec _ _ S (hg ⟨0,by omega⟩) (hg ⟨1,by omega⟩) hS
  refine Fin.cases ?_ (fun n => ?_) r
  · left
    simp [chainCell,cell_correct_zero,chain_cell_one,hi,hj]
    exact hg ⟨1,by omega⟩
  · by_cases hn0 : n.val = 0
    · left
      have he : n = (⟨0,by omega⟩ : Fin L) := Fin.ext hn0
      rw [chainCell,cell_correct_label]
      simp only [chain_cell_one]
      rw [he]
      simp [chain_cell_one,hi,hj,succ_zero_label hL,early_labels_distinct hL,early_one_ne_zero hL]
      exact add_nonneg (hg ⟨1,by omega⟩) (sub_nonneg.mpr hs.2.1)
    · by_cases hn1 : n.val = 1
      · left
        have he : n = (⟨1,by omega⟩ : Fin L) := Fin.ext hn1
        rw [chainCell,cell_correct_label]
        simp only [chain_cell_one]
        rw [he]
        simp [chain_cell_one,hi,hj,succ_one_label hL,early_two_ne_zero hL]
      · right
        have hne : n.succ ≠ (2 : Fin (L+1)) := (succ_eq_two hL n).not.mpr hn1
        simp only [chainCell,cell_correct_label,chain_cell_one,hi, Fin.succ_ne_zero,false_or,hne,and_false,ite_false,add_zero,
          Nat.lt_irrefl,false_and,Fin.reduceEq]
        split_ifs
        · exact chain_late_le hL g S t hg hS ht n (by omega)
        · exact late_peak_nonneg _

private theorem late_first_two_le {L : ℕ} (hL : 3 ≤ L) (g : Fin L → ℝ) (S t : ℝ) (hg : ∀ i, 0 ≤ g i) (hS : 0 ≤ S) (ht : 0 ≤ t)
    (a : Pair L) (hi : 1 ≤ a.val.1.val) (n : Fin L) (hn : 2 ≤ n.val) (r : Fin (L + 1)) :
    chainCell hL g S t a 0 n.succ + chainCell hL g S t a 1 r ≤ twoLate (balancedChain hL g S t hg hS ht) := by
  have hn1 : n.succ ≠ (1 : Fin (L+1)) := by
    exact (succ_eq_one hL n).not.mpr (by omega)
  have hn2 : n.succ ≠ (2 : Fin (L+1)) := by
    exact (succ_eq_two hL n).not.mpr (by omega)
  have hfirst : chainCell hL g S t a 0 n.succ = if n.val ≤ a.val.1.val then g n else 0 := by
    simp [chainCell,cell_correct_label,chain_cell_zero,hn1,hn2]
  rw [hfirst]
  refine Fin.cases ?_ (fun m => ?_) r
  · simp only [chainCell,cell_correct_zero,chain_cell_one, show ¬a.val.1.val < 0 by omega,show ¬a.val.1.val < 1 by omega,
      false_and,ite_false,Fin.reduceEq,add_zero]
    split_ifs
    · exact chain_single_late hL g S t hg hS ht n hn
    · exact two_late_subset _ ∅ (by simp) (by simp)
  · have hmiddle : chainCell hL g S t a 1 m.succ = if a.val.1.val < m.val ∧ m.val ≤ a.val.2.val then g m else 0 := by
      simp [chainCell,cell_correct_label,chain_cell_one, show ¬a.val.1.val < 0 by omega,show ¬a.val.1.val < 1 by omega]
    rw [hmiddle]
    split_ifs with hni hmi hmi
    · exact chain_two_late hL g S t hg hS ht n m hn (by omega) (by intro h; subst m; omega)
    · simpa using chain_single_late hL g S t hg hS ht n hn
    · simpa using chain_single_late hL g S t hg hS ht m (by omega)
    · simpa using two_late_subset (balancedChain hL g S t hg hS ht) ∅ (by simp) (by simp)

private theorem table_score_bound {L : ℕ} (hL : 3 ≤ L) (g : Fin L → ℝ) (S t B : ℝ) (hg : ∀ i, 0 ≤ g i) (hS : 0 ≤ S) (ht : 0 ≤ t)
    (hhigh : latePeak (balancedChain hL g S t hg hS ht) ≤ t) (hW : g ⟨0,by omega⟩ + g ⟨1,by omega⟩ + S + t ≤ B)
    (hX0 : g ⟨0,by omega⟩ + balancedSplit (g ⟨0,by omega⟩) (g ⟨1,by omega⟩) S + latePeak (balancedChain hL g S t hg hS ht) + t ≤ B)
    (hX1 : g ⟨1,by omega⟩ + (S-balancedSplit (g ⟨0,by omega⟩) (g ⟨1,by omega⟩) S) + latePeak (balancedChain hL g S t hg hS ht) + t ≤ B)
    (hP : S + latePeak (balancedChain hL g S t hg hS ht) + t ≤ B) (hTwo : twoLate (balancedChain hL g S t hg hS ht) + t ≤ B)
    (a : Pair L) (labels : Labels (Fin (L + 1))) :
    score (balancedChain hL g S t hg hS ht) (table (.inr (.inr a)) labels).val ≤ B := by
  rw [table_score_cells]
  have hlast := last_cell_le hL g S t hg hS ht a hhigh labels.2.2
  by_cases hi : a.val.1.val = 0
  · have hfirst := head_first_cell_le hL g S t hg hS a hi labels.1
    rcases head_middle_cell_le hL g S t hg hS ht a hi labels.2.1 with hmid | hmid
    · linarith
    · linarith
  · have hi' : 1 ≤ a.val.1.val := by omega
    have hmid := middle_cell_le hL g S t hg hS ht a hi' labels.2.1
    have hs := balanced_split_spec _ _ S (hg ⟨0,by omega⟩) (hg ⟨1,by omega⟩) hS
    refine Fin.cases ?_ (fun n => ?_) labels.1
    · have he : chainCell hL g S t a 0 0 = S := by
        simp [chainCell,cell_correct_zero,chain_cell_zero,hi']
      rw [he]
      linarith
    · by_cases hn0 : n.val = 0
      · have he : n = (⟨0,by omega⟩ : Fin L) := Fin.ext hn0
        rw [he]
        have he : chainCell hL g S t a 0 (⟨0,by omega⟩ : Fin L).succ = g ⟨0,by omega⟩ + balancedSplit (g ⟨0,by omega⟩) (g ⟨1,by omega⟩) S := by
          rw [chainCell,cell_correct_label]
          simp [chain_cell_zero,succ_zero_label hL,early_labels_distinct hL,early_one_ne_zero hL]
        rw [he]
        linarith
      · by_cases hn1 : n.val = 1
        · have he : n = (⟨1,by omega⟩ : Fin L) := Fin.ext hn1
          rw [he]
          have he : chainCell hL g S t a 0 (⟨1,by omega⟩ : Fin L).succ = g ⟨1,by omega⟩ + (S-balancedSplit (g ⟨0,by omega⟩) (g ⟨1,by omega⟩) S) := by
            rw [chainCell,cell_correct_label]
            simp [chain_cell_zero,hi',succ_one_label hL,early_two_ne_zero hL,Ne.symm (early_labels_distinct hL)]
          rw [he]
          linarith
        · have hb := late_first_two_le hL g S t hg hS ht a hi' n (by omega) labels.2.1
          linarith
private theorem full_view_determines (stop : Bool) (xs : List ℕ) (q r : ℕ → Bool)
    (h : view false xs q = view false xs r) : view stop xs q = view stop xs r := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      have hh : q i = r i := (List.cons.inj h).1
      have ht : view false xs q = view false xs r := (List.cons.inj h).2
      simp only [view,hh,ih ht]

private theorem stopped_support_le_full {L : ℕ} (y : FullScore L) : support true y ≤ support false y := by
  unfold support
  apply Finset.sup'_le
  intro f _
  obtain ⟨xs,hlen,hlow,_,hf⟩ := f.property
  let g : Catalog false L := ⟨f.val,⟨xs,hlen,hlow,by simp, fun b c h => hf b c (full_view_determines true xs _ _ h)⟩⟩
  exact score_le_support false y g

private theorem chain_support_upper {L : ℕ} (hL : 3 ≤ L) (g : Fin L → ℝ) (S t : ℝ) (hg : ∀ i, 0 ≤ g i) (hS : 0 ≤ S) (ht : 0 ≤ t)
    (hhigh : latePeak (balancedChain hL g S t hg hS ht) ≤ t) (stop : Bool) :
    delta hL stop (balancedChain hL g S t hg hS ht) ≤ max (highLower hL (balancedChain hL g S t hg hS ht))
        (latePeak (balancedChain hL g S t hg hS ht) - early hL (balancedChain hL g S t hg hS ht)) := by
  let y := balancedChain hL g S t hg hS ht
  let D := max (highLower hL y) (latePeak y - early hL y)
  have he : early hL y = g ⟨0,by omega⟩ + g ⟨1,by omega⟩ := by
    simp [y,early,chain_gamma]
  have hpair : pairTotal y = S := chain_pair_total hL g S t hg hS ht
  have hw : inputAnchor hL y = g ⟨0,by omega⟩ + g ⟨1,by omega⟩ + S + t := by
    unfold inputAnchor
    rw [he,hpair]
    rfl
  have hd0 : 0 ≤ D := (le_max_left 0 _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hd2 : twoLate y - early hL y - S ≤ D := by
    have h : twoLate y - early hL y - pairTotal y ≤ highLower hL y := (le_max_right _ _).trans (le_max_left _ _)
    rw [hpair] at h
    exact h.trans (le_max_left _ _)
  have hdm : latePeak y - earlyCapacity hL y ≤ D := (le_max_right _ _).trans (le_max_left _ _)
  have hde : latePeak y - early hL y ≤ D := le_max_right _ _
  have hc : min (g ⟨0,by omega⟩ + balancedSplit (g ⟨0,by omega⟩) (g ⟨1,by omega⟩) S)
      (g ⟨1,by omega⟩ + (S-balancedSplit (g ⟨0,by omega⟩) (g ⟨1,by omega⟩) S)) = earlyCapacity hL y := by
    rw [(balanced_split_spec _ _ S (hg ⟨0,by omega⟩) (hg ⟨1,by omega⟩) hS).2.2]
    simp [earlyCapacity,he,hpair,y,chain_gamma]
  have hc0 := min_le_left (g ⟨0,by omega⟩ + balancedSplit (g ⟨0,by omega⟩) (g ⟨1,by omega⟩) S)
    (g ⟨1,by omega⟩ + (S-balancedSplit (g ⟨0,by omega⟩) (g ⟨1,by omega⟩) S))
  have hc1 := min_le_right (g ⟨0,by omega⟩ + balancedSplit (g ⟨0,by omega⟩) (g ⟨1,by omega⟩) S)
    (g ⟨1,by omega⟩ + (S-balancedSplit (g ⟨0,by omega⟩) (g ⟨1,by omega⟩) S))
  rw [hc] at hc0 hc1
  have hb : support stop y ≤ inputAnchor hL y + D := by
    unfold support
    apply Finset.sup'_le
    intro f _
    obtain ⟨a,labels,hrows,hterminal⟩ := chain_represented hL stop f
    have hscore : score y f.val = score y (table (.inr (.inr a)) labels).val := by
      rw [chain_score,chain_score]
      have hzero := hrows (⟨0,by omega⟩ : Fin L)
      have hone := hrows (⟨1,by omega⟩ : Fin L)
      simp only [hrows,hzero,hone,hterminal]
    rw [hscore]
    apply table_score_bound hL g S t (inputAnchor hL y+D) hg hS ht hhigh
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
  change support stop y - inputAnchor hL y ≤ D
  linarith

private theorem chain_peak_excess_lower {L : ℕ} (hL : 3 ≤ L) (g : Fin L → ℝ) (S t : ℝ) (hg : ∀ i, 0 ≤ g i) (hS : 0 ≤ S) (ht : 0 ≤ t) :
    latePeak (balancedChain hL g S t hg hS ht) - early hL (balancedChain hL g S t hg hS ht) ≤ delta hL true (balancedChain hL g S t hg hS ht) := by
  let y := balancedChain hL g S t hg hS ht
  have he : 0 ≤ early hL y := add_nonneg (gamma_nonneg _ _) (gamma_nonneg _ _)
  have hd : 0 ≤ delta hL true y := by
    have h := arbitrary_input_lower_bound hL y (chain_early_pair hL g S t hg hS ht)
    have h0 : 0 ≤ highLower hL y := (le_max_left _ _).trans (le_max_left _ _)
    exact h0.trans h
  have hp : pairTotal y = S := chain_pair_total hL g S t hg hS ht
  have each (j : Fin L) (hj : 2 ≤ j.val) : gamma y j ≤ early hL y + delta hL true y := by
    let a : Pair L := ⟨(⟨1,by omega⟩,j),by change 1<j.val; omega⟩
    let f := table (.inr (.inr a)) (0,j.succ,0)
    have hsum : g j ≤ ∑ n, if f.val (chainWord L n.val) = n.succ then g n else 0 := by
      have h := Finset.single_le_sum (f := fun n : Fin L =>
        if f.val (chainWord L n.val) = n.succ then g n else 0)
        (fun n _ => by split <;> simp [hg]) (Finset.mem_univ j)
      simpa [f,table,cell,label,a,chainWord,show 1<j.val by omega] using h
    have hscore := score_le_support true y f
    rw [chain_score] at hscore
    have hfirst : f.val (chainWord L 0) = 0 := by simp [f,table,cell,label,a,chainWord]
    have hsecond : f.val (chainWord L 1) = 0 := by simp [f,table,cell,label,a,chainWord]
    have hend : f.val (fun _ => true) = 0 := by simp [f,table,cell,label,a]
    simp only [hfirst,hsecond,hend,true_or,ite_true] at hscore
    have hgJ : gamma y j = g j := chain_gamma hL g S t hg hS ht j
    change gamma y j ≤ early hL y + (support true y-inputAnchor hL y)
    have hw : inputAnchor hL y = early hL y + S + t := by
      unfold inputAnchor
      rw [hp]
      rfl
    linarith
  have hpeak : latePeak y ≤ early hL y + delta hL true y := by
    unfold latePeak
    apply Finset.sup'_le
    intro o _
    cases o with
    | none => simp only [Option.elim_none]; linarith
    | some j =>
      simp only [Option.elim_some]
      split_ifs with hj
      · exact each j hj
      · linarith
  change latePeak y - early hL y ≤ delta hL true y
  linarith

/-- The native balanced chain preserves the complete coefficient data and has
exactly the same complete N and O excess throughout the high-terminal slice. -/
theorem balanced_chain_exact {L : ℕ} (hL : 3 ≤ L) (g : Fin L → ℝ) (S t : ℝ) (hg : ∀ i, 0 ≤ g i) (hS : 0 ≤ S) (ht : 0 ≤ t)
    (hhigh : latePeak (balancedChain hL g S t hg hS ht) ≤ t) :
    let V := balancedChain hL g S t hg hS ht
    beta V = g ∧ coefficientMass V = (∑ i, g i) + S + t ∧ pairTotal V = S ∧ inputAnchor hL V = g ⟨0,by omega⟩ + g ⟨1,by omega⟩ + S + t ∧
      EarlyPair V ∧ (∀ i, gamma V i = g i) ∧
      delta hL false V = max (highLower hL V) (latePeak V - early hL V) ∧
      delta hL true V = max (highLower hL V) (latePeak V - early hL V) := by
  dsimp only
  let V := balancedChain hL g S t hg hS ht
  have hP : EarlyPair V := chain_early_pair hL g S t hg hS ht
  have hlo : max (highLower hL V) (latePeak V - early hL V) ≤ delta hL true V := by
    apply max_le
    · exact arbitrary_input_lower_bound hL V hP
    · exact chain_peak_excess_lower hL g S t hg hS ht
  have hmono : delta hL true V ≤ delta hL false V := by
    exact sub_le_sub_right (stopped_support_le_full V) _
  refine ⟨chain_beta hL g S t hg hS ht,chain_coefficient_mass hL g S t hg hS ht,
    chain_pair_total hL g S t hg hS ht,?_,hP,chain_gamma hL g S t hg hS ht,?_,?_⟩
  · simp only [inputAnchor,early,chain_gamma,chain_pair_total]
    rfl
  · exact le_antisymm (chain_support_upper hL g S t hg hS ht hhigh false) (hlo.trans hmono)
  · exact le_antisymm (chain_support_upper hL g S t hg hS ht hhigh true) hlo

#print axioms balanced_chain_exact
private theorem total_gamma {L : ℕ} (y : FullScore L) : (∑ i, gamma y i) = ∑ b, y.C b := by
  classical
  let z : FullScore L := { y with P := fun _ => 0, nonnegP := fun _ => le_rfl, terminalP := rfl }
  calc
    (∑ i, gamma y i) = ∑ b, ∑ i, numerical z i b := by
      simp only [gamma, numerical, z, add_zero]
      exact Finset.sum_comm
    _ = ∑ b, y.C b := by
      simp_rw [numerical_total]
      simp only [z, add_zero]

/-- The chain gives an actual same-Q, same-anchor comparison on precisely the
source branch mu <= E + DeltaO; the complementary branch is not asserted here. -/
theorem balanced_chain_comparison {L : ℕ} (hL : 3 ≤ L) (y : FullScore L) (hA : ∀ b, y.A b = 0) (hP : EarlyPair y) (hhigh : latePeak y ≤ y.T)
    (hbranch : latePeak y ≤ early hL y + delta hL true y) :
    ∃ V : FullScore L, (∀ b, V.A b = 0) ∧ EarlyPair V ∧ beta V = beta y ∧
      coefficientMass V = coefficientMass y ∧ inputAnchor hL V = inputAnchor hL y ∧
      delta hL false V ≤ delta hL true y := by
  have hS : 0 ≤ pairTotal y := Finset.sum_nonneg (fun b _ => y.nonnegP b)
  let V := balancedChain hL (gamma y) (pairTotal y) y.T (gamma_nonneg y) hS y.nonnegT
  have hgamma : ∀ i, gamma V i = gamma y i := chain_gamma hL (gamma y) (pairTotal y) y.T (gamma_nonneg y) hS y.nonnegT
  have hpairs : pairTotal V = pairTotal y := chain_pair_total hL (gamma y) (pairTotal y) y.T (gamma_nonneg y) hS y.nonnegT
  have hpeak : latePeak V = latePeak y := by simp only [latePeak,hgamma]
  have htwo : twoLate V = twoLate y := by simp only [twoLate,hgamma]
  have he : early hL V = early hL y := by simp only [early,hgamma]
  have hcap : earlyCapacity hL V = earlyCapacity hL y := by
    simp only [earlyCapacity,he,hpairs,hgamma]
  have hlow : highLower hL V = highLower hL y := by
    simp only [highLower,htwo,he,hpairs,hpeak,hcap]
  have hx := balanced_chain_exact hL (gamma y) (pairTotal y) y.T (gamma_nonneg y) hS
    y.nonnegT (by change latePeak V ≤ y.T; rw [hpeak]; exact hhigh)
  change beta V = gamma y ∧ coefficientMass V = (∑ i, gamma y i) + pairTotal y + y.T ∧
      pairTotal V = pairTotal y ∧ inputAnchor hL V = _ ∧ EarlyPair V ∧
      (∀ i, gamma V i = gamma y i) ∧ _ at hx
  have hb : beta y = gamma y := by
    funext i
    simp only [beta,gamma,hA,sub_zero]
  have hm : coefficientMass y = (∑ i, gamma y i) + pairTotal y + y.T := by
    rw [total_gamma]
    simp only [coefficientMass,hA,zero_add,Finset.sum_add_distrib,pairTotal]
  refine ⟨V,(by intro b; rfl),hx.2.2.2.2.1,hx.1.trans hb.symm,hx.2.1.trans hm.symm,?_,?_⟩
  · simpa only [inputAnchor,early] using hx.2.2.2.1
  · rw [hx.2.2.2.2.2.2.1,hlow,hpeak,he]
    exact max_le (arbitrary_input_lower_bound hL y hP) (by linarith)

#print axioms balanced_chain_comparison

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain
