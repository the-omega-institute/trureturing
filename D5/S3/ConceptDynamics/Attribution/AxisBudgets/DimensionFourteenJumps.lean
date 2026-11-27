/- GID: D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionFourteenJumps
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionFourteenJumps
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: An optimal-size fourteen-coordinate budget needs two ordinary rank jumps. -/

import D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteCapacity
import D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteDiagonalParity
import D5.S3.Combinatorics.Graph.RankCuts.RankedIntervalParity
import D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

/-! A saturated capacity lower bound forces the rank-cut pattern odd, even, odd. -/

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionFourteenJumps

open Finset
open D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteCapacity
open D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteDiagonalParity
open D5.S3.Combinatorics.Graph.RankCuts.RankedIntervalParity
open D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor
open D5.S3.ConceptDynamics.Attribution.ParitySeedFactor

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ordinary selected edges with at least one rank strictly between their endpoints. -/
def rankJumps (rank : V → ℕ) (top : V) (edge : V → V → Bool) : Finset (V × V) :=
  univ.filter fun (a, b) => a ≠ top ∧ rank a + 1 < rank b ∧ edge a b = true

private def crosses (rank : V → ℕ) (r : ℕ) (e : V × V) : Prop :=
  rank e.1 < r ∧ r < rank e.2

private instance (rank : V → ℕ) (r : ℕ) : DecidablePred (crosses rank r) :=
  fun e => inferInstanceAs (Decidable (rank e.1 < r ∧ r < rank e.2))

private theorem two_jumps_from_three_cuts {V : Type*} [DecidableEq V]
    (rank : V → ℕ) (jumps : Finset (V × V))
    (first : (jumps.filter (fun edge => rank edge.1 < 5 ∧ 5 < rank edge.2)).card % 2 = 1)
    (middle : (jumps.filter (fun edge => rank edge.1 < 7 ∧ 7 < rank edge.2)).card % 2 = 0)
    (last : (jumps.filter (fun edge => rank edge.1 < 9 ∧ 9 < rank edge.2)).card % 2 = 1) :
    2 ≤ jumps.card := by
  let cuts : Fin 3 → ℕ := ![5, 7, 9]
  let lo : (↑jumps : Type _) → ℕ := fun i => rank i.val.1
  let hi : (↑jumps : Type _) → ℕ := fun i => rank i.val.2
  have monotone : Monotone cuts := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [cuts]
  have interior (slot : ℕ) (h : 0 < slot ∧ slot ≤ 3) :
      paddedParity cuts lo hi slot =
        (jumps.filter (fun edge => rank edge.1 < cuts ⟨slot - 1, by omega⟩ ∧
          cuts ⟨slot - 1, by omega⟩ < rank edge.2)).card % 2 := by
    rw [paddedParity, dite_eq_left h]
    congr 1
    rw [card_filter]
    symm
    exact Finset.sum_subtype jumps (fun _ => Iff.rfl) _
  have p0 : paddedParity cuts lo hi 0 = 0 := rfl
  have p1 : paddedParity cuts lo hi 1 = 1 := by
    have h := interior 1 (by decide)
    have value : cuts ⟨1 - 1, by decide⟩ = 5 := by decide
    rw [value] at h
    exact h.trans first
  have p2 : paddedParity cuts lo hi 2 = 0 := by
    have h := interior 2 (by decide)
    have value : cuts ⟨2 - 1, by decide⟩ = 7 := by decide
    rw [value] at h
    exact h.trans middle
  have p3 : paddedParity cuts lo hi 3 = 1 := by
    have h := interior 3 (by decide)
    have value : cuts ⟨3 - 1, by decide⟩ = 9 := by decide
    rw [value] at h
    exact h.trans last
  have p4 : paddedParity cuts lo hi 4 = 0 := rfl
  have bound := changes_le_twice_jumps cuts monotone lo hi
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Fintype.card_coe] at bound
  norm_num [p0, p1, p2, p3, p4] at bound
  omega


private def layer (rank : V → ℕ) (r : ℕ) := univ.filter fun a => rank a = r

private def inflow (rank : V → ℕ) (top : V) (edge : V → V → ℕ) (r : ℕ) :=
  ∑ b ∈ univ.filter (fun a => rank a ≤ r), edge top b

private def bypass (rank : V → ℕ) (edge : V → V → ℕ) (r : ℕ) :=
  ∑ a ∈ univ.filter (fun a => rank a < r),
    ∑ b ∈ univ.filter (fun b => r < rank b), edge a b

private def diagonal (rank : V → ℕ) (edge : V → V → ℕ) (r : ℕ) :=
  ∑ a ∈ layer rank r, edge a a

omit [DecidableEq V] in
private theorem inflow_mono (rank : V → ℕ) (top : V) (edge : V → V → ℕ) :
    Monotone (inflow rank top edge) := by
  intro r s hr
  apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.zero_le _)
  intro b hb
  simp only [mem_filter, mem_univ, true_and] at hb ⊢
  exact hb.trans hr

private theorem sum_diagonal_le_charge (rank : V → ℕ) (top : V) (edge : V → V → ℕ)
    (ranks : Finset ℕ) (selected : ∀ r ∈ ranks, r < rank top ∧ r % 2 = 1) :
    (∑ r ∈ ranks, diagonal rank edge r) ≤
      ∑ a, ∑ b, if a ≠ top ∧ rank a % 2 = 1 ∧ rank b % 2 = 1 then edge a b else 0 := by
  unfold diagonal layer
  rw [sum_fiberwise_eq_sum_filter, sum_filter]
  refine sum_le_sum fun a _ => ?_
  by_cases ha : rank a ∈ ranks
  · have htop : a ≠ top := fun h => by
      subst a
      exact (Nat.lt_irrefl _) (selected _ ha).1
    simpa [ha, htop, (selected _ ha).2] using
      (single_le_sum
        (f := fun b => if a ≠ top ∧ rank a % 2 = 1 ∧ rank b % 2 = 1 then edge a b else 0)
        (fun _ _ => Nat.zero_le _) (mem_univ a))
  · simp [ha]

private theorem bypass_eq_jump_count (rank : V → ℕ) (top : V) (edge : V → V → Bool)
    (r : ℕ) (hr : r < rank top) :
    bypass rank (fun a b => (edge a b).toNat) r =
      ((rankJumps rank top edge).filter (crosses rank r)).card := by
  unfold bypass rankJumps
  rw [filter_filter, card_filter, Fintype.sum_prod_type]
  simp only [sum_filter]
  refine sum_congr rfl fun a _ => ?_
  by_cases ha : rank a < r
  · simp only [ha, ite_true]
    refine sum_congr rfl fun b _ => ?_
    by_cases hb : r < rank b
    · have htop : a ≠ top := fun he => by rw [he] at ha; omega
      have hspan : rank a + 1 < rank b := by omega
      by_cases h : edge a b = true
      · simp [crosses, ha, hb, htop, hspan, h]
      · have hf : edge a b = false := Bool.eq_false_of_not_eq_true h
        simp [crosses, ha, hb, htop, hspan, hf]
    · simp [crosses, hb]
  · simp [crosses, ha]

/-- A saturated set of three layers leaves no diagonal charge at the three intervening ranks. -/
private theorem two_jumps_of_saturation (rank : V → ℕ) (top : V) (f : V → V → Bool)
    (e : V → V → ℕ) (he : e = fun a b => (f a b).toNat)
    (topRank : rank top = 13)
    (ordered : ∀ a b, a ≠ top → e a b ≠ 0 → a = b ∨ rank a < rank b)
    (rowOdd : ∀ a ≠ top, (∑ b, e a b) % 2 = 1)
    (colOdd : ∀ b ≠ top, (∑ a, e a b) % 2 = 1)
    (rowTop : (∑ b, e top b) ≤ 2)
    (low : 11 ≤ diagonal rank e 1 + inflow rank top e 1)
    (mid : 100 ≤ diagonal rank e 3)
    (high : 50 ≤ diagonal rank e 11)
    (count5 : (layer rank 5).card % 2 = 1)
    (count7 : (layer rank 7).card % 2 = 0)
    (count9 : (layer rank 9).card % 2 = 1)
    (paid : (∑ a, ∑ b, if a ≠ top ∧ rank a % 2 = 1 ∧ rank b % 2 = 1 then e a b else 0) ≤ 159) :
    2 ≤ (rankJumps rank top f).card := by
  have hsum := (sum_diagonal_le_charge rank top e {1, 3, 5, 7, 9, 11}
    (by intro r hr; simp only [mem_insert, mem_singleton] at hr
        rcases hr with h | h | h | h | h | h <;> simp [h, topRank])).trans paid
  have hsum' : diagonal rank e 1 + diagonal rank e 3 + diagonal rank e 5 +
      diagonal rank e 7 + diagonal rank e 9 + diagonal rank e 11 ≤ 159 := by
    simpa [sum_insert, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsum
  have cap (r : ℕ) : inflow rank top e r ≤ 2 := by
    apply le_trans (b := ∑ b, e top b) _ rowTop
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
  have at1 : inflow rank top e 1 = 2 := by have := cap 1; omega
  have d5 : diagonal rank e 5 = 0 := by omega
  have d7 : diagonal rank e 7 = 0 := by omega
  have d9 : diagonal rank e 9 = 0 := by omega
  have saturated (r : ℕ) (h : 1 ≤ r) : inflow rank top e r = 2 := by
    have := inflow_mono rank top e h
    have := cap r
    omega
  have parity (r : ℕ) (hr : r < 13) : diagonal rank e r % 2 =
      ((layer rank r).card + inflow rank top e r + bypass rank e r) % 2 := by
    apply diagonal_parity rank top r e (by omega) ordered
    · intro a ha
      apply rowOdd a
      have ha' : rank a ≤ r := (mem_filter.mp ha).2
      intro h
      rw [h, topRank] at ha'
      omega
    · intro b hb
      apply colOdd b
      have hb' : rank b ≤ r := (mem_filter.mp hb).2
      intro h
      rw [h, topRank] at hb'
      omega
  have odd5 : bypass rank e 5 % 2 = 1 := by
    have p := parity 5 (by decide)
    rw [d5, saturated 5 (by decide)] at p
    omega
  have even7 : bypass rank e 7 % 2 = 0 := by
    have p := parity 7 (by decide)
    rw [d7, saturated 7 (by decide)] at p
    omega
  have odd9 : bypass rank e 9 % 2 = 1 := by
    have p := parity 9 (by decide)
    rw [d9, saturated 9 (by decide)] at p
    omega
  apply two_jumps_from_three_cuts rank (rankJumps rank top f)
  · rw [he, bypass_eq_jump_count rank top _ _ (by omega)] at odd5
    exact odd5
  · rw [he, bypass_eq_jump_count rank top _ _ (by omega)] at even7
    exact even7
  · rw [he, bypass_eq_jump_count rank top _ _ (by omega)] at odd9
    exact odd9

private theorem subset_top (i : Fin 14) (A : AxisSubset 14 i) : A.val ⊆ (axisTop i).val :=
  fun j hj => mem_erase.mpr ⟨fun h => A.property (h ▸ hj), mem_univ j⟩

private theorem top_card (i : Fin 14) : (axisTop i).val.card = 13 := by
  unfold axisTop
  simp [Finset.card_erase_of_mem (mem_univ i)]

private theorem subset_layer_count (i : Fin 14) (r : ℕ) :
    (layer (fun A : AxisSubset 14 i => A.val.card) r).card = Nat.choose 13 r := by
  rw [← top_card i, ← card_powersetCard r (axisTop i).val]
  refine card_bij (fun A _ => A.val) ?_ ?_ ?_
  · intro A hA
    exact mem_powersetCard.mpr ⟨subset_top i A, (mem_filter.mp hA).2⟩
  · intro A _ B _ h
    exact Subtype.ext h
  · intro B hB
    obtain ⟨included, size⟩ := mem_powersetCard.mp hB
    have outside : i ∉ B := fun h => (axisTop i).property (included h)
    exact ⟨⟨B, outside⟩, mem_filter.mpr ⟨mem_univ _, size⟩, rfl⟩



private theorem chosen_rank_count (i : Fin 14) (S : Finset ℕ) :
    (univ.filter (fun A : AxisSubset 14 i => A.val.card ∈ S)).card
      = ∑ s ∈ S, Nat.choose 13 s := by
  rw [← sum_card_fiberwise_eq_card_filter (univ : Finset (AxisSubset 14 i)) S
    (fun A => A.val.card)]
  apply sum_congr rfl
  intro r _
  exact subset_layer_count i r

private theorem rank_lt_top_iff (i : Fin 14) (A : AxisSubset 14 i) :
    A.val.card < 13 ↔ A ≠ axisTop i := by
  constructor
  · intro h he
    simp [he, top_card] at h
  · intro h
    rw [← top_card i]
    apply card_lt_card
    exact (ssubset_iff_subset_ne).mpr ⟨subset_top i A, fun he => h (Subtype.ext he)⟩


/-- A factor on the fourteen-coordinate lattice with budget at most 640 needs two rank jumps. -/
theorem two_jumps_at_640 (i : Fin 14)
    (f : AxisSubset 14 i → AxisSubset 14 i → Bool)
    (selected : Bool)
    (row : ∀ A, residualDegree 3 selected (decide (A = axisTop i))
      (∑ B, (f A B).toNat))
    (col : ∀ B, residualDegree 3 selected (decide (B = axisTop i))
      (∑ A, (f A B).toNat))
    (support : ∀ A B, A ≠ axisTop i → f A B = true → A.val ⊆ B.val)
    (cost : axisCost i f ≤ 640) :
    2 ≤ (rankJumps (fun A => A.val.card) (axisTop i) f).card := by
  let ρ (A : AxisSubset 14 i) := A.val.card
  let t := axisTop i
  let e (A B : AxisSubset 14 i) : ℕ := (f A B).toNat
  have ht : ρ t = 13 := top_card i
  have eligible : ∀ r < 13, r < ρ t := by omega
  have ordered (A B : AxisSubset 14 i) (ha : A ≠ t) (he : e A B ≠ 0) :
      A = B ∨ ρ A < ρ B := by
    by_cases hab : A = B
    · exact Or.inl hab
    · have h : f A B = true := by cases h : f A B <;> simp_all [e]
      exact Or.inr (card_lt_card ((ssubset_iff_subset_ne).mpr
        ⟨support A B ha h, fun heq => hab (Subtype.ext heq)⟩))
  have ordinary_degree (d : ℕ) (h : residualDegree 3 selected false d) :
      1 ≤ d ∧ d ≤ 3 ∧ d % 2 = 1 := by
    have odd : d % 2 = 1 := by simpa [residualDegree] using h.2
    exact ⟨by omega, by simpa [residualDegree] using h.1, odd⟩
  have top_degree (d : ℕ) (h : residualDegree 3 selected true d) :
      d ≤ 2 := by
    cases hs : selected
    · have hcap : d ≤ 1 := by simpa [residualDegree, hs] using h.1
      exact hcap.trans (by decide)
    · simpa [residualDegree, hs] using h.1
  have row_o (A : AxisSubset 14 i) (ha : A ≠ t) :=
    ordinary_degree (∑ B, e A B) (by
      have hA : A ≠ axisTop i := ha
      simpa [hA, e] using row A)
  have col_o (B : AxisSubset 14 i) (hb : B ≠ t) :=
    ordinary_degree (∑ A, e A B) (by
      have hB : B ≠ axisTop i := hb
      simpa [hB, e] using col B)
  have row_cap : (∑ B, e t B) ≤ 2 :=
    top_degree _ (by simpa only [t, e, decide_true, eq_self] using row t)
  have col_cap : (∑ A, e A t) ≤ 2 :=
    top_degree _ (by simpa only [t, e, decide_true, eq_self] using col t)
  let L (r : ℕ) := (univ.filter (fun A : AxisSubset 14 i => ρ A ≤ r)).card
  let Ls (r : ℕ) := (univ.filter (fun A : AxisSubset 14 i => ρ A < r)).card
  let H (r : ℕ) := (univ.filter (fun A : AxisSubset 14 i => r ≤ ρ A ∧ A ≠ t)).card
  let Hs (r : ℕ) := (univ.filter (fun A : AxisSubset 14 i => r < ρ A ∧ A ≠ t)).card
  have hs (r : ℕ) : ((univ.filter (fun A : AxisSubset 14 i => r < ρ A)).erase t).card = Hs r := by
    congr 1
    ext A
    simp [and_comm]
  have l_count (r : ℕ) : L r = ∑ s ∈ range (r + 1), Nat.choose 13 s := by
    simpa [L, ρ, Nat.lt_succ_iff] using chosen_rank_count i (range (r + 1))
  have ls_count (r : ℕ) : Ls r = ∑ s ∈ range r, Nat.choose 13 s := by
    simpa [Ls, ρ] using chosen_rank_count i (range r)
  have h_count (r : ℕ) : H r = ∑ s ∈ (range 13).filter (r ≤ ·), Nat.choose 13 s := by
    simpa [H, ρ, t, ← rank_lt_top_iff i, and_comm] using
      chosen_rank_count i ((range 13).filter (r ≤ ·))
  have hs_count (r : ℕ) : Hs r = ∑ s ∈ (range 13).filter (r < ·), Nat.choose 13 s := by
    simpa [Hs, ρ, t, ← rank_lt_top_iff i, and_comm] using
      chosen_rank_count i ((range 13).filter (r < ·))
  let G (r : ℕ) : ℕ := ∑ a ∈ univ.filter (fun A : AxisSubset 14 i => r ≤ ρ A ∧ A ≠ t), e a t
  have gcap (r : ℕ) : G r ≤ 2 :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)).trans col_cap
  have fcap (r : ℕ) : inflow ρ t e r ≤ 2 :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)).trans row_cap
  have bound (r : ℕ) (hr : r < 13) :
      max (L r - (Ls r * 3 + inflow ρ t e r)) (H r - (Hs r * 3 + G r)) ≤ diagonal ρ e r := by
    rw [← hs]
    exact two_sided_rank_capacity ρ t r 3 e (eligible r hr) ordered
      (fun A ha => (row_o A ha).1) (fun B hb => (col_o B hb).1)
      (fun A ha => (row_o A ha).2.1) (fun B hb => (col_o B hb).2.1)
  have low : 11 ≤ diagonal ρ e 1 + inflow ρ t e 1 := by
    have h := (le_max_left _ _).trans (bound 1 (by decide))
    rw [l_count, ls_count] at h
    have hL : (∑ s ∈ range (1 + 1), Nat.choose 13 s) = 14 := by decide
    have hLs : (∑ s ∈ range 1, Nat.choose 13 s) = 1 := by decide
    rw [hL, hLs] at h
    omega
  have mid : 100 ≤ diagonal ρ e 3 := by
    have h := (le_max_left _ _).trans (bound 3 (by decide))
    rw [l_count, ls_count] at h
    have hL : (∑ s ∈ range (3 + 1), Nat.choose 13 s) = 378 := by decide
    have hLs : (∑ s ∈ range 3, Nat.choose 13 s) = 92 := by decide
    rw [hL, hLs] at h
    have := fcap 3
    omega
  have high : 50 ≤ diagonal ρ e 11 := by
    have h := (le_max_right _ _).trans (bound 11 (by decide))
    rw [h_count, hs_count] at h
    have hH : (∑ s ∈ (range 13).filter (11 ≤ ·), Nat.choose 13 s) = 91 := by decide
    have hHs : (∑ s ∈ (range 13).filter (11 < ·), Nat.choose 13 s) = 13 := by decide
    rw [hH, hHs] at h
    have := gcap 11
    omega
  have count (r : ℕ) : (layer ρ r).card = Nat.choose 13 r := subset_layer_count i r
  unfold axisCost at cost
  apply two_jumps_of_saturation ρ t f e rfl ht ordered
    (fun A ha => (row_o A ha).2.2) (fun B hb => (col_o B hb).2.2) row_cap low mid high
  · rw [count]
    decide
  · rw [count]
    decide
  · rw [count]
    decide
  · change 4 * (1 + ∑ A, ∑ B, if A ≠ t ∧ ρ A % 2 = 1 ∧ ρ B % 2 = 1 then e A B else 0) ≤ 640 at cost
    omega

end D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionFourteenJumps
