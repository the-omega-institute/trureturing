/- GID: D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteenCovers
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteenCovers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rank capacities and diagonal parity give the two sixteen-coordinate budget bounds. -/

import D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor
import D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteDiagonalParity
import D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteCapacity
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteenCovers

namespace OmegaAxisEndpointArithmeticTrial

/-- Capacity saturation and cut parity for inclusion covers. -/
private theorem cover_endpoint (d₁ d₃ d₅ d₇ d₉ d₁₁ d₁₃ f₁ f₃ f₅ f₇ f₉ : ℕ)
    (h₁ : 13 ≤ d₁ + f₁) (h₃ : 213 ≤ d₃ + f₃)
    (h₁₁ : 213 ≤ d₁₁) (h₁₃ : 73 ≤ d₁₃)
    (h₁₃' : f₁ ≤ f₃) (h₃₅ : f₃ ≤ f₅) (h₅₇ : f₅ ≤ f₇) (h₇₉ : f₇ ≤ f₉)
    (cap : f₉ ≤ 2)
    (p₅ : d₅ % 2 = (1 + f₅) % 2)
    (p₇ : d₇ % 2 = (1 + f₇) % 2)
    (p₉ : d₉ % 2 = (1 + f₉) % 2) :
    510 ≤ d₁ + d₃ + d₅ + d₇ + d₉ + d₁₁ + d₁₃ ∧
      (d₁ + d₃ + d₅ + d₇ + d₉ + d₁₁ + d₁₃ ≤ 510 →
        f₁ = 1 ∧ f₉ = 1 ∧ d₁ = 12 ∧ d₃ = 212 ∧ d₁₁ = 213 ∧ d₁₃ = 73) := by
  by_cases hf : f₃ = 2
  · have d₅_pos : 1 ≤ d₅ := by omega
    have d₇_pos : 1 ≤ d₇ := by omega
    have d₉_pos : 1 ≤ d₉ := by omega
    exact ⟨by omega, fun h => by omega⟩
  · have lower₁ : 12 ≤ d₁ := by omega
    have lower₃ : 212 ≤ d₃ := by omega
    refine ⟨by omega, fun h => ?_⟩
    have hdiag₉ : d₉ = 0 := by omega
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

end OmegaAxisEndpointArithmeticTrial


namespace SixteenAdjacentRank

open Finset
open D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteDiagonalParity
open D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor

noncomputable section

section RankSums

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

private def layer (rank : V → ℕ) (r : ℕ) : Finset V :=
  univ.filter fun a => rank a = r

private def diag (rank : V → ℕ) (e : V → V → ℕ) (r : ℕ) : ℕ :=
  ∑ a ∈ layer rank r, e a a

private def up (rank : V → ℕ) (e : V → V → ℕ) (r : ℕ) : ℕ :=
  ∑ a ∈ layer rank r, ∑ b ∈ layer rank (r + 1), e a b

private def extra (rank : V → ℕ) (e : V → V → ℕ) (top : V) (r : ℕ) : ℕ :=
  ∑ b ∈ layer rank r, e top b

private def prev (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => u r

private theorem row_layer (rank : V → ℕ) (e : V → V → ℕ) (top : V)
    (cover : ∀ a b, a ≠ top → e a b ≠ 0 → a = b ∨ rank b = rank a + 1)
    (r : ℕ) (notTop : r ≠ rank top) :
    (∑ a ∈ layer rank r, ∑ b, e a b) = diag rank e r + up rank e r := by
  unfold diag up
  rw [← sum_add_distrib]
  refine sum_congr rfl fun a ha => ?_
  have hr : rank a = r := (mem_filter.mp ha).2
  have htop : a ≠ top := fun h => notTop (hr.symm.trans (congrArg rank h))
  calc
    (∑ b, e a b) = ∑ b, ((if b = a then e a b else 0) +
      if rank b = r + 1 then e a b else 0) := by
      refine sum_congr rfl fun b _ => ?_
      by_cases h : b = a
      · subst b
        simp [hr]
      · by_cases above : rank b = r + 1
        · simp [h, above]
        · have zero : e a b = 0 := by
            by_contra hn
            exact (cover a b htop hn).elim (fun he => h he.symm) (by simpa only [hr] using above)
          simp [zero, h, above]
    _ = _ := by simp [sum_add_distrib, layer, sum_filter]

private theorem col_parts (rank : V → ℕ) (e : V → V → ℕ) (top : V)
    (cover : ∀ a b, a ≠ top → e a b ≠ 0 → a = b ∨ rank b = rank a + 1)
    (b : V) (hb : b ≠ top) :
    (∑ a, e a b) = e b b + (∑ a, if a ≠ top ∧ rank b = rank a + 1 then e a b else 0) +
      e top b := by
  calc
    (∑ a, e a b) = ∑ a, (((if a = b then e a b else 0) +
      if a ≠ top ∧ rank b = rank a + 1 then e a b else 0) +
      if a = top then e a b else 0) := by
      refine sum_congr rfl fun a _ => ?_
      by_cases ha : a = top
      · subst a
        simp [hb.symm]
      · by_cases he : a = b
        · subst a
          simp [hb]
        · by_cases hr : rank b = rank a + 1
          · simp [ha, he, hr]
          · have hz : e a b = 0 := by
              by_contra h
              exact (cover a b ha h).elim he hr
            simp [hz]
    _ = _ := by simp [sum_add_distrib]

private theorem col_layer (rank : V → ℕ) (e : V → V → ℕ) (top : V)
    (cover : ∀ a b, a ≠ top → e a b ≠ 0 → a = b ∨ rank b = rank a + 1)
    (r : ℕ) (notTop : r ≠ rank top) (below : ∀ t, r = t + 1 → t ≠ rank top) :
    (∑ b ∈ layer rank r, ∑ a, e a b) =
      diag rank e r + prev (up rank e) r + extra rank e top r := by
  have parts : (∑ b ∈ layer rank r, ∑ a, e a b) =
      ∑ b ∈ layer rank r, (e b b +
        (∑ a, if a ≠ top ∧ rank b = rank a + 1 then e a b else 0) + e top b) := by
    refine sum_congr rfl fun b hb => ?_
    have hbr : rank b = r := (mem_filter.mp hb).2
    have hbTop : b ≠ top := fun h => notTop (hbr.symm.trans (congrArg rank h))
    exact col_parts rank e top cover b hbTop
  rw [parts]
  unfold diag extra
  simp only [sum_add_distrib, add_left_inj, add_right_inj]
  cases r with
  | zero =>
    simp only [prev]
    apply sum_eq_zero
    intro b hb
    have hr : rank b = 0 := (mem_filter.mp hb).2
    simp [hr]
  | succ r =>
    simp only [prev, up]
    rw [sum_comm (s := layer rank r) (t := layer rank (r + 1))]
    refine sum_congr rfl fun b hb => ?_
    have hr : rank b = r + 1 := (mem_filter.mp hb).2
    unfold layer
    rw [sum_filter]
    refine sum_congr rfl fun a _ => ?_
    by_cases ha : rank a = r
    · have htop : a ≠ top := fun h => below r rfl (ha.symm.trans (congrArg rank h))
      simp [hr, ha, htop]
    · simp [hr, ha, Ne.symm ha]

omit [DecidableEq V] in
private theorem sum_layer_lower (rank : V → ℕ) (e : V → ℕ) (r : ℕ)
    (positive : ∀ v ∈ layer rank r, 1 ≤ e v) :
    (layer rank r).card ≤ ∑ v ∈ layer rank r, e v := by
  simpa using sum_le_sum positive

omit [DecidableEq V] in
private theorem sum_layer_upper (rank : V → ℕ) (e : V → ℕ) (r cap : ℕ)
    (bounded : ∀ v ∈ layer rank r, e v ≤ cap) :
    (∑ v ∈ layer rank r, e v) ≤ (layer rank r).card * cap := by
  simpa [nsmul_eq_mul] using sum_le_sum bounded

omit [DecidableEq V] in
private theorem layers_covered (rank : V → ℕ) (v : V → ℕ) (ranks : Finset ℕ) :
    (∑ r ∈ ranks, ∑ a ∈ layer rank r, v a) ≤ ∑ a, v a := by
  unfold layer
  rw [sum_fiberwise_eq_sum_filter]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)

private theorem odd_diagonal_cost (rank : V → ℕ) (e : V → V → ℕ)
    (top : V) (ranks : Finset ℕ)
    (ordinary : ∀ r ∈ ranks, r ≠ rank top)
    (odd : ∀ r ∈ ranks, r % 2 = 1) :
    (∑ r ∈ ranks, diag rank e r) ≤
      ∑ a, ∑ b, if a ≠ top ∧ rank a % 2 = 1 ∧ rank b % 2 = 1 then e a b else 0 := by
  unfold diag layer
  rw [sum_fiberwise_eq_sum_filter]
  rw [sum_filter]
  refine sum_le_sum fun a _ => ?_
  by_cases h : rank a ∈ ranks
  · rw [ite_eq_left h]
    have ha : a ≠ top := fun eq => ordinary (rank a) h (congrArg rank eq)
    let cost (b : V) := if a ≠ top ∧ rank a % 2 = 1 ∧ rank b % 2 = 1 then e a b else 0
    have hb := single_le_sum (f := cost) (fun _ _ => Nat.zero_le _) (mem_univ a)
    simpa [cost, ha, odd _ h] using hb
  · simp [h]

private theorem cover_layer_sixteen
    (rank : V → ℕ) (e : V → V → ℕ) (top : V)
    (topRank : rank top = 15) (uniqueTop : ∀ v, rank v = 15 → v = top)
    (cover : ∀ a b, a ≠ top → e a b ≠ 0 → a = b ∨ rank b = rank a + 1)
    (counts : ∀ r ≤ 14, (layer rank r).card = Nat.choose 15 r)
    (rowCap : ∀ a, (∑ b, e a b) ≤ if a = top then 2 else 3)
    (colCap : ∀ b, (∑ a, e a b) ≤ if b = top then 2 else 3)
    (rowOdd : ∀ a ≠ top, (∑ b, e a b) % 2 = 1)
    (colOdd : ∀ b ≠ top, (∑ a, e a b) % 2 = 1) :
    let cost := 4 * (1 + ∑ a, ∑ b,
      if a ≠ top ∧ rank a % 2 = 1 ∧ rank b % 2 = 1 then e a b else 0)
    2044 ≤ cost ∧ (cost ≤ 2044 →
      (∑ b ∈ univ.filter (fun b => rank b ≤ 1), e top b) = 1 ∧
      (∑ b ∈ univ.filter (fun b => rank b ≤ 9), e top b) = 1) := by
  let d := diag rank e
  let u := up rank e
  let x := extra rank e top
  have outside (r : ℕ) (hr : r ≤ 14) (v : V) (h : v ∈ layer rank r) : v ≠ top := by
    have hv := (mem_filter.mp h).2
    rintro rfl
    omega
  have rowSizes (r : ℕ) (hr : r ≤ 14) : Nat.choose 15 r ≤ d r + u r := by
    rw [← row_layer rank e top cover r (by omega), ← counts r hr]
    exact sum_layer_lower rank _ r fun a ha => by
      have h := rowOdd a (outside r hr a ha)
      omega
  have colSizes (r : ℕ) (hr : r ≤ 14) : Nat.choose 15 r ≤ d r + prev u r + x r := by
    rw [← col_layer rank e top cover r (by omega) (fun t ht => by omega), ← counts r hr]
    exact sum_layer_lower rank _ r fun a ha => by
      have h := colOdd a (outside r hr a ha)
      omega
  have rowUpper (r : ℕ) (hr : r ≤ 14) : d r + u r ≤ Nat.choose 15 r * 3 := by
    rw [← row_layer rank e top cover r (by omega), ← counts r hr]
    exact sum_layer_upper rank _ r 3 fun a ha => by simpa [outside r hr a ha] using rowCap a
  have colUpper (r : ℕ) (hr : r ≤ 14) : d r + prev u r + x r ≤ Nat.choose 15 r * 3 := by
    rw [← col_layer rank e top cover r (by omega) (fun t ht => by omega), ← counts r hr]
    exact sum_layer_upper rank _ r 3 fun a ha => by simpa [outside r hr a ha] using colCap a
  have diagonalMod (r : ℕ) (hr : r ≤ 9) :
      d r % 2 = (Nat.choose 15 r + ∑ t ∈ range (r + 1), x t) % 2 := by
    have ordinary (a b : V) (ha : a ≠ top) (h : e a b ≠ 0) :
        a = b ∨ rank a < rank b := by
      rcases cover a b ha h with heq | hsucc
      · exact Or.inl heq
      · exact Or.inr (by omega)
    have beforeTop (v : V) (h : v ∈ univ.filter fun v => rank v ≤ r) : v ≠ top := by
      have hv := (mem_filter.mp h).2
      rintro rfl
      omega
    have hd := diagonal_parity (rank := rank) (top := top) (r := r) (e := e)
      (by omega) ordinary (fun a ha => rowOdd a (beforeTop a ha))
      (fun b hb => colOdd b (beforeTop b hb))
    change d r % 2 =
      ((layer rank r).card + (∑ b ∈ univ.filter (fun b => rank b ≤ r), e top b) +
        ∑ a ∈ univ.filter (fun a => rank a < r),
          ∑ b ∈ univ.filter (fun b => r < rank b), e a b) % 2 at hd
    have skips : (∑ a ∈ univ.filter (fun a => rank a < r),
        ∑ b ∈ univ.filter (fun b => r < rank b), e a b) = 0 := by
      apply sum_eq_zero
      intro a ha
      have haRank := (mem_filter.mp ha).2
      have htop : a ≠ top := by rintro rfl; omega
      apply sum_eq_zero
      intro b hb
      have hbRank := (mem_filter.mp hb).2
      by_contra h
      rcases cover a b htop h with heq | hsucc
      · subst b
        omega
      · omega
    have inflow : (∑ b ∈ univ.filter (fun b => rank b ≤ r), e top b) =
        ∑ t ∈ range (r + 1), x t := by
      unfold x extra layer
      rw [sum_fiberwise_eq_sum_filter]
      simp
    rw [skips, add_zero, inflow, counts r (by omega)] at hd
    exact hd
  have topRow : x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 ≤ 2 := by
    have h := (layers_covered rank (e top) (range 8)).trans (by simpa using rowCap top)
    simpa [x, extra, sum_range_succ] using h
  have topLayer : layer rank 15 = {top} := by
    ext a
    simp only [layer, mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨uniqueTop a, fun h => h.symm ▸ topRank⟩
  have topCol : u 14 ≤ 2 := by
    change (∑ a ∈ layer rank 14, ∑ b ∈ layer rank 15, e a b) ≤ 2
    rw [topLayer]
    simp only [sum_singleton]
    exact (sum_le_sum_of_subset_of_nonneg (subset_univ (layer rank 14))
      (fun a _ _ => Nat.zero_le (e a top))).trans (by simpa using colCap top)

  let f (r : ℕ) := ∑ t ∈ range (r + 1), x t
  have mono : Monotone f := by
    intro a b hab
    exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
      (fun _ _ _ => Nat.zero_le _)
  have fcap : f 9 ≤ 2 :=
    (layers_covered rank (e top) (range 10)).trans (by simpa using rowCap top)
  have lower₁ : 13 ≤ d 1 + f 1 := by
    have a := rowUpper 0 (by decide)
    have b := colSizes 0 (by decide)
    have c := colSizes 1 (by decide)
    norm_num [prev, f, sum_range_succ, show Nat.choose 15 0 = 1 by decide,
      show Nat.choose 15 1 = 15 by decide] at a b c ⊢
    change d 1 + u 0 + x 1 ≥ 15 at c
    omega
  have lower₃ : 213 ≤ d 3 + f 3 := by
    have a₀ := rowUpper 0 (by decide)
    have a₁ := rowUpper 1 (by decide)
    have a₂ := rowUpper 2 (by decide)
    have b₀ := colSizes 0 (by decide)
    have b₁ := colSizes 1 (by decide)
    have b₂ := colSizes 2 (by decide)
    have b₃ := colSizes 3 (by decide)
    norm_num [prev, f, sum_range_succ, show Nat.choose 15 0 = 1 by decide,
      show Nat.choose 15 1 = 15 by decide, show Nat.choose 15 2 = 105 by decide,
      show Nat.choose 15 3 = 455 by decide] at a₀ a₁ a₂ b₀ b₁ b₂ b₃ ⊢
    change d 1 + u 0 + x 1 ≥ 15 at b₁
    change d 2 + u 1 + x 2 ≥ 105 at b₂
    change d 3 + u 2 + x 3 ≥ 455 at b₃
    omega
  have factsTop : 213 ≤ d 11 ∧ 73 ≤ d 13 := by
    have a₁₁ := rowSizes 11 (by decide)
    have a₁₂ := rowSizes 12 (by decide)
    have a₁₃ := rowSizes 13 (by decide)
    have a₁₄ := rowSizes 14 (by decide)
    have b₁₂ := colUpper 12 (by decide)
    have b₁₃ := colUpper 13 (by decide)
    have b₁₄ := colUpper 14 (by decide)
    norm_num [prev, show Nat.choose 15 11 = 1365 by decide,
      show Nat.choose 15 12 = 455 by decide, show Nat.choose 15 13 = 105 by decide,
      show Nat.choose 15 14 = 15 by decide] at a₁₁ a₁₂ a₁₃ a₁₄ b₁₂ b₁₃ b₁₄
    change d 12 + u 11 + x 12 ≤ 1365 at b₁₂
    change d 13 + u 12 + x 13 ≤ 315 at b₁₃
    change d 14 + u 13 + x 14 ≤ 45 at b₁₄
    exact ⟨by omega, by omega⟩
  have p₅ : d 5 % 2 = (1 + f 5) % 2 := by
    have h := diagonalMod 5 (by decide)
    change d 5 % 2 = (Nat.choose 15 5 + f 5) % 2 at h
    rw [show Nat.choose 15 5 = 3003 by decide] at h
    omega
  have p₇ : d 7 % 2 = (1 + f 7) % 2 := by
    have h := diagonalMod 7 (by decide)
    change d 7 % 2 = (Nat.choose 15 7 + f 7) % 2 at h
    rw [show Nat.choose 15 7 = 6435 by decide] at h
    omega
  have p₉ : d 9 % 2 = (1 + f 9) % 2 := by
    have h := diagonalMod 9 (by decide)
    change d 9 % 2 = (Nat.choose 15 9 + f 9) % 2 at h
    rw [show Nat.choose 15 9 = 5005 by decide] at h
    omega
  have paid := OmegaAxisEndpointArithmeticTrial.cover_endpoint
    (d 1) (d 3) (d 5) (d 7) (d 9) (d 11) (d 13) (f 1) (f 3) (f 5) (f 7) (f 9)
    lower₁ lower₃ factsTop.1 factsTop.2 (mono (by decide)) (mono (by decide))
    (mono (by decide)) (mono (by decide)) fcap p₅ p₇ p₉
  let oddRanks : Finset ℕ := {1, 3, 5, 7, 9, 11, 13}
  have hcost := odd_diagonal_cost rank e top oddRanks
    (by intro r hr; simp [oddRanks] at hr; omega)
    (by intro r hr; simp [oddRanks] at hr; omega)
  have heq : (∑ r ∈ oddRanks, d r) = d 1 + d 3 + d 5 + d 7 + d 9 + d 11 + d 13 := by
    simp [oddRanks, add_assoc]
  change (∑ r ∈ oddRanks, d r) ≤ _ at hcost
  rw [heq] at hcost
  dsimp only
  refine ⟨by have h := paid.1; omega, fun h => ?_⟩
  obtain ⟨h₁, h₉, -⟩ := paid.2 (by omega)
  have inflow (r : ℕ) : (∑ b ∈ univ.filter (fun b => rank b ≤ r), e top b) = f r := by
    unfold f x extra layer
    rw [sum_fiberwise_eq_sum_filter]
    simp
  exact ⟨(inflow 1).trans h₁, (inflow 9).trans h₉⟩


end RankSums


private theorem subset_top (i : Fin 16) (A : AxisSubset 16 i) : A.val ⊆ (axisTop i).val :=
  fun j hj => mem_erase.mpr ⟨fun h => A.property (h ▸ hj), mem_univ j⟩

private theorem top_card (i : Fin 16) : (axisTop i).val.card = 15 := by
  unfold axisTop
  simp [Finset.card_erase_of_mem (mem_univ i)]

private theorem subset_layer_count (i : Fin 16) (r : ℕ) :
    (layer (fun A : AxisSubset 16 i => A.val.card) r).card = Nat.choose 15 r := by
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


private theorem adjacent_cost_ge_2044_and_inflow (i : Fin 16) (e : AxisSubset 16 i → AxisSubset 16 i → ℕ)
    (cover : ∀ A B, A ≠ axisTop i → e A B ≠ 0 → A = B ∨ B.val.card = A.val.card + 1)
    (rowCap : ∀ A, (∑ B, e A B) ≤ if A = axisTop i then 2 else 3)
    (colCap : ∀ B, (∑ A, e A B) ≤ if B = axisTop i then 2 else 3)
    (rowOdd : ∀ A ≠ axisTop i, (∑ B, e A B) % 2 = 1)
    (colOdd : ∀ B ≠ axisTop i, (∑ A, e A B) % 2 = 1) :
    let cost := 4 * (1 + ∑ A, ∑ B, if A ≠ axisTop i ∧
      A.val.card % 2 = 1 ∧ B.val.card % 2 = 1 then e A B else 0)
    2044 ≤ cost ∧ (cost ≤ 2044 →
      (∑ B ∈ univ.filter (fun B => B.val.card ≤ 1), e (axisTop i) B) = 1 ∧
      (∑ B ∈ univ.filter (fun B => B.val.card ≤ 9), e (axisTop i) B) = 1) := by
  have unique (A : AxisSubset 16 i) (h : A.val.card = 15) : A = axisTop i := by
    apply Subtype.ext
    exact eq_of_subset_of_card_le (subset_top i A) (by rw [top_card i, h])
  exact cover_layer_sixteen (fun A : AxisSubset 16 i => A.val.card) e (axisTop i)
    (top_card i) unique cover (fun r _ => subset_layer_count i r) rowCap colCap rowOdd colOdd


end

open D5.S3.ConceptDynamics.Attribution.ParitySeedFactor
open D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteCapacity

private theorem chosen_rank_count (i : Fin 16) (S : Finset ℕ) :
    (univ.filter (fun A : AxisSubset 16 i => A.val.card ∈ S)).card
      = ∑ s ∈ S, Nat.choose 15 s := by
  rw [← sum_card_fiberwise_eq_card_filter (univ : Finset (AxisSubset 16 i)) S
    (fun A => A.val.card)]
  apply sum_congr rfl
  intro r _
  exact subset_layer_count i r

private theorem rank_lt_top_iff (i : Fin 16) (A : AxisSubset 16 i) :
    A.val.card < 15 ↔ A ≠ axisTop i := by
  constructor
  · intro h he
    simp [he, top_card] at h
  · intro h
    rw [← top_card i]
    apply card_lt_card
    exact (ssubset_iff_subset_ne).mpr ⟨subset_top i A, fun he => h (Subtype.ext he)⟩

-- Normalize finite rank counts without unfolding the factor itself.
set_option maxHeartbeats 2000000 in
private theorem full_budget_ge_for_coordinate (i : Fin 16) (budget : ℕ)
    (feasible : axisFactorWithin 3 i budget) : 2036 ≤ budget := by
  obtain ⟨edge, selected, _, _, row, col, support, cost⟩ := feasible
  let ρ (A : AxisSubset 16 i) := A.val.card
  let t := axisTop i
  let e (A B : AxisSubset 16 i) := (edge A B).toNat
  let R : Finset ℕ := {1,3,11,13}
  have cut := paid_edges_ge_rank_capacity ρ t 3 e R
  have ht : ρ t = 15 := top_card i
  have eligible : ∀ r ∈ R, r < ρ t ∧ r % 2 = 1 := by
    rw [ht]
    decide
  have ordered (A B : AxisSubset 16 i) (ha : A ≠ t) (he : e A B ≠ 0) :
      A = B ∨ ρ A < ρ B := by
    by_cases hab : A = B
    · exact Or.inl hab
    · have h : edge A B = true := by cases h : edge A B <;> simp_all [e]
      exact Or.inr (card_lt_card ((ssubset_iff_subset_ne).mpr
        ⟨support A B ha h, fun heq => hab (Subtype.ext heq)⟩))
  have ordinary_degree (d : ℕ) (h : residualDegree 3 selected false d) :
      1 ≤ d ∧ d ≤ 3 := by
    have odd : d % 2 = 1 := by simpa [residualDegree] using h.2
    exact ⟨by omega, by simpa [residualDegree] using h.1⟩
  have top_degree (d : ℕ) (h : residualDegree 3 selected true d) :
      d ≤ 2 := by
    cases hs : selected
    · have hcap : d ≤ 1 := by simpa [residualDegree, hs] using h.1
      exact hcap.trans (by decide)
    · simpa [residualDegree, hs] using h.1
  have bound := cut eligible ordered
    (fun A ha => (ordinary_degree _ (by simpa [t, ha, e] using row A)).1)
    (fun B hb => (ordinary_degree _ (by simpa [t, hb, e] using col B)).1)
    (fun A ha => (ordinary_degree _ (by simpa [t, ha, e] using row A)).2)
    (fun B hb => (ordinary_degree _ (by simpa [t, hb, e] using col B)).2)
  have row_cap : (∑ B, e t B) ≤ 2 :=
    top_degree _ (by simpa only [t, e, decide_true, eq_self] using row t)
  have col_cap : (∑ A, e A t) ≤ 2 :=
    top_degree _ (by simpa only [t, e, decide_true, eq_self] using col t)
  let L (r : ℕ) := (univ.filter (fun A : AxisSubset 16 i => ρ A ≤ r)).card
  let Ls (r : ℕ) := (univ.filter (fun A : AxisSubset 16 i => ρ A < r)).card
  let H (r : ℕ) := (univ.filter (fun A : AxisSubset 16 i => r ≤ ρ A ∧ A ≠ t)).card
  let Hs (r : ℕ) := (univ.filter (fun A : AxisSubset 16 i => r < ρ A ∧ A ≠ t)).card
  have hs (r : ℕ) : ((univ.filter (fun A : AxisSubset 16 i => r < ρ A)).erase t).card = Hs r := by
    congr 1
    ext A
    simp [and_comm]
  have l_count (r : ℕ) : L r = ∑ s ∈ range (r+1), Nat.choose 15 s := by
    simpa [L, ρ, Nat.lt_succ_iff] using chosen_rank_count i (range (r+1))
  have ls_count (r : ℕ) : Ls r = ∑ s ∈ range r, Nat.choose 15 s := by
    simpa [Ls, ρ] using chosen_rank_count i (range r)
  have h_count (r : ℕ) : H r = ∑ s ∈ (range 15).filter (r ≤ ·), Nat.choose 15 s := by
    simpa [H, ρ, t, ← rank_lt_top_iff i, and_comm] using
      chosen_rank_count i ((range 15).filter (r ≤ ·))
  have hs_count (r : ℕ) : Hs r = ∑ s ∈ (range 15).filter (r < ·), Nat.choose 15 s := by
    simpa [Hs, ρ, t, ← rank_lt_top_iff i, and_comm] using
      chosen_rank_count i ((range 15).filter (r < ·))
  let F (r : ℕ) : ℕ := ∑ b ∈ univ.filter (fun B : AxisSubset 16 i => ρ B ≤ r), e t b
  let G (r : ℕ) : ℕ := ∑ a ∈ univ.filter (fun A : AxisSubset 16 i => r ≤ ρ A ∧ A ≠ t), e a t
  change (∑ r ∈ R, max (L r - (Ls r * 3 + F r))
    (H r - (((univ.filter (fun A : AxisSubset 16 i => r < ρ A)).erase t).card * 3 + G r))) ≤
      _ at bound
  have fixed := (show (∑ r ∈ R, max (L r - (Ls r * 3 + 2)) (H r - (Hs r * 3 + 2))) ≤
      ∑ r ∈ R, max (L r - (Ls r * 3 + F r)) (H r - (Hs r * 3 + G r)) from
    Finset.sum_le_sum fun r _ => by
      have hF : F r ≤ 2 :=
        (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)).trans row_cap
      have hG : G r ≤ 2 :=
        (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)).trans col_cap
      apply max_le_max <;> omega)
  simp_rw [hs] at bound
  have bound := fixed.trans bound
  simp_rw [l_count, ls_count, h_count, hs_count] at bound
  have computed : (∑ r ∈ R, max
      ((∑ s ∈ range (r+1), Nat.choose 15 s) - ((∑ s ∈ range r, Nat.choose 15 s) * 3 + 2))
      ((∑ s ∈ (range 15).filter (r ≤ ·), Nat.choose 15 s) -
        ((∑ s ∈ (range 15).filter (r < ·), Nat.choose 15 s) * 3 + 2))) = 508 := by
       decide
  rw [computed] at bound
  exact (Nat.mul_le_mul_left 4 (Nat.add_le_add_left bound 1)).trans cost

end SixteenAdjacentRank

open Finset
open D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor
open D5.S3.ConceptDynamics.Attribution.ParitySeedFactor

section

private abbrev coordinate : Fin 16 := 0

def coverWithin (budget : ℕ) : Prop :=
  ∃ (f : AxisSubset 16 coordinate → AxisSubset 16 coordinate → Bool) (selected : Bool),
    f (axisTop coordinate) (axisTop coordinate) = false ∧
    (selected = false → 3 ≤ 3) ∧
    (∀ A, residualDegree 3 selected (decide (A = axisTop coordinate))
      (∑ B, (f A B).toNat)) ∧
    (∀ B, residualDegree 3 selected (decide (B = axisTop coordinate))
      (∑ A, (f A B).toNat)) ∧
    (∀ A B, A ≠ axisTop coordinate → f A B = true →
      A.val ⊆ B.val ∧ (A = B ∨ B.val.card = A.val.card + 1)) ∧
    axisCost coordinate f ≤ budget

/-- Every factor supported on inclusion covers and diagonals uses a budget of at least 2044. -/
theorem cover_budget_ge (budget : ℕ) (h : coverWithin budget) : 2044 ≤ budget := by
  obtain ⟨f, selected, _, _, rows, cols, covers, cost⟩ := h
  let e (A B : AxisSubset 16 coordinate) : ℕ := (f A B).toNat
  have cap (A : AxisSubset 16 coordinate) (n : ℕ)
      (d : residualDegree 3 selected (decide (A = axisTop coordinate)) n) :
      n ≤ if A = axisTop coordinate then 2 else 3 := by
    by_cases hA : A = axisTop coordinate <;> cases hs : selected <;>
      simp_all [residualDegree] <;> omega
  have odd (A : AxisSubset 16 coordinate) (n : ℕ)
      (d : residualDegree 3 selected (decide (A = axisTop coordinate)) n)
      (hA : A ≠ axisTop coordinate) : n % 2 = 1 := by simpa [residualDegree, hA] using d.2
  have hcover (A B : AxisSubset 16 coordinate) (hA : A ≠ axisTop coordinate)
      (hne : e A B ≠ 0) : A = B ∨ B.val.card = A.val.card + 1 := by
    have positive : f A B = true := by cases h : f A B <;> simp_all [e]
    exact (covers A B hA positive).2
  have lb := (SixteenAdjacentRank.adjacent_cost_ge_2044_and_inflow coordinate e hcover
    (fun A => cap A _ (rows A)) (fun B => cap B _ (cols B))
    (fun A hA => odd A _ (rows A) hA) (fun B hB => odd B _ (cols B) hB)).1
  exact lb.trans cost

/-- Rank capacities bound the budget of the full inclusion graph at coordinate zero. -/
theorem full_budget_ge (budget : ℕ) (h : axisFactorWithin 3 coordinate budget) :
    2036 ≤ budget :=
  SixteenAdjacentRank.full_budget_ge_for_coordinate coordinate budget h

end

end D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteenCovers
