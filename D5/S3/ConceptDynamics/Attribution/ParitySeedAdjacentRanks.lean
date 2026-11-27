/- GID: D5/S3/ConceptDynamics/Attribution/ParitySeedAdjacentRanks
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParitySeedAdjacentRanks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/Attribution/ParitySeedAdjacentRanks.claim; result=D5/S3/ConceptDynamics/Attribution/ParitySeedAdjacentRanks.result; claim=D5/S3/ConceptDynamics/Attribution/ParitySeedAdjacentRanks.claim
   digest: Refute adjacent-rank compression of an eight-coordinate fixed-seed budget. -/

import D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.ParitySeedAdjacentRanks

open Finset
open D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor
open D5.S3.ConceptDynamics.Attribution.ParitySeedFactor

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
private theorem sum_layer_parity (rank : V → ℕ) (e : V → ℕ) (r : ℕ)
    (odd : ∀ v ∈ layer rank r, e v % 2 = 1) :
    (∑ v ∈ layer rank r, e v) % 2 = (layer rank r).card % 2 := by
  have h := Nat.ModEq.sum (s := layer rank r) fun v hv =>
    (show e v ≡ 1 [MOD 2] from by simpa [Nat.ModEq] using odd v hv)
  simpa [Nat.ModEq] using h

omit [DecidableEq V] in
private theorem lower_four_layers (rank : V → ℕ) (v : V → ℕ) :
    (∑ a ∈ layer rank 0, v a) + (∑ a ∈ layer rank 1, v a) +
      (∑ a ∈ layer rank 2, v a) + (∑ a ∈ layer rank 3, v a) ≤ ∑ a, v a := by
  simp only [layer, sum_filter, ← sum_add_distrib]
  apply sum_le_sum
  intro a _
  by_cases h0 : rank a = 0 <;> by_cases h1 : rank a = 1 <;>
    by_cases h2 : rank a = 2 <;> by_cases h3 : rank a = 3 <;> simp_all

private theorem cover_layer_obstruction
    (rank : V → ℕ) (e : V → V → ℕ) (top : V)
    (topRank : rank top = 7) (uniqueTop : ∀ v, rank v = 7 → v = top)
    (cover : ∀ a b, a ≠ top → e a b ≠ 0 → a = b ∨ rank b = rank a + 1)
    (counts : ∀ r ≤ 6, (layer rank r).card = Nat.choose 7 r)
    (rowCap : ∀ a, (∑ b, e a b) ≤ (if a = top then 2 else 3))
    (colCap : ∀ b, (∑ a, e a b) ≤ (if b = top then 2 else 3))
    (rowOdd : ∀ a ≠ top, (∑ b, e a b) % 2 = 1)
    (colOdd : ∀ b ≠ top, (∑ a, e a b) % 2 = 1) :
    9 ≤ diag rank e 1 + diag rank e 3 + diag rank e 5 := by
  let d := diag rank e
  let u := up rank e
  let x := extra rank e top
  have outside (r : ℕ) (hl : r ≤ 6) (v : V) (h : v ∈ layer rank r) : v ≠ top := by
    have hv := (mem_filter.mp h).2
    rintro rfl
    omega
  have rowSizes (r : ℕ) (hr : r ≤ 6) :
      Nat.choose 7 r ≤ d r + u r := by
    rw [← row_layer rank e top cover r (by omega), ← counts r hr]
    exact sum_layer_lower rank _ r fun a ha => by
      have h := rowOdd a (outside r hr a ha)
      omega
  have colSizes (r : ℕ) (hr : r ≤ 6) :
      Nat.choose 7 r ≤ d r + prev u r + x r := by
    rw [← col_layer rank e top cover r (by omega) (fun t ht => by omega), ← counts r hr]
    exact sum_layer_lower rank _ r fun a ha => by
      have h := colOdd a (outside r hr a ha)
      omega
  have rowUpper (r : ℕ) (hr : r ≤ 6) : d r + u r ≤ Nat.choose 7 r * 3 := by
    rw [← row_layer rank e top cover r (by omega), ← counts r hr]
    exact sum_layer_upper rank _ r 3 fun a ha => by simpa [outside r hr a ha] using rowCap a
  have colUpper (r : ℕ) (hr : r ≤ 6) : d r + prev u r + x r ≤ Nat.choose 7 r * 3 := by
    rw [← col_layer rank e top cover r (by omega) (fun t ht => by omega), ← counts r hr]
    exact sum_layer_upper rank _ r 3 fun a ha => by simpa [outside r hr a ha] using colCap a
  have rowMod (r : ℕ) (hr : r ≤ 6) : (d r + u r) % 2 = (Nat.choose 7 r) % 2 := by
    rw [← row_layer rank e top cover r (by omega), ← counts r hr]
    exact sum_layer_parity rank _ r fun a ha => rowOdd a (outside r hr a ha)
  have colMod (r : ℕ) (hr : r ≤ 6) : (d r + prev u r + x r) % 2 = (Nat.choose 7 r) % 2 := by
    rw [← col_layer rank e top cover r (by omega) (fun t ht => by omega), ← counts r hr]
    exact sum_layer_parity rank _ r fun a ha => colOdd a (outside r hr a ha)
  have topRow : x 0 + x 1 + x 2 + x 3 ≤ 2 :=
    (lower_four_layers rank (e top)).trans (by simpa using rowCap top)
  have topLayer : layer rank 7 = {top} := by
    ext a
    simp only [layer, mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨uniqueTop a, fun h => h.symm ▸ topRank⟩
  have topCol : u 6 ≤ 2 := by
    change (∑ a ∈ layer rank 6, ∑ b ∈ layer rank 7, e a b) ≤ 2
    rw [topLayer]
    simp only [sum_singleton]
    have h := sum_le_sum_of_subset_of_nonneg (subset_univ (layer rank 6))
      (fun a _ _ => Nat.zero_le (e a top))
    exact h.trans (by simpa using colCap top)
  have low : 8 ≤ d 0 + d 1 + u 0 + x 0 + x 1 := by
    have first := colSizes 0 (by decide)
    have second := colSizes 1 (by decide)
    simp [prev] at first second
    omega
  have rowsFive : 21 ≤ d 5 + u 5 := by simpa only [show Nat.choose 7 5 = 21 by decide] using rowSizes 5 (by decide)
  have rowsSix : 7 ≤ d 6 + u 6 := by simpa using rowSizes 6 (by decide)
  have colsSix : d 6 + u 5 + x 6 ≤ 21 := by simpa [prev] using colUpper 6 (by decide)
  have middle : (d 3 + u 3) % 2 = 1 := by simpa only [show Nat.choose 7 3 % 2 = 1 by decide] using rowMod 3 (by decide)
  have balance (r : ℕ) (hr : r ≤ 3) : (d r + u r) % 2 = (d r + prev u r + x r) % 2 :=
    (rowMod r (by omega)).trans (colMod r (by omega)).symm
  have emptyRow : d 0 + u 0 ≤ 3 := by simpa using rowUpper 0 (by decide)
  by_contra! small
  change d 1 + d 3 + d 5 < 9 at small
  have lowBound : 3 ≤ d 1 := by omega
  have high : 5 ≤ d 5 := by omega
  have noDiag : d 3 = 0 := by omega
  have topLow : x 0 + x 1 = 2 := by omega
  have topHigher : x 2 + x 3 = 0 := by omega
  have b0 := balance 0 (by decide)
  have b1 := balance 1 (by decide)
  have b2 := balance 2 (by decide)
  have b3 := balance 3 (by decide)
  simp only [prev] at b0 b1 b2 b3
  omega

end RankSums

private theorem subset_top (i : Fin 8) (A : AxisSubset 8 i) : A.val ⊆ (axisTop i).val :=
  fun j hj => mem_erase.mpr ⟨fun h => A.property (h ▸ hj), mem_univ j⟩

private theorem top_card (i : Fin 8) : (axisTop i).val.card = 7 := by
  unfold axisTop
  simp [Finset.card_erase_of_mem (mem_univ i)]

private theorem subset_layer_count (i : Fin 8) (r : ℕ) :
    (layer (fun A : AxisSubset 8 i => A.val.card) r).card = Nat.choose 7 r := by
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

private theorem rank_odd_diagonal_lower (i : Fin 8) (e : AxisSubset 8 i → AxisSubset 8 i → ℕ) :
    let rank (A : AxisSubset 8 i) := A.val.card
    diag rank e 1 + diag rank e 3 + diag rank e 5 ≤
      ∑ A, ∑ B, if A ≠ axisTop i ∧ rank A % 2 = 1 ∧ rank B % 2 = 1
        then e A B else 0 := by
  dsimp only
  simp only [diag, layer, sum_filter, ← sum_add_distrib]
  refine sum_le_sum fun A _ => ?_
  let rank := A.val.card
  by_cases h : rank = 1 ∨ rank = 3 ∨ rank = 5
  · have nTop : A ≠ axisTop i := by
      intro ht
      have h7 : rank = 7 := (congrArg (fun A : AxisSubset 8 i => A.val.card) ht).trans (top_card i)
      omega
    have odd : A.val.card % 2 = 1 := by
      change rank % 2 = 1
      omega
    have bound := single_le_sum
      (f := fun B : AxisSubset 8 i =>
        if A ≠ axisTop i ∧ A.val.card % 2 = 1 ∧ B.val.card % 2 = 1 then e A B else 0)
      (fun _ _ => Nat.zero_le _) (mem_univ A)
    rw [ite_eq_left (show A ≠ axisTop i ∧ A.val.card % 2 = 1 ∧
      A.val.card % 2 = 1 from ⟨nTop, odd, odd⟩)] at bound
    change ((if rank = 1 then e A A else 0) + (if rank = 3 then e A A else 0)
      + (if rank = 5 then e A A else 0)) ≤ _
    rcases h with h1 | h3 | h5
    · have h3 : rank ≠ 3 := by omega
      have h5 : rank ≠ 5 := by omega
      simpa only [ite_eq_left h1, ite_eq_right h3, ite_eq_right h5, add_zero, zero_add] using bound
    · have h1 : rank ≠ 1 := by omega
      have h5 : rank ≠ 5 := by omega
      simpa only [ite_eq_right h1, ite_eq_left h3, ite_eq_right h5, add_zero, zero_add] using bound
    · have h1 : rank ≠ 1 := by omega
      have h3 : rank ≠ 3 := by omega
      simpa only [ite_eq_right h1, ite_eq_right h3, ite_eq_left h5, add_zero, zero_add] using bound
  · obtain ⟨h1, h3, h5⟩ : rank ≠ 1 ∧ rank ≠ 3 ∧ rank ≠ 5 := by omega
    change ((if rank = 1 then e A A else 0) + (if rank = 3 then e A A else 0)
      + (if rank = 5 then e A A else 0)) ≤ _
    simp [h1, h3, h5]

/-- Adjacent ranks and diagonals force at least forty fixed seeds at the permitted coordinate. -/
private theorem axis_cover_budget_ge_forty (i : Fin 8) (e : AxisSubset 8 i → AxisSubset 8 i → ℕ)
    (cover : ∀ A B, A ≠ axisTop i → e A B ≠ 0 →
      A = B ∨ B.val.card = A.val.card + 1)
    (rowCap : ∀ A, (∑ B, e A B) ≤ (if A = axisTop i then 2 else 3))
    (colCap : ∀ B, (∑ A, e A B) ≤ (if B = axisTop i then 2 else 3))
    (rowOdd : ∀ A ≠ axisTop i, (∑ B, e A B) % 2 = 1)
    (colOdd : ∀ B ≠ axisTop i, (∑ A, e A B) % 2 = 1) :
    40 ≤ 4 * (1 + ∑ A, ∑ B, if A ≠ axisTop i ∧
      A.val.card % 2 = 1 ∧ B.val.card % 2 = 1 then e A B else 0) := by
  have unique (A : AxisSubset 8 i) (h : A.val.card = 7) : A = axisTop i := by
    apply Subtype.ext
    exact eq_of_subset_of_card_le (subset_top i A) (by rw [top_card i, h])
  have h := cover_layer_obstruction (fun A : AxisSubset 8 i => A.val.card) e (axisTop i)
    (top_card i) unique cover (fun r _ => subset_layer_count i r) rowCap colCap rowOdd colOdd
  have bound := h.trans (rank_odd_diagonal_lower i e)
  dsimp only at bound
  omega

/-- Column indices for each row in subset-mask order. Bit j represents coordinate j plus one. -/
private def witnessRows : Array (List ℕ) := #[
  [1, 8, 64], [3, 5, 33], [2, 6, 34], [19, 35, 67], [4, 20, 54], [7, 69, 101], [14, 102, 118], [15],
  [12, 72, 105], [9, 11, 41], [10, 26, 74], [75], [13, 44, 47], [29], [46], [31],
  [24, 27, 90], [17, 81, 121], [18, 22, 50], [83], [21, 52, 85], [53], [86], [23, 31, 87],
  [25, 28, 56], [89], [30], [91], [92], [31], [94], [63],
  [32, 36, 40], [37, 49, 97], [59], [39], [38, 45, 124], [39], [39], [55],
  [42, 60, 122], [57], [43], [47], [45], [45, 61, 109], [62], [47],
  [48, 58, 112], [51], [54], [59], [60], [55, 61, 117], [54, 62, 118], [55],
  [58], [61], [58, 59, 122], [123], [60, 62, 124], [63], [63], [127],
  [65, 66, 68], [79], [115], [75, 83, 99], [70, 76, 102], [71], [71, 78, 102], [71],
  [73, 88, 104], [75, 77, 105], [78], [107], [78], [93], [94], [95],
  [80, 82, 84], [83], [90], [91], [85], [85, 93, 117], [94], [119],
  [120], [121], [90], [91], [93], [95], [95], [127],
  [96, 98, 100], [105], [99], [99], [116], [103], [110], [111],
  [108], [109], [106], [111], [110], [109], [110], [111],
  [113], [117], [114, 118, 122], [123], [124], [119], [126], [119],
  [121], [125], [126], [123], [125], [125], [126], [0, 16]]

private def subsetNumber (A : AxisSubset 8 (0 : Fin 8)) : ℕ :=
  ∑ j ∈ A.val, 2 ^ (j.val - 1)

private def witnessEdge (A B : AxisSubset 8 (0 : Fin 8)) : Bool :=
  (witnessRows[subsetNumber A]?.getD []).contains (subsetNumber B)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem eight_axis_achieves_thirty_six : axisFactorWithin 3 (0 : Fin 8) 36 := by
  refine ⟨witnessEdge, true, ?_, by decide, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · unfold residualDegree
    decide +kernel
  · unfold residualDegree
    decide +kernel
  · decide +kernel
  · change axisCost 0 witnessEdge ≤ 36
    unfold axisCost
    decide +kernel

/-- The adjacent-rank restriction preserves the eight-coordinate axis budget of thirty-six. -/
def claim : Prop :=
  axisFactorWithin 3 (0 : Fin 8) 36 →
  ∃ (f : AxisSubset 8 (0 : Fin 8) → AxisSubset 8 (0 : Fin 8) → Bool) (selected : Bool),
    f (axisTop 0) (axisTop 0) = false ∧
    (∀ A, residualDegree 3 selected (decide (A = axisTop 0)) (∑ B, (f A B).toNat)) ∧
    (∀ B, residualDegree 3 selected (decide (B = axisTop 0)) (∑ A, (f A B).toNat)) ∧
    (∀ A B, A ≠ axisTop 0 → f A B = true →
      A.val ⊆ B.val ∧ (A = B ∨ B.val.card = A.val.card + 1)) ∧
    axisCost 0 f ≤ 36

/-- Adjacent ranks fail to preserve a realizable one-coordinate fixed-seed budget. -/
theorem result : ¬ claim := by
  intro preserves
  obtain ⟨f, selected, _, rows, cols, allowed, cost⟩ := preserves eight_axis_achieves_thirty_six
  let e (A B : AxisSubset 8 (0 : Fin 8)) : ℕ := (f A B).toNat
  have across (A B : AxisSubset 8 (0 : Fin 8)) (ordinary : A ≠ axisTop 0)
      (present : e A B ≠ 0) : A = B ∨ B.val.card = A.val.card + 1 := by
    have chosen : f A B = true := by
      cases h : f A B
      · exact (present (by simp [e, h])).elim
      · rfl
    exact (allowed A B ordinary chosen).2
  have rowUpper (A : AxisSubset 8 (0 : Fin 8)) :
      (∑ B, e A B) ≤ if A = axisTop 0 then 2 else 3 := by
    have cap := (rows A).1
    by_cases h : A = axisTop 0
    · cases selected <;> simp [h, e] at cap ⊢ <;> omega
    · simpa [h, e] using cap
  have colUpper (B : AxisSubset 8 (0 : Fin 8)) :
      (∑ A, e A B) ≤ if B = axisTop 0 then 2 else 3 := by
    have cap := (cols B).1
    by_cases h : B = axisTop 0
    · cases selected <;> simp [h, e] at cap ⊢ <;> omega
    · simpa [h, e] using cap
  have rowParity (A : AxisSubset 8 (0 : Fin 8)) (h : A ≠ axisTop 0) :
      (∑ B, e A B) % 2 = 1 := by
    simpa [h, e] using (rows A).2
  have colParity (B : AxisSubset 8 (0 : Fin 8)) (h : B ≠ axisTop 0) :
      (∑ A, e A B) % 2 = 1 := by
    simpa [h, e] using (cols B).2
  have tooLarge : 40 ≤ axisCost 0 f :=
    axis_cover_budget_ge_forty 0 e across rowUpper colUpper rowParity colParity
  omega

end

end D5.S3.ConceptDynamics.Attribution.ParitySeedAdjacentRanks
