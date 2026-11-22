/- GID: D5/S3/ConceptDynamics/Attribution/ParityMixedRankBounds
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParityMixedRankBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Combine row and column parity mismatches on selected rank cuts. -/

import D5.S3.ConceptDynamics.Attribution.ParityStackedRankBounds

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds

open Finset
open D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds
open D5.S3.ConceptDynamics.Attribution.ParityStackedRankBounds

def lowEven {n : ℕ} (r : ℕ) : Finset (EvenSubset n) :=
  univ.filter fun p => p.val.card < r

def highOdd {n : ℕ} (r : ℕ) : Finset (OddSubset n) :=
  univ.filter fun q => n - r < q.val.card

abbrev RankCutTable (n : ℕ) :=
  EvenSubset n × (EvenSubset n → OddSubset n → ℕ) × (Finset ℕ × Finset ℕ)

private def mismatch {Y : Type*} [Fintype Y] (mass : Y → ℕ) (free : Finset Y) : Prop :=
  (∑ y, mass y) % 2 ≠ (∑ y ∈ free, mass y) % 2

private theorem odd_outside {Y : Type*} [Fintype Y] [DecidableEq Y]
    (mass : Y → ℕ) (free : Finset Y) (h : mismatch mass free) :
    ∃ y, y ∉ free ∧ mass y % 2 = 1 := by
  by_contra! absent
  apply h
  have same (y : Y) :
      mass y ≡ (if y ∈ free then mass y else 0) [MOD 2] := by
    by_cases hy : y ∈ free
    · simp [hy, Nat.ModEq]
    · have none := absent y hy
      simp only [hy, ite_false, Nat.ModEq, Nat.zero_mod]
      omega
  have congruence := Nat.ModEq.sum (s := univ) (fun y _ => same y)
  change (∑ y, mass y) % 2 = (∑ y, if y ∈ free then mass y else 0) % 2 at congruence
  rw [← sum_filter] at congruence
  simpa only [filter_mem_eq_inter, univ_inter] using congruence

private def highRows {n : ℕ} (full : EvenSubset n) (r : ℕ) : Finset (EvenSubset n) :=
  (univ.erase full).filter fun p => r ≤ p.val.card

/-- Targets for which the free columns leave an odd balance. -/
def rowTargets {n : ℕ} (table : RankCutTable n) (r : ℕ) : Finset (EvenSubset n) :=
  if r ∈ table.2.2.1 then
    (highRows table.1 r).filter fun p =>
      (∑ q, table.2.1 p q) % 2 ≠ (∑ q ∈ lowOddRanks r, table.2.1 p q) % 2
  else ∅

/-- Targets for which the low rows and the distinguished row leave an odd balance. -/
def columnTargets {n : ℕ} (table : RankCutTable n) (r : ℕ) : Finset (OddSubset n) :=
  if r ∈ table.2.2.2 then
    (highOdd r).filter fun q =>
      (∑ p, table.2.1 p q) % 2 ≠
        (∑ p ∈ insert table.1 (lowEven r), table.2.1 p q) % 2
  else ∅

private theorem row_targets {n : ℕ} (table : RankCutTable n) (r : ℕ)
    {p : EvenSubset n} (hp : p ∈ rowTargets table r) :
    p ∈ highRows table.1 r ∧ mismatch (table.2.1 p) (lowOddRanks r) := by
  unfold rowTargets at hp
  split at hp
  · exact mem_filter.mp hp
  · exact (notMem_empty p hp).elim

private theorem column_targets {n : ℕ} (table : RankCutTable n) (r : ℕ)
    {q : OddSubset n} (hq : q ∈ columnTargets table r) :
    q ∈ highOdd r ∧ mismatch (fun p => table.2.1 p q) (insert table.1 (lowEven r)) := by
  unfold columnTargets at hq
  split at hq
  · exact mem_filter.mp hq
  · exact (notMem_empty q hq).elim

/-- Use the larger target family at a shared threshold, with ties assigned to rows. -/
def charges {n : ℕ} (table : RankCutTable n) (r : ℕ)
    (p : EvenSubset n) (q : OddSubset n) : Prop :=
  if (columnTargets table r).card ≤ (rowTargets table r).card then
    p ∈ rowTargets table r ∧ q ∉ lowOddRanks r
  else q ∈ columnTargets table r ∧ p ∉ insert table.1 (lowEven r)

instance {n : ℕ} (table : RankCutTable n) (r : ℕ) (p : EvenSubset n) (q : OddSubset n) :
    Decidable (charges table r p q) := by unfold charges; infer_instance

/-- Sum the larger selected target count at each threshold. -/
def cutDeficitSum {n : ℕ} (table : RankCutTable n) : ℕ :=
  ∑ r ∈ table.2.2.1 ∪ table.2.2.2,
    max (rowTargets table r).card (columnTargets table r).card

/-- Count the selected thresholds that can charge an ordinary cell. -/
def chargeCount {n : ℕ} (table : RankCutTable n) (p : EvenSubset n) (q : OddSubset n) : ℕ :=
  ((table.2.2.1 ∪ table.2.2.2).filter fun r => charges table r p q).card

private theorem sum_indicator {X : Type*} [Fintype X] [DecidableEq X]
    (s : Finset X) (f : X → ℕ) :
    (∑ x ∈ s, f x) = ∑ x, if x ∈ s then f x else 0 := by
  rw [← sum_filter]
  simp only [filter_mem_eq_inter, univ_inter]

private theorem representative_cells {n : ℕ} (table : RankCutTable n) (r : ℕ) :
    ∃ cells : Finset (EvenSubset n × OddSubset n),
      cells.card = max (rowTargets table r).card (columnTargets table r).card ∧
      ∀ p q, (p, q) ∈ cells → charges table r p q ∧ table.2.1 p q % 2 = 1 := by
  classical
  by_cases row : (columnTargets table r).card ≤ (rowTargets table r).card
  · have existsCell (p : rowTargets table r) :
        ∃ q, q ∉ lowOddRanks r ∧ table.2.1 p.val q % 2 = 1 :=
      odd_outside _ _ (row_targets table r p.property).2
    choose chooseCol colFree oddMass using existsCell
    let toCell (p : rowTargets table r) := (p.val, chooseCol p)
    have injective : Function.Injective toCell := fun _ _ eq =>
      Subtype.ext (congrArg Prod.fst eq)
    refine ⟨univ.image toCell, ?_, ?_⟩
    · rw [card_image_of_injective _ injective, card_univ, Fintype.card_coe, max_eq_left row]
    · intro p q mem
      obtain ⟨x, _, hx⟩ := mem_image.mp mem
      have hp : p = x.val := (congrArg Prod.fst hx).symm
      have hq : q = chooseCol x := (congrArg Prod.snd hx).symm
      subst p
      subst q
      exact ⟨by simpa only [charges, ite_eq_left row] using
        And.intro x.property (colFree x), oddMass x⟩
  · have existsCell (q : columnTargets table r) :
        ∃ p, p ∉ insert table.1 (lowEven r) ∧ table.2.1 p q.val % 2 = 1 :=
      odd_outside _ _ (column_targets table r q.property).2
    choose chooseRow rowFree oddMass using existsCell
    let toCell (q : columnTargets table r) := (chooseRow q, q.val)
    have injective : Function.Injective toCell := fun _ _ eq =>
      Subtype.ext (congrArg Prod.snd eq)
    refine ⟨univ.image toCell, ?_, ?_⟩
    · rw [card_image_of_injective _ injective, card_univ, Fintype.card_coe,
        max_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge row))]
    · intro p q mem
      obtain ⟨x, _, hx⟩ := mem_image.mp mem
      have hp : p = chooseRow x := (congrArg Prod.fst hx).symm
      have hq : q = x.val := (congrArg Prod.snd hx).symm
      subst p
      subst q
      exact ⟨by simpa only [charges, ite_eq_right row] using
        And.intro x.property (rowFree x), oddMass x⟩

/-- The number of selected thresholds in the interval available to an ordinary cell. -/
def intervalCap {n : ℕ} (table : RankCutTable n) (p : EvenSubset n) (q : OddSubset n) : ℕ :=
  if p = table.1 then 0 else
    ((table.2.2.1 ∪ table.2.2.2) ∩ Ioc (n - q.val.card) p.val.card).card

private theorem exact_allocation {n : ℕ} (table : RankCutTable n) :
    ∃ allocated : EvenSubset n → OddSubset n → ℕ,
      (∑ p, ∑ q, allocated p q) = cutDeficitSum table ∧
      ∀ p q, allocated p q ≤ (table.2.1 p q % 2) * chargeCount table p q := by
  classical
  choose cells size support using representative_cells table
  let thresholds := table.2.2.1 ∪ table.2.2.2
  let allocation (p : EvenSubset n) (q : OddSubset n) :=
    (thresholds.filter fun r => (p, q) ∈ cells r).card
  refine ⟨allocation, ?_, ?_⟩
  · have cardCells (r : ℕ) :
        (cells r).card = ∑ p : EvenSubset n, ∑ q : OddSubset n,
          if (p, q) ∈ cells r then 1 else 0 := by
      rw [card_eq_sum_ones, sum_indicator, Fintype.sum_prod_type]
    have entry (p : EvenSubset n) (q : OddSubset n) : allocation p q =
        ∑ r ∈ thresholds, if (p, q) ∈ cells r then 1 else 0 := by
      dsimp only [allocation]
      rw [card_eq_sum_ones, sum_filter]
    simp_rw [entry]
    have sumCards : cutDeficitSum table = ∑ r ∈ thresholds, (cells r).card := by
      simp only [cutDeficitSum, thresholds, size]
    rw [sumCards]
    simp_rw [cardCells]
    rw [sum_comm (s := thresholds) (t := (univ : Finset (EvenSubset n)))]
    apply sum_congr rfl
    intro p _
    rw [sum_comm]
  · intro p q
    have subset : (thresholds.filter fun r => (p, q) ∈ cells r) ⊆
        thresholds.filter (fun r => charges table r p q) := by
      intro r hr
      obtain ⟨hsel, hm⟩ := mem_filter.mp hr
      exact mem_filter.mpr ⟨hsel, (support r p q hm).1⟩
    by_cases h : table.2.1 p q % 2 = 1
    · rw [h, Nat.one_mul]
      exact card_le_card subset
    · have empty : (thresholds.filter fun r => (p, q) ∈ cells r) = ∅ :=
        eq_empty_iff_forall_notMem.mpr fun r hr => h (support r p q (mem_filter.mp hr).2).2
      simp only [allocation, empty, card_empty, Nat.zero_le]

private theorem charges_region {n : ℕ} (table : RankCutTable n) (r : ℕ)
    (p : EvenSubset n) (q : OddSubset n) (h : charges table r p q) :
    p ≠ table.1 ∧ r ∈ Ioc (n - q.val.card) p.val.card := by
  have size : q.val.card ≤ n := by simpa using card_le_univ q.val
  have inside (notFull : p ≠ table.1) (hi : r ≤ p.val.card) (lo : n - r < q.val.card) :
      p ≠ table.1 ∧ r ∈ Ioc (n - q.val.card) p.val.card :=
    ⟨notFull, mem_Ioc.mpr ⟨by omega, hi⟩⟩
  unfold charges at h
  split at h
  · have hp := (row_targets table r h.1).1
    have rank : p ≠ table.1 ∧ r ≤ p.val.card := by simpa [highRows] using hp
    have lo : n - r < q.val.card := by simpa [lowOddRanks, Nat.not_le] using h.2
    exact inside rank.1 rank.2 lo
  · have hq := (column_targets table r h.1).1
    have rank : p ≠ table.1 ∧ r ≤ p.val.card := by simpa [lowEven, Nat.not_lt] using h.2
    have lo : n - r < q.val.card := by simpa [highOdd] using hq
    exact inside rank.1 rank.2 lo

private theorem chargeCount_le_interval {n : ℕ} (table : RankCutTable n)
    (p : EvenSubset n) (q : OddSubset n) :
    chargeCount table p q ≤ intervalCap table p q := by
  by_cases hp : p = table.1
  · have empty : ((table.2.2.1 ∪ table.2.2.2).filter fun r => charges table r p q) = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun r hr => (charges_region table r p q (mem_filter.mp hr).2).1 hp
    rw [intervalCap, ite_eq_left hp, chargeCount, empty, card_empty]
  · rw [intervalCap, ite_eq_right hp]
    apply card_le_card
    intro r hr
    obtain ⟨selected, charged⟩ := mem_filter.mp hr
    exact mem_inter.mpr ⟨selected, (charges_region table r p q charged).2⟩

/-- The intersection of two profiles bounds the number of selected thresholds available to their cell. -/
private theorem intervalCap_le_intersection {n : ℕ} (table : RankCutTable n)
    (p : EvenSubset n) (q : OddSubset n) :
    intervalCap table p q ≤ if p = table.1 then 0 else (p.val ∩ q.val).card := by
  by_cases hp : p = table.1
  · simp [intervalCap, hp]
  · simp only [intervalCap, ite_eq_right hp]
    have bound := card_le_card (inter_subset_right (s₁ := table.2.2.1 ∪ table.2.2.2)
      (s₂ := Ioc (n - q.val.card) p.val.card))
    rw [Nat.card_Ioc] at bound
    have union : (p.val ∪ q.val).card ≤ n := by simpa using card_le_univ (p.val ∪ q.val)
    have both := card_union_add_card_inter p.val q.val
    omega

/-- Allocate one odd cell per counted target and bound the available charges of every cell. -/
theorem mixed_rank_lower (n : ℕ) (table : RankCutTable n) :
    (cutDeficitSum table ≤ ∑ p : EvenSubset n, ∑ q : OddSubset n,
      (table.2.1 p q % 2) * chargeCount table p q) ∧
    (∀ p q, chargeCount table p q ≤ intervalCap table p q) ∧
    (∀ p q, intervalCap table p q ≤ if p = table.1 then 0 else (p.val ∩ q.val).card) ∧
    (∃ allocated : EvenSubset n → OddSubset n → ℕ,
      (∑ p, ∑ q, allocated p q) = cutDeficitSum table ∧
      ∀ p q, allocated p q ≤ (table.2.1 p q % 2) * chargeCount table p q) := by
  obtain ⟨allocated, eq, cap⟩ := exact_allocation table
  refine ⟨?_, chargeCount_le_interval table, intervalCap_le_intersection table, allocated, eq, cap⟩
  rw [← eq]
  exact sum_le_sum fun p _ => sum_le_sum fun q _ => cap p q

end D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds
