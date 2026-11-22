/- GID: D5/S3/ConceptDynamics/Attribution/ParitySeedAxisFactor
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParitySeedAxisFactor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Characterize one-coordinate fixed-seed budgets on the Boolean lattice. -/

import D5.S3.ConceptDynamics.Attribution.ParitySeedFactor
import Mathlib.Data.Finset.BooleanAlgebra

open Finset
open D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds
open D5.S3.ConceptDynamics.Attribution.ParitySeedFactor
open D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor

noncomputable section

private abbrev AxisSubset (d : ℕ) (i : Fin d) := {A : Finset (Fin d) // i ∉ A}

private def eraseParityEquiv {d : ℕ} (i : Fin d) (r : ℕ) (hr : r < 2) :
    {s : Finset (Fin d) // s.card % 2 = r} ≃ AxisSubset d i where
  toFun s := ⟨s.val.erase i, notMem_erase i s.val⟩
  invFun A :=
    ⟨if A.val.card % 2 = r then A.val else insert i A.val, by
      split
      · assumption
      · rename_i h
        rw [card_insert_of_notMem A.property]
        omega⟩
  left_inv s := by
    apply Subtype.ext
    change (if (s.val.erase i).card % 2 = r then s.val.erase i
      else insert i (s.val.erase i)) = s.val
    by_cases hs : i ∈ s.val
    · rw [ite_eq_right, insert_erase hs]
      have hc := card_erase_add_one hs
      have hmod := s.property
      omega
    · simp [erase_eq_of_notMem hs, s.property]
  right_inv A := by
    apply Subtype.ext
    change (if A.val.card % 2 = r then A.val else insert i A.val).erase i = A.val
    split
    · exact erase_eq_of_notMem A.property
    · exact erase_insert A.property

private def complementOdd {d : ℕ} (even : d % 2 = 0) : OddSubset d ≃ OddSubset d where
  toFun q := ⟨q.valᶜ, by
    have hcard : q.val.card ≤ d := by simpa using card_le_univ q.val
    have hodd := q.property
    rw [card_compl, Fintype.card_fin]
    omega⟩
  invFun q := ⟨q.valᶜ, by
    have hcard : q.val.card ≤ d := by simpa using card_le_univ q.val
    have hodd := q.property
    rw [card_compl, Fintype.card_fin]
    omega⟩
  left_inv q := Subtype.ext (compl_compl q.val)
  right_inv q := Subtype.ext (compl_compl q.val)

private theorem axis_incidence {d : ℕ} (even : d % 2 = 0) (i : Fin d)
    (p : EvenSubset d) (q : OddSubset d) :
    (∀ j, j ≠ i → j ∉ p.val ∩ q.val) ↔
      (eraseParityEquiv i 0 (by decide) p).val ⊆
        (eraseParityEquiv i 1 (by decide) (complementOdd even q)).val := by
  change (∀ j, j ≠ i → j ∉ p.val ∩ q.val) ↔ p.val.erase i ⊆ q.valᶜ.erase i
  simp only [mem_inter, subset_iff, mem_erase, mem_compl]
  constructor
  · intro h j hj
    exact ⟨hj.1, fun hq => h j hj.1 ⟨hj.2, hq⟩⟩
  · intro h j hne hj
    exact (h ⟨hne, hj.1⟩).2 hj.2

private theorem recovered_axis_mem {d : ℕ} (i : Fin d) (r : ℕ) (hr : r < 2)
    (s : {s : Finset (Fin d) // s.card % 2 = r}) :
    i ∈ s.val ↔ (eraseParityEquiv i r hr s).val.card % 2 ≠ r := by
  change i ∈ s.val ↔ (s.val.erase i).card % 2 ≠ r
  have hp := s.property
  by_cases h : i ∈ s.val
  · have hc := card_erase_add_one h
    simp only [h, true_iff]
    omega
  · simp [h, hp]

private theorem axis_charge {d : ℕ} (even : d % 2 = 0) (i : Fin d)
    (p : EvenSubset d) (q : OddSubset d) :
    i ∈ p.val ∩ q.val ↔
      (eraseParityEquiv i 0 (by decide) p).val.card % 2 = 1 ∧
      (eraseParityEquiv i 1 (by decide) (complementOdd even q)).val.card % 2 = 1 := by
  rw [mem_inter, recovered_axis_mem i 0 (by decide) p]
  rw [show i ∈ q.val ↔ i ∉ (complementOdd even q).val by simp [complementOdd]]
  rw [recovered_axis_mem i 1 (by decide)]
  omega

private theorem nonaxis_zero_iff {d : ℕ} (i : Fin d)
    (f : EvenSubset d → OddSubset d → Bool)
    (full : EvenSubset d) (marked : OddSubset d) :
    (∀ j, j ≠ i → residualCount f full marked j = 0) ↔
    (∀ j, j ∈ marked.val → j = i) ∧
      ∀ p q, p ≠ full → f p q = true → ∀ j, j ≠ i → j ∉ p.val ∩ q.val := by
  constructor
  · intro zero
    constructor
    · intro j hj
      by_contra hne
      have h := zero j hne
      simp [residualCount, hj] at h
    · intro p q hp he j hne hj
      let cost (a : EvenSubset d) (b : OddSubset d) :=
        if a ≠ full ∧ j ∈ a.val ∩ b.val then (f a b).toNat else 0
      have single : cost p q ≤ ∑ b, cost p b := single_le_sum
        (fun _ _ => Nat.zero_le _) (mem_univ q)
      have row : (∑ b, cost p b) ≤ ∑ a, ∑ b, cost a b :=
        single_le_sum (f := fun a => ∑ b, cost a b) (fun _ _ => Nat.zero_le _) (mem_univ p)
      have degreeZero : (∑ a, ∑ b, cost a b) = 0 := by
        have h := zero j hne
        change 4 * ((if j ∈ marked.val then 1 else 0) + ∑ a, ∑ b, cost a b) = 0 at h
        omega
      have le := single.trans row
      rw [degreeZero] at le
      change (if p ≠ full ∧ j ∈ p.val ∩ q.val then (f p q).toNat else 0) ≤ 0 at le
      rw [ite_eq_left ⟨hp, hj⟩, he] at le
      exact Nat.not_succ_le_zero 0 le
  · rintro ⟨onlyMark, onlyEdges⟩ j hne
    have noMark : j ∉ marked.val := fun hj => hne (onlyMark j hj)
    have entry (p : EvenSubset d) (q : OddSubset d) :
        (if p ≠ full ∧ j ∈ p.val ∩ q.val then (f p q).toNat else 0) = 0 := by
      split
      · rename_i h
        cases he : f p q
        · rfl
        · exact (onlyEdges p q h.1 he j hne h.2).elim
      · rfl
    unfold residualCount
    simp_rw [entry]
    simp [noMark]

private theorem only_axis_mark {d : ℕ} (i : Fin d) (marked : OddSubset d) :
    (∀ j, j ∈ marked.val → j = i) ↔ marked.val = {i} := by
  constructor
  · intro h
    have ne : marked.val.Nonempty := by
      apply card_pos.mp
      have odd := marked.property
      omega
    obtain ⟨j, hj⟩ := ne
    have hi : i ∈ marked.val := h j hj ▸ hj
    ext a
    simp only [mem_singleton]
    exact ⟨h a, fun he => he.symm ▸ hi⟩
  · intro h j hj
    simpa [h] using hj

private def axisRows {d : ℕ} (i : Fin d) : EvenSubset d ≃ AxisSubset d i :=
  eraseParityEquiv i 0 (by decide)

private def axisCols {d : ℕ} (even : d % 2 = 0) (i : Fin d) :
    OddSubset d ≃ AxisSubset d i :=
  (complementOdd even).trans (eraseParityEquiv i 1 (by decide))

private def axisTop {d : ℕ} (i : Fin d) : AxisSubset d i :=
  ⟨univ.erase i, notMem_erase i univ⟩

private def singletonOdd {d : ℕ} (i : Fin d) : OddSubset d :=
  ⟨{i}, by simp⟩

private theorem axis_image_col {d : ℕ} (even : d % 2 = 0) (i : Fin d) :
    axisCols even i (singletonOdd i) = axisTop i := by
  apply Subtype.ext
  change ({i} : Finset (Fin d))ᶜ.erase i = univ.erase i
  ext j
  simp [eq_comm]

private theorem axis_sum_row {d : ℕ} (even : d % 2 = 0) (i : Fin d)
    (f : AxisSubset d i → AxisSubset d i → Bool) (A : AxisSubset d i) :
    (∑ q : OddSubset d, (f A (axisCols even i q)).toNat) = ∑ B, (f A B).toNat :=
  (axisCols even i).sum_comp (fun B => (f A B).toNat)

private theorem axis_sum_col {d : ℕ} (i : Fin d)
    (f : AxisSubset d i → AxisSubset d i → Bool) (B : AxisSubset d i) :
    (∑ p : EvenSubset d, (f (axisRows i p) B).toNat) = ∑ A, (f A B).toNat :=
  (axisRows i).sum_comp (fun A => (f A B).toNat)

private def axisCost {d : ℕ} (i : Fin d) (f : AxisSubset d i → AxisSubset d i → Bool) : ℕ :=
  4 * (1 + ∑ A, ∑ B,
    if A ≠ axisTop i ∧ A.val.card % 2 = 1 ∧ B.val.card % 2 = 1
    then (f A B).toNat else 0)

private theorem reindex_axis_cost {d : ℕ} (even : d % 2 = 0) (i : Fin d)
    (f : AxisSubset d i → AxisSubset d i → Bool)
    (full : EvenSubset d) (hfull : full.val = univ) :
    residualCount (fun p q => f (axisRows i p) (axisCols even i q)) full (singletonOdd i) i =
      axisCost i f := by
  have pivot : axisRows i full = axisTop i := by
    apply Subtype.ext
    exact congrArg (fun s : Finset (Fin d) => s.erase i) hfull
  have offPivot (p : EvenSubset d) : p ≠ full ↔ axisRows i p ≠ axisTop i := by
    rw [← pivot, (axisRows i).injective.ne_iff]
  let score (A B : AxisSubset d i) : ℕ :=
    if A ≠ axisTop i ∧ A.val.card % 2 = 1 ∧ B.val.card % 2 = 1
    then (f A B).toNat else 0
  have counts (p : EvenSubset d) (q : OddSubset d) :
      (if p ≠ full ∧ i ∈ p.val ∩ q.val then (f (axisRows i p) (axisCols even i q)).toNat else 0) =
      score (axisRows i p) (axisCols even i q) := by
    unfold score
    have agree : (p ≠ full ∧ i ∈ p.val ∩ q.val) ↔
        axisRows i p ≠ axisTop i ∧ (axisRows i p).val.card % 2 = 1 ∧
          (axisCols even i q).val.card % 2 = 1 :=
      and_congr (offPivot p) (axis_charge even i p q)
    by_cases h : p ≠ full ∧ i ∈ p.val ∩ q.val
    · rw [ite_eq_left h, ite_eq_left (agree.mp h)]
    · rw [ite_eq_right h, ite_eq_right (mt agree.mpr h)]
  unfold residualCount axisCost
  simp only [singletonOdd, mem_singleton_self, ite_true]
  apply congrArg (fun t : ℕ => 4 * (1 + t))
  calc
    _ = ∑ p : EvenSubset d, ∑ q : OddSubset d, score (axisRows i p) (axisCols even i q) :=
      sum_congr rfl (fun p _ => sum_congr rfl (fun q _ => counts p q))
    _ = ∑ p : EvenSubset d, ∑ B : AxisSubset d i, score (axisRows i p) B :=
      sum_congr rfl (fun p _ => (axisCols even i).sum_comp (score (axisRows i p)))
    _ = ∑ A : AxisSubset d i, ∑ B : AxisSubset d i, score A B :=
      (axisRows i).sum_comp (fun A => ∑ B, score A B)

/-- A single-coordinate budget expressed as a parity factor on two copies of the subset lattice. -/
def axisFactorWithin {d : ℕ} (k : ℕ) (i : Fin d) (budget : ℕ) : Prop :=
  ∃ (f : AxisSubset d i → AxisSubset d i → Bool) (selected : Bool),
    f (axisTop i) (axisTop i) = false ∧ (selected = false → 3 ≤ k) ∧
    (∀ A, residualDegree k selected (decide (A = axisTop i)) (∑ B, (f A B).toNat)) ∧
    (∀ B, residualDegree k selected (decide (B = axisTop i)) (∑ A, (f A B).toNat)) ∧
    (∀ A B, A ≠ axisTop i → f A B = true → A.val ⊆ B.val) ∧
    axisCost i f ≤ budget

private theorem reindex_axis_iff (n k : ℕ) (i : Fin (n + 2)) (budget : ℕ)
    (even : (n + 2) % 2 = 0) :
    markedFactorWithin n k (fun j => if j = i then budget else 0) ↔
      axisFactorWithin k i budget := by
  let L := axisRows i
  let R := axisCols even i
  let full : EvenSubset (n + 2) := ⟨univ, by simpa using even⟩
  let marked := singletonOdd i
  have lTop : L full = axisTop i := rfl
  have rTop : R marked = axisTop i := axis_image_col even i
  have lEnd (p : EvenSubset (n + 2)) :
      decide (p = full) = decide (L p = axisTop i) := by
    simp only [← lTop, L.injective.eq_iff]
  have rEnd (q : OddSubset (n + 2)) :
      decide (q = marked) = decide (R q = axisTop i) := by
    simp only [← rTop, R.injective.eq_iff]
  constructor
  · rintro ⟨_, g, q₀, selected, edge, enough, rows, cols, counts⟩
    have zeros : ∀ j, j ≠ i → residualCount g full q₀ j = 0 := by
      intro j hj
      exact Nat.eq_zero_of_le_zero (by simpa [hj] using counts j)
    obtain ⟨markOnly, edgeOnly⟩ := (nonaxis_zero_iff i g full q₀).mp zeros
    have atMark : q₀ = marked := Subtype.ext ((only_axis_mark i q₀).mp markOnly)
    subst q₀
    let f (A B : AxisSubset (n + 2) i) := g (L.symm A) (R.symm B)
    have gather (p : EvenSubset (n + 2)) (q : OddSubset (n + 2)) :
        f (L p) (R q) = g p q := by simp [f]
    have score := reindex_axis_cost even i f full rfl
    change residualCount (fun p q => f (L p) (R q)) full marked i = axisCost i f at score
    simp only [gather] at score
    refine ⟨f, selected, ?_, enough, ?_, ?_, ?_, ?_⟩
    · calc
        f (axisTop i) (axisTop i) = f (L full) (R marked) :=
          congrArg₂ f lTop.symm rTop.symm
        _ = g full marked := gather full marked
        _ = false := edge
    · intro A
      obtain ⟨p, rfl⟩ := L.surjective A
      have row := rows p
      change residualDegree k selected (decide (p = full)) (∑ q, (g p q).toNat) at row
      rw [← axis_sum_row even i f (L p), ← lEnd p]
      change residualDegree k selected (decide (p = full))
        (∑ q, (f (L p) (R q)).toNat)
      simpa only [gather] using row
    · intro B
      obtain ⟨q, rfl⟩ := R.surjective B
      have col := cols q
      change residualDegree k selected (decide (q = marked)) (∑ p, (g p q).toNat) at col
      rw [← axis_sum_col i f (R q), ← rEnd q]
      change residualDegree k selected (decide (q = marked))
        (∑ p, (f (L p) (R q)).toNat)
      simpa only [gather] using col
    · intro A B hA present
      obtain ⟨p, rfl⟩ := L.surjective A
      obtain ⟨q, rfl⟩ := R.surjective B
      have hp : p ≠ full := fun e => hA (e ▸ lTop)
      rw [gather] at present
      exact (axis_incidence even i p q).mp (edgeOnly p q hp present)
    · rw [← score]
      simpa using counts i
  · rintro ⟨f, selected, edge, enough, rows, cols, permitted, count⟩
    let g (p : EvenSubset (n + 2)) (q : OddSubset (n + 2)) := f (L p) (R q)
    have zeros : ∀ j, j ≠ i → residualCount g full marked j = 0 := by
      apply (nonaxis_zero_iff i g full marked).mpr
      refine ⟨(only_axis_mark i marked).mpr rfl, ?_⟩
      intro p q hp present
      have off : L p ≠ axisTop i := fun e => hp (L.injective (e.trans lTop.symm))
      exact (axis_incidence even i p q).mpr (permitted (L p) (R q) off present)
    refine ⟨even, g, marked, selected, ?_, enough, ?_, ?_, ?_⟩
    · change f (L full) (R marked) = false
      rwa [lTop, rTop]
    · intro p
      change residualDegree k selected (decide (p = full))
        (∑ q : OddSubset (n + 2), (f (L p) (R q)).toNat)
      rw [lEnd, axis_sum_row]
      exact rows _
    · intro q
      change residualDegree k selected (decide (q = marked))
        (∑ p : EvenSubset (n + 2), (f (L p) (R q)).toNat)
      rw [rEnd, axis_sum_col]
      exact cols _
    · intro j
      change residualCount g full marked j ≤ if j = i then budget else 0
      by_cases h : j = i
      · subst j
        rw [ite_eq_left rfl, reindex_axis_cost even i f full rfl]
        exact count
      · rw [zeros j h, ite_eq_right h]

/-- A single-coordinate fixed-seed budget is equivalent to the parity-factor problem
on two copies of the subsets of the remaining coordinates. -/
theorem axis_budget_iff (n k : ℕ) (even : (n + 2) % 2 = 0) (odd : k % 2 = 1)
    (i : Fin (n + 2)) (budget : ℕ) :
    (∃ z : Fin (n + 2) → ℕ, RealizableSeedCounts n k z ∧
      (∀ j, z j ≤ if j = i then budget else 0)) ↔
      axisFactorWithin k i budget :=
  (parity_factor_budget_iff n k even odd _).trans (reindex_axis_iff n k i budget even)






end

end D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor
