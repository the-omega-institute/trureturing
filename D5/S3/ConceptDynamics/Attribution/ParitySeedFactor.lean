/- GID: D5/S3/ConceptDynamics/Attribution/ParitySeedFactor
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParitySeedFactor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reduce marked parity supports to parity factors with additive coordinate counts. -/

import D5.S3.ConceptDynamics.Attribution.ParitySeedSupport

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.ParitySeedFactor

open ParityOddRankBounds ParitySeedSupport ParitySeedCountSpectrum
open ParitySeedOptimization

noncomputable section
attribute [local instance] Classical.propDecidable

private def eraseMark {P Q : Type*} [DecidableEq P] [DecidableEq Q]
    (e : P → Q → Bool) (p₀ : P) (q₀ : Q) (p : P) (q : Q) : Bool :=
  e p q && decide (p ≠ p₀ ∨ q ≠ q₀)

private def insertMark {P Q : Type*} [DecidableEq P] [DecidableEq Q]
    (f : P → Q → Bool) (p₀ : P) (q₀ : Q) (selected : Bool) (p : P) (q : Q) : Bool :=
  f p q || (selected && decide (p = p₀ ∧ q = q₀))

private def markMass (selected : Bool) : ℕ := if selected then 1 else 2

private theorem sum_with_mark {A : Type*} [Fintype A] [DecidableEq A]
    (a₀ : A) (mass : ℕ) (base degree : A → ℕ)
    (atMark : base a₀ = degree a₀ + mass)
    (elsewhere : ∀ a, a ≠ a₀ → base a = degree a) :
    (∑ a, base a) = (∑ a, degree a) + mass := by
  calc
    (∑ a, base a) = ∑ a, (degree a + if a = a₀ then mass else 0) := by
      apply sum_congr rfl
      intro a _
      by_cases h : a = a₀
      · subst a
        simpa using atMark
      · simpa [h] using elsewhere a h
    _ = _ := by simp [sum_add_distrib]

private theorem erase_row_mass {d : ℕ} (e : EvenSubset d → OddSubset d → Bool)
    (full : EvenSubset d) (marked : OddSubset d) (p : EvenSubset d) :
    (∑ q, minimalBase e full marked p q) =
      (∑ q, (eraseMark e full marked p q).toNat) +
        (if p = full then markMass (e full marked) else 0) := by
  apply sum_with_mark marked
  · by_cases hp : p = full
    · subst p
      cases h : e full marked <;> simp [h, minimalBase, eraseMark, markMass]
    · simp [hp, minimalBase, eraseMark]
  · intro q hq
    simp [hq, minimalBase, eraseMark]

private theorem erase_col_mass {d : ℕ} (e : EvenSubset d → OddSubset d → Bool)
    (full : EvenSubset d) (marked : OddSubset d) (q : OddSubset d) :
    (∑ p, minimalBase e full marked p q) =
      (∑ p, (eraseMark e full marked p q).toNat) +
        (if q = marked then markMass (e full marked) else 0) := by
  apply sum_with_mark full
  · by_cases hq : q = marked
    · subst q
      cases h : e full marked <;> simp [h, minimalBase, eraseMark, markMass]
    · simp [hq, minimalBase, eraseMark]
  · intro p hp
    simp [hp, minimalBase, eraseMark]

/-- Degrees lie in an interval of one parity, with adjusted bounds at the two marked endpoints. -/
def residualDegree (k : ℕ) (selected endpoint : Bool) (degree : ℕ) : Prop :=
  degree ≤ (if endpoint then if selected then k - 1 else k - 2 else k) ∧
  degree % 2 = (if endpoint && selected then 0 else 1)

private theorem residualDegree_iff (k : ℕ) (selected endpoint : Bool) (degree : ℕ)
    (positive : 0 < k) (enough : selected = false → 3 ≤ k) :
    residualDegree k selected endpoint degree ↔
      let mass := degree + if endpoint then markMass selected else 0
      mass ≤ k ∧ mass % 2 = 1 := by
  dsimp [residualDegree, markMass]
  cases endpoint
  · simp
  · cases selected
    · have hk := enough rfl
      simp
      omega
    · simp
      omega

private theorem enough_if_unselected (k degree : ℕ) (selected : Bool)
    (cap : degree + markMass selected ≤ k) (odd : (degree + markMass selected) % 2 = 1) :
    selected = false → 3 ≤ k := by
  intro unselected
  simp [unselected, markMass] at cap odd
  omega

/-- Coordinate count expressed additively on the residual edges, with one marked-column charge. -/
def residualCount {d : ℕ} (f : EvenSubset d → OddSubset d → Bool)
    (full : EvenSubset d) (marked : OddSubset d) (i : Fin d) : ℕ :=
  4 * ((if i ∈ marked.val then 1 else 0) +
    ∑ p, ∑ q, if p ≠ full ∧ i ∈ p.val ∩ q.val then (f p q).toNat else 0)

private theorem erase_count {d : ℕ} (e : EvenSubset d → OddSubset d → Bool)
    (full : EvenSubset d) (fullSet : full.val = univ) (marked : OddSubset d) (i : Fin d) :
    supportCount (minimalBase e full marked) full marked i =
      residualCount (eraseMark e full marked) full marked i := by
  unfold supportCount residualCount
  apply congrArg (fun x : ℕ => 4 * x)
  let score (p : EvenSubset d) := ∑ q : OddSubset d, if i ∈ p.val ∩ q.val then
    if p = full then if q = marked then (1 : ℕ) else 0
    else minimalBase e full marked p q % 2 else 0
  let remainder (p : EvenSubset d) := ∑ q : OddSubset d,
    if p ≠ full ∧ i ∈ p.val ∩ q.val then (eraseMark e full marked p q).toNat else 0
  let offset : ℕ := if i ∈ marked.val then 1 else 0
  change (∑ p, score p) = offset + ∑ p, remainder p
  rw [← sum_erase_add _ score (mem_univ full), ← sum_erase_add _ remainder (mem_univ full)]
  have fullRow (q : OddSubset d) :
      (if i ∈ full.val ∩ q.val then if full = full then if q = marked then (1 : ℕ) else 0
        else minimalBase e full marked full q % 2 else 0) =
      (if q = marked then (if i ∈ marked.val then 1 else 0) else 0) := by
    by_cases hq : q = marked
    · subst q
      simp [fullSet]
    · simp [hq]
  have fullScore : score full = offset := by
    calc
      score full = ∑ q : OddSubset d, if q = marked then offset else 0 :=
        sum_congr rfl (fun q _ => fullRow q)
      _ = offset := by simp
  have noRemaining : remainder full = 0 := by simp [remainder]
  rw [fullScore, noRemaining, add_zero, add_comm]
  apply congrArg (offset + ·)
  refine sum_congr rfl fun p hp => sum_congr rfl fun q _ => ?_
  have hne := (mem_erase.mp hp).1
  cases h : e p q <;> simp [hne, h, minimalBase, eraseMark]

/-- A parity factor on the bipartite profile graph with the marked edge removed. -/
def markedFactorWithin (n k : ℕ) (budget : Fin (n + 2) → ℕ) : Prop :=
  ∃ (even : (n + 2) % 2 = 0) (f : EvenSubset (n + 2) → OddSubset (n + 2) → Bool)
    (marked : OddSubset (n + 2)) (selected : Bool),
    let full : EvenSubset (n + 2) := ⟨univ, by simpa using even⟩
    f full marked = false ∧ (selected = false → 3 ≤ k) ∧
    (∀ p, residualDegree k selected (decide (p = full)) (∑ q, (f p q).toNat)) ∧
    (∀ q, residualDegree k selected (decide (q = marked)) (∑ p, (f p q).toNat)) ∧
    ∀ i, residualCount f full marked i ≤ budget i

private theorem factor_support_iff (n k : ℕ) (positive : 0 < k) (budget : Fin (n + 2) → ℕ) :
    markedSupportWithin n k budget ↔ markedFactorWithin n k budget := by
  constructor
  · rintro ⟨even, e, marked, rows, cols, counts⟩
    let full : EvenSubset (n + 2) := ⟨univ, by simpa using even⟩
    let f := eraseMark e full marked
    let selected := e full marked
    have row := rows full
    change (∑ q, minimalBase e full marked full q) ≤ k ∧
      (∑ q, minimalBase e full marked full q) % 2 = 1 at row
    rw [erase_row_mass, ite_eq_left rfl] at row
    have enough := enough_if_unselected k _ selected row.1 row.2
    refine ⟨even, f, marked, selected, by
      change f full marked = false
      simp [f, eraseMark], enough, ?_, ?_, ?_⟩
    · intro p
      have h := rows p
      change (∑ q, minimalBase e full marked p q) ≤ k ∧
        (∑ q, minimalBase e full marked p q) % 2 = 1 at h
      rw [erase_row_mass] at h
      apply (residualDegree_iff k selected _ _ positive enough).mpr
      simpa [selected, f] using h
    · intro q
      have h := cols q
      change (∑ p, minimalBase e full marked p q) ≤ k ∧
        (∑ p, minimalBase e full marked p q) % 2 = 1 at h
      rw [erase_col_mass] at h
      apply (residualDegree_iff k selected _ _ positive enough).mpr
      simpa [selected, f] using h
    · intro i
      exact (erase_count e full rfl marked i).symm.le.trans (counts i)
  · rintro ⟨even, f, marked, selected, absent, enough, rows, cols, counts⟩
    let full : EvenSubset (n + 2) := ⟨univ, by simpa using even⟩
    let e := insertMark f full marked selected
    change f full marked = false at absent
    have bit : e full marked = selected := by
      simp [e, insertMark, absent]
    have restore : eraseMark e full marked = f := by
      funext p q
      by_cases hp : p = full <;> by_cases hq : q = marked
      · subst p
        subst q
        simp [eraseMark, absent]
      all_goals simp [e, insertMark, eraseMark, hp, hq]
    refine ⟨even, e, marked, ?_, ?_, ?_⟩
    · intro p
      change (∑ q, minimalBase e full marked p q) ≤ k ∧
        (∑ q, minimalBase e full marked p q) % 2 = 1
      simp only [erase_row_mass, restore, bit]
      simpa using (residualDegree_iff k selected _ _ positive enough).mp (rows p)
    · intro q
      change (∑ p, minimalBase e full marked p q) ≤ k ∧
        (∑ p, minimalBase e full marked p q) % 2 = 1
      simp only [erase_col_mass, restore, bit]
      simpa using (residualDegree_iff k selected _ _ positive enough).mp (cols q)
    · intro i
      change supportCount (minimalBase e full marked) full marked i ≤ budget i
      rw [erase_count e full rfl, restore]
      exact counts i

/-- Simultaneous coordinate budgets are equivalent to a parity factor and its additive counts. -/
theorem parity_factor_budget_iff (n k : ℕ) (even : (n + 2) % 2 = 0) (odd : k % 2 = 1)
    (budget : Fin (n + 2) → ℕ) :
    (∃ z : Fin (n + 2) → ℕ, RealizableSeedCounts n k z ∧ (∀ i, z i ≤ budget i)) ↔
    markedFactorWithin n k budget := by
  have positive : 0 < k := by omega
  exact (binary_support_iff n k even odd budget).trans (factor_support_iff n k positive budget)

end

end D5.S3.ConceptDynamics.Attribution.ParitySeedFactor
