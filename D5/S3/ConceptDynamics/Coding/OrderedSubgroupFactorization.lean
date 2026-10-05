/- GID: D5/S3/ConceptDynamics/Coding/OrderedSubgroupFactorization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/OrderedSubgroupFactorization
   mirror-E: none(waiver:registration-paused)
   anchors: []
   utility: none
   digest: The natural minimum scan preserves both original margins in one table. -/

import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.OrderedSubgroupFactorization

open scoped BigOperators

universe u v

/-- Residual row demands, residual column capacities, and the one recorded table. -/
abbrev AllocationState (Row : Type u) (Column : Type v) :=
  (Row → ℕ) × (Column → ℕ) × (Row × Column → ℕ)

/-- One pre-update minimum is used in both subtractions and the actual cell write. -/
def allocateCell {Row : Type u} {Column : Type v}
    [DecidableEq Row] [DecidableEq Column]
    (s : AllocationState Row Column) (cell : Row × Column) : AllocationState Row Column :=
  let amount := min (s.1 cell.1) (s.2.1 cell.2)
  (fun i => if i = cell.1 then s.1 i - amount else s.1 i,
   fun j => if j = cell.2 then s.2.1 j - amount else s.2.1 j,
   fun ij => s.2.2 ij + if ij = cell then amount else 0)

/-- The whole rectangle is scanned in the supplied row order and column order,
including every zero allocation. Actual coset lists can use their prescribed least-element order. -/
def orderedAllocation {Row : Type u} {Column : Type v}
    [DecidableEq Row] [DecidableEq Column]
    (rows : List Row) (columns : List Column)
    (demand : Row → ℕ) (capacity : Column → ℕ) : AllocationState Row Column :=
  (rows ×ˢ columns).foldl allocateCell (demand, capacity, fun _ => 0)

/-- Complete-grid complementarity closes both original ledgers simultaneously.
No feasible table or row-completion premise is supplied. The prefix assertion
also records zero unvisited cells and persistent exhaustion of visited endpoints. -/
theorem ordered_allocation_complete
    {Row : Type u} {Column : Type v}
    [Fintype Row] [Fintype Column] [DecidableEq Row] [DecidableEq Column]
    (rows : List Row) (columns : List Column)
    (allRows : ∀ i, i ∈ rows) (allColumns : ∀ j, j ∈ columns)
    (demand : Row → ℕ) (capacity : Column → ℕ)
    (balanced : (∑ i, demand i) = ∑ j, capacity j) :
    let s := orderedAllocation rows columns demand capacity
    (∀ i, s.1 i = 0 ∧ (∑ j, s.2.2 (i, j)) = demand i) ∧
    (∀ j, s.2.1 j = 0 ∧ (∑ i, s.2.2 (i, j)) = capacity j) ∧
    (∀ past future, rows ×ˢ columns = past ++ future →
      let t := past.foldl allocateCell (demand, capacity, fun _ => 0)
      (∀ i, t.1 i + (∑ j, t.2.2 (i, j)) = demand i) ∧
      (∀ j, t.2.1 j + (∑ i, t.2.2 (i, j)) = capacity j) ∧
      (∀ cell ∈ past, t.1 cell.1 = 0 ∨ t.2.1 cell.2 = 0) ∧
      (∀ cell, cell ∉ past → t.2.2 cell = 0) ∧
      (∀ i, t.1 i ≤ demand i) ∧ (∀ j, t.2.1 j ≤ capacity j)) := by
  classical
  let Inv (past : List (Row × Column)) (s : AllocationState Row Column) : Prop :=
    (∀ i, s.1 i + (∑ j, s.2.2 (i, j)) = demand i) ∧
    (∀ j, s.2.1 j + (∑ i, s.2.2 (i, j)) = capacity j) ∧
    (∀ cell ∈ past, s.1 cell.1 = 0 ∨ s.2.1 cell.2 = 0) ∧
    (∀ cell, cell ∉ past → s.2.2 cell = 0) ∧
    (∀ i, s.1 i ≤ demand i) ∧ (∀ j, s.2.1 j ≤ capacity j)
  have step (past : List (Row × Column)) (s : AllocationState Row Column)
      (cell : Row × Column) (hs : Inv past s) :
      Inv (past ++ [cell]) (allocateCell s cell) := by
    let x := min (s.1 cell.1) (s.2.1 cell.2)
    have rowSum (i : Row) :
        (∑ j, (allocateCell s cell).2.2 (i, j)) =
          (∑ j, s.2.2 (i, j)) + if i = cell.1 then x else 0 := by
      rcases cell with ⟨a, b⟩
      by_cases hi : i = a
      · subst i
        simp [allocateCell, x, Finset.sum_add_distrib]
      · simp [allocateCell, x, hi]
    have columnSum (j : Column) :
        (∑ i, (allocateCell s cell).2.2 (i, j)) =
          (∑ i, s.2.2 (i, j)) + if j = cell.2 then x else 0 := by
      rcases cell with ⟨a, b⟩
      by_cases hj : j = b
      · subst j
        simp [allocateCell, x, Finset.sum_add_distrib]
      · simp [allocateCell, x, hj]
    have rowDecrease (i : Row) : (allocateCell s cell).1 i ≤ s.1 i := by
      simp only [allocateCell]
      split_ifs <;> omega
    have columnDecrease (j : Column) : (allocateCell s cell).2.1 j ≤ s.2.1 j := by
      simp only [allocateCell]
      split_ifs <;> omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      rw [rowSum]
      have old := hs.1 i
      by_cases hi : i = cell.1
      · subst i
        have hx : x ≤ s.1 cell.1 := min_le_left _ _
        simp only [allocateCell, x, ↓reduceIte]
        omega
      · simpa [allocateCell, hi] using old
    · intro j
      rw [columnSum]
      have old := hs.2.1 j
      by_cases hj : j = cell.2
      · subst j
        have hx : x ≤ s.2.1 cell.2 := min_le_right _ _
        simp only [allocateCell, x, ↓reduceIte]
        omega
      · simpa [allocateCell, hj] using old
    · intro old hold
      rcases List.mem_append.mp hold with hold | hold
      · rcases hs.2.2.1 old hold with hr | hc
        · left
          have h := rowDecrease old.1
          omega
        · right
          have h := columnDecrease old.2
          omega
      · have heq : old = cell := by simpa using hold
        subst old
        by_cases h : s.1 cell.1 ≤ s.2.1 cell.2
        · left
          simp [allocateCell, min_eq_left h]
        · right
          simp [allocateCell, min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))]
    · intro old hold
      have hp : old ∉ past := fun h => hold (List.mem_append_left _ h)
      have hn : old ≠ cell := by
        intro h
        apply hold
        simp [h]
      simp [allocateCell, hs.2.2.2.1 old hp, hn]
    · intro i
      exact (rowDecrease i).trans (hs.2.2.2.2.1 i)
    · intro j
      exact (columnDecrease j).trans (hs.2.2.2.2.2 j)
  have prefixInvariant (past : List (Row × Column)) :
      Inv past (past.foldl allocateCell (demand, capacity, fun _ => 0)) := by
    induction past using List.reverseRecOn with
    | nil => simp [Inv]
    | append_singleton past cell ih =>
        rw [List.foldl_append]
        exact step past _ cell ih
  let s := orderedAllocation rows columns demand capacity
  have final : Inv (rows ×ˢ columns) s := prefixInvariant _
  have totals : (∑ i, s.1 i) = ∑ j, s.2.1 j := by
    have hr := Finset.sum_congr (s₁ := (Finset.univ : Finset Row)) rfl
      (fun i _ => final.1 i)
    have hc := Finset.sum_congr (s₁ := (Finset.univ : Finset Column)) rfl
      (fun j _ => final.2.1 j)
    simp only [Finset.sum_add_distrib] at hr hc
    rw [Finset.sum_comm] at hr
    apply Nat.add_right_cancel
    exact hr.trans (balanced.trans hc.symm)
  have allExhausted (i : Row) (j : Column) : s.1 i = 0 ∨ s.2.1 j = 0 :=
    final.2.2.1 (i, j) (List.mem_product.mpr ⟨allRows i, allColumns j⟩)
  have rowsZero (i : Row) : s.1 i = 0 := by
    by_contra hi
    have columnsZero (j : Column) : s.2.1 j = 0 := (allExhausted i j).resolve_left hi
    have hsum : (∑ j, s.2.1 j) = 0 := Finset.sum_eq_zero (fun j _ => columnsZero j)
    have hbound : s.1 i ≤ ∑ k, s.1 k :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have columnsZero (j : Column) : s.2.1 j = 0 := by
    have hsum : (∑ i, s.1 i) = 0 := Finset.sum_eq_zero (fun i _ => rowsZero i)
    have hbound : s.2.1 j ≤ ∑ k, s.2.1 k :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact ⟨rowsZero i, by simpa [rowsZero i] using final.1 i⟩
  · intro j
    exact ⟨columnsZero j, by simpa [columnsZero j] using final.2.1 j⟩
  · intro past future _
    exact prefixInvariant past

section NativeCosets

variable {H : Type u} [Group H] [Fintype H] [LinearOrder H]
  (K : Subgroup H) [DecidablePred (fun h : H => h ∈ K)]

/-- Source C=hK is Mathlib's left coset; this definition uses its actual members. -/
def sourceRightCoset (h : H) : Finset H :=
  Finset.univ.filter (fun x => h⁻¹ * x ∈ K)

/-- Source L=Kh is Mathlib's right coset; no commutation is used. -/
def sourceLeftCoset (h : H) : Finset H :=
  Finset.univ.filter (fun x => x * h⁻¹ ∈ K)

/-- The actual set KhK, enumerated by the two subgroup multipliers in their order. -/
def sourceDoubleCoset (h : H) : Finset H :=
  ((Finset.univ.filter (fun k : H => k ∈ K)) ×ˢ
    (Finset.univ.filter (fun k : H => k ∈ K))).image
    (fun pair => pair.1 * h * pair.2)

/-- Least representatives depend only on the prescribed order of actual members. -/
def leastRightRepresentative (h : H) : H :=
  (sourceRightCoset K h).min' ⟨h, by simp [sourceRightCoset]⟩

def leastLeftRepresentative (h : H) : H :=
  (sourceLeftCoset K h).min' ⟨h, by simp [sourceLeftCoset]⟩

def leastDoubleRepresentative (h : H) : H :=
  (sourceDoubleCoset K h).min' (by
    refine ⟨h, Finset.mem_image.mpr ?_⟩
    exact ⟨(1, 1), by simp, by simp⟩)

/-- Image removes repeated cosets before ordering their least representatives. -/
def rightRepresentatives : Finset H := Finset.univ.image (leastRightRepresentative K)
def leftRepresentatives : Finset H := Finset.univ.image (leastLeftRepresentative K)
def doubleRepresentatives : Finset H := Finset.univ.image (leastDoubleRepresentative K)

def blockRows (d : H) : Finset H :=
  (rightRepresentatives K).filter (fun r => r ∈ sourceDoubleCoset K d)

def blockColumns (d : H) : Finset H :=
  (leftRepresentatives K).filter (fun c => c ∈ sourceDoubleCoset K d)

/-- Sorting the representative subtypes is sorting by their actual least group elements. -/
def blockAllocation (a : MonoidAlgebra ℕ H) (b : ℕ) (d : H) :
    AllocationState (blockRows K d) (blockColumns K d) :=
  orderedAllocation
    ((Finset.univ : Finset (blockRows K d)).sort (· ≤ ·))
    ((Finset.univ : Finset (blockColumns K d)).sort (· ≤ ·))
    (fun r => a.coeff r.val) (fun _ => b)

/-- The coefficient table records only the least actual cell member.
An empty cell contributes zero; exact transient applications verify that actual
block cells are nonempty. -/
def blockMass (a : MonoidAlgebra ℕ H) (b : ℕ) (d : H) : H → ℕ :=
  let table := blockAllocation K a b d
  fun h => ∑ r : blockRows K d, ∑ c : blockColumns K d,
    let cell := sourceRightCoset K r.val ∩ sourceLeftCoset K c.val
    if hc : cell.Nonempty then
      if cell.min' hc = h then table.2.2 (r, c) else 0
    else 0

/-- Native coefficients are assembled directly, without a second allocation algorithm. -/
def orderedFactor (a : MonoidAlgebra ℕ H) (b : ℕ) : MonoidAlgebra ℕ H :=
  let blocks := ((doubleRepresentatives K).sort (· ≤ ·)).map (blockMass K a b)
  let mass := fun h => (blocks.map (fun f => f h)).sum
  MonoidAlgebra.ofCoeff {
    support := Finset.univ.filter (fun h => mass h ≠ 0)
    toFun := mass
    mem_support_toFun := by intro h; simp }

def subgroupUniform : MonoidAlgebra ℕ H :=
  MonoidAlgebra.ofCoeff {
    support := Finset.univ.filter (fun k : H => k ∈ K)
    toFun := fun k => if k ∈ K then 1 else 0
    mem_support_toFun := by intro k; simp }

def groupUniform : MonoidAlgebra ℕ H :=
  MonoidAlgebra.ofCoeff {
    support := Finset.univ
    toFun := fun _ => 1
    mem_support_toFun := by intro h; simp }

/-- Exact finite failures retain two actual unequal coefficients or an actual block. -/
def firstCoefficientMismatch (a : MonoidAlgebra ℕ H) : Option (H × H) :=
  ((Finset.univ : Finset H).sort (· ≤ ·)).findSome? (fun h =>
    (((sourceRightCoset K h).filter (fun x => a.coeff h ≠ a.coeff x)).sort
      (· ≤ ·)).head?.map (fun x => (h, x)))

def firstBalanceMismatch (a : MonoidAlgebra ℕ H) (b : ℕ) : Option H :=
  (((doubleRepresentatives K).filter (fun d =>
    (∑ r ∈ blockRows K d, a.coeff r) ≠ (blockRows K d).card * b)).sort (· ≤ ·)).head?

/-- This is the prescribed finite inspection and producer, not an abstract feasible witness.
Exact transient applications verify product correctness, both fixed-factor criteria,
and the actual finite failure witnesses without retained companion declarations. -/
def inspectAndConstruct (a : MonoidAlgebra ℕ H) (b : ℕ) :
    Sum (Sum (H × H) H) (MonoidAlgebra ℕ H) :=
  match firstCoefficientMismatch K a with
  | some pair => .inl (.inl pair)
  | none => match firstBalanceMismatch K a b with
    | some d => .inl (.inr d)
    | none => .inr (orderedFactor K a b)

end NativeCosets

#print axioms ordered_allocation_complete

end D5.S3.ConceptDynamics.Coding.OrderedSubgroupFactorization
