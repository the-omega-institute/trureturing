/- GID: D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Partitions/HalvingPartitionNonregularity
   mirror-E: none(waiver:unbounded-symbolic-question)
   anchors: []
   utility: none
   digest: Exact ordered-list count and unrestricted binary matrix-family question. -/

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! Exact source carriers and the unrestricted regularity question. -/

namespace D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity

/-- A value-set test: coincident lower and upper halves are not separate labels. -/
def IsHalf (previous next : ℕ) : Prop :=
  next = previous / 2 ∨ next = (previous + 1) / 2

instance (previous next : ℕ) : Decidable (IsHalf previous next) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The virtual predecessor is supplied separately; every finite length is allowed. -/
def Follows : ℕ → List ℕ → Prop
  | _, [] => True
  | previous, next :: rest => IsHalf previous next ∧ Follows next rest

instance (previous : ℕ) (parts : List ℕ) : Decidable (Follows previous parts) := by
  induction parts generalizing previous with
  | nil => exact isTrue trivial
  | cons next rest ih => exact @instDecidableAnd _ _ (inferInstance) (ih next)

/-- Independent source carrier: actual positive ordered lists of total n. -/
def SourceLists (n : ℕ) :=
  {parts : List ℕ // (∀ x ∈ parts, 0 < x) ∧ parts.sum = n ∧ Follows n parts}

/-- The existing finite composition carrier, filtered by the same halving condition. -/
def HalvingCompositions (n : ℕ) := {c : Composition n // Follows n c.blocks}

/-- The list is unchanged in both directions; no order or multiplicity is quotiented. -/
def sourceEquiv (n : ℕ) : SourceLists n ≃ HalvingCompositions n where
  toFun p := ⟨⟨p.1, fun h => p.2.1 _ h, p.2.2.1⟩, p.2.2.2⟩
  invFun c := ⟨c.1.blocks, ⟨fun _ h => c.1.blocks_pos h, c.1.blocks_sum, c.2⟩⟩
  left_inv p := by cases p; rfl
  right_inv c := by cases c; rfl

instance (n : ℕ) : Fintype (HalvingCompositions n) := by
  unfold HalvingCompositions
  infer_instance

instance (n : ℕ) : Finite (SourceLists n) :=
  Finite.of_equiv (HalvingCompositions n) (sourceEquiv n).symm

/-- Counts the independently specified lists, without a recurrence or proposed formula. -/
noncomputable def count (n : ℕ) : ℕ := Nat.card (SourceLists n)

/-- Fixed integral matrices, all inputs, both digits, arbitrary positive dimension. -/
def MatrixFamily (a : ℕ → ℤ) : Prop :=
  ∃ d : ℕ, ∃ hd : 0 < d, ∃ F : ℕ → Fin d → ℤ,
    ∃ M0 M1 : Matrix (Fin d) (Fin d) ℤ,
      (∀ n, F n ⟨0, hd⟩ = a n) ∧
      (∀ n, F (2 * n) = M0.mulVec (F n)) ∧
      (∀ n, F (2 * n + 1) = M1.mulVec (F n))

/-- A finite indexed family, with no independence or basis assumption. -/
def ClosedFamily (a : ℕ → ℤ) : Prop :=
  ∃ d : ℕ, ∃ hd : 0 < d, ∃ b : Fin d → ℕ → ℤ,
    ∃ c0 c1 : Fin d → Fin d → ℤ,
      (∀ n, b ⟨0, hd⟩ n = a n) ∧
      (∀ i n, b i (2 * n) = ∑ j, c0 i j * b j n) ∧
      (∀ i n, b i (2 * n + 1) = ∑ j, c1 i j * b j n)

/-- The registered negative event; no theorem asserting it is supplied here. -/
def claim : Prop := ¬ MatrixFamily (fun n => (count n : ℤ))

end D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity
