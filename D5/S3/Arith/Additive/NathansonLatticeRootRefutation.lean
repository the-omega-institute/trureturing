/- GID: D5/S3/Arith/Additive/NathansonLatticeRootRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/Additive/NathansonLatticeRootRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Algebra.Group.Pointwise.Finset.Basic, mathlib/module/Mathlib.Data.Finset.Sort, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Arith/Additive/NathansonLatticeRootRefutation.claim; result=D5/S3/Arith/Additive/NathansonLatticeRootRefutation.result; claim=D5/S3/Arith/Additive/NathansonLatticeRootRefutation.claim
   digest: Full-range least lattice diameters at h=2 and k=3 refute the exact root bound. -/

import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

namespace D5.S3.Arith.Additive.NathansonLatticeRootRefutation

open scoped Pointwise

/-- The entire range over all k-element integer sets; repetitions are allowed in hA. -/
def integerRange (h k : ℕ) : Set ℕ :=
  {t | ∃ A : Finset ℤ, A.card = k ∧ (nsmulRec h A).card = t}

/-- Integer lattice points of the inclusive n-dimensional cube. -/
def cube (n D : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun _ : Fin n => Finset.Icc (0 : ℤ) (D : ℤ))

/-- A positive interval diameter covering exactly the entire integer range. -/
def intervalCovers (h k D : ℕ) : Prop :=
  0 < D ∧ integerRange h k =
    {t | ∃ A : Finset ℤ, A.card = k ∧ A ⊆ Finset.Icc 0 (D : ℤ) ∧
      (nsmulRec h A).card = t}

/-- A positive lattice-cube diameter covering exactly the same entire integer range. -/
def cubeCovers (h k n D : ℕ) : Prop :=
  0 < D ∧ integerRange h k =
    {t | ∃ A : Finset (Fin n → ℤ), A.card = k ∧ A ⊆ cube n D ∧
      (nsmulRec h A).card = t}

/-- The actual least positive covering diameter, on its explicit existence domain. -/
noncomputable def N (h k : ℕ) (H : ∃ D, intervalCovers h k D) : ℕ := Nat.find H

/-- The actual least positive lattice-cube covering diameter, on its existence domain. -/
noncomputable def Nn (h k n : ℕ) (H : ∃ D, cubeCovers h k n D) : ℕ := Nat.find H

/-- The universal exact real-root inequality, with existence of its minima made explicit. -/
def claim : Prop :=
  ∀ h k n : ℕ, 2 ≤ h → 2 ≤ k → 1 ≤ n →
    ∃ (H : ∃ D, intervalCovers h k D) (Hn : ∃ D, cubeCovers h k n D),
      (Nn h k n Hn : ℝ) ≤ (N h k H : ℝ) ^ (1 / (n : ℝ))

private theorem pair_sums {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (a b c : α) :
    nsmulRec 2 ({a,b,c} : Finset α) = {a+a,a+b,a+c,b+b,b+c,c+c} := by
  ext x
  simp only [nsmulRec, zero_add, Finset.mem_add, Finset.mem_insert,
    Finset.mem_singleton]
  aesop (add simp [add_comm])

private theorem ordered_triple_card (a b c : ℤ) (hab : a < b) (hbc : b < c) :
    (nsmulRec 2 ({a,b,c} : Finset ℤ)).card = 5 ∨
      (nsmulRec 2 ({a,b,c} : Finset ℤ)).card = 6 := by
  rw [pair_sums]
  by_cases h : a+c = b+b
  · left
    simp only [h, Finset.insert_idem]
    simp (disch := simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
      only [Finset.card_insert_of_notMem, Finset.card_singleton]
  · right
    simp (disch := simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
      only [Finset.card_insert_of_notMem, Finset.card_singleton]

/-- The full range of two-fold sumsets of arbitrary integer triples. -/
theorem range_two_three : integerRange 2 3 = {5,6} := by
  ext t
  constructor
  · rintro ⟨A,hA,ht⟩
    let f := A.orderEmbOfFin hA
    have heq : A = {f 0,f 1,f 2} := by
      rw [← A.image_orderEmbOfFin_univ hA,
        show (Finset.univ : Finset (Fin 3)) = {0,1,2} by decide]
      simp [f]
    have hcard := ordered_triple_card (f 0) (f 1) (f 2)
      (f.strictMono (by decide)) (f.strictMono (by decide))
    rw [← heq, ht] at hcard
    simpa using hcard
  · intro ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact ⟨{0,1,2}, by decide, by decide +kernel⟩
    · exact ⟨{0,1,3}, by decide, by decide +kernel⟩

end D5.S3.Arith.Additive.NathansonLatticeRootRefutation
