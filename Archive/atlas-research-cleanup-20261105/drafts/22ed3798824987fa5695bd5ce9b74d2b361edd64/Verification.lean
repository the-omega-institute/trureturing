import PairedDeletionFiber

set_option autoImplicit false

open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
open D5.S3.Combinatorics.CircularWords.PairedDeletionFiber

universe u
variable {α : Type u} [DecidableEq α]

-- The requested at-least-four range is an exact specialization.
example {A : Finset α} (hA : 4 ≤ A.card)
    {a b : α} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    {C D : Cycle α} (hC : C.Nodup) (hD : D.Nodup)
    (sC : C.toFinset = A) (sD : D.toFinset = A) :
    (delete a C = delete a D ∧ delete b C = delete b D) ↔
      C = D ∨ ∃ r ∈ A, r ≠ a ∧ r ≠ b ∧ adjacentSwapAt r a b C D :=
  paired_fiber_iff (by omega) ha hb hab hC hD sC sD

-- An arbitrary word cut through the deleted block is covered by rotation.
example {A : Finset α} (hA : 3 ≤ A.card)
    {r a b : α} (hr : r ∈ A) (ha : a ∈ A) (hb : b ∈ A)
    (hra : r ≠ a) (hrb : r ≠ b) (hab : a ≠ b)
    (P : List α) (hN : (a :: r :: P ++ [b]).Nodup)
    (hs : (a :: r :: P ++ [b] : Cycle α).toFinset = A) :
    ∃ D : Cycle α, D.Nodup ∧ D.toFinset = A ∧
      D ≠ (a :: r :: P ++ [b] : Cycle α) ∧
      delete a (a :: r :: P ++ [b] : Cycle α) = delete a D ∧
      delete b (a :: r :: P ++ [b] : Cycle α) = delete b D := by
  apply (exists_nontrivial_alternative_iff_cyclicAdjacent hA ha hb hab
    (Cycle.nodup_coe_iff.mpr hN) hs).mpr
  refine ⟨r, hr, hra, hrb, P, [], Or.inr ?_⟩
  simpa [List.append_assoc] using Cycle.coe_cons_eq_coe_append (r :: P ++ [b]) a

-- The size-three boundary is inhabited in the actual quotient model.
example : ∃ D : Cycle (Fin 3), D.Nodup ∧ D.toFinset = Finset.univ ∧
    D ≠ ([0,1,2] : Cycle (Fin 3)) ∧
    delete 0 ([0,1,2] : Cycle (Fin 3)) = delete 0 D ∧
    delete 1 ([0,1,2] : Cycle (Fin 3)) = delete 1 D := by
  apply (exists_nontrivial_alternative_iff_cyclicAdjacent (by decide)
    (a := (0 : Fin 3)) (b := (1 : Fin 3)) (by simp) (by simp) (by decide)
    (C := ([0,1,2] : Cycle (Fin 3))) (by decide) (by decide)).mpr
  refine ⟨2, by simp, by decide, by decide, [], [], Or.inl ?_⟩
  exact Cycle.coe_eq_coe.mpr ⟨2, by decide⟩
