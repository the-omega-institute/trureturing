/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport/SquareTranspose
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport/SquareTranspose
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coordinate exchange is a graph isomorphism for positive rectangular square grids. -/

/-
admission_basis: escape-witness
escape_witness: coordinate swap exchanges every oriented horizontal bond with an
oriented vertical bond, and conversely, for the existing square strip graph.
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.SquareTranspose

/-- Coordinate exchange interchanges the two actual square bond directions. -/
def squareTranspose (n k : ℕ) : stripGraph false n k ≃g stripGraph false k n where
  toEquiv := Equiv.prodComm _ _
  map_rel_iff' := by
    intro a b
    let horizontal (n k : ℕ) (x y : Fin (n + 1) × Fin (k + 1)) : Prop :=
      ∃ i : Fin (n + 1), ∃ j : Fin k, x = (i, j.castSucc) ∧ y = (i, j.succ)
    let vertical (n k : ℕ) (x y : Fin (n + 1) × Fin (k + 1)) : Prop :=
      ∃ i : Fin n, ∃ j : Fin (k + 1), x = (i.castSucc, j) ∧ y = (i.succ, j)
    have swapForward (r c : ℕ) (x y : Fin (r + 1) × Fin (c + 1)) :
        horizontal r c x y ∨ vertical r c x y →
          horizontal c r x.swap y.swap ∨ vertical c r x.swap y.swap := by
      rintro (⟨i, j, rfl, rfl⟩ | ⟨i, j, rfl, rfl⟩)
      · exact Or.inr ⟨j, i, rfl, rfl⟩
      · exact Or.inl ⟨j, i, rfl, rfl⟩
    change ((horizontal k n a.swap b.swap ∨ vertical k n a.swap b.swap) ∨
      (horizontal k n b.swap a.swap ∨ vertical k n b.swap a.swap)) ↔
      ((horizontal n k a b ∨ vertical n k a b) ∨
        (horizontal n k b a ∨ vertical n k b a))
    exact ⟨Or.imp (swapForward k n a.swap b.swap) (swapForward k n b.swap a.swap),
      Or.imp (swapForward n k a b) (swapForward n k b a)⟩

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.SquareTranspose
