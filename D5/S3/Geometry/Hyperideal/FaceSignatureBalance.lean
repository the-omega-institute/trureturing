/- GID: D5/S3/Geometry/Hyperideal/FaceSignatureBalance
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/FaceSignatureBalance
   mirror-E: none(waiver:finite-tetrahedral-face-incidence)
   anchors: []
   utility: none
   digest: Equal low-edge counts on all four faces characterize opposite-pair balance. -/

import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.Hyperideal.FaceSignatureBalance

/-- Faces omit vertices 1, 2, 3, 4 respectively; local edges have order
    (12,13,14,34,24,23). Each face reads its three actual local edges. -/
def faceLowCount (low : Fin 6 → Bool) : Fin 4 → ℕ :=
  ![(low 3).toNat + (low 4).toNat + (low 5).toNat,
    (low 1).toNat + (low 2).toNat + (low 3).toNat,
    (low 0).toNat + (low 2).toNat + (low 4).toNat,
    (low 0).toNat + (low 1).toNat + (low 5).toNat]

/-- For every six-edge coloring, all four face signatures agree exactly when
    each of the three opposite edge pairs has the same color. -/
theorem equal_face_counts_iff_opposite_balance :
    ∀ low : Fin 6 → Bool,
      (∀ i j : Fin 4, faceLowCount low i = faceLowCount low j) ↔
        low 0 = low 3 ∧ low 1 = low 4 ∧ low 2 = low 5 := by
  intro low
  have hfaces :
      (∀ i j : Fin 4, faceLowCount low i = faceLowCount low j) ↔
        faceLowCount low 0 = faceLowCount low 1 ∧
        faceLowCount low 0 = faceLowCount low 2 ∧
        faceLowCount low 0 = faceLowCount low 3 := by
    constructor
    · intro h
      exact ⟨h 0 1, h 0 2, h 0 3⟩
    · rintro ⟨h01, h02, h03⟩ i j
      have hi : faceLowCount low i = faceLowCount low 0 := by
        fin_cases i
        · rfl
        · exact h01.symm
        · exact h02.symm
        · exact h03.symm
      have hj : faceLowCount low j = faceLowCount low 0 := by
        fin_cases j
        · rfl
        · exact h01.symm
        · exact h02.symm
        · exact h03.symm
      exact hi.trans hj.symm
  have hbits : ∀ b0 b1 b2 b3 b4 b5 : Bool,
      (b3.toNat + b4.toNat + b5.toNat = b1.toNat + b2.toNat + b3.toNat ∧
       b3.toNat + b4.toNat + b5.toNat = b0.toNat + b2.toNat + b4.toNat ∧
       b3.toNat + b4.toNat + b5.toNat = b0.toNat + b1.toNat + b5.toNat) ↔
        b0 = b3 ∧ b1 = b4 ∧ b2 = b5 := by
    intro b0 b1 b2 b3 b4 b5
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
      cases b4 <;> cases b5 <;> decide
  rw [hfaces]
  simpa [faceLowCount] using
    hbits (low 0) (low 1) (low 2) (low 3) (low 4) (low 5)

#print axioms equal_face_counts_iff_opposite_balance

end D5.S3.Geometry.Hyperideal.FaceSignatureBalance
