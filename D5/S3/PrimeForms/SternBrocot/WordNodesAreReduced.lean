/- GID: D5/S3/PrimeForms/SternBrocot/WordNodesAreReduced
   generality: I
   mirror-B: D5/B/S3/PrimeForms/SternBrocot/WordNodesAreReduced
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every left-right word carries a unimodular matrix, so every tree node is reduced. -/

import D5.S3.PrimeForms.Crossing.ExactPropagation

/- Library-search audit trail (2026-08-19):
   * Searched the object rather than the name. The pinned Mathlib tree was probed for
     `SternBrocot`, `Stern.Brocot`, `mediant`, and `Farey`; all four return zero files.
     The probe was calibrated first on `goldenRatio`, which returns two files, so the
     zero counts are absence and not a broken search.
   * `D5` carries no `SpecialLinearGroup` or `SL(2)` use, so no in-repo tree exists to
     extend; the matrix coordinates of `ExactPropagation` are reused instead of introducing
     a second matrix encoding.
   * `ExactPropagation.lower_row_coprime` is the exact statement taking the unimodular
     equation to coprimality of the lower row. It is imported and applied, not reproved.
   * Placed in a new `SternBrocot/` bucket under `D5/S3/PrimeForms`: the stratum is forced
     by the import, and SL-003 counts files rather than entries, so `PrimeForms` stays at
     its twelve.
-/

namespace D5.S3.PrimeForms.SternBrocot.WordNodesAreReduced

open D5.S3.PrimeForms.Crossing.ExactPropagation

/-- The unimodular equation in the positive-matrix coordinates. -/
def Unimodular (A : PositiveMatrix) : Prop := A.a * A.d = A.b * A.c + 1

/-- The root of the tree. -/
def rootMatrix : PositiveMatrix := ⟨1, 0, 0, 1⟩

/-- The left generator. -/
def leftStep : PositiveMatrix := ⟨1, 0, 1, 1⟩

/-- The right generator. -/
def rightStep : PositiveMatrix := ⟨1, 1, 0, 1⟩

/-- The matrix of a left-right word, read from the root outwards. -/
def wordMatrix : List Bool → PositiveMatrix
  | [] => rootMatrix
  | false :: rest => leftStep.mul (wordMatrix rest)
  | true :: rest => rightStep.mul (wordMatrix rest)

theorem unimodular_root : Unimodular rootMatrix := by
  simp [Unimodular, rootMatrix]

theorem unimodular_left : Unimodular leftStep := by
  simp [Unimodular, leftStep]

theorem unimodular_right : Unimodular rightStep := by
  simp [Unimodular, rightStep]

/-- Unimodularity is preserved by the matrix product. -/
theorem unimodular_mul {A B : PositiveMatrix} (hA : Unimodular A) (hB : Unimodular B) :
    Unimodular (A.mul B) := by
  have hAZ : (A.a : Int) * A.d - (A.b : Int) * A.c = 1 := by
    have : (A.a : Int) * A.d = (A.b : Int) * A.c + 1 := by exact_mod_cast hA
    linarith
  have hBZ : (B.a : Int) * B.d - (B.b : Int) * B.c = 1 := by
    have : (B.a : Int) * B.d = (B.b : Int) * B.c + 1 := by exact_mod_cast hB
    linarith
  show (A.mul B).a * (A.mul B).d = (A.mul B).b * (A.mul B).c + 1
  simp only [PositiveMatrix.mul]
  zify
  linear_combination ((B.a : Int) * B.d - (B.b : Int) * B.c) * hAZ + hBZ

/-- Every word of left and right steps carries a unimodular matrix. -/
theorem unimodular_wordMatrix (w : List Bool) : Unimodular (wordMatrix w) := by
  induction w with
  | nil => exact unimodular_root
  | cons step rest ih =>
      cases step
      · exact unimodular_mul unimodular_left ih
      · exact unimodular_mul unimodular_right ih

/-- Every node of the tree is a reduced fraction: its lower row is coprime. -/
theorem word_node_is_reduced (w : List Bool) :
    (wordMatrix w).d.Coprime (wordMatrix w).c :=
  lower_row_coprime (unimodular_wordMatrix w)

/-- The lower-right coordinate is never zero, so the node denomines a fraction. -/
theorem wordMatrix_lower_right_pos (w : List Bool) : 0 < (wordMatrix w).d := by
  induction w with
  | nil => simp [wordMatrix, rootMatrix]
  | cons step rest ih =>
      cases step
      · show 0 < (leftStep.mul (wordMatrix rest)).d
        simp only [PositiveMatrix.mul, leftStep]
        omega
      · show 0 < (rightStep.mul (wordMatrix rest)).d
        simp only [PositiveMatrix.mul, rightStep]
        omega

/-- Along an all-left word the upper-left coordinate stays one. -/
theorem left_word_upper_left (n : Nat) : (wordMatrix (List.replicate n false)).a = 1 := by
  induction n with
  | zero => simp [wordMatrix, rootMatrix]
  | succ k ih =>
      rw [List.replicate_succ]
      show (leftStep.mul (wordMatrix (List.replicate k false))).a = 1
      simp only [PositiveMatrix.mul, leftStep]
      omega

/-- The tree does not collapse: along an all-left word the lower-left coordinate is the
word length, so distinct lengths give distinct nodes. -/
theorem left_word_lower_left (n : Nat) : (wordMatrix (List.replicate n false)).c = n := by
  induction n with
  | zero => simp [wordMatrix, rootMatrix]
  | succ k ih =>
      rw [List.replicate_succ]
      show (leftStep.mul (wordMatrix (List.replicate k false))).c = k + 1
      simp only [PositiveMatrix.mul, leftStep]
      rw [left_word_upper_left k, ih]
      omega

/-- The tree's prototype primality theorem: every left-right word carries a unimodular
matrix, its lower row is coprime, and its lower-right coordinate is positive, so every
node of the tree is a fraction already in lowest terms. The fourth conjunct is the
non-collapse witness: the lower-left coordinate along an all-left word is the word
length, so the quantifier ranges over infinitely many distinct nodes rather than
dressing a single fact in a universal. -/
theorem stern_brocot_nodes_are_reduced_package (w : List Bool) (n : Nat) :
    Unimodular (wordMatrix w) ∧
      (wordMatrix w).d.Coprime (wordMatrix w).c ∧
      0 < (wordMatrix w).d ∧
      (wordMatrix (List.replicate n false)).c = n :=
  ⟨unimodular_wordMatrix w, word_node_is_reduced w, wordMatrix_lower_right_pos w,
    left_word_lower_left n⟩

#print axioms stern_brocot_nodes_are_reduced_package

end D5.S3.PrimeForms.SternBrocot.WordNodesAreReduced
