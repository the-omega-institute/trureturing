/- GID: D5/S3/Quantum/Reduction/IsometricCompression
   generality: G
   mirror-B: D5/B/S3/Quantum/Reduction/IsometricCompression
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: A one-step operator intertwining persists through every finite operator word. -/

import Mathlib

/-!
# Finite operator-word intertwining

The carrier is the actual rectangular complex matrix algebra. The definitions
identify an isometric frame's support, its compression, and the discarded normal
component. The retained theorem transports a one-step intertwining through a
finite operator word. It makes no norm or differential-geometric claim.
-/

noncomputable section
open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Reduction.IsometricCompression

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {n d m e : Type*}
  [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d]
  [Fintype m] [DecidableEq m] [Fintype e] [DecidableEq e]

/-- The orthogonal support of an isometric frame. -/
def support (U : Matrix n d ℂ) : Matrix n n ℂ := U * Uᴴ

/-- Pull back a physical operator to the logical space. -/
def compress (U : Matrix n d ℂ) (A : Matrix n n ℂ) : Matrix d d ℂ :=
  Uᴴ * A * U

/-- The component of a rectangular map outside the output frame. -/
def normal (W : Matrix m e ℂ) (B : Matrix m d ℂ) : Matrix m d ℂ :=
  (1 - support W) * B

/-- Intertwining persists through every finite operator word, including the empty history. -/
theorem word_intertwines {ι : Type*} (U : Matrix n d ℂ)
    (K : ι → Matrix n n ℂ) (k : ι → Matrix d d ℂ)
    (h : ∀ a, K a * U = U * k a) (w : List ι) :
    (w.map K).prod * U = U * (w.map k).prod := by
  induction w with
  | nil => simp
  | cons a w ih =>
      simp only [List.map_cons, List.prod_cons]
      calc
        K a * (w.map K).prod * U = K a * ((w.map K).prod * U) :=
          Matrix.mul_assoc _ _ _
        _ = K a * (U * (w.map k).prod) := by rw [ih]
        _ = (K a * U) * (w.map k).prod := (Matrix.mul_assoc _ _ _).symm
        _ = U * (k a * (w.map k).prod) := by rw [h a, Matrix.mul_assoc]

#print axioms word_intertwines

end D5.S3.Quantum.Reduction.IsometricCompression
