/- GID: D5/S3/ConceptDynamics/Coding/UnitWordGyration
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/UnitWordGyration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The same dyadic cochain on an arbitrary finite unit word and its actual collapsed edge. -/

/- Finite unit-word collapse using the same
rectangular dyadicGyration. No singular original intermediate is inverted:
the input here is explicitly the word AFTER a proved kernel reduction.
The finite kernel ladder separately constructs this input from an
arbitrary based path with unit endpoints.
-/
import D5.S3.ConceptDynamics.Coding.CountedLocalizedGyrationResidue

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SourceOnly.UnitWordGyration

open D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration

abbrev Mat (n m : ℕ) := Matrix (Fin n) (Fin m) GyrationDyadic

structure Vertex where
  dim : ℕ
  time : (Mat dim dim)ˣ

/-- ROW convention: R*S is the source, S*R the target. -/
structure Edge (A B : Vertex) where
  R : Mat A.dim B.dim
  S : Mat B.dim A.dim
  rs : R*S = (A.time : Mat A.dim A.dim)
  sr : S*R = (B.time : Mat B.dim B.dim)

namespace Edge
variable {A B C : Vertex}

def inverse (e : Edge A B) : Mat B.dim A.dim :=
  e.S * (↑A.time⁻¹ : Mat A.dim A.dim)

theorem inverse_left (e : Edge A B) : e.R * e.inverse = 1 := by
  rw [inverse, ← Matrix.mul_assoc, e.rs, Units.mul_inv]

theorem inverse_right (e : Edge A B) : e.inverse * e.R = 1 := by
  have hb : (B.time : Mat B.dim B.dim) * (e.inverse * e.R) =
      (B.time : Mat B.dim B.dim) := by
    calc
      _ = (e.S * e.R) * (e.inverse * e.R) := by rw [e.sr]
      _ = e.S * ((e.R * e.inverse) * e.R) := by
        simp only [Matrix.mul_assoc]
      _ = e.S * e.R := by rw [inverse_left, Matrix.one_mul]
      _ = (B.time : Mat B.dim B.dim) := e.sr
  have hc := congrArg (fun M : Mat B.dim B.dim =>
    (↑B.time⁻¹ : Mat B.dim B.dim) * M) hb
  simpa only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] using hc

theorem inverse_source (e : Edge A B) :
    e.inverse * (A.time : Mat A.dim A.dim) = e.S := by
  rw [inverse, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem intertwines (e : Edge A B) :
    (A.time : Mat A.dim A.dim) * e.R = e.R * (B.time : Mat B.dim B.dim) := by
  rw [← e.rs, ← e.sr, Matrix.mul_assoc]

def identity (A : Vertex) : Edge A A where
  R := 1
  S := (A.time : Mat A.dim A.dim)
  rs := Matrix.one_mul _
  sr := Matrix.mul_one _

/-- Multiplying forward maps is repaired to LAG ONE with the actual
inverse of the second forward map. This repair is justified by units. -/
def comp (e : Edge A B) (f : Edge B C) : Edge A C where
  R := e.R * f.R
  S := f.inverse * e.S
  rs := by
    calc
      _ = e.R * (f.R * f.inverse) * e.S := by simp only [Matrix.mul_assoc]
      _ = (A.time : Mat A.dim A.dim) := by
        rw [inverse_left, Matrix.mul_one, e.rs]
  sr := by
    calc
      _ = (f.inverse * (e.S * e.R)) * f.R := by simp only [Matrix.mul_assoc]
      _ = (f.inverse * (B.time : Mat B.dim B.dim)) * f.R := by rw [e.sr]
      _ = f.S * f.R := by rw [inverse_source]
      _ = (C.time : Mat C.dim C.dim) := f.sr

def weight (d : ℕ) [NeZero d] (e : Edge A B) : ZMod 3 :=
  dyadicGyration d e.R e.S

theorem identity_weight {d : ℕ} [NeZero d] (hd : 3 ∣ d) (A : Vertex) :
    (identity A).weight d = 0 := by
  let e : ℕ := padicValInt 3 (((2 * d).factorial : ℕ) : ℤ)
  have h := canonicalLocalizedGyration_triangle hd e le_rfl (gyrationDyadicReduction d)
    (1 : Mat A.dim A.dim) 1 (A.time : Mat A.dim A.dim)
  simp only [Matrix.one_mul, Matrix.mul_one] at h
  exact add_left_cancel (h.trans (add_zero _).symm)

/-- An actual RS triangle, with third factor f.inverse*e.S. No SE
commutative square is substituted for a triangle. -/
theorem comp_weight {d : ℕ} [NeZero d] (hd : 3 ∣ d)
    (e : Edge A B) (f : Edge B C) :
    (e.comp f).weight d = e.weight d + f.weight d := by
  have h₁ : f.R * (f.inverse * e.S) = e.S := by
    rw [← Matrix.mul_assoc, inverse_left, Matrix.one_mul]
  have h₂ : (f.inverse * e.S) * e.R = f.S := by
    rw [Matrix.mul_assoc, e.sr, inverse_source]
  let k : ℕ := padicValInt 3 (((2 * d).factorial : ℕ) : ℤ)
  have h := canonicalLocalizedGyration_triangle hd k le_rfl (gyrationDyadicReduction d)
    e.R f.R (f.inverse * e.S)
  rw [h₁, h₂] at h
  exact h.symm

end Edge

/-- A finite ordinary word, with every intermediate unit exposed in its
type. The original positive Word is NOT redefined as this type. -/
inductive Word : Vertex → Vertex → Type
  | nil (A : Vertex) : Word A A
  | cons {A B C : Vertex} (e : Edge A B) (tail : Word B C) : Word A C

namespace Word
variable {A B : Vertex}

def forward : {A B : Vertex} → Word A B → Mat A.dim B.dim
  | _, _, .nil _ => 1
  | _, _, .cons e tail => e.R * forward tail

def collapse : {A B : Vertex} → Word A B → Edge A B
  | _, _, .nil A => .identity A
  | _, _, .cons e tail => e.comp (collapse tail)

def weight (d : ℕ) [NeZero d] : {A B : Vertex} → Word A B → ZMod 3
  | _, _, .nil _ => 0
  | _, _, .cons e tail => e.weight d + weight d tail

theorem collapse_forward (w : Word A B) : w.collapse.R = w.forward := by
  induction w with
  | nil A => rfl
  | cons e tail ih =>
      change e.R * tail.collapse.R = e.R * tail.forward
      rw [ih]

/-- The complete finite-word comparison once the kernel ladder has
actually supplied unit intermediates. Its proof is induction on the
word, consuming one literal triangle at every step. -/
theorem collapse_weight {d : ℕ} [NeZero d] (hd : 3 ∣ d) (w : Word A B) :
    w.collapse.weight d = w.weight d := by
  induction w with
  | nil A => exact Edge.identity_weight hd A
  | cons e tail ih =>
      change (e.comp tail.collapse).weight d = e.weight d + tail.weight d
      rw [Edge.comp_weight hd, ih]

def loopUnit (w : Word A A) : (Mat A.dim A.dim)ˣ where
  val := w.collapse.R
  inv := w.collapse.inverse
  val_inv := w.collapse.inverse_left
  inv_val := w.collapse.inverse_right

theorem loopUnit_commutes (w : Word A A) :
    Commute (w.loopUnit : Mat A.dim A.dim) (A.time : Mat A.dim A.dim) :=
  w.collapse.intertwines.symm

/-- The terminal expression is the ONE-EDGE value of the ACTUAL product
of forward maps. No gamma is supplied as a hypothesis or used to define
the word value. At the literal original endpoint, transpose converts this
expression to gamma after the independently owned induced-unit equality. -/
theorem loop_one_edge {d : ℕ} [NeZero d] (hd : 3 ∣ d) (w : Word A A) :
    w.weight d = dyadicGyration d w.forward
      ((↑w.loopUnit⁻¹ : Mat A.dim A.dim) * (A.time : Mat A.dim A.dim)) := by
  calc
    w.weight d = w.collapse.weight d := (collapse_weight hd w).symm
    _ = dyadicGyration d w.collapse.R w.collapse.S := rfl
    _ = dyadicGyration d w.collapse.R
        (w.collapse.inverse * (A.time : Mat A.dim A.dim)) := by
      rw [Edge.inverse_source]
    _ = _ := by
      rw [collapse_forward]
      rfl

end Word
end SourceOnly.UnitWordGyration
