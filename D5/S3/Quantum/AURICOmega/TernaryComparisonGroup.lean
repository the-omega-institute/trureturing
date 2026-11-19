/- GID: D5/S3/Quantum/AURICOmega/TernaryComparisonGroup
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/TernaryComparisonGroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Origin-free ternary comparison structures become groups at every base point. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Relation

/-! Origin-free ternary comparison structures.

A ternary comparison structure has two primitives: a ternary transfer and a real-valued
symmetric reading. No base point, no binary operation and no topology are part of the data. -/

open scoped InnerProductSpace

namespace D5.S3.Quantum.AURICOmega.TernaryComparisonGroup

/-- A set with a ternary transfer `tri` and a real reading `kappa`. The transfer cancels
repeated arguments and is associative; the reading is symmetric, equals one exactly on the
diagonal, is nonnegative, is invariant under transfer on either side, and has positive
semidefinite finite Gram forms. -/
structure TernaryComparison (M : Type*) where
  /-- The ternary transfer. -/
  tri : M → M → M → M
  /-- The symmetric reading. -/
  kappa : M → M → ℝ
  tri_self_left : ∀ x z : M, tri x x z = z
  tri_self_right : ∀ x z : M, tri x z z = x
  tri_assoc : ∀ x y z u v : M, tri (tri x y z) u v = tri x y (tri z u v)
  kappa_symm : ∀ x y : M, kappa x y = kappa y x
  kappa_eq_one_iff : ∀ x y : M, kappa x y = 1 ↔ x = y
  kappa_nonneg : ∀ x y : M, 0 ≤ kappa x y
  kappa_tri_right : ∀ x y u v : M, kappa (tri x u v) (tri y u v) = kappa x y
  kappa_tri_left : ∀ u v x y : M, kappa (tri u v x) (tri u v y) = kappa x y
  kappa_gram_nonneg : ∀ (n : ℕ) (x : Fin n → M) (c : Fin n → ℝ),
    0 ≤ ∑ i, ∑ j, c i * c j * kappa (x i) (x j)

namespace TernaryComparison

variable {M : Type*} (C : TernaryComparison M)

/-- The transfer is sensitive to the order of its outer arguments. -/
def Noncommutative : Prop :=
  ∃ x y z : M, C.tri x y z ≠ C.tri z y x

/-- The reading takes values arbitrarily close to zero. -/
def TouchesZero : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ x y : M, C.kappa x y < ε

/-- Any two points are joined by a finite chain whose consecutive readings are
within any prescribed positive distance of one. -/
def ChainConnected : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ x y : M,
    Relation.ReflTransGen (fun a b : M => 1 - ε < C.kappa a b) x y

/-- Every finite Gram matrix of the reading has rank at most `r`. -/
def GramRankLE (r : ℕ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → M),
    (Matrix.of fun i j : Fin n => C.kappa (x i) (x j)).rank ≤ r

/-- The reading is the Gram kernel of a map into Euclidean `r`-space. -/
def HasFeatureRank (r : ℕ) : Prop :=
  ∃ φ : M → EuclideanSpace ℝ (Fin r), ∀ x y : M, C.kappa x y = ⟪φ x, φ y⟫_ℝ

/-- The group obtained by fixing a base point `o`: the product is `tri x o y`, the identity is
`o` and the inverse is `tri o x o`. The group axioms follow from the transfer identities. -/
abbrev groupAt (o : M) : Group M where
  mul x y := C.tri x o y
  one := o
  inv x := C.tri o x o
  mul_assoc x y z := C.tri_assoc x o y o z
  one_mul := C.tri_self_left o
  mul_one x := C.tri_self_right x o
  inv_mul_cancel x := by
    change C.tri (C.tri o x o) o x = o
    rw [C.tri_assoc, C.tri_self_left, C.tri_self_right]

/-- At any base point, the transfer is recovered as `x * y⁻¹ * z`. -/
theorem tri_eq_mul_inv_mul (o x y z : M) :
    C.tri x y z = (letI := C.groupAt o; x * y⁻¹ * z) := by
  change C.tri x y z = C.tri (C.tri x o (C.tri o y o)) o z
  rw [C.tri_assoc, C.tri_assoc, C.tri_self_left, ← C.tri_assoc, C.tri_self_right]

/-- Changing the base point from `o` to `o'` by `x ↦ tri x o o'` is a bijection. -/
theorem baseChange_bijective (o o' : M) : Function.Bijective (fun x : M => C.tri x o o') := by
  refine Function.bijective_iff_has_inverse.mpr ⟨fun x => C.tri x o' o, ?_, ?_⟩
  · intro x
    change C.tri (C.tri x o o') o' o = x
    rw [C.tri_assoc, C.tri_self_left, C.tri_self_right]
  · intro x
    change C.tri (C.tri x o' o) o o' = x
    rw [C.tri_assoc, C.tri_self_left, C.tri_self_right]

/-- The transfer is order sensitive exactly when the group at a base point `o` is
noncommutative. -/
theorem noncommutative_iff (o : M) :
    C.Noncommutative ↔ ∃ x y : M, C.tri x o y ≠ C.tri y o x := by
  constructor
  · rintro ⟨x, y, z, hxyz⟩
    by_contra hcomm
    push Not at hcomm
    let _ : CommGroup M := { C.groupAt o with mul_comm := hcomm }
    apply hxyz
    rw [C.tri_eq_mul_inv_mul o x y z, C.tri_eq_mul_inv_mul o z y x]
    change x * y⁻¹ * z = z * y⁻¹ * x
    rw [mul_comm (x * y⁻¹) z, ← mul_assoc, mul_right_comm]
  · rintro ⟨x, y, hxy⟩
    exact ⟨x, o, y, hxy⟩

/-- The reading of a point with itself is one. -/
theorem kappa_self (x : M) : C.kappa x x = 1 :=
  (C.kappa_eq_one_iff x x).mpr rfl

end TernaryComparison

end D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
