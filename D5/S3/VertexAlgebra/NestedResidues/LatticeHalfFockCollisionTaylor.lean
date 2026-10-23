/- GID: D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockCollisionTaylor
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/LatticeHalfFockCollisionTaylor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original fractional numerator and its associated-coordinate cocycle. -/

import D5.S3.VertexAlgebra.NestedResidues.ContextualKernelExtraction

/-! The relocated research proofs retain signed Laurent powers and empty cases.
Classical formal local-field calculus:
Matsuo--Nagatomo; Bakalov--Kac, math/0402315. Hahn/Laurent/binomial infrastructure:
mathlib, Apache 2.0 (Aaron Anderson, María Inés de Frutos-Fernández,
Filippo A. E. Nuccio). Actual field composition: Scott Carnahan, vertexAlg
4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache 2.0. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


namespace D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout
open UniformGradedLocalCorrelator
open CollisionRationalExpansions.OrderedRationalExpansion
open scoped BigOperators
noncomputable section

/-- Coefficients of the common fractional collision numerator, before division
by the three pairwise poles. Integer numerator powers are unrestricted. -/
def collisionTaylor (P : LabelledPolynomial ℂ 3) (gamma : ℤ) (u v : ℕ) : ℂ :=
  Finsupp.linearCombination ℂ (fun e : Exponent 3 =>
    Ring.choose ((e 0 : ℂ) - 1 / 2) u *
      Ring.choose ((e 1 : ℂ) - (gamma : ℂ) / 2) v) P.coeff

/-- The same numerator in the left-associated coordinates h=y-v, t=v-z.
The shift by u is the power of z+t remaining after the first extraction. -/
def associatedTaylor (P : LabelledPolynomial ℂ 3) (gamma : ℤ) (u v : ℕ) : ℂ :=
  Finsupp.linearCombination ℂ (fun e : Exponent 3 =>
    Ring.choose ((e 0 : ℂ) - 1 / 2) u *
      Ring.choose ((e 0 : ℂ) + (e 1 : ℂ) - (u : ℂ) - ((gamma : ℂ) + 1) / 2) v)
    P.coeff

private theorem fractional_coordinate_cocycle (a b : ℂ) (u v : ℕ) :
    Ring.choose a u * Ring.choose (a + b - u) v =
      ∑ j ∈ Finset.range (v + 1),
        ((u + j).choose u : ℂ) * Ring.choose a (u + j) * Ring.choose b (v - j) := by
  have vandermonde := Ring.add_choose_eq (R := ℂ)
    (r := a - u) (s := b) v (Commute.all _ _)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at vandermonde
  rw [show a + b - (u : ℂ) = (a - u) + b by ring, vandermonde, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have product := Ring.choose_smul_choose a (n := u + j) (k := u) (by omega)
  rw [nsmul_eq_mul, Nat.add_sub_cancel_left] at product
  rw [product]
  ring

theorem associatedTaylor_cocycle (P : LabelledPolynomial ℂ 3)
    (gamma : ℤ) (u v : ℕ) :
    associatedTaylor P gamma u v =
      ∑ j ∈ Finset.range (v + 1),
        ((u + j).choose u : ℂ) * collisionTaylor P gamma (u + j) (v - j) := by
  classical
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp [associatedTaylor, collisionTaylor]
  | add P Q hP hQ =>
    simp only [associatedTaylor, collisionTaylor, AddMonoidAlgebra.coeff_add,
      map_add, mul_add, Finset.sum_add_distrib] at hP hQ ⊢
    rw [hP, hQ]
  | single e c =>
    simp only [associatedTaylor, collisionTaylor, AddMonoidAlgebra.coeff_single,
      Finsupp.linearCombination_single, smul_eq_mul]
    have cocycle := fractional_coordinate_cocycle
      ((e 0 : ℂ) - 1 / 2) ((e 1 : ℂ) - (gamma : ℂ) / 2) u v
    have exponent : (e 0 : ℂ) - 1 / 2 + ((e 1 : ℂ) - (gamma : ℂ) / 2) - u =
        (e 0 : ℂ) + (e 1 : ℂ) - u - ((gamma : ℂ) + 1) / 2 := by ring
    rw [exponent] at cocycle
    rw [cocycle, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

def fusedResidueWeight (A k : ℤ) : ℂ :=
  if k < 0 then ((Ring.choose A (-k - 1).toNat : ℤ) : ℂ) else 0

end
end D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout
