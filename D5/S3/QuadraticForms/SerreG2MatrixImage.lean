/- GID: D5/S3/QuadraticForms/SerreG2MatrixImage
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/SerreG2MatrixImage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An actual fourteen-dimensional matrix image of mathlib Serre G2. -/

/-
admission_basis: escape-witness
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19944
utility none: universal matrix Lie homomorphism and dimension argument.
Classical G2 matrices and Serre relations are prior mathematics. The KMV
application credits Haobo Ma, then Wenlin Zhang. No priority is claimed.
-/

import D5.S3.QuadraticForms.SerreG2MatrixTable
import Mathlib.Algebra.Lie.SerreConstruction
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.QuadraticForms.SerreG2MatrixImage

attribute [local instance 100] LieRing.ofAssociativeRing
variable {k : Type*} [Field k] [CharZero k]

private abbrev intBasisMatrix := D5.S3.QuadraticForms.SerreG2MatrixTable.basisMatrix
private abbrev bracketCoefficients := D5.S3.QuadraticForms.SerreG2MatrixTable.coefficients

/-- Scalar extension of the explicit integral seven-dimensional representation. -/
def basisMatrix (i : Fin 14) : Matrix (Fin 7) (Fin 7) k :=
  (intBasisMatrix i).map (Int.castRingHom k)

private theorem basisMatrix_bracket (i j : Fin 14) :
    ⁅basisMatrix (k := k) i, basisMatrix j⁆ =
      ∑ t, bracketCoefficients i j t • basisMatrix (k := k) t := by
  ext r s
  have hz : (∑ u, intBasisMatrix i r u * intBasisMatrix j u s) -
      (∑ u, intBasisMatrix j r u * intBasisMatrix i u s) =
      ∑ t, bracketCoefficients i j t • intBasisMatrix t r s := by
    simpa only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.sum_apply, Matrix.smul_apply] using congrArg
      (fun A : Matrix (Fin 7) (Fin 7) ℤ => A r s)
      (D5.S3.QuadraticForms.SerreG2MatrixTable.bracket i j)
  have h := congrArg (Int.castRingHom k) hz
  simpa only [basisMatrix, Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
    map_sum, map_sub, map_mul, map_zsmul] using h

private def spanModule : Submodule k (Matrix (Fin 7) (Fin 7) k) :=
  Submodule.span k (Set.range (basisMatrix (k := k)))

private theorem basis_mem (i : Fin 14) : basisMatrix (k := k) i ∈ spanModule :=
  Submodule.subset_span ⟨i,rfl⟩

/-- The fourteen-dimensional carrier is an actual matrix Lie subalgebra. -/
def matrixImage : LieSubalgebra k (Matrix (Fin 7) (Fin 7) k) :=
  { spanModule (k := k) with
    lie_mem' := by
      intro x y hx hy
      change ⁅x,y⁆ ∈ spanModule (k := k)
      change x ∈ spanModule (k := k) at hx
      change y ∈ spanModule (k := k) at hy
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨i,rfl⟩ := hx
          induction hy using Submodule.span_induction with
          | mem y hy =>
              obtain ⟨j,rfl⟩ := hy
              rw [basisMatrix_bracket]
              exact (spanModule (k := k)).sum_mem (fun t _ =>
                (spanModule (k := k)).toAddSubgroup.zsmul_mem (basis_mem t) _)
          | zero => simp
          | add x y hx hy ihx ihy => simpa only [lie_add] using
              (spanModule (k := k)).add_mem ihx ihy
          | smul t x hx ih => simpa only [lie_smul] using
              (spanModule (k := k)).smul_mem t ih
      | zero => simp
      | add x y hx hy ihx ihy => simpa only [add_lie] using
          (spanModule (k := k)).add_mem ihx ihy
      | smul t x hx ih => simpa only [smul_lie] using
          (spanModule (k := k)).smul_mem t ih }

private def extractCoordinates (A : Matrix (Fin 7) (Fin 7) k) : Fin 14 → k :=
  ![A 0 0, A 1 1 + A 0 0, A 0 1 / (1 : k), A 1 2 / (1 : k), A 0 2 / (1 : k), A 0 3 / (-4 : k), A 0 4 / (6 : k), A 0 5 / (-6 : k), A 1 0 / (1 : k), A 2 1 / (1 : k), A 2 0 / (-1 : k), A 3 0 / (-2 : k), A 4 0 / (-6 : k), A 5 0 / (-6 : k)]

set_option maxHeartbeats 2000000 in
-- Coordinate extraction expands fourteen fixed matrices over the arbitrary field.
private theorem extract_assemble (x : Fin 14 → k) :
    extractCoordinates (Fintype.linearCombination k (basisMatrix (k := k)) x) = x := by
  funext i
  fin_cases i <;>
    simp [extractCoordinates, Fintype.linearCombination_apply, basisMatrix, intBasisMatrix, D5.S3.QuadraticForms.SerreG2MatrixTable.basisMatrix,
      Fin.sum_univ_succ]

private noncomputable def coordinateEquiv : (Fin 14 → k) ≃ₗ[k] matrixImage (k := k) := by
  let f := Fintype.linearCombination k (basisMatrix (k := k))
  have hf : Function.Injective f := Function.LeftInverse.injective extract_assemble
  have hr : LinearMap.range f = (matrixImage (k := k)).toSubmodule :=
    Fintype.range_linearCombination k (basisMatrix (k := k))
  exact (LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ hr)

instance : FiniteDimensional k (matrixImage (k := k)) :=
  Module.Finite.equiv (coordinateEquiv (k := k))

/-- The dimension belongs to the proved matrix image, not to a replacement
or a dimension-tagged definition of G2. -/
theorem matrixImage_finrank : Module.finrank k (matrixImage (k := k)) = 14 := by
  rw [← (coordinateEquiv (k := k)).finrank_eq]
  simp

private def basisElement (i : Fin 14) : matrixImage (k := k) :=
  ⟨basisMatrix i,basis_mem i⟩

private theorem basisElement_bracket (i j : Fin 14) :
    ⁅basisElement (k := k) i, basisElement j⁆ =
      ∑ t, bracketCoefficients i j t • basisElement (k := k) t := by
  apply Subtype.ext
  simpa [Fin.sum_univ_succ, basisElement] using basisMatrix_bracket (k := k) i j

private def generators : CartanMatrix.Generators (Fin 2) → matrixImage (k := k)
  | .H i => basisElement (if i = 0 then 0 else 1)
  | .E i => basisElement (if i = 0 then 2 else 3)
  | .F i => basisElement (if i = 0 then 8 else 9)

private noncomputable def freeMap :
    FreeLieAlgebra k (CartanMatrix.Generators (Fin 2)) →ₗ⁅k⁆ matrixImage (k := k) :=
  FreeLieAlgebra.lift k generators

set_option maxHeartbeats 4000000 in
-- The six relation families reduce twenty-four fixed Serre identities using the integral table.
private theorem relations_vanish :
    CartanMatrix.Relations.toIdeal k CartanMatrix.G₂ ≤ (freeMap (k := k)).ker := by
  apply LieSubmodule.lieSpan_le.mpr
  intro x hx
  simp only [CartanMatrix.Relations.toSet, Set.mem_union, Set.mem_range] at hx
  rcases hx with (((((hx | hx) | hx) | hx) | hx) | hx) <;>
    obtain ⟨⟨i,j⟩,rfl⟩ := hx <;>
    change freeMap (k := k) _ = 0
  all_goals
    fin_cases i <;> fin_cases j <;>
      norm_num [CartanMatrix.Relations.HH, CartanMatrix.Relations.EF,
        CartanMatrix.Relations.HE, CartanMatrix.Relations.HF,
        CartanMatrix.Relations.adE, CartanMatrix.Relations.adF,
        CartanMatrix.G₂, freeMap, generators,
        LieHom.map_lie, Module.End.pow_apply, Function.iterate_succ_apply', LieAlgebra.ad_apply,
        basisElement_bracket, bracketCoefficients,
        D5.S3.QuadraticForms.SerreG2MatrixTable.coefficients, Fin.sum_univ_succ]

/-- A map from mathlib's actual Serre-presentation G2 to the explicit matrix
image. Its definition uses the proved Serre relations. -/
noncomputable def serreMap : LieAlgebra.g₂ k →ₗ⁅k⁆ matrixImage (k := k) :=
  { (CartanMatrix.Relations.toIdeal k CartanMatrix.G₂).toSubmodule.liftQ
      (freeMap (k := k)).toLinearMap relations_vanish with
    map_lie' := by
      intro x y
      induction x using Submodule.Quotient.induction_on
      induction y using Submodule.Quotient.induction_on
      exact (freeMap (k := k)).map_lie _ _ }

private noncomputable def serreGenerator (x : CartanMatrix.Generators (Fin 2)) : LieAlgebra.g₂ k :=
  Submodule.Quotient.mk (FreeLieAlgebra.of k x)

private theorem serreMap_generator (x : CartanMatrix.Generators (Fin 2)) :
    serreMap (serreGenerator x) = generators (k := k) x := by
  change freeMap (k := k) (FreeLieAlgebra.of k x) = generators (k := k) x
  exact FreeLieAlgebra.lift_of_apply _ _

private noncomputable def serreWord (i : Fin 14) : LieAlgebra.g₂ k :=
  let h₀ := serreGenerator (.H 0)
  let h₁ := serreGenerator (.H 1)
  let e₀ := serreGenerator (.E 0)
  let e₁ := serreGenerator (.E 1)
  let f₀ := serreGenerator (.F 0)
  let f₁ := serreGenerator (.F 1)
  ![h₀,h₁,e₀,e₁,⁅e₀,e₁⁆,⁅e₀,⁅e₀,e₁⁆⁆,⁅e₀,⁅e₀,⁅e₀,e₁⁆⁆⁆,
    ⁅e₁,⁅e₀,⁅e₀,⁅e₀,e₁⁆⁆⁆⁆,
    f₀,f₁,⁅f₀,f₁⁆,⁅f₀,⁅f₀,f₁⁆⁆,⁅f₀,⁅f₀,⁅f₀,f₁⁆⁆⁆,
    ⁅f₁,⁅f₀,⁅f₀,⁅f₀,f₁⁆⁆⁆⁆] i

set_option maxHeartbeats 8000000 in
-- Fourteen explicit Serre words are reduced using the checked integral bracket table.
private theorem serreMap_word (i : Fin 14) :
    serreMap (serreWord i) = basisElement (k := k) i := by
  fin_cases i <;>
    norm_num [serreWord, LieHom.map_lie, serreMap_generator, generators,
      basisElement_bracket, bracketCoefficients,
      D5.S3.QuadraticForms.SerreG2MatrixTable.coefficients, Fin.sum_univ_succ]

/-- This is a surjection from the actual standard Serre object. In particular,
it is stronger than assigning a dimension or a root list to an unrelated type. -/
theorem serreMap_surjective : Function.Surjective (serreMap (k := k)) := by
  intro x
  have hx : x.val ∈ LinearMap.range (Fintype.linearCombination k (basisMatrix (k := k))) := by
    rw [Fintype.range_linearCombination]
    exact x.property
  obtain ⟨v,hv⟩ := hx
  refine ⟨∑ i, v i • serreWord i, ?_⟩
  apply Subtype.ext
  simpa [map_sum, map_smul, serreMap_word, basisElement,
    Fin.sum_univ_succ, Fintype.linearCombination_apply] using hv

/-- If the actual Serre G2 object is simple, the constructed surjection is a
proved Lie equivalence with the fourteen-dimensional matrix image. The KMV
exclusion uses precisely this correspondence: a hypothetical isomorphism to a
nonabelian simple ideal supplies the simplicity hypothesis. No unconditional
Serre normal-form theorem is being assumed. -/
noncomputable def correspondence_of_isSimple
    [LieAlgebra.IsSimple k (LieAlgebra.g₂ k)] :
    LieAlgebra.g₂ k ≃ₗ⁅k⁆ matrixImage (k := k) := by
  have hn : (basisElement (k := k) 2) ≠ 0 := by
    intro h
    have hh := congrArg (fun x : matrixImage (k := k) => x.val 0 1) h
    norm_num [basisElement, basisMatrix, intBasisMatrix, D5.S3.QuadraticForms.SerreG2MatrixTable.basisMatrix] at hh
  have hk : (serreMap (k := k)).ker = ⊥ := by
    rcases LieAlgebra.IsSimple.eq_bot_or_eq_top (serreMap (k := k)).ker with h | h
    · exact h
    · exfalso
      obtain ⟨x,hx⟩ := serreMap_surjective (basisElement (k := k) 2)
      apply hn
      rw [← hx]
      exact LieHom.mem_ker.mp (by rw [h]; exact LieSubmodule.mem_top x)
  exact LieEquiv.ofBijective serreMap ⟨(LieHom.ker_eq_bot serreMap).mp hk, serreMap_surjective⟩

end D5.S3.QuadraticForms.SerreG2MatrixImage
