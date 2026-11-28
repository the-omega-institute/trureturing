/- GID: D5/S3/LinearAlgebra/Matrix/TensorIdentity
   generality: G
   mirror-B: none(waiver:covered-by-hyperfinite-type-ii1-factor-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite complex matrix amplification by tensoring with the identity. -/

import OmegaBuild.Commands
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Data.Complex.Basic

/-! Omega original.
Finite complex matrix amplification by tensoring with the identity. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Omega.MatrixTensorIdentity

open Matrix
open scoped Kronecker

/-- Square complex matrices on the indicated finite alphabet. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

private def productTensor (d b : ℕ) :
    Mat d →⋆ₐ[ℂ] Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ where
  toFun a := a ⊗ₖ (1 : Mat b)
  map_one' := one_kronecker_one
  map_mul' a c := by
    simpa only [one_mul] using (mul_kronecker_mul a c (1 : Mat b) (1 : Mat b))
  map_zero' := by simp
  map_add' a c := add_kronecker a c 1
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_kronecker,
      one_kronecker_one]
  map_star' a := by
    simp only [star_eq_conjTranspose, conjTranspose_kronecker, conjTranspose_one]

/-- The lexicographic index equivalence for an amplification. -/
def indices {d b m : ℕ} (h : d * b = m) : Fin d × Fin b ≃ Fin m :=
  finProdFinEquiv.trans (finCongr h)

/-- Amplification by an identity of dimension `b` in lexicographic coordinates. -/
def embed {d b m : ℕ} (h : d * b = m) : Mat d →⋆ₐ[ℂ] Mat m where
  toAlgHom := (reindexAlgEquiv ℂ ℂ (indices h)).toAlgHom.comp (productTensor d b).toAlgHom
  map_star' a := by
    change reindex (indices h) (indices h) (productTensor d b (star a)) =
      star (reindex (indices h) (indices h) (productTensor d b a))
    rw [map_star]
    rfl

theorem embed_apply {d b m : ℕ} (h : d * b = m) (a : Mat d) (i j : Fin d × Fin b) :
    embed h a (indices h i) (indices h j) = a i.1 j.1 * (1 : Mat b) i.2 j.2 := by
  change (a ⊗ₖ (1 : Mat b)) ((indices h).symm (indices h i)) ((indices h).symm (indices h j)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

theorem embed_injective {d b m : ℕ} (h : d * b = m) (hb : 0 < b) :
    Function.Injective (embed h) := by
  intro a c he
  ext i j
  let o : Fin b := ⟨0, hb⟩
  have hh := congrArg (fun x : Mat m => x (indices h (i, o)) (indices h (j, o))) he
  change embed h a (indices h (i, o)) (indices h (j, o)) =
    embed h c (indices h (i, o)) (indices h (j, o)) at hh
  simpa only [embed_apply, one_apply_eq, mul_one] using hh

theorem trace_embed {d b m : ℕ} (h : d * b = m) (a : Mat d) :
    trace (embed h a) = trace a * (b : ℂ) := by
  change (∑ i : Fin m, (a ⊗ₖ (1 : Mat b)) ((indices h).symm i) ((indices h).symm i)) = _
  rw [(indices h).symm.sum_comp (fun i => (a ⊗ₖ (1 : Mat b)) i i)]
  change trace (a ⊗ₖ (1 : Mat b)) = _
  rw [trace_kronecker, trace_one, Fintype.card_fin]

theorem embed_diagonal {d b m : ℕ} (h : d * b = m) (f : Fin d → ℂ) :
    embed h (diagonal f) = diagonal (fun i => f ((indices h).symm i).1) := by
  apply Matrix.ext
  intro i j
  obtain ⟨x, rfl⟩ := (indices h).surjective i
  obtain ⟨y, rfl⟩ := (indices h).surjective j
  rw [embed_apply]
  by_cases hx : x.1 = y.1 <;> by_cases hy : x.2 = y.2 <;>
    simp [diagonal_apply, one_apply, Equiv.apply_eq_iff_eq, Prod.ext_iff, hx, hy]

end Omega.MatrixTensorIdentity
