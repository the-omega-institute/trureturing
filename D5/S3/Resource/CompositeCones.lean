/- GID: D5/S3/Resource/CompositeCones
   generality: G
   mirror-B: D5/B/S3/Resource/CompositeCones
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Define separable and block-positive matrix cones and prove their two basic inclusions. -/

/- The statements below concern cones of finite complex matrices only; no physical
interpretation is asserted here.

The source writes the chain with PROPER inclusion symbols, SEP ⊂ PSD ⊂ SEP*. This module proves
only the two INCLUSIONS. That either of them is proper -- that some positive semidefinite matrix
is not separable, or that some block-positive matrix is not positive semidefinite -- is NOT
established here and no witness is exhibited. -/

/- Library-search audit trail (2026-08-12):
   * `Matrix.PosSemidef.kronecker` proves that a Kronecker product of positive
     semidefinite matrices is positive semidefinite.
   * `Matrix.posSemidef_sum` proves positive semidefiniteness of a finite sum.
   * `Matrix.PosSemidef.re_dotProduct_nonneg` gives the real nonnegativity of
     the quadratic form used in the block-positive definition.
   The import closure is the umbrella `Mathlib` import (generality `G`).
-/

import Mathlib

namespace D5.S3.Resource.CompositeCones

open scoped Kronecker
open scoped ComplexOrder

/-- A matrix is separable when it is a finite sum of Kronecker products of PSD factors.

The finite family is encoded by `Fin k`, with `k = 0` allowed. -/
def separableCone {m n : ℕ} (W : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) : Prop :=
  ∃ k : ℕ,
    ∃ A : Fin k → Matrix (Fin m) (Fin m) ℂ,
      ∃ B : Fin k → Matrix (Fin n) (Fin n) ℂ,
        (∀ i, (A i).PosSemidef ∧ (B i).PosSemidef) ∧
          W = ∑ i : Fin k, A i ⊗ₖ B i

/-- A matrix is block positive when its quadratic form is nonnegative on every product vector. -/
def blockPositive {m n : ℕ} (W : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) : Prop :=
  ∀ (a : Fin m → ℂ) (b : Fin n → ℂ),
    0 ≤ RCLike.re
      (dotProduct (star (fun ij : Fin m × Fin n => a ij.1 * b ij.2))
        (Matrix.mulVec W (fun ij : Fin m × Fin n => a ij.1 * b ij.2)))

theorem separable_isPosSemidef {m n : ℕ}
    {W : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ} :
    separableCone W → W.PosSemidef := by
  fail_if_success ((try simp); done)
  rintro ⟨k, A, B, hAB, rfl⟩
  simpa only using
    (Matrix.posSemidef_sum (s := (Finset.univ : Finset (Fin k)))
      (x := fun i : Fin k => A i ⊗ₖ B i)
      (by
        intro i hi
        exact (hAB i).1.kronecker (hAB i).2))

theorem posSemidef_blockPositive {m n : ℕ}
    {W : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ} :
    W.PosSemidef → blockPositive W := by
  fail_if_success ((try simp); done)
  intro hW
  unfold blockPositive
  intro a b
  exact hW.re_dotProduct_nonneg (fun ij : Fin m × Fin n => a ij.1 * b ij.2)

#print axioms separable_isPosSemidef
#print axioms posSemidef_blockPositive

end D5.S3.Resource.CompositeCones
