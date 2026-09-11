/- GID: D5/S3/Quantum/Matrix/SchurMinimum
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/SchurMinimum
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.PosDef]
   utility: none
   digest: The Schur quadratic form is the attained minimum over the internal block. -/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic

/-!
Admission basis: rule-11-upstream-wrapper; proof_shape: bind-only.
Upstream: Matrix.schur_complement_eq₂₂, Mathlib/LinearAlgebra/Matrix/Hermitian.lean:378,
at Mathlib db584cd6d46c92f209a44c0f1c829460d327499d (Lean v4.33.0).
Necessary atom clause (verbatim):
\min_y
\begin{pmatrix}x\\y\end{pmatrix}^{\!*}
K
\begin{pmatrix}x\\y\end{pmatrix}
=
x^*Sx,
\qquad
S=A-BC^{-1}B^*.

The upstream identity supplies the decomposition; IsLeast additionally exposes
attainment at -C⁻¹B* x and the lower bound from C positive definite. This is only
instantiation, positivity projection and normalization, with no new lemma.
The sole theorem is symbolic for arbitrary finite block sizes, hence utility none:
no bounded enumeration, certified instance, checker or numerical reduction.
ComplexOrder compares real values in the Hermitian quadratic forms.
The repository Schur associativity interface concerns elimination order and does
not state this minimum. No repository theorem is used as a frozen prerequisite.
-/

noncomputable section

open Matrix
open scoped Matrix ComplexOrder

namespace D5.S3.Quantum.Matrix.SchurMinimum

/-- Positive definiteness of the internal block gives an attained boundary minimum. -/
theorem schur_quadratic_is_least
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n n ℂ)
    (_hA : A.IsHermitian) (hC : C.PosDef) (x : m → ℂ) :
    let S := A - B * C⁻¹ * Bᴴ
    IsLeast (Set.range fun y : n → ℂ =>
      star (x ⊕ᵥ y) ᵥ* Matrix.fromBlocks A B Bᴴ C ⬝ᵥ (x ⊕ᵥ y))
      (star x ᵥ* S ⬝ᵥ x) := by
  let := hC.isUnit.invertible
  refine ⟨⟨-((C⁻¹ * Bᴴ) *ᵥ x), ?_⟩, ?_⟩
  · dsimp only
    rw [schur_complement_eq₂₂ A B x _ hC.isHermitian]
    simp
  · rintro z ⟨y, rfl⟩
    dsimp only
    rw [schur_complement_eq₂₂ A B x y hC.isHermitian]
    exact le_add_of_nonneg_left (by
      simpa only [dotProduct_mulVec] using
        hC.posSemidef.dotProduct_mulVec_nonneg ((C⁻¹ * Bᴴ) *ᵥ x + y))

#print axioms schur_quadratic_is_least

end D5.S3.Quantum.Matrix.SchurMinimum
