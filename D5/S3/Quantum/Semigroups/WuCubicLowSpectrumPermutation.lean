import D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
import OmegaBuild.Commands

/-! Column permutations reduce arbitrary low spectra to the ordered shell. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped Matrix

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrumPermutation

open WuCubicDirectedOccupationCap (Mat)
open WuRepeatedMiddleCubic (Frame)
open WuCubicAngularCertificate (normalizedDeficit physicalFrame
  normalized_deficit_eq_ordinary_trace)
open private levelsAt from D5.S3.Quantum.Semigroups.WuCubicSignedTransfer

/-- Column `i` of the reindexed unitary is column `σ i` of `U`. -/
def permuteColumns (U : unitary Mat) (σ : Equiv.Perm (Fin 4)) : unitary Mat :=
  ⟨(U : Mat).submatrix (Equiv.refl _) σ,
    (Matrix.submatrix_equiv_mem_unitary).2 U.property⟩

private theorem spectralMatrix_permute (V : Frame) (σ : Equiv.Perm (Fin 4))
    (x : Fin 4 → ℝ) :
    V.submatrix (Equiv.refl _) σ * diagonal (fun i => ((x ∘ σ) i : ℂ)) *
      (V.submatrix (Equiv.refl _) σ)ᴴ = V * diagonal (fun i => (x i : ℂ)) * Vᴴ := by
  let d : Fin 4 → ℂ := fun i => (x i : ℂ)
  change _ * diagonal (d ∘ σ) * _ = V * diagonal d * Vᴴ
  rw [← Matrix.submatrix_diagonal_equiv d σ, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rfl

private theorem levelsAt_eq {x : Fin 4 → ℝ} (hx : x 3 = 1) :
    levelsAt (x 0) (x 1) (x 2) = x := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact hx.symm

/-- Simultaneous reindexing of the free levels and frame columns preserves the deficit. -/
theorem normalizedDeficit_permute {r : ℝ} (hr : 1 ≤ r) (U : unitary Mat)
    (σ : Equiv.Perm (Fin 4)) (hσ : σ 3 = 3) (m n q : ℝ) :
    let x : Fin 4 → ℝ := ![m, n, q, 1]
    normalizedDeficit r (permuteColumns U σ) (x (σ 0)) (x (σ 1)) (x (σ 2)) =
      normalizedDeficit r U m n q := by
  let x := levelsAt m n q
  change normalizedDeficit r (permuteColumns U σ) (x (σ 0)) (x (σ 1)) (x (σ 2)) = _
  have hx : (x ∘ σ) 3 = 1 := (congrArg x hσ).trans (show x 3 = 1 from rfl)
  have hV : physicalFrame (permuteColumns U σ) = (physicalFrame U).submatrix (Equiv.refl _) σ :=
    rfl
  have hM := spectralMatrix_permute (physicalFrame U) σ x
  rw [normalized_deficit_eq_ordinary_trace hr (permuteColumns U σ),
    normalized_deficit_eq_ordinary_trace hr U]
  rw [hV, show levelsAt (x (σ 0)) (x (σ 1)) (x (σ 2)) = x ∘ σ from levelsAt_eq hx, hM]

/-- The first three levels can be sorted in `[0,1]` while fixing the fourth column.
The same permutation works for every `r ≥ 1`, including at repeated or zero levels. -/
theorem exists_sorted_normalizedDeficit (U : unitary Mat) (x : Fin 3 → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    let y := x ∘ Tuple.sort x
    ∃ σ : Equiv.Perm (Fin 4), σ 3 = 3 ∧
      (∀ i : Fin 3, σ i.castSucc = (Tuple.sort x i).castSucc) ∧
      0 ≤ y 0 ∧ y 0 ≤ y 1 ∧ y 1 ≤ y 2 ∧ y 2 ≤ 1 ∧
      ∀ r : ℝ, 1 ≤ r → normalizedDeficit r (permuteColumns U σ) (y 0) (y 1) (y 2) =
        normalizedDeficit r U (x 0) (x 1) (x 2) := by
  intro y
  let σ : Equiv.Perm (Fin 4) :=
    finSuccEquivLast.trans ((Tuple.sort x).optionCongr.trans finSuccEquivLast.symm)
  have hlast : σ 3 = 3 := by
    change σ (Fin.last 3) = Fin.last 3
    simp only [σ, Equiv.trans_apply, finSuccEquivLast_last, Equiv.optionCongr_apply,
      Option.map_none, finSuccEquivLast_symm_none]
  have hcast (i : Fin 3) : σ i.castSucc = (Tuple.sort x i).castSucc := by
    simp [σ, Equiv.optionCongr_apply]
  have hmono : Monotone y := Tuple.monotone_sort x
  refine ⟨σ, hlast, hcast, (hx (Tuple.sort x 0)).1,
    hmono (show (0 : Fin 3) ≤ 1 by decide), hmono (show (1 : Fin 3) ≤ 2 by decide),
    (hx (Tuple.sort x 2)).2, ?_⟩
  let z := levelsAt (x 0) (x 1) (x 2)
  have hz (i : Fin 3) : z (σ i.castSucc) = y i := by
    rw [hcast]
    change z (Tuple.sort x i).castSucc = x (Tuple.sort x i)
    generalize Tuple.sort x i = j
    fin_cases j <;> rfl
  intro r hr
  rw [← hz 0, ← hz 1, ← hz 2]
  exact normalizedDeficit_permute hr U σ hlast (x 0) (x 1) (x 2)

#print axioms normalizedDeficit_permute
#print axioms exists_sorted_normalizedDeficit

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrumPermutation
