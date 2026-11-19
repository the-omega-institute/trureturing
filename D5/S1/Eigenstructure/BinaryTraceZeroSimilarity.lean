/- GID: D5/S1/Eigenstructure/BinaryTraceZeroSimilarity
   generality: I
   mirror-B: D5/B/S1/Eigenstructure/BinaryTraceZeroSimilarity
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Similarity representatives for nonzero trace-zero binary matrices of size three. -/

import D5.S1.Eigenstructure.BinaryCubicCompanion
import D5.S1.Eigenstructure.BinaryCubicRepeatedRoot
import D5.S1.Eigenstructure.NilpotentDimensionThree
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.IntervalCases

/-! The binary matrices that occur as nonzero Heawood switching invariants. -/

namespace D5.S1.Eigenstructure.BinaryTraceZeroSimilarity

open Module Polynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false

local notation "F₂" => ZMod 2
local notation "Mat" => Matrix (Fin 3) (Fin 3) F₂
local notation "Space" => Fin 3 → F₂

/-- The representatives are in the order N1, N2, S, J, C, K. -/
def representative (i : Fin 6) : Mat :=
  ![!![0, 1, 0; 0, 0, 0; 0, 0, 0],
    !![0, 1, 0; 0, 0, 1; 0, 0, 0],
    !![1, 0, 0; 0, 1, 0; 0, 0, 0],
    !![1, 1, 0; 0, 1, 0; 0, 0, 0],
    !![0, 0, 1; 1, 0, 0; 0, 1, 0],
    !![0, 0, 1; 1, 0, 1; 0, 1, 0]] i

private theorem binary_scalar (x : F₂) : x = 0 ∨ x = 1 := by
  revert x
  decide

private theorem trace_zero_charpoly (M : Mat) (htrace : M.trace = 0) :
    M.charpoly = X ^ 3 + C (M.charpoly.coeff 1) * X + C (M.charpoly.coeff 0) := by
  have hdegree : M.charpoly.natDegree = 3 := by simp
  have h₂ : M.charpoly.coeff 2 = 0 := by
    have h := Matrix.trace_eq_neg_charpoly_coeff M
    simpa [htrace, eq_comm] using h
  have h₃ : M.charpoly.coeff 3 = 1 := by
    simpa [hdegree] using M.charpoly_monic.coeff_natDegree
  ext n
  by_cases hn : 3 < n
  · rw [coeff_eq_zero_of_natDegree_lt (p := M.charpoly) (by omega)]
    simp [coeff_X_pow, coeff_X, coeff_C,
      show n ≠ 3 by omega, show 1 ≠ n by omega, show n ≠ 0 by omega]
  · interval_cases n <;> simp [coeff_X_pow, coeff_C, h₂, h₃]

private theorem exists_normal_basis (M : Mat) (hne : M ≠ 0) (htrace : M.trace = 0) :
    ∃ (b : Basis (Fin 3) F₂ Space) (k : Fin 6),
      LinearMap.toMatrix b b (Matrix.toLin' M) = representative k := by
  let f : Module.End F₂ Space := Matrix.toLin' M
  have hfne : f ≠ 0 := fun h => hne (Matrix.toLin'.injective (by simpa [f] using h))
  have hdim : finrank F₂ Space = 3 := by simp
  let a := M.charpoly.coeff 1
  let c := M.charpoly.coeff 0
  have hchar : f.charpoly = X ^ 3 + C a * X + C c := by
    simpa [f, a, c] using trace_zero_charpoly M htrace
  rcases binary_scalar c with hc | hc
  · rcases binary_scalar a with ha | ha
    · have hp : f.charpoly = X ^ 3 := by simpa [hc, ha] using hchar
      have hcube : f ^ 3 = 0 := by
        simpa [hp, aeval_X_pow] using LinearMap.aeval_self_charpoly f
      obtain ⟨b, h0, h1, hcase⟩ := NilpotentDimensionThree.exists_basis f hdim hfne hcube
      rcases hcase with ⟨_, h2⟩ | ⟨_, h2⟩
      · refine ⟨b, 0, ?_⟩
        ext i j
        change LinearMap.toMatrix b b f i j = _
        fin_cases i <;> fin_cases j <;>
          simp [LinearMap.toMatrix_apply, h0, h1, h2, representative]
      · refine ⟨b, 1, ?_⟩
        ext i j
        change LinearMap.toMatrix b b f i j = _
        fin_cases i <;> fin_cases j <;>
          simp [LinearMap.toMatrix_apply, h0, h1, h2, representative]
    · have hp : f.charpoly = X ^ 3 + X := by simpa [hc, ha] using hchar
      obtain ⟨b, h0, h2, hcase⟩ := BinaryCubicRepeatedRoot.exists_basis f hdim hp
      rcases hcase with ⟨_, h1⟩ | ⟨_, h1⟩
      · refine ⟨b, 2, ?_⟩
        ext i j
        change LinearMap.toMatrix b b f i j = _
        fin_cases i <;> fin_cases j <;>
          simp [LinearMap.toMatrix_apply, h0, h1, h2, representative]
      · refine ⟨b, 3, ?_⟩
        ext i j
        change LinearMap.toMatrix b b f i j = _
        fin_cases i <;> fin_cases j <;>
          simp [LinearMap.toMatrix_apply, h0, h1, h2, representative]
  · have hp : f.charpoly = X ^ 3 + C a * X + 1 := by simpa [hc] using hchar
    obtain ⟨b, h0, h1, h2⟩ := BinaryCubicCompanion.exists_basis hdim f a hp
    rcases binary_scalar a with ha | ha
    · refine ⟨b, 4, ?_⟩
      ext i j
      change LinearMap.toMatrix b b f i j = _
      fin_cases i <;> fin_cases j <;>
        simp [LinearMap.toMatrix_apply, h0, h1, h2, ha, representative]
    · refine ⟨b, 5, ?_⟩
      ext i j
      change LinearMap.toMatrix b b f i j = _
      fin_cases i <;> fin_cases j <;>
        simp [LinearMap.toMatrix_apply, h0, h1, h2, ha, representative]

/-- Every nonzero trace-zero binary matrix of size three is conjugate to one
of the six indicated representatives. -/
theorem exists_conjugate (M : Mat) (hne : M ≠ 0) (htrace : M.trace = 0) :
    ∃ (k : Fin 6) (g : Matˣ), M = (g : Mat) * representative k * (↑g⁻¹ : Mat) := by
  obtain ⟨b, k, hb⟩ := exists_normal_basis M hne htrace
  let e := Pi.basisFun F₂ (Fin 3)
  let f := Matrix.toLin' M
  let A := LinearMap.toMatrix b e (LinearMap.id : Space →ₗ[F₂] Space)
  let B := LinearMap.toMatrix e b (LinearMap.id : Space →ₗ[F₂] Space)
  let g : Matˣ :=
    ⟨A, B, by simp [A, B], by simp [A, B]⟩
  refine ⟨k, g, ?_⟩
  change M = A * representative k * B
  rw [← hb]
  change M = A * LinearMap.toMatrix b b f * B
  calc
    M = LinearMap.toMatrix e e f := by simp [e, f]
    _ = _ := by simp [A, B]

end D5.S1.Eigenstructure.BinaryTraceZeroSimilarity
