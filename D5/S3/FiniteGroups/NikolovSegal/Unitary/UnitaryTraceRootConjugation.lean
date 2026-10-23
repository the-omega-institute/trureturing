/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryTraceRootConjugation
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryTraceRootConjugation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryTraceRoot
import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryPoweredConjugation
import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryDiagonalSeparation

namespace NikolovSegal.UnitaryField
open Matrix
variable {F : Type*} [Field F] [Finite F]

theorem traceRoot3_conjugation (ι : F ≃+* F) (w : Fin 3 → Fˣ)
    (hw : ∏ i, w i = 1)
    (h02 : involutionUnit ι (w 0) * w 2 = 1)
    (h11 : involutionUnit ι (w 1) * w 1 = 1)
    (s : ℕ) (x y : F) :
    (diagonalSL w hw)^s * traceRoot3 ι x y * ((diagonalSL w hw)^s)⁻¹ =
      traceRoot3 ι ((((w 0 / w 1)^s : Fˣ) : F) * x)
        ((((w 0 / w 2)^s : Fˣ) : F) * y) := by
  have h0 : involutionUnit ι (w 0) = (w 2)⁻¹ := eq_inv_of_mul_eq_one_left h02
  have h1 : involutionUnit ι (w 1) = (w 1)⁻¹ := eq_inv_of_mul_eq_one_left h11
  have hc : involutionUnit ι (w 0 / w 1) = w 1 / w 2 := by
    simp [map_div, h0, h1, div_eq_mul_inv, mul_comm]
  have hcF : ι ((((w 0 / w 1)^s : Fˣ) : F)) = (((w 1 / w 2)^s : Fˣ) : F) := by
    have hh := congrArg (fun u : Fˣ => (u : F)) ((map_pow (involutionUnit ι) _ s).trans
      (congrArg (fun u : Fˣ => u^s) hc))
    exact hh
  have hcF' : (ι (w 0) / ι (w 1))^s = ((w 1 : F) / (w 2 : F))^s := by
    simpa using hcF
  apply Subtype.ext
  ext i j
  rw [actual_powered_conjugation]
  fin_cases i <;> fin_cases j <;>
    simp [traceRoot3, map_mul, hcF', div_self]

def threeEntries (ι : F ≃+* F) (u : Fˣ) : Fin 3 → Fˣ :=
  ![u, (u / involutionUnit ι u)⁻¹, (involutionUnit ι u)⁻¹]

theorem prod_threeEntries (ι : F ≃+* F) (u : Fˣ) : ∏ i, threeEntries ι u i = 1 := by
  simp [Fin.prod_univ_three, threeEntries, div_eq_mul_inv, mul_assoc]

def threeDiagonal (ι : F ≃+* F) (u : Fˣ) : SpecialLinearGroup (Fin 3) F :=
  diagonalSL (threeEntries ι u) (prod_threeEntries ι u)

theorem threeEntries_unitary (ι : F ≃+* F) (hinv : Function.Involutive ι) (u : Fˣ) :
    involutionUnit ι (threeEntries ι u 0) * threeEntries ι u 2 = 1 ∧
      involutionUnit ι (threeEntries ι u 1) * threeEntries ι u 1 = 1 := by
  have hi : involutionUnit ι (involutionUnit ι u) = u := by
    apply Units.ext
    exact hinv u
  simp [threeEntries, map_inv, map_div, hi, div_eq_mul_inv, mul_comm, mul_assoc]

theorem threeDiagonal_unitary (ι : F ≃+* F) (hinv : Function.Involutive ι) (u : Fˣ) :
    adjoint ι (threeDiagonal ι u).val * antiDiagonal3 * (threeDiagonal ι u).val =
      antiDiagonal3 := by
  have h := threeEntries_unitary ι hinv u
  have h20 : involutionUnit ι (threeEntries ι u 2) * threeEntries ι u 0 = 1 := by
    have hi : involutionUnit ι (involutionUnit ι u) = u := by
      apply Units.ext
      exact hinv u
    simp [threeEntries, map_inv, hi]
  have ha : adjoint ι (threeDiagonal ι u).val = diagonal (fun i => ι (threeEntries ι u i)) := by
    ext i j
    by_cases hij : i = j <;> simp [threeDiagonal, diagonalSL, adjoint, Matrix.diagonal, hij, eq_comm]
  have hv : (threeDiagonal ι u).val = diagonal (fun i => (threeEntries ι u i : F)) := rfl
  ext i j
  rw [ha, hv, mul_diagonal, diagonal_mul]
  fin_cases i <;> fin_cases j <;>
    simp [antiDiagonal3, threeDiagonal, diagonalSL]
  · exact congrArg (fun z : Fˣ => (z : F)) h.1
  · exact congrArg (fun z : Fˣ => (z : F)) h.2
  · exact congrArg (fun z : Fˣ => (z : F)) h20

/- One diagonal is selected before every short-root target. Trace and norm
provide actual Hermitian root matrices; their powered action has the literal
two coefficients, both distinct from one. Characteristic two is allowed. -/
theorem regular_unitary_trace_root3 (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F)
    (s : ℕ) (hs : 0 < s) (hQ : 8*s + 2 < Nat.card (fixedField ι)) :
    ∃ u : Fˣ,
      adjoint ι (threeDiagonal ι u).val * antiDiagonal3 * (threeDiagonal ι u).val = antiDiagonal3 ∧
      ((threeEntries ι u 0 / threeEntries ι u 1)^s : Fˣ) ≠ 1 ∧
      ((threeEntries ι u 0 / threeEntries ι u 2)^s : Fˣ) ≠ 1 ∧
      ∀ x : F, ∃ y : F, y + ι y = -(x * ι x) ∧
        adjoint ι (traceRoot3 ι x y).val * antiDiagonal3 * (traceRoot3 ι x y).val = antiDiagonal3 ∧
        (threeDiagonal ι u)^s * traceRoot3 ι x y * ((threeDiagonal ι u)^s)⁻¹ =
          traceRoot3 ι ((((threeEntries ι u 0 / threeEntries ι u 1)^s : Fˣ) : F) * x)
            ((((threeEntries ι u 0 / threeEntries ι u 2)^s : Fˣ) : F) * y) := by
  obtain ⟨u, _, _, hsep⟩ := regular_odd_diagonal ι hinv hne 1 s (by omega) hs (by nlinarith)
  have he0 : oddEntries ι (positiveWeight 1) u (.some (.inl 0)) = threeEntries ι u 0 := by
    simp [oddEntries, pairedEntries, positiveWeight, threeEntries]
  have he1 : oddEntries ι (positiveWeight 1) u none = threeEntries ι u 1 := by
    simp [oddEntries, positiveWeight, threeEntries]
  have he2 : oddEntries ι (positiveWeight 1) u (.some (.inr 0)) = threeEntries ι u 2 := by
    simp [oddEntries, pairedEntries, positiveWeight, threeEntries]
  have hU := threeEntries_unitary ι hinv u
  refine ⟨u, threeDiagonal_unitary ι hinv u, ?_, ?_, ?_⟩
  · simpa only [he0, he1] using hsep (.some (.inl 0)) none (by simp)
  · simpa only [he0, he2] using hsep (.some (.inl 0)) (.some (.inr 0)) (by simp)
  · intro x
    obtain ⟨y, hy, hR⟩ := actual_trace_root_exists ι hinv hne x
    exact ⟨y, hy, hR, traceRoot3_conjugation ι _ _ hU.1 hU.2 s x y⟩

end NikolovSegal.UnitaryField
