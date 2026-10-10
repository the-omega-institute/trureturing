/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryExponentAvoidance
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Transvection

namespace NikolovSegal.UnitaryField

open Matrix
variable {F : Type*} [Field F] [Finite F]
variable {I : Type*} [Fintype I] [DecidableEq I]

def hermitianForm (τ : I ≃ I) : Matrix I I F := fun i j => if τ i = j then 1 else 0

def adjoint (ι : F ≃+* F) (A : Matrix I I F) : Matrix I I F := A.transpose.map ι

def diagonalSL (w : I → Fˣ) (hw : ∏ i, w i = 1) : SpecialLinearGroup I F :=
  ⟨diagonal (fun i => (w i : F)), by
    rw [det_diagonal]
    rw [← Units.coe_prod, hw]
    rfl⟩

theorem diagonal_hermitian (ι : F ≃+* F) (τ : I ≃ I) (w : I → Fˣ)
    (hw : ∀ i, involutionUnit ι (w i) * w (τ i) = 1) :
    adjoint ι (diagonal fun i => (w i : F)) * hermitianForm τ *
      diagonal (fun i => (w i : F)) = hermitianForm τ := by
  ext i j
  have ha : adjoint ι (diagonal fun i => (w i : F)) =
      diagonal (fun i => ι (w i)) := by
    ext r c
    by_cases h : r = c <;> simp [adjoint, diagonal, h, eq_comm]
  rw [ha, mul_diagonal, diagonal_mul]
  by_cases h : τ i = j
  · subst j
    have hh := congrArg (fun u : Fˣ => (u : F)) (hw i)
    simpa [hermitianForm] using hh
  · simp [hermitianForm, h]

theorem diagonal_conjugation_entries (w : I → Fˣ) (A : Matrix I I F) (r c : I) :
    (diagonal (fun i => (w i : F)) * A *
      diagonal (fun i => (((w i)⁻¹ : Fˣ) : F))) r c =
      ((w r / w c : Fˣ) : F) * A r c := by
  rw [mul_diagonal, diagonal_mul]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

def pairSwap (d : ℕ) : (Fin d ⊕ Fin d) ≃ (Fin d ⊕ Fin d) := Equiv.sumComm _ _

def pairedEntries (ι : F ≃+* F) {d : ℕ} (a : Fin d → ℤ) (u : Fˣ) :
    (Fin d ⊕ Fin d) → Fˣ
  | .inl i => u ^ a i
  | .inr i => (involutionUnit ι u) ^ (-a i)

theorem pairedEntries_hermitian (ι : F ≃+* F) (hinv : Function.Involutive ι)
    {d : ℕ} (a : Fin d → ℤ) (u : Fˣ) (i : Fin d ⊕ Fin d) :
    involutionUnit ι (pairedEntries ι a u i) *
      pairedEntries ι a u (pairSwap d i) = 1 := by
  have hi : involutionUnit ι (involutionUnit ι u) = u := by
    apply Units.ext
    exact hinv u
  cases i <;> simp [pairedEntries, pairSwap, map_zpow, hi]

theorem prod_zpow_base {G : Type*} [CommGroup G] {J : Type*} (s : Finset J)
    (u : G) (a : J → ℤ) : (∏ i ∈ s, u ^ a i) = u ^ (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, zpow_add]

theorem prod_pairedEntries (ι : F ≃+* F) {d : ℕ} (a : Fin d → ℤ) (u : Fˣ) :
    (∏ i, pairedEntries ι a u i) =
      (u / involutionUnit ι u) ^ (∑ i, a i) := by
  rw [Fintype.prod_sum_type]
  simp only [pairedEntries]
  rw [prod_zpow_base, prod_zpow_base]
  rw [div_zpow]
  simp only [Finset.sum_neg_distrib, zpow_neg, div_eq_mul_inv]

def oddSwap (d : ℕ) : Option (Fin d ⊕ Fin d) ≃ Option (Fin d ⊕ Fin d) :=
  Equiv.optionCongr (pairSwap d)

def oddEntries (ι : F ≃+* F) {d : ℕ} (a : Fin d → ℤ) (u : Fˣ) :
    Option (Fin d ⊕ Fin d) → Fˣ
  | none => (u / involutionUnit ι u) ^ (-(∑ i, a i))
  | some i => pairedEntries ι a u i

theorem prod_oddEntries (ι : F ≃+* F) {d : ℕ} (a : Fin d → ℤ) (u : Fˣ) :
    ∏ i, oddEntries ι a u i = 1 := by
  rw [Fintype.prod_option]
  simp only [oddEntries, prod_pairedEntries, zpow_neg]
  exact inv_mul_cancel _

theorem oddEntries_hermitian (ι : F ≃+* F) (hinv : Function.Involutive ι)
    {d : ℕ} (a : Fin d → ℤ) (u : Fˣ) (i : Option (Fin d ⊕ Fin d)) :
    involutionUnit ι (oddEntries ι a u i) *
      oddEntries ι a u (oddSwap d i) = 1 := by
  cases i with
  | none =>
    have hi : involutionUnit ι (involutionUnit ι u) = u := by
      apply Units.ext
      exact hinv u
    simp [oddEntries, oddSwap, map_zpow, map_div, hi, div_zpow,
      mul_comm, mul_left_comm, mul_assoc]
  | some i => exact pairedEntries_hermitian ι hinv a u i

def evenDiagonal (ι : F ≃+* F) {d : ℕ} (a : Fin d → ℤ)
    (ha : ∑ i, a i = 0) (u : Fˣ) : SpecialLinearGroup (Fin d ⊕ Fin d) F :=
  diagonalSL (pairedEntries ι a u) (by rw [prod_pairedEntries, ha, zpow_zero])

def oddDiagonal (ι : F ≃+* F) {d : ℕ} (a : Fin d → ℤ) (u : Fˣ) :
    SpecialLinearGroup (Option (Fin d ⊕ Fin d)) F :=
  diagonalSL (oddEntries ι a u) (prod_oddEntries ι a u)

theorem evenDiagonal_unitary (ι : F ≃+* F) (hinv : Function.Involutive ι)
    {d : ℕ} (a : Fin d → ℤ) (ha : ∑ i, a i = 0) (u : Fˣ) :
    adjoint ι (evenDiagonal ι a ha u).val * hermitianForm (pairSwap d) *
      (evenDiagonal ι a ha u).val = hermitianForm (pairSwap d) :=
  diagonal_hermitian ι (pairSwap d) _ (pairedEntries_hermitian ι hinv a u)

theorem oddDiagonal_unitary (ι : F ≃+* F) (hinv : Function.Involutive ι)
    {d : ℕ} (a : Fin d → ℤ) (u : Fˣ) :
    adjoint ι (oddDiagonal ι a u).val * hermitianForm (oddSwap d) *
      (oddDiagonal ι a u).val = hermitianForm (oddSwap d) :=
  diagonal_hermitian ι (oddSwap d) _ (oddEntries_hermitian ι hinv a u)

end NikolovSegal.UnitaryField
