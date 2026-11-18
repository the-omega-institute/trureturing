import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.PureState.BargmannRealRephasing

/-! Source-bound registrations for real rephasing of a matrix with a row free of zeros.
Each record selects the cyclic product `G i j * G j k * G k i` of the original statement, read
out as a function of the third index `k` at fixed size, matrix and indices `i`, `j`, and keeps
every other clause verbatim. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.PureState.BargmannRealRephasing
open Complex Matrix
open scoped ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Quantum.PureState.BargmannRealRephasing

abbrev Params := Σ N : ℕ, Σ _ : Matrix (Fin N) (Fin N) ℂ, Σ _ : Fin N, Fin N

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Params (fun p => Fin p.1) (fun _ => ℂ)

/-- The matrix with diagonal `1` and off-diagonal `2`. -/
private def twoMatrix : Matrix (Fin 2) (Fin 2) ℂ := fun a b => if a = b then 1 else 2

private theorem triple_dependence :
    twoMatrix 0 0 * twoMatrix 0 0 * twoMatrix 0 0 ≠
      twoMatrix 0 0 * twoMatrix 0 1 * twoMatrix 1 0 := by
  norm_num [twoMatrix]

private theorem one_hermitian : (1 : Matrix (Fin 1) (Fin 1) ℂ).IsHermitian :=
  isHermitian_one

private theorem one_posSemidef : (1 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef :=
  PosSemidef.one

private theorem one_ne_zero_entries : ∀ i j, (1 : Matrix (Fin 1) (Fin 1) ℂ) i j ≠ 0 := by
  intro i j
  rw [Subsingleton.elim i j, one_apply_eq]
  exact one_ne_zero

namespace Rephasing

def actual : Realization signature :=
  realize signature
    (fun _ p k => p.2.1 p.2.2.1 p.2.2.2 * p.2.1 p.2.2.2 k * p.2.1 k p.2.2.1)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => I) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (_ : G.IsHermitian)
    (i₀ : Fin N) (_ : ∀ j, G i₀ j ≠ 0),
    (∃ θ : Fin N → ℝ, ∀ i j,
        (Complex.exp (θ i * I) * G i j * Complex.exp (-(θ j) * I)).im = 0) ↔
      ∀ i j k, (R.readout () ⟨N, G, i, j⟩ k).im = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (N := 1) 1 one_hermitian 0 (one_ne_zero_entries 0)).mp
    ⟨fun _ => 0, fun i j => by rw [Subsingleton.elim i j]; simp⟩ 0 0 0
  simp [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨⟨2, twoMatrix, 0, 0⟩, 0, 1, triple_dependence⟩

def source : Registration arena
    (type_of% @exists_real_rephasing_iff_triple_products_real) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_real_rephasing_iff_triple_products_real, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_real_rephasing_iff_triple_products_real) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.PureState.BargmannRealRephasing.Rephasing.unit
  realizationName := `Reg.D5.S3.Quantum.PureState.BargmannRealRephasing.Rephasing.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p k => p.2.1 p.2.2.1 p.2.2.2 * p.2.1 p.2.2.2 k * p.2.1 k p.2.2.1)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.PureState.BargmannRealRephasing
    definition := none
    coordinates := #[0, 1, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "body", "body", "fn",
        "arg", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end Rephasing

namespace RealGram

def actual : Realization signature :=
  realize signature
    (fun _ p k => p.2.1 p.2.2.1 p.2.2.2 * p.2.1 p.2.2.2 k * p.2.1 k p.2.2.1)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => I) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (_ : G.PosSemidef)
    (i₀ : Fin N) (_ : ∀ j, G i₀ j ≠ 0),
    (∃ θ : Fin N → ℝ, ∃ B : Matrix (Fin N) (Fin N) ℝ, ∀ i j,
        Complex.exp (θ i * I) * G i j * Complex.exp (-(θ j) * I) = ((Bᵀ * B) i j : ℂ)) ↔
      ∀ i j k, (R.readout () ⟨N, G, i, j⟩ k).im = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (N := 1) 1 one_posSemidef 0 (one_ne_zero_entries 0)).mp
    ⟨fun _ => 0, 1, fun i j => by rw [Subsingleton.elim i j]; simp⟩ 0 0 0
  simp [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨⟨2, twoMatrix, 0, 0⟩, 0, 1, triple_dependence⟩

def source : Registration arena
    (type_of% @exists_real_gram_rephasing_iff_triple_products_real) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_real_gram_rephasing_iff_triple_products_real, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_real_gram_rephasing_iff_triple_products_real) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.PureState.BargmannRealRephasing.RealGram.unit
  realizationName := `Reg.D5.S3.Quantum.PureState.BargmannRealRephasing.RealGram.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p k => p.2.1 p.2.2.1 p.2.2.2 * p.2.1 p.2.2.2 k * p.2.1 k p.2.2.1)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.PureState.BargmannRealRephasing
    definition := none
    coordinates := #[0, 1, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "body", "body", "fn",
        "arg", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end RealGram

end Reg.D5.S3.Quantum.PureState.BargmannRealRephasing
