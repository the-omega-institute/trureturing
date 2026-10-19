import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Subentropy.SpectralFormula
import Reg.Support.DependentFamily

/-! Observe the logarithm in the complete simple-spectrum subentropy identity. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Quantum.Subentropy.SpectralFormula

open _root_.D5.S3.Quantum.Subentropy.Basic
open _root_.D5.S3.Quantum.Subentropy.SpectralFormula
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators

universe u

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => Real.log x + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (hpinj : Function.Injective p),
    matrixSubentropy (diagonal (fun i => (p i : ℂ))) =
      -(∑ i, p i ^ Fintype.card ι * R.readout () () (p i) /
        (∏ j ∈ Finset.univ.erase i, (p i - p j)))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := @h (ULift.{u} Unit) inferInstance inferInstance (fun _ => 1)
    (by norm_num) (by simp) (fun i j _ => Subsingleton.elim i j)
  have hpure := matrixSubentropy_pure (fun _ : ULift.{u} Unit => (1 : ℂ)) (by simp)
  have hdiag : (diagonal (fun _ : ULift.{u} Unit => (1 : ℂ))) =
      Matrix.vecMulVec (fun _ => (1 : ℂ)) (star (fun _ => (1 : ℂ))) := by
    ext i j
    simp [Subsingleton.elim i j, Matrix.vecMulVec_apply]
  norm_num only [Complex.ofReal_one] at he
  rw [hdiag, hpure] at he
  norm_num [rejected, realize] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, (1 / 3), ?_⟩
  simpa [actual, realize] using
    (Real.log_ne_zero_of_pos_of_ne_one
      (by norm_num : 0 < (1 / 3 : ℝ)) (by norm_num : (1 / 3 : ℝ) ≠ 1)).symm

def source_registration : Registration arena.{u}
    (type_of% @matrixSubentropy_diagonal_eq_distinct_formula.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@matrixSubentropy_diagonal_eq_distinct_formula, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@matrixSubentropy_diagonal_eq_distinct_formula.{u})
      (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Subentropy.SpectralFormula.matrixSubentropy_diagonal_eq_distinct_formula.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.SpectralFormula.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.log x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.SpectralFormula
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Quantum.Subentropy.SpectralFormula
