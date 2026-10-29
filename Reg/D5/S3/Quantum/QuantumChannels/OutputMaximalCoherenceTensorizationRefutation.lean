import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation
import Reg.Support.DependentFamily

/-! Source-bound registration for positivity preservation by a Kraus map. -/

namespace Reg.D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation

open _root_.D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.checkUnivs false
noncomputable section
universe u

abbrev signature : Signature where
  Params := Σ a : Type u, Σ b : Type u, Σ κ : Type u,
    (κ → Matrix b a ℂ) × Matrix a a ℂ
  State p := Matrix p.2.1 p.2.1 ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M => M.PosSemidef) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type u} {κ : Type u}
    [Fintype a] [DecidableEq a] [Finite b] [Fintype κ]
    (K : κ → Matrix b a ℂ) (ρ : Matrix a a ℂ) (_hρ : ρ.PosSemidef),
    R.readout () ⟨a, ⟨b, ⟨κ, (K, ρ)⟩⟩⟩ (krausApply K ρ)

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  let a := ULift.{u} Unit
  let b := ULift.{u} Unit
  let κ := ULift.{u} Unit
  let K : κ → Matrix b a ℂ := fun _ => 0
  let ρ : Matrix a a ℂ := 0
  have hh := h (a := a) (b := b) (κ := κ) K ρ Matrix.PosSemidef.zero
  exact hh

private theorem dependence :
    ObservationalDependence signature.{u} actual.{u} := by
  intro i
  let a := ULift.{u} Unit
  let b := ULift.{u} Unit
  let κ := ULift.{u} Unit
  let K : κ → Matrix b a ℂ := fun _ => 0
  let ρ : Matrix a a ℂ := 0
  let p : signature.{u}.Params := ⟨a, ⟨b, ⟨κ, (K, ρ)⟩⟩⟩
  refine ⟨p, 0, -(1 : Matrix b b ℂ), ?_⟩
  intro he
  have hnot : ¬ (-(1 : Matrix b b ℂ)).PosSemidef := by
    intro h
    have hd := h.diag_nonneg (i := (⟨()⟩ : b))
    change (0 : ℂ) ≤ -1 at hd
    norm_num [Complex.le_def] at hd
  exact hnot (Eq.mp he Matrix.PosSemidef.zero)

def source_registration : Registration arena.{u}
    (type_of% @kraus_psd.{u,u,u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kraus_psd.{u,u,u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@kraus_psd.{u,u,u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => M.PosSemidef) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation
