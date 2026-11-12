import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.QuantumBounds.HamiltonianDisplacement
import Mathlib.Analysis.InnerProductSpace.PiL2

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.QuantumBounds
open _root_.D5.S3.QuantumBounds.HamiltonianDisplacement

noncomputable section
universe u
namespace Reg.D5.S3.QuantumBounds.HamiltonianDisplacement

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (A : E →L[ℂ] E) (hA : IsSelfAdjoint A)
    (psi : E) (hpsi : ‖psi‖ = 1) (hbar : ℝ) (hhbar : 0 < hbar) (t : ℝ),
    let mu : ℝ := (inner ℂ psi (A psi)).re
    let Delta : ℝ := ‖A psi - (mu : ℂ) • psi‖
    R.readout () () (FubiniStudyRecordTime.fsAngle psi
      ((NormedSpace.exp ((-Complex.I * (t : ℂ) / (hbar : ℂ)) • A)) psi))
      (|t| * Delta / hbar)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let E := EuclideanSpace ℂ (ULift.{u} Unit)
  let psi : E := EuclideanSpace.single ⟨()⟩ 1
  have hp : ‖psi‖ = 1 := by simp [psi]
  exact h (E := E) 0 (by simp) psi hp 1 (by norm_num) 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh

def family : Registration arena.{u} (type_of% (@hamiltonian_displacement.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hamiltonian_displacement, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@hamiltonian_displacement.{u}) (Realization signature) (type_of% (ℝ)) Unit := {
  unitName := `D5.S3.QuantumBounds.HamiltonianDisplacement.hamiltonian_displacement.__information_unit
  realizationName := `Reg.D5.S3.QuantumBounds.HamiltonianDisplacement.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.HamiltonianDisplacement
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.QuantumBounds.HamiltonianDisplacement
