import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.TraceClass.LogRegularization
import Reg.Support.DependentFamily
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped ComplexOrder
open QuantumLogEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Analysis.TraceClass.LogRegularization

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def emptyAnchor : Empty → Unit → ℂ := fun a => nomatch a

def actual : Realization signature.{u} :=
  realize signature (fun _ _ z => z.re) emptyAnchor

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => -1) emptyAnchor

def theoremLaw (R : Realization signature.{u}) : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : H →L[ℂ] H} (hA : 0 ≤ A) (rho : TraceClass H) (hrho : 0 ≤ rho.1),
    0 ≤ R.readout ⟨()⟩ () (TraceClass.tracePairing A rho)

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

theorem actual_law : arena.{u}.Law actual := by
  intro H _ _ _ A hA rho hrho
  exact tracePairing_nonneg hA rho hrho

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let K := EuclideanSpace ℂ (ULift.{u} Unit)
  let rho : TraceClass K := TraceClass.ofOperator 0 isTraceClass_zero
  have hf := h (A := (0 : K →L[ℂ] K)) le_rfl rho le_rfl
  norm_num [rejected, realize] at hf

def family : Registration arena.{u} (arena.Law actual) where
  actual := realize signature (fun _ _ z => z.re) emptyAnchor
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    simp [actual, realize]

-- The complete operator and positivity telescope is retained in theoremLaw.
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@QuantumLogEnergy.tracePairing_nonneg.{u})
    (type_of% (realize signature.{u} (fun _ _ z => z.re) emptyAnchor))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.LogRegularization.pairingUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.LogRegularization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ z => z.re) emptyAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.TraceClass.LogRegularization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end Reg.D5.S3.Quantum.Analysis.TraceClass.LogRegularization
