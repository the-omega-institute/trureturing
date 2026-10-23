import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.TraceClass.SpectralEnergy
import Reg.Support.DependentFamily
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped ComplexOrder ENNReal
open QuantumLogEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Analysis.TraceClass.SpectralEnergy

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ≥0∞
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)
def rejected := realize signature.{u} (fun _ _ _ => 1) (fun a => nomatch a)

def theoremLaw (R : Realization signature.{u}) : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : Reference H) (rho : TraceClass H) (hrho : 0 ≤ rho.1),
    R.readout ⟨()⟩ () (spectralEnergy T rho) = regularizedSupremum T rho

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

theorem actual_law : arena.{u}.Law actual := by
  intro H _ _ _ T rho hrho
  exact spectralEnergy_eq_regularizedSupremum T rho hrho

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let K := EuclideanSpace ℂ (ULift.{u} Unit)
  let r : TraceClass K := TraceClass.ofOperator 0 isTraceClass_zero
  let T : Reference K := ⟨r, le_rfl, zero_le_one⟩
  have hf := h T r le_rfl
  have hz : regularizedSupremum T r = 0 := by
    unfold regularizedSupremum regularizedEnergy
    have hr : r = 0 := rfl
    simp only [hr, map_zero, Complex.zero_re, ENNReal.ofReal_zero, iSup_const]
  simpa only [rejected, realize, hz, one_ne_zero] using hf

def family : Registration arena.{u} (arena.Law actual) where
  actual := realize signature (fun _ _ z => z) (fun a => nomatch a)
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

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@QuantumLogEnergy.spectralEnergy_eq_regularizedSupremum.{u})
    (type_of% (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.SpectralEnergy.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.SpectralEnergy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end Reg.D5.S3.Quantum.Analysis.TraceClass.SpectralEnergy
