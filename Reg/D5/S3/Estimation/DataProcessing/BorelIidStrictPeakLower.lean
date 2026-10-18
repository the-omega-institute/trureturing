import D5.S3.Estimation.DataProcessing.BorelIidStrictPeakLower
import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.AuricFib
import Reg.Support.DependentFamily

noncomputable section
namespace Reg.D5.S3.Estimation.DataProcessing.BorelIidStrictPeakLower
open _root_.D5.S3.Estimation.DataProcessing.BorelIidStrictPeakLower
open _root_.D5.S3.Estimation.DataProcessing.IidStrictPeakSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory Filter Topology Set
open scoped BigOperators

abbrev signature : Signature where
  Params := Measure ℝ
  State _ := Fin 5
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ μ s => modeMass μ s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def fullLaw (r : Realization signature) : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
    let X := r.readout () μ 1+r.readout () μ 3
    let D := r.readout () μ 0*r.readout () μ 3-r.readout () μ 1*r.readout () μ 2
    (∀ s, Tendsto (fun n => quantizedMass μ n s) atTop (𝓝 (r.readout () μ s))) ∧
    (∀ s, 0 ≤ r.readout () μ s) ∧ (∑ s, r.readout () μ s) = 1 ∧
    r.readout () μ 2+r.readout () μ 3 = X ∧ r.readout () μ 4 = X ∧
    0 ≤ X ∧ X ≤ 1/3 ∧ -X/15 ≤ D ∧ -1/45 ≤ D

abbrev arena : Arena where
  signature := signature
  Law := fullLaw

private theorem rejected_law : ¬ fullLaw rejected := by
  intro h
  have ht := h (Measure.dirac (0 : ℝ))
  have hn := ht.2.2.1
  norm_num [rejected,realize] at hn

def family : Registration arena (type_of% borel_iid_lower_surface) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨borel_iid_lower_surface,rejected,rejected_law⟩
  sensitivity := ⟨fun _ => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim _ _)).elim,rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := by
    intro _
    refine ⟨Measure.dirac (0 : ℝ),0,1,?_⟩
    have hpi : Measure.pi (fun _ : Fin 5 => Measure.dirac (0 : ℝ)) =
        Measure.dirac (fun _ : Fin 5 => (0 : ℝ)) := by
      apply Measure.pi_eq
      intro sets hs
      classical
      by_cases h : ∀ i, (0 : ℝ) ∈ sets i
      · simp [Measure.dirac_apply',hs,h]
      · obtain ⟨i,hi⟩ := not_forall.mp h
        have hz : (∏ i : Fin 5, Measure.dirac (0 : ℝ) (sets i)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Measure.dirac_apply',hs,hi])
        rw [hz]
        simp [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs),h]
    norm_num [actual,realize,modeMass,source,hpi,mode,peak]

def selection : Contract.SourceSelection where
  owner := `D5.S3.Estimation.DataProcessing.BorelIidStrictPeakLower
  definition := none
  coordinates := #[0]
  readouts := #[{
    path := #["body","body","value","fn","arg","fn"]
    stateBinder := 0
    functionOperand := true
    stateOperand := none
    booleanPredicate := false}]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    borel_iid_lower_surface
    (type_of% (realize signature (fun _ μ s => modeMass μ s) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Estimation.DataProcessing.BorelIidStrictPeakLower.borel_iid_lower_surface.__information_unit
  realizationName := `Reg.D5.S3.Estimation.DataProcessing.BorelIidStrictPeakLower.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ μ s => modeMass μ s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev analysisSource : Analysis.Source borel_iid_lower_surface :=
  Analysis.Source.ofRegistration _ family .exact selection

def analysis : AuricFib.Contract.Application borel_iid_lower_surface where
  evidence := .typed {
    source := analysisSource
    plan := {task := (),initial := [],additions := [[()],[]]}
    acquisition := .unavailable "The Borel source has no acquired encoded law fiber or native continuation map"}

#print axioms family
end Reg.D5.S3.Estimation.DataProcessing.BorelIidStrictPeakLower
