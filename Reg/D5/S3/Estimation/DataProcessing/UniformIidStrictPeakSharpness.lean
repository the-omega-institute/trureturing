import D5.S3.Estimation.DataProcessing.UniformIidStrictPeakSharpness
import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.AuricFib
import Reg.Support.DependentFamily

noncomputable section
namespace Reg.D5.S3.Estimation.DataProcessing.UniformIidStrictPeakSharpness
open _root_.D5.S3.Estimation.DataProcessing.UniformIidStrictPeakSharpness
open _root_.D5.S3.Estimation.DataProcessing.IidStrictPeakSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter Topology Set

abbrev signature : Signature where
  Params := ℕ
  State _ := Fin 5
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q s => modeLaw (uniform q) s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def fullLaw (r : Realization signature) : Prop :=
  let D := fun q => r.readout () q 0*r.readout () q 3-r.readout () q 1*r.readout () q 2
  (∀ q : ℕ, 0 < q →
    r.readout () q 1+r.readout () q 3 =
      ((q:ℝ)-1)*(2*(q:ℝ)-1)/(6*(q:ℝ)^2) ∧
    r.readout () q 3 =
      (((q:ℝ)-1)*(2*(q:ℝ)-1)/(6*(q:ℝ)^2))*
        (2*(q:ℝ)^2-2*(q:ℝ)+1)/(5*(q:ℝ)^2) ∧
    D q = -((q:ℝ)-1)*(2*(q:ℝ)-1)*
      (2*(q:ℝ)^4-13*(q:ℝ)^3+9*(q:ℝ)^2-5*(q:ℝ)+1)/(180*(q:ℝ)^6)) ∧
  (∀ q : ℕ, 2 ≤ q → q ≤ 5 → 0 < D q) ∧
  (∀ q : ℕ, 6 ≤ q → D q < 0) ∧
  Tendsto D atTop (𝓝 (-1/45 : ℝ)) ∧
  IsGLB finiteDeterminants (-1/45) ∧ (-1/45 : ℝ) ∉ finiteDeterminants

abbrev arena : Arena where
  signature := signature
  Law := fullLaw

private theorem rejected_law : ¬ fullLaw rejected := by
  intro h
  have hx := (h.1 2 (by norm_num)).1
  norm_num [rejected,realize] at hx

def family : Registration arena (type_of% uniform_peak_sharpness) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨uniform_peak_sharpness,rejected,rejected_law⟩
  sensitivity := ⟨fun _ => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim _ _)).elim,rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := by
    intro _
    refine ⟨1,0,1,?_⟩
    have hlt (a b : Fin 1) : ¬ a < b := by
      rw [Subsingleton.elim a b]
      exact lt_irrefl _
    norm_num [actual,realize,modeLaw,productAverage,average,mode,peak,uniform,hlt]

def selection : Contract.SourceSelection where
  owner := `D5.S3.Estimation.DataProcessing.UniformIidStrictPeakSharpness
  definition := none
  coordinates := #[0]
  readouts := #[{
    path := #["fn","arg","body","body","fn","arg","fn","arg","fn","arg","fn"]
    stateBinder := 0
    functionOperand := true
    stateOperand := none
    booleanPredicate := false}]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    uniform_peak_sharpness
    (type_of% (realize signature (fun _ q s => modeLaw (uniform q) s) (fun e => nomatch e)))
    Unit Unit where
  unitName := `D5.S3.Estimation.DataProcessing.UniformIidStrictPeakSharpness.uniform_peak_sharpness.__information_unit
  realizationName := `Reg.D5.S3.Estimation.DataProcessing.UniformIidStrictPeakSharpness.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q s => modeLaw (uniform q) s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev analysisSource : Analysis.Source uniform_peak_sharpness :=
  Analysis.Source.ofRegistration _ family .exact selection

def analysis : AuricFib.Contract.Application uniform_peak_sharpness where
  evidence := .typed {
    source := analysisSource
    plan := {task := (),initial := [],additions := [[()],[]]}
    acquisition := .unavailable "No native continuation correspondence or encoded finite macro-law presentation"}

#print axioms family
end Reg.D5.S3.Estimation.DataProcessing.UniformIidStrictPeakSharpness
