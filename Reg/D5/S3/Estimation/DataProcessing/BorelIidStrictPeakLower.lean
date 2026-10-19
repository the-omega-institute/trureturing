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
    0 ≤ X ∧ X ≤ 1/3 ∧ -X/15 ≤ D ∧ -1/45 ≤ D ∧
    (∃ s ∈ Icc (0 : ℝ) 1, s^3 = 1-3*X ∧
      s^3/45*(1-s)*(1+s+7*s^2-3*s^3-3*s^4) ≤ D+X/15 ∧
      0 ≤ s^3/45*(1-s)*(1+s+7*s^2-3*s^3-3*s^4)) ∧
    (0 < X → X < 1/3 → -X/15 < D) ∧
    (∀ c : ℝ, 3*X+(μ.real {c})^3 ≤ 1 ∧
      (μ.real {c})^3/45 ≤ D+1/45 ∧
      (0 < μ.real {c} → -1/45 < D)) ∧
    X = ∫ v, (μ.real (Iio v))^2 ∂μ ∧
    (X = 0 ↔ ∃ c : ℝ, μ = Measure.dirac c) ∧
    r.readout () μ 3 ≤ 2/15 ∧ X-1/5 ≤ r.readout () μ 3 ∧
    (X = 1/3 ↔ D = -1/45) ∧ (X = 1/3 ↔ NullSingletonClass μ) ∧
    (D = -X/15 ↔ (∃ c : ℝ, μ = Measure.dirac c) ∨ NullSingletonClass μ) ∧
    (D = -1/45 ↔ NullSingletonClass μ) ∧
    ((∃ c : ℝ, μ = Measure.dirac c) → D = 0)

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
    norm_num [actual,realize,modeMass,hpi,mode,peak]

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

/-- The selected parameter is the uniform probability law on [0,1]. The state
is a mode label, and the observed value is that label's probability mass. -/
abbrev atomlessDomain : Analysis.Domain analysisSource where
  parameter := volume.restrict (Icc (0 : ℝ) 1)
  State := Fin 5
  readout _ s := modeMass (volume.restrict (Icc (0 : ℝ) 1)) s
  scope := .whole (Equiv.refl _) (fun _ _ => rfl)

private theorem interval_mass (s : Fin 5) :
    modeMass (volume.restrict (Icc (0 : ℝ) 1)) s =
      ((![2,3,3,2,5] s : ℕ) : ℝ)/15 := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  letI : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  haveI : NullSingletonClass μ := by dsimp [μ]; infer_instance
  rcases borel_iid_lower_surface μ with
    ⟨_,_,hm,hy,hz,_,_,_,_,_,_,_,_,_,hkhi,hklo,_,hnull,_⟩
  have hx := hnull.mpr (inferInstance : NullSingletonClass μ)
  rw [Fin.sum_univ_five] at hm
  fin_cases s <;> norm_num <;> change _ = _ <;> linarith

private def massValues : Fin 5 → Analysis.Value :=
  ![.nat 2,.nat 3,.nat 3,.nat 2,.nat 5]

private def decodeMass : Analysis.Value → Option ℝ
  | .nat n => some ((n : ℝ)/15)
  | _ => none

private def massKernel : Fin 5 → Fin 5 → Bool :=
  ![![true,false,false,true,false],
    ![false,true,true,false,false],
    ![false,true,true,false,false],
    ![true,false,false,true,false],
    ![false,false,false,false,true]]

def atomlessPlan : Analysis.Plan analysisSource where
  task := ()
  initial := []
  additions := [[()],[]]

/-- Complete five-label presentation for the probability-mass observation.
The two nontrivial fibers are {null,both ends} and {left,right}. -/
def atomlessPresentation : Analysis.FinitePresentation atomlessPlan atomlessDomain where
  stateFintype := inferInstanceAs (Fintype (Fin 5))
  stateDecidableEq := inferInstanceAs (DecidableEq (Fin 5))
  enumeration := {
    states := ([0,1,2,3,4] : List (Fin 5))
    nodup := by decide
    complete := by decide }
  values _ := massValues
  decode _ := decodeMass
  values_correct := by
    intro role row
    change Unit at role
    cases role
    change Fin 5 at row
    change decodeMass (massValues row) = some
      (modeMass (volume.restrict (Icc (0 : ℝ) 1)) (([0,1,2,3,4] : List (Fin 5)).get row))
    fin_cases row <;> norm_num [massValues,decodeMass,interval_mass]
  kernel _ := massKernel
  kernel_correct := by
    intro role left right
    change Unit at role
    cases role
    change Fin 5 at left right
    change massKernel left right = true ↔
      modeMass (volume.restrict (Icc (0 : ℝ) 1)) (([0,1,2,3,4] : List (Fin 5)).get left) =
      modeMass (volume.restrict (Icc (0 : ℝ) 1)) (([0,1,2,3,4] : List (Fin 5)).get right)
    fin_cases left <;> fin_cases right <;> norm_num [massKernel,interval_mass]
  taskValues := massValues
  task_correct := by
    intro row
    change Fin 5 at row
    change decodeMass (massValues row) = some
      (modeMass (volume.restrict (Icc (0 : ℝ) 1)) (([0,1,2,3,4] : List (Fin 5)).get row))
    fin_cases row <;> norm_num [massValues,decodeMass,interval_mass]
  layers := ![fun _ _ => true,massKernel,massKernel]
  layers_correct := by
    intro position left right
    change Fin 3 at position
    change Fin 5 at left right
    change (![fun _ _ => true,massKernel,massKernel] position left right = true ↔
      ∀ (_role : Unit) (_h : _role ∈ (([] : List Unit) ++
        ([[()],[]].take position.val).flatten)),
        modeMass (volume.restrict (Icc (0 : ℝ) 1)) (([0,1,2,3,4] : List (Fin 5)).get left) =
        modeMass (volume.restrict (Icc (0 : ℝ) 1)) (([0,1,2,3,4] : List (Fin 5)).get right))
    fin_cases position <;> fin_cases left <;> fin_cases right <;>
      norm_num [massKernel,interval_mass,List.take,List.flatten]

/-- This finite analysis concerns mode-label mass observations in the selected
uniform-law fiber. It supplies no native reader, seam, guard or continuation. -/
def atomlessMassAnalysis : AuricFib.Contract.Application borel_iid_lower_surface where
  evidence := .typed {
    source := analysisSource
    plan := atomlessPlan
    acquisition := .finite atomlessDomain atomlessPresentation }

#print axioms atomlessPresentation

#print axioms family
end Reg.D5.S3.Estimation.DataProcessing.BorelIidStrictPeakLower
