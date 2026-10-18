import D5.S3.Estimation.DataProcessing.FiniteIidStrictPeakLower
import Reg.D5.S3.Estimation.DataProcessing.IidStrictPeakSource

noncomputable section
namespace Reg.D5.S3.Estimation.DataProcessing.FiniteIidStrictPeakLower
open _root_.D5.S3.Estimation.DataProcessing.FiniteIidStrictPeakLower
open _root_.D5.S3.Estimation.DataProcessing.IidStrictPeakSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Estimation.DataProcessing.IidStrictPeakSource
open LeanInformationAudit Set
open scoped BigOperators
universe u

def fullLaw (r : Realization signature.{u}) : Prop :=
  ∀ {A : Type u} [Fintype A] [LinearOrder A]
    (p : A → ℝ) (_hp : ∀ a, 0 ≤ p a) (_hs : ∑ a, p a = 1),
    let X := observedLaw r p 1 + observedLaw r p 3
    let D := observedLaw r p 0*observedLaw r p 3-observedLaw r p 1*observedLaw r p 2
    0 ≤ X ∧ X < 1/3 ∧
    (X = 0 ↔ ∃ i, p i = 1 ∧ ∀ j, j ≠ i → p j = 0) ∧
    (∃ s ∈ Icc (0 : ℝ) 1, s^3 = 1-3*X ∧
      s^3/45*(1-s)*(1+s+7*s^2-3*s^3-3*s^4) ≤ D+X/15 ∧
      0 ≤ s^3/45*(1-s)*(1+s+7*s^2-3*s^3-3*s^4)) ∧
    -X/15 ≤ D ∧ -1/45 < D ∧
    (D = -X/15 ↔ ∃ i, p i = 1 ∧ ∀ j, j ≠ i → p j = 0)

abbrev lowerArena : Arena where
  signature := signature.{u}
  Law := fullLaw

private theorem rejected_law : ¬ fullLaw rejected.{u} := by
  intro h
  have hnorm : (∑ a : ULift.{u} (Fin 2), (1/2 : ℝ)) = 1 := by norm_num
  have ht := h (fun _ : ULift.{u} (Fin 2) => (1/2 : ℝ)) (fun _ => by norm_num) hnorm
  have hd := ht.2.2.1
  have hx : observedLaw rejected (fun _ : ULift.{u} (Fin 2) => (1/2 : ℝ)) 1+
      observedLaw rejected (fun _ : ULift.{u} (Fin 2) => (1/2 : ℝ)) 3 = 0 := by
    simp [observedLaw,rejected,realize,modeLaw,productAverage,average]
  obtain ⟨i,hi,_⟩ := hd.mp hx
  norm_num at hi

def family : Registration lowerArena.{u} (type_of% (@finite_iid_lower_surface.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_iid_lower_surface,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim _ _)).elim,rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := actual_dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.Estimation.DataProcessing.FiniteIidStrictPeakLower
  definition := none
  coordinates := #[0,3]
  readouts := #[{
    path := #["body","body","body","body","body","body","value","fn","arg","fn","arg"]
    stateBinder := 0
    functionOperand := true
    stateOperand := none
    booleanPredicate := false}]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_iid_lower_surface.{u})
    (type_of% (realize signature.{u}
      (fun _ q s => q.mass s) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Estimation.DataProcessing.FiniteIidStrictPeakLower.finite_iid_lower_surface.__information_unit
  realizationName := `Reg.D5.S3.Estimation.DataProcessing.FiniteIidStrictPeakLower.family
  realizationSource := none
  generated := false
  arena := .source ⟨lowerArena⟩
  objectArena := .source ⟨lowerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source lowerArena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ q s => q.mass s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev analysisSource : Analysis.Source (@finite_iid_lower_surface.{u}) :=
  Analysis.Source.ofRegistration _ family .exact selection

def analysis : AuricFib.Contract.Application (@finite_iid_lower_surface.{u}) where
  evidence := .typed {
    source := analysisSource
    plan := {task := (),initial := [],additions := [[()],[]]}
    acquisition := .unavailable "The full real-mass family has no acquired native Window continuation"}

#print axioms family
end Reg.D5.S3.Estimation.DataProcessing.FiniteIidStrictPeakLower
