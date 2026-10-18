import D5.S3.Estimation.DataProcessing.IidStrictPeakSource
import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.AuricFib
import Reg.Support.DependentFamily

noncomputable section
namespace Reg.D5.S3.Estimation.DataProcessing.IidStrictPeakSource
open _root_.D5.S3.Estimation.DataProcessing.IidStrictPeakSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
universe u

/-- All finite ordered alphabets and all their signed mass functions remain parameters. -/
structure Parameters where
  Alphabet : Type u
  mass : Alphabet → ℝ

/-- The source mass instrument precedes the independent product and peak classifier. -/
abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.Alphabet
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ q s => q.mass s) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature (fun _ _ _ => (0 : ℝ))
  (fun e => nomatch e)

def observedLaw (r : Realization signature.{u}) {A : Type u} [Fintype A] [LinearOrder A]
    (p : A → ℝ) (s : Fin 5) : ℝ := modeLaw (r.readout () ⟨A,p⟩) s

def fullLaw (r : Realization signature.{u}) : Prop :=
  ∀ {A : Type u} [Fintype A] [LinearOrder A]
    (p : A → ℝ) (_hp : ∀ a, 0 ≤ p a) (_hs : ∑ a, p a = 1),
    (∀ a b c d e : A, ¬ (peak a b c ∧ peak b c d) ∧
      ¬ (peak c d e ∧ peak b c d)) ∧
    (∀ s, 0 ≤ observedLaw r p s) ∧ (∑ s, observedLaw r p s) = 1 ∧
    observedLaw r p 1 + observedLaw r p 3 = ∑ b, p b * lowerMass p b ^ 2 ∧
    observedLaw r p 2 + observedLaw r p 3 = ∑ b, p b * lowerMass p b ^ 2 ∧
    observedLaw r p 4 = ∑ b, p b * lowerMass p b ^ 2 ∧
    observedLaw r p 3 = ∑ c, p c * wingMass p c ^ 2 ∧
    (∑ c, p c * wingMass p c) = ∑ b, p b * lowerMass p b ^ 2 ∧
    observedLaw r p 0 * observedLaw r p 3 - observedLaw r p 1 * observedLaw r p 2 =
      (1 - ∑ b, p b * lowerMass p b ^ 2) *
        (∑ c, p c * wingMass p c ^ 2) - (∑ b, p b * lowerMass p b ^ 2)^2

abbrev arena : Arena where
  signature := signature.{u}
  Law := fullLaw

private theorem rejected_law : ¬ fullLaw rejected.{u} := by
  intro h
  have hnorm : (∑ a : ULift.{u} Unit, (1 : ℝ)) = 1 := by simp
  have ht := h (fun _ : ULift.{u} Unit => (1 : ℝ)) (fun _ => by norm_num) hnorm
  have hm := ht.2.2.1
  norm_num [observedLaw,rejected,realize,modeLaw,productAverage,average] at hm

theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro _
  let q : Parameters.{u} := ⟨ULift.{u} (Fin 2),fun a => if a.down = 0 then 0 else 1⟩
  refine ⟨q,⟨0⟩,⟨1⟩,?_⟩
  norm_num [actual,realize,q]

def family : Registration arena.{u} (type_of% (@iid_peak_source.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@iid_peak_source,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim _ _)).elim,rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := actual_dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.Estimation.DataProcessing.IidStrictPeakSource
  definition := none
  coordinates := #[0,3]
  readouts := #[{
    path := #["body","body","body","body","body","body","arg","fn","arg","body","arg","fn","arg"]
    stateBinder := 0
    functionOperand := true
    stateOperand := none
    booleanPredicate := false}]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@iid_peak_source.{u})
    (type_of% (realize signature.{u}
      (fun _ q s => q.mass s) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Estimation.DataProcessing.IidStrictPeakSource.iid_peak_source.__information_unit
  realizationName := `Reg.D5.S3.Estimation.DataProcessing.IidStrictPeakSource.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
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

abbrev analysisSource : Analysis.Source (@iid_peak_source.{u}) :=
  Analysis.Source.ofRegistration _ family .exact selection

/-- The same full theorem supplies a five-mode macro source. Native seam,
guard and continuation semantics are not part of strict-peak classification. -/
def analysis : AuricFib.Contract.Application (@iid_peak_source.{u}) where
  evidence := .typed {
    source := analysisSource
    plan := {task := (),initial := [],additions := [[()],[]]}
    acquisition := .unavailable "Arbitrary real five-mode source law; no native Window continuation bridge"}

#print axioms family
end Reg.D5.S3.Estimation.DataProcessing.IidStrictPeakSource
