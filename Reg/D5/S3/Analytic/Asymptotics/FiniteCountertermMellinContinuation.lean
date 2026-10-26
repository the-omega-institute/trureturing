import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Asymptotics.FiniteCountertermMellinContinuation
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Analytic.Asymptotics.FiniteCountertermMellinContinuation

open Set MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Asymptotics.FiniteCountertermMellinContinuation
open LeanInformationAudit

noncomputable section
universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℂ)
    (fun _ => ℂ → ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => HasMellin f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} {u : Finset ι} {f : ι → ℝ → ℂ}
    {value : ι → ℂ} {s : ℂ}, (∀ i ∈ u, HasMellin (f i) s (value i)) →
      R.readout () () (fun t => ∑ i ∈ u, f i t) s (∑ i ∈ u, value i)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h (ULift.{u} Empty) ∅ (fun _ _ => 0) (fun _ => 0) 1 (by simp)
  exact hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let indicator : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator (fun _ => 1)
  refine ⟨(), (fun _ => 0), indicator, ?_⟩
  intro he
  have hzero : HasMellin (fun _ : ℝ => (0 : ℂ)) 1 0 := by
    simpa only [Finset.sum_empty] using
      (hasMellin_finset_sum (ι := Empty) (u := ∅) (f := fun _ _ => 0)
        (value := fun _ => 0) (s := 1) (by simp))
  have hindicator : HasMellin indicator 1 0 :=
    Eq.mp (congrFun (congrFun he 1) 0) hzero
  have hone : HasMellin indicator 1 1 := by
    simpa [indicator] using
      (hasMellin_one_Ioc (s := (1 : ℂ)) (by norm_num))
  exact zero_ne_one (hindicator.2.symm.trans hone.2)

def family : Registration arena.{u} (type_of% (@hasMellin_finset_sum.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hasMellin_finset_sum.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasMellin_finset_sum.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Asymptotics.FiniteCountertermMellinContinuation.hasMellin_finset_sum.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Asymptotics.FiniteCountertermMellinContinuation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => HasMellin f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Asymptotics.FiniteCountertermMellinContinuation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Analytic.Asymptotics.FiniteCountertermMellinContinuation
