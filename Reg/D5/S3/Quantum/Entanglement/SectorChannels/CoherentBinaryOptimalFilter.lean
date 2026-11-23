import D5.S3.Quantum.Entanglement.SectorChannels.CoherentBinaryOptimalFilter
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Tactic.NormNum

/-! Observe the largest optimal filter, not merely the optimal score; the
alternative always chooses the larger threshold and fails on actual curves. -/

set_option autoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.SectorChannels.CoherentBinaryOptimalFilter
open _root_.D5.S3.Quantum.Entanglement.SectorChannels.CoherentBinaryOptimalFilter
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => FilterCurve) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ β => largestFilter β) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ β => β.t₂) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ β : FilterCurve,
    let chosen := r.readout () () β
    0<chosen ∧ chosen<1 ∧
    ∀ t : ℝ, 0≤t → t≤1 →
      score β.q β.w t ≤ score β.q β.w chosen ∧
      (score β.q β.w t = score β.q β.w chosen ↔
        (t=β.t₁ ∧ 2*β.w≤β.q) ∨ (t=β.t₂ ∧ β.q≤2*β.w)) ∧
      (score β.q β.w t = score β.q β.w chosen → t≤chosen)

private def low : FilterCurve :=
  ⟨1/4,9/100,1/5,3/5,by norm_num,by norm_num,by norm_num,by norm_num,by norm_num,
    by norm_num,by norm_num⟩

private def high : FilterCurve :=
  ⟨1/4,16/100,2/5,4/5,by norm_num,by norm_num,by norm_num,by norm_num,by norm_num,
    by norm_num,by norm_num⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := ((h low).2.2 (1/5) (by norm_num) (by norm_num)).1
  change score low.q low.w (1/5) ≤ score low.q low.w low.t₂ at he
  norm_num [score,low,min_def] at he

private theorem actual_dependence : actual.readout () () low ≠ actual.readout () () high := by
  change largestFilter low ≠ largestFilter high
  norm_num [largestFilter,low,high]

def family : Registration arena (type_of% @largest_optimal_filter) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@largest_optimal_filter,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    exact ⟨(),low,high,actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@largest_optimal_filter) (type_of% actual) FilterCurve Unit where
  unitName := `D5.S3.Quantum.Entanglement.SectorChannels.CoherentBinaryOptimalFilter.largest_optimal_filter.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.SectorChannels.CoherentBinaryOptimalFilter.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SectorChannels.CoherentBinaryOptimalFilter
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end
end Reg.D5.S3.Quantum.Entanglement.SectorChannels.CoherentBinaryOptimalFilter
