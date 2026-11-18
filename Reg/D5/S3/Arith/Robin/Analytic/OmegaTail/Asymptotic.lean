import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaTail.Asymptotic
import Reg.Support.SingleDependentReadout

/-! The exact limit statement as a dependent readout of convergence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail (C0)
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail.Asymptotic

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Asymptotic

namespace ZeroRate

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Filter ℝ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () ()
    (fun x : ℝ => log (tailCount 0 x : ℝ) / scale x) atTop (𝓝 C0)

private theorem rejected_law : ¬ arena.Law rejected := by
  exact id

def family : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.Analytic.OmegaTail.Asymptotic.result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.Analytic.OmegaTail.Asymptotic.result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun _ : ℝ => 0), (fun _ : ℝ => 1), ?_⟩
    intro he
    have he' := congrFun (congrFun he atTop) (𝓝 (0 : ℝ))
    have hh : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 0) :=
      Eq.mp he' tendsto_const_nhds
    have hzero : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hh
    norm_num at hzero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.Robin.Analytic.OmegaTail.Asymptotic.result) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Asymptotic.result.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Asymptotic.ZeroRate.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Asymptotic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ZeroRate

end Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Asymptotic
