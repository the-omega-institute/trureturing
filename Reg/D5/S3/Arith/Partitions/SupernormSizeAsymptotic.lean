import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Partitions.SupernormSizeAsymptotic
import Reg.Support.SingleDependentReadout

/-! The complete size-ensemble limit, observing its reciprocal supernorm weight. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Real LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Partitions.SupernormSizeAsymptotic

namespace Reg.D5.S3.Arith.Partitions.SupernormSizeAsymptotic

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ n => Wsize n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := Tendsto (fun n : ℕ => (n : ℝ) * R.readout () () n) atTop
    (𝓝 (exp eulerMascheroniConstant))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
      (𝓝 (exp eulerMascheroniConstant)) := by
    simpa only [arena, rejected, realize, mul_zero] using h
  have he : (0 : ℝ) = exp eulerMascheroniConstant :=
    tendsto_nhds_unique tendsto_const_nhds hz
  exact (exp_ne_zero _) he.symm

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize, Wsize, supernorm, Nat.nth_prime_zero_eq_two]

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Partitions.SupernormSizeAsymptotic.result) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Partitions.SupernormSizeAsymptotic.result,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Partitions.SupernormSizeAsymptotic.result)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Partitions.SupernormSizeAsymptotic.result.audit
  realizationName := `Reg.D5.S3.Arith.Partitions.SupernormSizeAsymptotic.family
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
    owner := `D5.S3.Arith.Partitions.SupernormSizeAsymptotic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "arg", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Partitions.SupernormSizeAsymptotic
