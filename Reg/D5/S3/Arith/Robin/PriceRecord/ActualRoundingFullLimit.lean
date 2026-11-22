import D5.S3.Arith.Robin.PriceRecord.ActualRoundingFullLimit
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualRoundingFullLimit

open Real Filter Finset
open scoped Topology
open LeanInformationAudit
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualRoundingFullLimit (actual_prime_gap_limit)
open _root_.D5.S3.Arith.Robin.PriceRecord.BoundaryPrimePrice (integerGap)
open _root_.D5.S3.Arith.Robin.ActualRobinClockCovariance (g)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature
  (fun _ _ L => sqrt L * log L * (∑ p ∈ Nat.primesLE ⌊L⌋₊, integerGap (p : ℝ) (g L)))
  (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := Tendsto (fun L : ℝ => R.readout () () L) atTop (𝓝 (2 * sqrt 2))

private theorem zero_not_limit :
    ¬ Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 (2 * sqrt 2)) := by
  intro h
  have hpos : 0 < 2 * sqrt 2 := by positivity
  exact hpos.ne (tendsto_nhds_unique tendsto_const_nhds h)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, ?_⟩
  by_contra! hconstant
  have hzero : ∀ L : ℝ, actual.readout () () L = 0 := by
    intro L
    rw [← hconstant L]
    simp [actual, realize]
  exact zero_not_limit (actual_prime_gap_limit.congr' (Eventually.of_forall hzero))

def family : Registration arena (type_of% (@actual_prime_gap_limit)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_prime_gap_limit, rejected, zero_not_limit⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected zero_not_limit
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_prime_gap_limit) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.ActualRoundingFullLimit.actual_prime_gap_limit.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.ActualRoundingFullLimit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ L => sqrt L * log L * (∑ p ∈ Nat.primesLE ⌊L⌋₊,
      integerGap (p : ℝ) (g L))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.ActualRoundingFullLimit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualRoundingFullLimit
