import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialReserve
import Reg.Support.SingleDependentReadout

/-! Dependent convergence readouts for the factorial reserve limits. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialReserve
open _root_.D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel (primeInterval)

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialReserve

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Filter ℝ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℝ => 0), (fun _ : ℝ => 1), ?_⟩
  intro he
  have h : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 0) :=
    Eq.mp (congrFun (congrFun he atTop) (𝓝 (0 : ℝ))) tendsto_const_nhds
  have hzero : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds h
  norm_num at hzero

namespace Continuous

abbrev arena : Arena where
  signature := signature
  Law O := ∀ r : ℕ,
    O.readout () () (fun P : ℝ => continuousReserve r P / (P / log P ^ r))
      atTop (𝓝 (r.factorial : ℝ))

private theorem rejected_law : ¬ arena.Law rejected := fun h => h 2

def family : Registration arena (type_of% @continuous_reserve_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨continuous_reserve_limit, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@continuous_reserve_limit) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialReserve.continuous_reserve_limit.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialReserve.Continuous.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialReserve
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Continuous

namespace Rounded

abbrev arena : Arena where
  signature := signature
  Law O := ∀ r : ℕ,
    Tendsto (fun P : ℝ => primeExcess r P / (P / log P ^ (r + 1)))
      atTop (𝓝 (r.factorial : ℝ)) ∧
    (∀ᶠ P : ℝ in atTop, cutoff r P ≤ Nat.primeCounting ⌊P⌋₊ ∧
      (deletionCount r P : ℝ) = primeExcess r P) ∧
    Tendsto (fun P : ℝ => roundedReserve r P / (P / log P ^ r))
      atTop (𝓝 (r.factorial : ℝ)) ∧
    O.readout () () (fun P : ℝ => safeReserve r P / (P / log P ^ r))
      atTop (𝓝 (r.factorial : ℝ))

private theorem rejected_law : ¬ arena.Law rejected := fun h => (h 2).2.2.2

def family : Registration arena (type_of% @factorial_reserve) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨factorial_reserve, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@factorial_reserve) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialReserve.factorial_reserve.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialReserve.Rounded.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialReserve
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Rounded

end Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialReserve
