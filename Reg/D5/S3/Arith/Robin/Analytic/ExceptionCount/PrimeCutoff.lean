import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.ExceptionCount.PrimeCutoff
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open _root_.D5.S3.Arith.Robin.Analytic.ExceptionCount.PrimeCutoff

namespace Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.PrimeCutoff

namespace CutoffTop

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Filter ℝ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () cutoff atTop atTop

private theorem rejected_law : ¬ arena.Law rejected := by
  exact id

def family : Registration arena (type_of% @cutoff_top) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cutoff_top, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun x : ℝ => x), (fun _ : ℝ => (0 : ℝ)), ?_⟩
    intro he
    have hEq := congrFun (congrFun he atTop) atTop
    change Tendsto (fun x : ℝ => x) atTop atTop =
      Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop at hEq
    have hId : Tendsto (fun x : ℝ => x) atTop atTop := tendsto_id
    have hh : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop := Eq.mp hEq hId
    exact not_tendsto_const_atTop (0 : ℝ) atTop hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cutoff_top) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.ExceptionCount.PrimeCutoff.cutoff_top.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.PrimeCutoff.CutoffTop.family
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
    owner := `D5.S3.Arith.Robin.Analytic.ExceptionCount.PrimeCutoff
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

end CutoffTop

namespace EnoughPrimes

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ᶠ t : ℝ in atTop, R.readout () () (exp t / t) (primeCount (cutoff t))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨t, ht⟩ := h.exists
  exact ht

def family : Registration arena (type_of% @enough_primes) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@enough_primes, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@enough_primes) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.ExceptionCount.PrimeCutoff.enough_primes.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.PrimeCutoff.EnoughPrimes.family
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
    owner := `D5.S3.Arith.Robin.Analytic.ExceptionCount.PrimeCutoff
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end EnoughPrimes

namespace SecondOrder

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Filter ℝ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (fun P : ℝ => log P * (log P * primeCount P / P - 1)) atTop (𝓝 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  exact id

def family : Registration arena (type_of% @second_order_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@second_order_count, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun x : ℝ => x), (fun _ : ℝ => (0 : ℝ)), ?_⟩
    intro he
    have hEq := congrFun (congrFun he atTop) atTop
    change Tendsto (fun x : ℝ => x) atTop atTop =
      Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop at hEq
    have hId : Tendsto (fun x : ℝ => x) atTop atTop := tendsto_id
    have hh : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop := Eq.mp hEq hId
    exact not_tendsto_const_atTop (0 : ℝ) atTop hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@second_order_count) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.ExceptionCount.PrimeCutoff.second_order_count.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.PrimeCutoff.SecondOrder.family
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
    owner := `D5.S3.Arith.Robin.Analytic.ExceptionCount.PrimeCutoff
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

end SecondOrder

end Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.PrimeCutoff
