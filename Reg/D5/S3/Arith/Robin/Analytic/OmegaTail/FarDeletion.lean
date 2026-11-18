import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaTail.FarDeletion
import Reg.Support.SingleDependentReadout

/-! Dependent readouts for the centered excess and the uniform retained-prime budget. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Real Finset LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail.FarDeletion
open _root_.D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel (primeInterval)

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.FarDeletion

namespace CenteredReserve

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Filter ℝ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    R.readout () () (fun P : ℝ => primeExcess P / (P / log P ^ 3)) atTop (𝓝 2) ∧
    (∀ P : ℝ, 1 < P → centeredCount P = ⌊centeredThreshold P⌋₊ + 1 ∧
      0 < (centeredCount P : ℝ) - centeredThreshold P ∧
        (centeredCount P : ℝ) - centeredThreshold P ≤ 1) ∧
    (∀ᶠ P : ℝ in atTop, 0 ≤ primeExcess P ∧ (deletionCount P : ℝ) = primeExcess P) ∧
    Tendsto (fun P : ℝ => continuousReserve P / (P / log P ^ 2)) atTop (𝓝 2) ∧
    Tendsto (fun P : ℝ => roundedReserve P / (P / log P ^ 2)) atTop (𝓝 2) ∧
    Tendsto (fun P : ℝ => safeReserve P / (P / log P ^ 2)) atTop (𝓝 2)

private theorem rejected_law : ¬ arena.Law rejected := fun h => h.1

def family : Registration arena (type_of% @centered_reserve) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨centered_reserve, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun _ : ℝ => 0), (fun _ : ℝ => 1), ?_⟩
    intro he
    have hh : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 0) :=
      Eq.mp (congrFun (congrFun he atTop) (𝓝 (0 : ℝ))) tendsto_const_nhds
    have hzero : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hh
    norm_num at hzero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@centered_reserve) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.FarDeletion.centered_reserve.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.FarDeletion.CenteredReserve.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.FarDeletion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CenteredReserve

namespace RetainedBudget

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law A :=
    ∀ᶠ P : ℝ in atTop,
      (∀ p : ℕ, p ∈ primeInterval (P / 2) (3 / 4 * P) ↔
        P / 2 < (p : ℝ) ∧ (p : ℝ) ≤ 3 / 4 * P ∧ p.Prime) ∧
      (∃ R ⊆ primeInterval (P / 2) (3 / 4 * P), R.card = deletionCount P) ∧
      ∀ R ⊆ primeInterval (P / 2) (3 / 4 * P), R.card = deletionCount P →
        (Nat.primesLE ⌊P⌋₊ \ R).card = centeredCount P ∧
          A.readout () () (∑ p ∈ Nat.primesLE ⌊P⌋₊ \ R, log (p : ℝ)) (P - safeReserve P)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨P, _, ⟨R, hR, hsize⟩, hbudget⟩ := h.exists
  exact (hbudget R hR hsize).2

def family : Registration arena (type_of% @far_deletion) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨far_deletion, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@far_deletion) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.FarDeletion.far_deletion.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.FarDeletion.RetainedBudget.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.FarDeletion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "arg", "arg", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RetainedBudget

end Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.FarDeletion
