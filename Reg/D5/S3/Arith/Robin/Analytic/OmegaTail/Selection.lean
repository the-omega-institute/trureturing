import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaTail.Selection
import Reg.Support.SingleDependentReadout

/-! Typed source families for actual prime capacities and exact finite selections. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real Finset LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open _root_.D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail.Selection

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Selection

namespace PrimeCapacity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Filter ℝ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b : ℝ}, 0 < a → a < b →
    R.readout () () (fun x : ℝ =>
      ((primeInterval (a * log x) (b * log x)).card : ℝ) / scale x) atTop (𝓝 (b - a))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (a := 1) (b := 2) (by norm_num) (by norm_num)

def family : Registration arena (type_of% @primeInterval_capacity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@primeInterval_capacity, rejected, rejected_law⟩
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
    (@primeInterval_capacity) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Selection.primeInterval_capacity.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Selection.PrimeCapacity.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Selection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PrimeCapacity

namespace ExactTotal
universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (j0 : J) (r : J → ℝ) (lambda : ℝ)
    (hr : ∀ j, 0 ≤ r j) (hr0 : 0 < r j0) (hsum : ∑ j, r j = 1),
    (∀ᶠ x : ℝ in atTop, R.readout () ()
      (∑ j, adjustedSelection j0 r lambda j x) (selectedCount lambda x)) ∧
    ∀ j, Tendsto (fun x : ℝ => (adjustedSelection j0 r lambda j x : ℝ) / scale x)
      atTop (𝓝 (r j))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (J := PUnit) PUnit.unit (fun _ => 1) 0
    (by simp) (by norm_num) (by simp)
  obtain ⟨x, hx⟩ := hh.1.exists
  exact hx

def family : Registration arena (type_of% @adjustedSelection_spec.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@adjustedSelection_spec, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), 1, ?_⟩
    intro he
    have hh : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) (Eq.refl 0)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@adjustedSelection_spec.{u}) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Selection.adjustedSelection_spec.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Selection.ExactTotal.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Selection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end ExactTotal

namespace CapacityFit
universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (j0 : J) (r d : J → ℝ) (lambda : ℝ) (P : J → ℝ → ℕ)
    (hr : ∀ j, 0 ≤ r j) (hr0 : 0 < r j0) (hsum : ∑ j, r j = 1)
    (hroom : ∀ j, r j < d j)
    (hP : ∀ j, Tendsto (fun x : ℝ => (P j x : ℝ) / scale x) atTop (𝓝 (d j))),
    ∀ᶠ x : ℝ in atTop, ∀ j, R.readout () () (adjustedSelection j0 r lambda j x) (P j x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hP : Tendsto (fun x : ℝ => (⌊2 * scale x⌋₊ : ℝ) / scale x) atTop (𝓝 2) :=
    (tendsto_nat_floor_mul_div_atTop (by norm_num : (0 : ℝ) ≤ 2)).comp scale_tendsto
  have hh := h (J := PUnit) PUnit.unit (fun _ => 1) (fun _ => 2) 0
    (fun _ x => ⌊2 * scale x⌋₊) (by simp) (by norm_num) (by simp)
    (by simp) (fun _ => hP)
  obtain ⟨x, hx⟩ := hh.exists
  exact hx PUnit.unit

def family : Registration arena (type_of% @adjustedSelection_fits.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@adjustedSelection_fits, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), 1, ?_⟩
    intro he
    have hh : (1 : ℕ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@adjustedSelection_fits.{u}) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Selection.adjustedSelection_fits.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Selection.CapacityFit.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Selection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end CapacityFit

namespace ProductBudget
universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (j0 : J) (r b : J → ℝ) (lambda : ℝ)
    (hr : ∀ j, 0 ≤ r j) (hr0 : 0 < r j0) (hsum : ∑ j, r j = 1)
    (hb : ∀ j, 0 < b j) (hslack : lambda + ∑ j, r j * log (b j) < 0),
    ∀ᶠ x : ℝ in atTop, R.readout () ()
      (∑ j, (adjustedSelection j0 r lambda j x : ℝ) * log (b j * log x)) (log x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (J := PUnit) PUnit.unit (fun _ => 1) (fun _ => exp (-1)) 0
    (by simp) (by norm_num) (by simp) (fun _ => exp_pos _) (by simp)
  obtain ⟨x, hx⟩ := hh.exists
  exact hx

def family : Registration arena (type_of% @adjustedSelection_budget.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@adjustedSelection_budget, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hh : (1 : ℝ) < 1 := Eq.mp (congrFun he 1) (by norm_num : (0 : ℝ) < 1)
    exact (lt_irrefl _ hh)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@adjustedSelection_budget.{u}) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Selection.adjustedSelection_budget.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Selection.ProductBudget.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Selection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end ProductBudget

namespace LogarithmicPrefactor

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Filter ℝ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (fun x : ℝ => log (log x) / scale x) atTop (𝓝 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  exact id

def family : Registration arena (type_of% @loglog_div_scale) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@loglog_div_scale, rejected, rejected_law⟩
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
    (@loglog_div_scale) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Selection.loglog_div_scale.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Selection.LogarithmicPrefactor.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Selection
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

end LogarithmicPrefactor

namespace IntervalCard

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b : ℝ} (hab : a ≤ b),
    R.readout () () ((primeInterval a b).card : ℝ) (primeCount b - primeCount a)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (a := 0) (b := 0) le_rfl

def family : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.Analytic.OmegaTail.Selection.primeInterval_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.Analytic.OmegaTail.Selection.primeInterval_card, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.Robin.Analytic.OmegaTail.Selection.primeInterval_card) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Selection.primeInterval_card.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Selection.IntervalCard.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Selection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end IntervalCard

end Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Selection
