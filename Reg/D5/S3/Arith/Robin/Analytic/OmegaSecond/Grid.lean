import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid

namespace Bounds

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ G : Mesh,
    R.readout () () G.cost (π ^ 2 / 6 + 2 * G.step * log 2) ∧
    π ^ 2 / 3 - 2 * (G.U + 2) * exp (-G.U) - 2 * G.step * log 2 ≤ G.mass
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h ⟨1, 1, by norm_num, by norm_num⟩).1
def family : Registration arena (type_of% @grid_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@grid_bounds, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@grid_bounds) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid.grid_bounds.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid.Bounds.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Bounds

namespace ExistsGrid

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {η ρ : ℝ}, 0 < η → 0 < ρ → ∃ G : Mesh,
    R.readout () () G.cost ((π ^ 2 / 6) * (1 + η / 2)) ∧ π ^ 2 / 3 - ρ ≤ G.mass
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨G, hG, _⟩ := h (η := 1) (ρ := 1) (by norm_num) (by norm_num)
  exact hG
def family : Registration arena (type_of% @exists_good_grid) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_good_grid, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_good_grid) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid.exists_good_grid.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid.ExistsGrid.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ExistsGrid

namespace StepPositive
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ G : Mesh, R.readout () () 0 G.step
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h ⟨1,1,by norm_num,by norm_num⟩
def family : Registration arena (type_of% @step_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@step_pos, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) < 1 := Eq.mp (congrFun he (1 : ℝ)) (by norm_num : (0 : ℝ) < 1)
    exact lt_irrefl _ hh
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@step_pos) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid.step_pos.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid.StepPositive.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end StepPositive

namespace NodeStep
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (G : Mesh) (i : ℕ), R.readout () () (G.node (i+1) - G.node i) G.step
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h ⟨1,1,by norm_num,by norm_num⟩ 0
def family : Registration arena (type_of% @node_step) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@node_step, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he (0 : ℝ)) (rfl : (0 : ℝ) = 0)
    norm_num at hh
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@node_step) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid.node_step.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid.NodeStep.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end NodeStep

namespace NodeEnd
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ G : Mesh, R.readout () () (G.node G.n) G.U
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h ⟨1,1,by norm_num,by norm_num⟩
def family : Registration arena (type_of% @node_end) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@node_end, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he (0 : ℝ)) (rfl : (0 : ℝ) = 0)
    norm_num at hh
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@node_end) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid.node_end.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid.NodeEnd.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end NodeEnd

namespace NodeZero
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ G : Mesh, R.readout () () (G.node 0) 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h ⟨1,1,by norm_num,by norm_num⟩
def family : Registration arena (type_of% @node_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@node_zero, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he (0 : ℝ)) (rfl : (0 : ℝ) = 0)
    norm_num at hh
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@node_zero) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid.node_zero.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid.NodeZero.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end NodeZero

end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid
