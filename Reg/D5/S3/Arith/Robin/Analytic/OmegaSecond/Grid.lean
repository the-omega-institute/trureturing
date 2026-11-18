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

end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid
