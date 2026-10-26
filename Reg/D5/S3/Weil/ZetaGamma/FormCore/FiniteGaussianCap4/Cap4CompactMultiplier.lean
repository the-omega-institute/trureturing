import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4CompactMultiplier
import Reg.Support.SingleDependentReadout
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open _root_.FiniteGaussianCap4
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4CompactMultiplier

namespace Debit
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => compactDebit x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (5 : ℝ)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, |R.readout () () x| ≤ 4
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  norm_num [rejected, realize] at hb
def family : Registration arena (type_of% @compactDebit_abs_le_four) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨compactDebit_abs_le_four, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    change compactDebit 0 ≠ compactDebit 1
    have hpi : ¬ Real.pi < 1 := by linarith [Real.pi_gt_three]
    norm_num [compactDebit, capWeight, hpi]
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@compactDebit_abs_le_four) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4CompactMultiplier.Debit.unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4CompactMultiplier.Debit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => compactDebit x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4CompactMultiplier
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Debit
namespace Domination
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => capWeight x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (x : ℝ), 0 ≤ x → x ^ 2 / 10 - compactDebit x ≤ R.readout () () x
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 (by norm_num)
  norm_num [rejected, realize, compactDebit] at hb
def family : Registration arena (type_of% @capWeight_ge_quadratic_minus_compact) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨capWeight_ge_quadratic_minus_compact, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (6 : ℝ), ?_⟩
    change capWeight 0 ≠ capWeight 6
    have hz : capWeight 0 = 0 := by simp [capWeight, Real.pi_pos.not_gt]
    have hd : compactDebit 6 = 0 := by norm_num [compactDebit]
    have hh := capWeight_ge_quadratic_minus_compact 6 (by norm_num)
    rw [hz]
    intro he
    rw [← he, hd] at hh
    norm_num at hh
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@capWeight_ge_quadratic_minus_compact) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4CompactMultiplier.Domination.unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4CompactMultiplier.Domination.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => capWeight x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4CompactMultiplier
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Domination
end Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4CompactMultiplier
