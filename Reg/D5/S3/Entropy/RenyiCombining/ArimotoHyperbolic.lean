import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic
open LeanInformationAudit

namespace Reg.D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic
noncomputable section
set_option autoImplicit false

namespace strictMonoOn_elasticity
abbrev signature := Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ n r => elasticity n r) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ r => -r) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℝ} (hn : (-1 < n ∧ n < 0) ∨ (0 < n ∧ n ≤ 1 / 2)), StrictMonoOn (R.readout () n) (Set.Ioi 0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (n := 1 / 2) (Or.inr ⟨by norm_num, by norm_num⟩) (a := 1) (b := 2)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at he
def family : Registration arena (type_of% (@_root_.D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic.strictMonoOn_elasticity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic.strictMonoOn_elasticity, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    have hp : 0 < elasticity 1 1 := by
      unfold elasticity
      exact div_pos (mul_pos (mul_pos (by norm_num) (Real.sinh_pos_iff.mpr (by norm_num)))
        (sq_pos_of_pos (Real.cosh_pos 1)))
        (mul_pos (Real.sinh_pos_iff.mpr (by norm_num)) (Real.cosh_pos _))
    change elasticity 1 0 ≠ elasticity 1 1
    simpa [elasticity] using hp.ne

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic.strictMonoOn_elasticity) (Realization signature) Unit Unit where
  unitName := `D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic.strictMonoOn_elasticity.__information_unit
  realizationName := `Reg.D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic.strictMonoOn_elasticity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n r => elasticity n r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end strictMonoOn_elasticity
end
end Reg.D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic
