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

namespace sinh_cosh_sub_pos
abbrev signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {z : ℝ} (hz : 0 < R.readout () () z),
    0 < Real.sinh z * Real.cosh z - z
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h (z := 0) (by norm_num [rejected, realize])
  norm_num at hzero
def family : Registration arena (type_of%
    (@_root_.D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic.sinh_cosh_sub_pos)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic.sinh_cosh_sub_pos,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 0, 1, by simp [actual, realize]⟩
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic.sinh_cosh_sub_pos)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic.sinh_cosh_sub_pos.unit
  realizationName := `Reg.D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic.sinh_cosh_sub_pos.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "domain", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end sinh_cosh_sub_pos

namespace f_hasDerivAt
abbrev signature := Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ s r =>
    (Real.sinh (r * s) * Real.cosh (r * s) - r * s) / Real.sinh (r * s) ^ 2)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s r : ℝ} (hs : 0 < s) (hr : 0 < r),
    HasDerivAt (f s) (R.readout () s r) r
private theorem derivative_pos :
    0 < (Real.sinh (1 : ℝ) * Real.cosh 1 - 1) / Real.sinh 1 ^ 2 :=
  div_pos (_root_.D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic.sinh_cosh_sub_pos zero_lt_one)
    (sq_pos_of_pos (Real.sinh_pos_iff.mpr zero_lt_one))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h (s := 1) (r := 1) zero_lt_one zero_lt_one
  change HasDerivAt (f 1) 0 1 at hz
  have hd := _root_.D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic.f_hasDerivAt
    (s := 1) (r := 1) zero_lt_one zero_lt_one
  have heq := hz.unique hd
  norm_num only [one_mul] at heq
  exact (ne_of_gt derivative_pos) heq.symm
def family : Registration arena (type_of%
    (@_root_.D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic.f_hasDerivAt)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic.f_hasDerivAt,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    change (Real.sinh (0 * 1) * Real.cosh (0 * 1) - 0 * 1) / Real.sinh (0 * 1) ^ 2 ≠
      (Real.sinh (1 * 1) * Real.cosh (1 * 1) - 1 * 1) / Real.sinh (1 * 1) ^ 2
    simpa only [zero_mul, one_mul, Real.sinh_zero, Real.cosh_zero,
      mul_one, sub_zero, zero_pow, zero_div] using derivative_pos.ne
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic.f_hasDerivAt)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic.f_hasDerivAt.unit
  realizationName := `Reg.D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic.f_hasDerivAt.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ s r =>
    (Real.sinh (r * s) * Real.cosh (r * s) - r * s) / Real.sinh (r * s) ^ 2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end f_hasDerivAt
end
end Reg.D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic
