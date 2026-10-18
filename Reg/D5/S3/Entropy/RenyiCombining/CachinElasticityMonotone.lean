import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone
open LeanInformationAudit

namespace Reg.D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone
noncomputable section
set_option autoImplicit false

namespace T_hasDerivAt
abbrev signature := Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ n r => -2 * n * r ^ (n - 1) / (1 + r ^ n) ^ (2 : ℕ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ r => (0 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n r : ℝ) (hr : 0 < r), HasDerivAt (T n) (R.readout () n r) r
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h 1 1 (by norm_num)
  have he := (T_hasDerivAt 1 1 (by norm_num)).unique hzero
  norm_num [rejected, realize] at he
def family : Registration arena (type_of% (@_root_.D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone.T_hasDerivAt)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone.T_hasDerivAt, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := by
    intro i
    refine ⟨1, 1, 2, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone.T_hasDerivAt) (Realization signature) Unit Unit where
  unitName := `D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone.T_hasDerivAt.__information_unit
  realizationName := `Reg.D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone.T_hasDerivAt.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n r => -2 * n * r ^ (n - 1) / (1 + r ^ n) ^ (2 : ℕ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end T_hasDerivAt

namespace A_eq
abbrev signature := Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ n r => A n r) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ r => (1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n r : ℝ) (hr : 0 < r), R.readout () n r =
    n * r ^ (n - 1) * (1 - r ^ (2 : ℕ)) / ((1 - r ^ n) * (1 + r ^ n))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0 1 (by norm_num)
  norm_num [rejected, realize] at he
def family : Registration arena (type_of% (@_root_.D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone.A_eq)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone.A_eq, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    norm_num [actual, realize, A]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone.A_eq) (Realization signature) Unit Unit where
  unitName := `D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone.A_eq.__information_unit
  realizationName := `Reg.D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone.A_eq.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n r => A n r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end A_eq

namespace monotoneOn_F
abbrev signature := Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ n r => F n r) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ r => -r) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℝ) (hn : 1 ≤ n), MonotoneOn (R.readout () n) (Set.Ioo 0 1)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 1 (by norm_num) (a := 1 / 4) (b := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at he
def family : Registration arena (type_of% (@_root_.D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone.monotoneOn_F)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone.monotoneOn_F, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := by
    intro i
    refine ⟨1, 0, 1 / 2, ?_⟩
    norm_num [actual, realize, F, A, B, T, Real.rpow_two]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone.monotoneOn_F) (Realization signature) Unit Unit where
  unitName := `D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone.monotoneOn_F.__information_unit
  realizationName := `Reg.D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone.monotoneOn_F.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n r => F n r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone
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
end monotoneOn_F

namespace antitoneOn_F_neg
abbrev signature := Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ n r => F n r) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ r => r) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℝ) (hn₀ : -1 < n) (hn₁ : n < 0),
    AntitoneOn (R.readout () n) (Set.Ioo 0 1)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (-1 / 2) (by norm_num) (by norm_num) (a := 1 / 4) (b := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at he
def family : Registration arena (type_of% (@_root_.D5.S3.Entropy.RenyiCombining.CachinNegativeBranch.antitoneOn_F_neg)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.RenyiCombining.CachinNegativeBranch.antitoneOn_F_neg, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := by
    intro i
    refine ⟨1, 0, 1 / 2, ?_⟩
    norm_num [actual, realize, F, A, B, T, Real.rpow_two]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.RenyiCombining.CachinNegativeBranch.antitoneOn_F_neg) (Realization signature) Unit Unit where
  unitName := `D5.S3.Entropy.RenyiCombining.CachinNegativeBranch.antitoneOn_F_neg.__information_unit
  realizationName := `Reg.D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone.antitoneOn_F_neg.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n r => F n r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end antitoneOn_F_neg

end
end Reg.D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone
