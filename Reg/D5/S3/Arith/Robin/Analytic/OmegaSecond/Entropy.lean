import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy

namespace LogChooseGeBinEntropy

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m a : ℕ), a ≤ m →
    R.readout () () ((m : ℝ) * binEntropy ((a : ℝ) / m) - log ((m : ℝ) + 1))
      (log (m.choose a : ℝ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 le_rfl

def family : Registration arena (type_of% @log_choose_ge_binEntropy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@log_choose_ge_binEntropy, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@log_choose_ge_binEntropy) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.log_choose_ge_binEntropy.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.LogChooseGeBinEntropy.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
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

end LogChooseGeBinEntropy

end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
