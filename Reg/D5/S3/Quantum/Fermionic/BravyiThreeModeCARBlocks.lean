import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks
import Reg.Support.SingleDependentReadout

/-! Source-bound registration of the exact CAR channel block reduction. -/

namespace Reg.D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks

open _root_.D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks
open _root_.D5.S3.Quantum.Fermionic.BravyiThreeModeDeterminantOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => SpinMatrix)
    (fun _ => SpinMatrix)

private def actual : Realization signature :=
  realize signature (fun _ lam L => channel lam L) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ lam L => channel lam L + 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (lam c p q : ℝ), c ^ 2 + p ^ 2 + q ^ 2 = 1 →
    signedBasis * R.readout () lam (normalInput c p q) * signedBasisᴴ =
      (determinantBlocks (chiral lam c p q) (complement lam c q)).map Complex.ofReal

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hn : (1 : ℝ) ^ 2 + 0 ^ 2 + 0 ^ 2 = 1 := by norm_num
  have hbad := h 0 1 0 0 hn
  dsimp only [rejected, realize] at hbad
  rw [mul_add, add_mul, mul_one, signedBasis_isUnitary, channel_normal_blocks 0 1 0 0 hn] at hbad
  exact one_ne_zero (add_left_cancel (hbad.trans (add_zero _).symm))

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨1, 0, 1, ?_⟩
  change channel 1 0 ≠ channel 1 1
  rw [channel_one, channel_one]
  exact zero_ne_one

def family : Registration arena (type_of% (@channel_normal_blocks)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@channel_normal_blocks, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@channel_normal_blocks) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks.channel_normal_blocks.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ lam L => channel lam L) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks
