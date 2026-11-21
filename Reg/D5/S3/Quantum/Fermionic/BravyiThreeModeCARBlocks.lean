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

namespace ChannelAtOne

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => SpinMatrix)
    (fun _ => SpinMatrix)

private def actual : Realization signature :=
  realize signature (fun _ _ L => channel 1 L) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ L : SpinMatrix, R.readout () () L = L

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact zero_ne_one (h 1)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  change channel 1 0 ≠ channel 1 1
  rw [channel_one, channel_one]
  exact zero_ne_one

def family : Registration arena (type_of% (@channel_one)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@channel_one, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@channel_one) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks.channel_one.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks.ChannelAtOne.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ L => channel 1 L) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ChannelAtOne


namespace SignedReorder

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => SpinMatrix)
    (fun _ => SpinMatrix)

private def actual : Realization signature :=
  realize signature (fun _ _ L => signedReorder L) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ L : SpinMatrix, R.readout () () L = signedBasis * L * signedBasisᴴ

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h1 := h 1
  change (0 : SpinMatrix) = signedBasis * 1 * signedBasisᴴ at h1
  rw [mul_one, signedBasis_isUnitary] at h1
  exact zero_ne_one h1

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  change signedReorder 0 ≠ signedReorder 1
  rw [signedReorder_eq, signedReorder_eq, mul_zero, zero_mul, mul_one,
    signedBasis_isUnitary]
  exact zero_ne_one

def family : Registration arena (type_of% (@signedReorder_eq)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@signedReorder_eq, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@signedReorder_eq) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks.signedReorder_eq.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks.SignedReorder.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ L => signedReorder L) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SignedReorder


namespace NormalInputTrace

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => SpinMatrix)
    (fun _ => ℂ)

private def actual : Realization signature :=
  realize signature (fun _ _ L => Matrix.trace L) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ c p q : ℝ, R.readout () () (normalInput c p q) =
    ((c ^ 2 + p ^ 2 + q ^ 2 : ℝ) : ℂ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h1 := h 1 0 0
  change (0 : ℂ) = ((1 ^ 2 + 0 ^ 2 + 0 ^ 2 : ℝ) : ℂ) at h1
  norm_num at h1

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  change Matrix.trace (0 : SpinMatrix) ≠ Matrix.trace (1 : SpinMatrix)
  norm_num [Matrix.trace_one]

def family : Registration arena (type_of% (@trace_normalInput)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@trace_normalInput, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@trace_normalInput) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks.trace_normalInput.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks.NormalInputTrace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ L => Matrix.trace L) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end NormalInputTrace


namespace GeneratorAdjoint

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => SpinMatrix)
    (fun _ => SpinMatrix)

private def actual : Realization signature :=
  realize signature (fun _ _ L => Lᴴ) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ j : Fin 6, R.readout () () (U j) = U j

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : U 0 = 0 := (h 0).symm
  have hu := U_square 0
  rw [hz, zero_mul] at hu
  exact zero_ne_one hu

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  change (0 : SpinMatrix)ᴴ ≠ (1 : SpinMatrix)ᴴ
  simpa only [Matrix.conjTranspose_zero, Matrix.conjTranspose_one] using
    (zero_ne_one : (0 : SpinMatrix) ≠ 1)

def family : Registration arena (type_of% (@U_hermitian)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@U_hermitian, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@U_hermitian) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks.U_hermitian.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks.GeneratorAdjoint.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ L => Lᴴ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end GeneratorAdjoint


namespace MajoranaAdjoint

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => SpinMatrix)
    (fun _ => SpinMatrix)

private def actual : Realization signature :=
  realize signature (fun _ _ L => Lᴴ) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ j : Fin 6, R.readout () () (majorana j) = majorana j

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : majorana 0 = 0 := (h 0).symm
  have hu := majorana_square 0
  rw [hz, zero_mul] at hu
  exact zero_ne_one hu

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  change (0 : SpinMatrix)ᴴ ≠ (1 : SpinMatrix)ᴴ
  simpa only [Matrix.conjTranspose_zero, Matrix.conjTranspose_one] using
    (zero_ne_one : (0 : SpinMatrix) ≠ 1)

def family : Registration arena (type_of% (@majorana_hermitian)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@majorana_hermitian, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@majorana_hermitian) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks.majorana_hermitian.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks.MajoranaAdjoint.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ L => Lᴴ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MajoranaAdjoint


namespace GeneratorSquare

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 6) (fun _ => SpinMatrix)
    (fun _ => SpinMatrix)

private def actual : Realization signature :=
  realize signature (fun _ j L => L * U j) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ j : Fin 6, R.readout () j (U j) = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact zero_ne_one (h 0)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨0, 0, U 0, ?_⟩
  change 0 * U 0 ≠ U 0 * U 0
  rw [zero_mul, U_square]
  exact zero_ne_one

def family : Registration arena (type_of% (@U_square)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@U_square, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@U_square) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks.U_square.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks.GeneratorSquare.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ j L => L * U j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end GeneratorSquare


namespace MajoranaSquare

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 6) (fun _ => SpinMatrix)
    (fun _ => SpinMatrix)

private def actual : Realization signature :=
  realize signature (fun _ j L => L * majorana j) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ j : Fin 6, R.readout () j (majorana j) = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact zero_ne_one (h 0)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨0, 0, majorana 0, ?_⟩
  change 0 * majorana 0 ≠ majorana 0 * majorana 0
  rw [zero_mul, majorana_square]
  exact zero_ne_one

def family : Registration arena (type_of% (@majorana_square)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@majorana_square, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@majorana_square) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks.majorana_square.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks.MajoranaSquare.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ j L => L * majorana j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MajoranaSquare

namespace SignedBasisUnitarity

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => SpinMatrix)
    (fun _ => SpinMatrix)

private def actual : Realization signature :=
  realize signature (fun _ _ L => L * signedBasisᴴ) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () signedBasis = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact zero_ne_one h

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, signedBasis, ?_⟩
  change 0 * signedBasisᴴ ≠ signedBasis * signedBasisᴴ
  rw [zero_mul, signedBasis_isUnitary]
  exact zero_ne_one

def family : Registration arena (type_of% (@signedBasis_isUnitary)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@signedBasis_isUnitary, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@signedBasis_isUnitary) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks.signedBasis_isUnitary.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks.SignedBasisUnitarity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ L => L * signedBasisᴴ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SignedBasisUnitarity


namespace WordUnitarity

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 64) (fun _ => SpinMatrix)
    (fun _ => SpinMatrix)

private def actual : Realization signature :=
  realize signature (fun _ m L => L * (word m)ᴴ) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : Fin 64, R.readout () m (word m) = 1 ∧ (word m)ᴴ * word m = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact zero_ne_one (h 0).1

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨0, 0, word 0, ?_⟩
  change 0 * (word 0)ᴴ ≠ word 0 * (word 0)ᴴ
  rw [zero_mul, (word_unitary 0).1]
  exact zero_ne_one

def family : Registration arena (type_of% (@word_unitary)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@word_unitary, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@word_unitary) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks.word_unitary.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks.WordUnitarity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m L => L * (word m)ᴴ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end WordUnitarity


namespace ChannelAtZero

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => SpinMatrix)
    (fun _ => SpinMatrix)

private def actual : Realization signature :=
  realize signature (fun _ _ L => channel 0 L) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (c p q : ℝ), c ^ 2 + p ^ 2 + q ^ 2 = 1 →
    R.readout () () (normalInput c p q) = (1 / 8 : ℂ) • (1 : SpinMatrix)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 : (0 : SpinMatrix) = (1 / 8 : ℂ) • (1 : SpinMatrix) :=
    h 1 0 0 (by norm_num)
  have he := congrFun (congrFun h0 0) 0
  norm_num [Matrix.one_apply] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, normalInput 1 0 0, ?_⟩
  change channel 0 0 ≠ channel 0 (normalInput 1 0 0)
  have hz : channel 0 0 = 0 := by simp [channel, conjugateWord]
  rw [hz, channel_normal_zero 1 0 0 (by norm_num)]
  intro h
  have he := congrFun (congrFun h 0) 0
  norm_num [Matrix.one_apply] at he

def family : Registration arena (type_of% (@channel_normal_zero)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@channel_normal_zero, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@channel_normal_zero) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks.channel_normal_zero.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks.ChannelAtZero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ L => channel 0 L) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ChannelAtZero


end

end Reg.D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks
