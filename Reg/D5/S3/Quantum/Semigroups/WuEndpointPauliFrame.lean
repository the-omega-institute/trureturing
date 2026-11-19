import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuEndpointPauliFrame

/-! Source-bound readouts for the Pauli overlap estimates. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace
open scoped Matrix
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (Pauli)
open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation (letterPhase letterProduct)
open Matrix
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.WuRankOneEndpointFloor

namespace Reg.D5.S3.Quantum.Semigroups.WuEndpointPauliFrame

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) (Eq.mp (congrFun h 0) (le_refl 0))

namespace FrameOverlap

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (u v : EuclideanSpace ℂ Mode),
    R.readout () () (‖⟪u, v⟫_ℂ‖ ^ 2 + ∑ j : Fin 4, ‖⟪u, (endpointU j).toEuclideanLin v⟫_ℂ‖ ^ 2)
      (2 * ‖u‖ ^ 2 * ‖v‖ ^ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0

def family : Registration arena (type_of% @pauli_frame_overlap_le_two) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pauli_frame_overlap_le_two, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pauli_frame_overlap_le_two) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointPauliFrame.pauli_frame_overlap_le_two.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointPauliFrame.FrameOverlap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointPauliFrame
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

end FrameOverlap

namespace TailOverlap

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (u v : EuclideanSpace ℂ Mode),
    R.readout () () (‖⟪u, endpointVolume.toEuclideanLin v⟫_ℂ‖ ^ 2 +
      ∑ j : Fin 4, ‖⟪u, (endpointTriple j).toEuclideanLin v⟫_ℂ‖ ^ 2)
      (2 * ‖u‖ ^ 2 * ‖v‖ ^ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0

def family : Registration arena (type_of% @pauli_tail_overlap_le_two) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pauli_tail_overlap_le_two, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pauli_tail_overlap_le_two) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointPauliFrame.pauli_tail_overlap_le_two.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointPauliFrame.TailOverlap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointPauliFrame
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

end TailOverlap


namespace GenericOverlap

universe u v

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} {J : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype J]
    (T : J → E →ₗ[ℂ] E) (hsym : ∀ j, (T j).IsSymmetric)
    (hsq : ∀ j x, T j (T j x) = x)
    (hanti : ∀ i j, i ≠ j → ∀ x, T i (T j x) = -(T j (T i x))) (u v : E),
    R.readout () () (‖⟪u, v⟫_ℂ‖ ^ 2 + ∑ j, ‖⟪u, T j v⟫_ℂ‖ ^ 2)
      (2 * ‖u‖ ^ 2 * ‖v‖ ^ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (E := EuclideanSpace ℂ (ULift.{u} Empty)) (J := ULift.{v} Empty)
    (fun j => nomatch j.down) (fun j => nomatch j.down)
    (fun j => nomatch j.down) (fun i => nomatch i.down) 0 0

def family : Registration arena (type_of% @WuEndpointPauliFrame.overlap_le.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@WuEndpointPauliFrame.overlap_le.{u, v}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@WuEndpointPauliFrame.overlap_le.{u, v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointPauliFrame.overlap_le.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointPauliFrame.GenericOverlap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointPauliFrame
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end GenericOverlap
namespace PauliEqualities

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => TwoMode)
    (fun _ => TwoMode → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (one_ne_zero : (1 : TwoMode) ≠ 0) (Eq.mp (congrFun h 0) rfl)

namespace WordProduct

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ p q r s : Pauli,
    R.readout () () (pauliWord p q * pauliWord r s)
      ((letterPhase p r * letterPhase q s) • pauliWord (letterProduct p r) (letterProduct q s))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h .I .I .I .I

def family : Registration arena (type_of% @pauliWord_mul) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pauliWord_mul, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pauliWord_mul) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointPauliFrame.pauliWord_mul.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointPauliFrame.PauliEqualities.WordProduct.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointPauliFrame
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end WordProduct


namespace GeneratorSquare

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ j : Fin 4, R.readout () () (endpointU j * endpointU j) 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0

def family : Registration arena (type_of% @endpointU_sq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@endpointU_sq, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@endpointU_sq) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointPauliFrame.endpointU_sq.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointPauliFrame.PauliEqualities.GeneratorSquare.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointPauliFrame
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

end GeneratorSquare


namespace Anticommutation

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (i j : Fin 4), i ≠ j → R.readout () () (endpointU i * endpointU j) (-(endpointU j * endpointU i))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 1 (by decide)

def family : Registration arena (type_of% @endpointU_anticommute) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@endpointU_anticommute, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@endpointU_anticommute) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointPauliFrame.endpointU_anticommute.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointPauliFrame.PauliEqualities.Anticommutation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointPauliFrame
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

end Anticommutation


namespace GeneratorConjugation

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (j k : Fin 4), R.readout () () (endpointU j * endpointGamma k * (endpointU j)ᴴ)
      (if j = k then -endpointGamma k else endpointGamma k)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0

def family : Registration arena (type_of% @endpointU_conj_gamma) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@endpointU_conj_gamma, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@endpointU_conj_gamma) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointPauliFrame.endpointU_conj_gamma.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointPauliFrame.PauliEqualities.GeneratorConjugation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointPauliFrame
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

end GeneratorConjugation

end PauliEqualities

namespace HermitianGeneratorObservation

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 4)
    (fun _ => TwoMode)

private def actual : Realization signature :=
  realize signature (fun _ _ x => endpointU x) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => Complex.I • (1 : TwoMode)) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  change endpointU 0 = endpointU 1 at h
  have hs := endpointU_anticommute 0 1 (by decide)
  rw [← h, endpointU_sq 0] at hs
  have he := congrArg (fun A : TwoMode => (A (0, 0) (0, 0)).re) hs
  norm_num [Matrix.one_apply] at he

namespace Source

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ j : Fin 4, (R.readout () () j).IsHermitian

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 0).apply (0, 0) (0, 0)
  have hi := congrArg Complex.im he
  norm_num [rejected, realize, Matrix.one_apply, Complex.star_def] at hi

def family : Registration arena (type_of% @endpointU_hermitian) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@endpointU_hermitian, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@endpointU_hermitian) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointPauliFrame.endpointU_hermitian.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointPauliFrame.HermitianGeneratorObservation.Source.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => endpointU x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointPauliFrame
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Source

end HermitianGeneratorObservation

end Reg.D5.S3.Quantum.Semigroups.WuEndpointPauliFrame
