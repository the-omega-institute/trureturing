import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.ConditionalExpansion.DirectBellKrausRecovery

/-! Source-bound observations for the Bell-kernel construction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix LeanInformationAudit
open scoped CStarAlgebra ComplexOrder MatrixOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.ConditionalExpansion
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceLeft)
open _root_.D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralSupport)
open UnitaryReconstruction.LiuWildChoiObstruction (bell outer)

namespace Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.DirectBellKrausRecovery

open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)

namespace SuccessWeight

universe u v w z

private abbrev observation := signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)

private def actual : Realization observation :=
  realize observation (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization observation :=
  realize observation (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := observation
  Law R := ∀ {A : Type u} {B : Type v} {I : Type w} {J : Type z}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype I] [Fintype J]
    [Nonempty A]
    (K : I → Matrix B A ℂ) (v : J → A × B → ℂ)
    (_hkernel : (∑ j, outer (v j)) =
      1 - spectralSupport (amplifyKraus K (1 - outer (bell A)))),
    let P := outer (bell A)
    let B₀ := amplifyKraus K (1 - P)
    let X₀ := amplifyKraus K P
    let Q := ∑ j, outer (v j)
    let operators := bellRecoveryKraus v
    let d : ℂ := Fintype.card A
    let p := (Q * X₀).trace / d ^ 2
    B₀.PosSemidef ∧ IsStarProjection Q ∧
    (∀ x : A × B → ℂ, B₀ *ᵥ x = 0 ↔ Q *ᵥ x = x) ∧
    (∑ j, (operators j)ᴴ * operators j) = d⁻¹ • partialTraceLeft Q ∧
    (∑ j, (operators j)ᴴ * operators j) ≤ (1 : Matrix B B ℂ) ∧
    (MatrixMap.of_kraus operators operators).IsCompletelyPositive ∧ R.readout () () 0 p ∧
    ∀ X : Matrix A A ℂ, MatrixMap.of_kraus operators operators (MatrixMap.of_kraus K K X) = p • X

private theorem rejected_law : ¬ arena.{u,v,w,z}.Law rejected := by
  intro h
  let A := ULift.{u} Unit
  let B := ULift.{v} Empty
  let K : ULift.{w} Unit → Matrix B A ℂ := fun _ => 0
  let vectors : ULift.{z} Unit → A × B → ℂ := fun _ _ => 0
  have hkernel : (∑ j, outer (vectors j)) =
      1 - spectralSupport (amplifyKraus K (1 - outer (bell A))) := by
    ext ⟨_, b⟩
    exact b.down.elim
  obtain ⟨_, _, _, _, _, _, hfalse, _⟩ := h K vectors hkernel
  exact hfalse

def family : Registration arena.{u,v,w,z} (type_of% @direct_bell_kernel_recovery.{u,v,w,z}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@direct_bell_kernel_recovery.{u,v,w,z}, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have he := congrFun h 0
    norm_num [actual, realize, Complex.le_def] at he

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@direct_bell_kernel_recovery.{u,v,w,z}) (Realization observation) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.ConditionalExpansion.direct_bell_kernel_recovery.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.DirectBellKrausRecovery.SuccessWeight.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,z}⟩
  objectArena := .source ⟨arena.{u,v,w,z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w,z} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize observation (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ConditionalExpansion.DirectBellKrausRecovery
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end SuccessWeight

end Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.DirectBellKrausRecovery
