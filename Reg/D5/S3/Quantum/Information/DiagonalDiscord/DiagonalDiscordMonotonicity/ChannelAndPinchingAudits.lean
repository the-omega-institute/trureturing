import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity
import Reg.D5.S3.Quantum.Information.PartialTraceMutualInformation
import Reg.Support.UniverseSingleReadout
import D5.S3.Quantum.Measurement.Auric.CoordinatePinchingEntropy

/-! Source-bound audits for pinching support, the reduced marginal, and local channel action. -/

namespace Reg.D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open _root_.D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open _root_.D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity
open _root_.D5.S3.Quantum.Measurement.Auric.CoordinatePinching
open _root_.D5.S3.Quantum.Measurement.Auric.ProjectiveTree
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

universe u

open Reg.D5.S3.Quantum.Information.PartialTraceMutualInformation.EntropySpectral
  (signature actual rejected singletonDensity dependence)

namespace PinchingSupportAudit

open Matrix
open scoped BigOperators Matrix
open _root_.D5.S3.Observer.Conditioning (unreadState)
open Reg.D5.S3.Quantum.Information.PartialTraceMutualInformation.EntropySpectral
  (diagonalDensity)

private abbrev Params :=
  Σ n : Type u, Σ _ : Fintype n, Σ _ : DecidableEq n, Σ k : ℕ, CompletePVM n k

private abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature Params.{u}
    (fun p => @DensityState p.1 p.2.1 p.2.2.1)
    (fun p => @DensityState p.1 p.2.1 p.2.2.1)

private def readPinch : ∀ (_ : Unit) (p : Params.{u}),
    signature.State p → signature.Output () p :=
  fun _ p ρ => @pinch p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 ρ

private def actual : Realization signature.{u} :=
  realize signature readPinch (fun e => nomatch e)

private def basisDensity {n : Type u} [Fintype n] [DecidableEq n] (i : n) :
    DensityState n :=
  diagonalDensity (fun j => if j = i then 1 else 0)
    (by intro j; split <;> norm_num) (by simp)

private theorem basisDensity_matrix {n : Type u} [Fintype n] [DecidableEq n] (i : n) :
    CStarMatrix.ofMatrix.symm (basisDensity i).1 =
      Matrix.diagonal (fun j => if j = i then 1 else 0) := by
  ext j k
  change (Matrix.diagonal (fun l => ((if l = i then 1 else 0 : ℝ) : ℂ))) j k = _
  by_cases h : j = k
  · subst k
    by_cases hj : j = i <;> simp [hj]
  · simp [Matrix.diagonal_apply_ne _ h]

private abbrev Qubit := ULift.{u} (Fin 2)

private def oneBlock {n : Type u} [Fintype n] [DecidableEq n] : CompletePVM n 1 :=
  coordinatePVM (fun _ => (0 : Fin 1))

private theorem oneBlock_fixes {n : Type u} [Fintype n] [DecidableEq n]
    (ρ : DensityState n) : pinch oneBlock ρ = ρ := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change CStarMatrix.ofMatrix.symm ((pinchingChannel oneBlock).toCompletelyPositiveMap
    (CStarMatrix.ofMatrix (CStarMatrix.ofMatrix.symm ρ.1))) = _
  rw [pinchingChannel_apply]
  have hp (j : Fin 1) : (oneBlock (n := n)).proj j = 1 := by
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp [oneBlock, coordinatePVM, Matrix.diagonal_one]
  simp [unreadState, hp]

open scoped Classical in
private def rejected : Realization signature.{u} :=
  realize signature (fun _ p ρ =>
    if h : p.1 = Qubit.{u} then
      @basisDensity p.1 p.2.1 p.2.2.1 (h.symm ▸ (⟨0⟩ : Qubit.{u}))
    else ρ) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {n : Type u} [Fintype n] [DecidableEq n] {k : ℕ}
    (p : CompletePVM n k) (ρ : DensityState n),
    SupportContained ρ (r.readout () ⟨n, inferInstance, inferInstance, k, p⟩ ρ)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let zeroIndex : Qubit.{u} := ⟨0⟩
  let oneIndex : Qubit.{u} := ⟨1⟩
  have hne : oneIndex ≠ zeroIndex := by decide
  have hp : SupportContained (basisDensity oneIndex) (basisDensity zeroIndex) := by
    simpa [rejected, realize] using h oneBlock (basisDensity oneIndex)
  let v : Qubit.{u} → ℂ := fun i => if i = oneIndex then 1 else 0
  have hz : CStarMatrix.ofMatrix.symm (basisDensity zeroIndex).1 *ᵥ v = 0 := by
    rw [basisDensity_matrix]
    funext j
    rw [Matrix.mulVec_diagonal]
    by_cases hj : j = oneIndex
    · subst j
      simp [v, hne]
    · simp [v, hj]
  have hbad : CStarMatrix.ofMatrix.symm (basisDensity oneIndex).1 *ᵥ v = 0 := hp hz
  rw [basisDensity_matrix] at hbad
  have hc := congrFun hbad oneIndex
  simp [Matrix.mulVec_diagonal, v] at hc

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro _
  let zeroIndex : Qubit.{u} := ⟨0⟩
  let oneIndex : Qubit.{u} := ⟨1⟩
  have hne : oneIndex ≠ zeroIndex := by decide
  refine ⟨⟨Qubit, inferInstance, inferInstance, 1, oneBlock⟩,
    basisDensity zeroIndex, basisDensity oneIndex, ?_⟩
  change pinch oneBlock (basisDensity zeroIndex) ≠ pinch oneBlock (basisDensity oneIndex)
  rw [oneBlock_fixes, oneBlock_fixes]
  intro h
  have he := congrArg (fun ρ : DensityState Qubit.{u} => CStarMatrix.ofMatrix.symm ρ.1) h
  rw [basisDensity_matrix, basisDensity_matrix] at he
  have hc := congrFun (congrFun he oneIndex) oneIndex
  change (Matrix.diagonal (fun j => if j = zeroIndex then (1 : ℂ) else 0)) oneIndex oneIndex =
    (Matrix.diagonal (fun j => if j = oneIndex then (1 : ℂ) else 0)) oneIndex oneIndex at hc
  simp [hne] at hc

def source :
    Registration arena.{u} (type_of% @supportContained_pinch.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@supportContained_pinch, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@supportContained_pinch.{u}) (Realization signature.{u})
      (type_of% @DensityState.{u}) Unit := {
  unitName := .str ``source "unit"
  realizationName := ``source
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature readPinch (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity
    definition := none
    coordinates := #[0, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end PinchingSupportAudit


namespace MarginalAudit

open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
  (marginalRight marginalRight_productState productState)
open scoped BigOperators Matrix
open PinchingSupportAudit (basisDensity basisDensity_matrix oneBlock oneBlock_fixes)

universe v

private abbrev Params :=
  Σ a : Type u, Σ b : Type v, Σ fa : Fintype a, Σ da : DecidableEq a,
    Σ _ : Fintype b, Σ _ : DecidableEq b, @QuantumChannel a a fa da fa da

private abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature Params.{u,v}
    (fun p => @DensityState (p.1 × p.2.1)
      (@instFintypeProd _ _ p.2.2.1 p.2.2.2.2.1)
      (@instDecidableEqProd _ _ p.2.2.2.1 p.2.2.2.2.2.1))
    (fun p => @DensityState p.1 p.2.2.1 p.2.2.2.1)

private def readMarginal : ∀ (_ : Unit) (p : Params.{u,v}),
    signature.State p → signature.Output () p :=
  fun _ p ρ => @QuantumChannel.mapState p.1 p.1 p.2.2.1 p.2.2.2.1 p.2.2.1 p.2.2.2.1
    p.2.2.2.2.2.2 (@marginalRight p.1 p.2.1 p.2.2.1 p.2.2.2.1
      p.2.2.2.2.1 p.2.2.2.2.2.1 ρ)

private def actual : Realization signature.{u,v} :=
  realize signature readMarginal (fun e => nomatch e)

private abbrev Qubit := ULift.{u} (Fin 2)
private abbrev Scalar := ULift.{v} Unit

private def testState (i : Qubit.{u}) : DensityState (Qubit.{u} × Scalar.{v}) :=
  productState (basisDensity i) singletonDensity

private abbrev testParams : Params.{u,v} :=
  ⟨Qubit, Scalar, inferInstance, inferInstance, inferInstance, inferInstance,
    pinchingChannel oneBlock⟩

private theorem read_testState (i : Qubit.{u}) :
    readMarginal () testParams.{u,v} (testState i) = basisDensity i := by
  have hm : marginalRight (testState.{u,v} i) = basisDensity i :=
    marginalRight_productState (basisDensity i) singletonDensity.{v}
  exact (congrArg (pinchingChannel oneBlock).mapState hm).trans (oneBlock_fixes _)

private theorem basisDensity_ne :
    basisDensity (⟨0⟩ : Qubit.{u}) ≠ basisDensity (⟨1⟩ : Qubit.{u}) := by
  intro h
  have he := congrArg (fun ρ : DensityState Qubit.{u} => CStarMatrix.ofMatrix.symm ρ.1) h
  rw [basisDensity_matrix, basisDensity_matrix] at he
  let i : Qubit.{u} := ⟨1⟩
  have hne : i ≠ (⟨0⟩ : Qubit.{u}) := by decide
  have hc := congrFun (congrFun he i) i
  change (Matrix.diagonal (fun j => if j = (⟨0⟩ : Qubit.{u}) then (1 : ℂ) else 0)) i i =
    (Matrix.diagonal (fun j => if j = i then (1 : ℂ) else 0)) i i at hc
  simp [hne] at hc

open scoped Classical in
private def rejected : Realization signature.{u,v} :=
  realize signature (fun _ p ρ =>
    if h : p.1 = Qubit.{u} then
      @basisDensity p.1 p.2.2.1 p.2.2.2.1 (h.symm ▸ (⟨1⟩ : Qubit.{u}))
    else readMarginal () p ρ) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] (Λ : QuantumChannel a a) (ρ : DensityState (a × b)),
    marginalRight ((localChannel Λ).mapState ρ) =
      r.readout () ⟨a, b, inferInstance, inferInstance, inferInstance, inferInstance, Λ⟩ ρ

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let ρ : DensityState (Qubit.{u} × Scalar.{v}) := testState ⟨0⟩
  have he : marginalRight ((localChannel (pinchingChannel oneBlock)).mapState ρ) =
      basisDensity ⟨1⟩ := by
    simpa [rejected, realize] using h (pinchingChannel oneBlock) ρ
  rw [marginalRight_localChannel] at he
  exact basisDensity_ne ((read_testState.{u,v} ⟨0⟩).symm.trans he)

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro _
  refine ⟨testParams, testState ⟨0⟩, testState ⟨1⟩, ?_⟩
  change readMarginal () testParams.{u,v} (testState ⟨0⟩) ≠
    readMarginal () testParams.{u,v} (testState ⟨1⟩)
  rw [read_testState, read_testState]
  exact basisDensity_ne

def source :
    Registration arena.{u,v} (type_of% @marginalRight_localChannel.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@marginalRight_localChannel, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@marginalRight_localChannel.{u,v}) (Realization signature.{u,v})
      (type_of% @DensityState.{max u v}) Unit := {
  unitName := .str ``source "unit"
  realizationName := ``source
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature readMarginal (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity
    definition := none
    coordinates := #[0, 1, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end MarginalAudit


namespace LocalActionAudit

open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder Kronecker Matrix MatrixOrder
open _root_.D5.S3.Quantum.Divergence.CanonicalChannelDPI (actual_kraus_representation)

universe v

private abbrev Params :=
  Σ a : Type u, Σ b : Type v, Σ _ : Fintype a, Σ _ : DecidableEq a,
    Σ _ : Fintype b, Σ _ : DecidableEq b, Matrix (a × b) (a × b) ℂ

private abbrev Mat (p : Params.{u,v}) := Matrix (p.1 × p.2.1) (p.1 × p.2.1) ℂ
private abbrev CMat (p : Params.{u,v}) := CStarMatrix (p.1 × p.2.1) (p.1 × p.2.1) ℂ

private abbrev cpMap (p : Params.{u,v}) :=
  letI : Fintype p.1 := p.2.2.1
  letI : Fintype p.2.1 := p.2.2.2.2.1
  CompletelyPositiveMap (CMat p) (CMat p)

private abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature Params.{u,v} cpMap Mat

private def readAction : ∀ (_ : Unit) (p : Params.{u,v}), cpMap p → Mat p :=
  fun _ p T =>
    letI : Fintype p.1 := p.2.2.1
    letI : Fintype p.2.1 := p.2.2.2.2.1
    CStarMatrix.ofMatrix.symm (T (CStarMatrix.ofMatrix p.2.2.2.2.2.2))

private def actual : Realization signature.{u,v} :=
  realize signature readAction (fun e => nomatch e)

private def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      [Nonempty a] (Λ : QuantumChannel a a) (X : Matrix (a × b) (a × b) ℂ),
    let M := actual_kraus_representation Λ
    r.readout () ⟨a, b, inferInstance, inferInstance, inferInstance, inferInstance, X⟩
      (localChannel (b := b) Λ).toCompletelyPositiveMap =
      ∑ j, (M.kraus j ⊗ₖ (1 : Matrix b b ℂ)) * X *
        (M.kraus j ⊗ₖ (1 : Matrix b b ℂ))ᴴ

private abbrev A := ULift.{u} Unit
private abbrev B := ULift.{v} Unit

private def testChannel : QuantumChannel (A.{u} × B.{v}) (A.{u} × B.{v}) :=
  localChannel (pinchingChannel (PinchingSupportAudit.oneBlock (n := A.{u})))

private abbrev testParams : Params.{u,v} :=
  ⟨A, B, inferInstance, inferInstance, inferInstance, inferInstance, 1⟩

private theorem testAction_ne_zero :
    readAction () testParams.{u,v} testChannel.{u,v}.toCompletelyPositiveMap ≠ 0 := by
  intro h
  have ht := testChannel.{u,v}.trace_preserving (CStarMatrix.ofMatrix (1 : Mat testParams.{u,v}))
  change Matrix.trace (readAction () testParams.{u,v} testChannel.{u,v}.toCompletelyPositiveMap) =
    Matrix.trace (1 : Mat testParams.{u,v}) at ht
  rw [h] at ht
  simpa [Matrix.trace] using ht

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let Λ := pinchingChannel (PinchingSupportAudit.oneBlock (n := A.{u}))
  let X : Mat testParams.{u,v} := 1
  have he := h Λ X
  exact testAction_ne_zero ((localChannel_apply Λ X).trans he.symm)

private def zeroCP :
    CompletelyPositiveMap (CStarMatrix (A.{u} × B.{v}) (A.{u} × B.{v}) ℂ)
      (CStarMatrix (A.{u} × B.{v}) (A.{u} × B.{v}) ℂ) where
  toLinearMap := 0
  map_cstarMatrix_nonneg' := by
    intro k _ _
    exact le_refl (0 : CStarMatrix (Fin k) (Fin k) (CStarMatrix (A × B) (A × B) ℂ))

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro _
  refine ⟨testParams, testChannel.toCompletelyPositiveMap, zeroCP, ?_⟩
  change readAction () testParams.{u,v} testChannel.toCompletelyPositiveMap ≠
    readAction () testParams.{u,v} zeroCP
  have hz : readAction () testParams.{u,v} zeroCP = 0 := rfl
  rw [hz]
  exact testAction_ne_zero

def source :
    Registration arena.{u,v} (type_of% @localChannel_apply.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@localChannel_apply, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@localChannel_apply.{u,v}) (Realization signature.{u,v})
      (type_of% @QuantumChannel.{max u v, max u v}) Unit := {
  unitName := .str ``source "unit"
  realizationName := ``source
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature readAction (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity
    definition := none
    coordinates := #[0, 1, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end LocalActionAudit


end
end Reg.D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity
