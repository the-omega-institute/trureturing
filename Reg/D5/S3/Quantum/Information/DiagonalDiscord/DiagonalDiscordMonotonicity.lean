import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity
import Reg.D5.S3.Quantum.Information.PartialTraceMutualInformation
import Reg.Support.UniverseSingleReadout
import D5.S3.Quantum.Measurement.Auric.CoordinatePinchingEntropy

/-! Source-bound audit of the entropy readout in the pinching gain identity. -/

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

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] {k : ℕ}
    (p : CompletePVM n k) (ρ : DensityState n),
    finiteTraceLogRelativeEntropy ρ (pinch p ρ) =
      vonNeumannEntropy (pinch p ρ) - R.readout () ⟨n, inferInstance, inferInstance⟩ ρ

private theorem bridge :
    (type_of% @finiteTraceLogRelativeEntropy_pinch.{u}) ↔ arena.{u}.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let p := coordinatePVM (fun _ : ULift.{u} Unit => (0 : Fin 1))
  let ρ : DensityState (ULift.{u} Unit) := singletonDensity
  have he : finiteTraceLogRelativeEntropy ρ (pinch p ρ) =
      vonNeumannEntropy (pinch p ρ) - (vonNeumannEntropy ρ + 1) := h p ρ
  rw [finiteTraceLogRelativeEntropy_pinch p ρ] at he
  linarith

def source_registration :
    Registration arena.{u} (type_of% @finiteTraceLogRelativeEntropy_pinch.{u}) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @finiteTraceLogRelativeEntropy_pinch.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@finiteTraceLogRelativeEntropy_pinch.{u}) (Realization signature.{u})
      (type_of% @DensityState.{u}) Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity.entropyGain
  realizationName := `Reg.D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p ρ => @vonNeumannEntropy p.1 p.2.1 p.2.2 ρ)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

namespace BasisGainAudit

open Matrix
open scoped BigOperators Kronecker Matrix
open _root_.D5.S3.Observer.Conditioning (unreadState unreadState_idempotent)
open _root_.D5.S3.Quantum.Measurement.Auric.CoordinatePinchingEntropy (pure_entropy)
open _root_.JointRecordDecoding (pureState)
open _root_.D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open Reg.D5.S3.Quantum.Information.PartialTraceMutualInformation.EntropySpectral
  (diagonalDensity diagonalEntropy)

universe v

private abbrev Params :=
  Σ a : Type u, Σ b : Type v, Σ fa : Fintype a, Σ da : DecidableEq a,
    Σ _ : Fintype b, Σ _ : DecidableEq b, @Matrix.unitaryGroup a da fa ℂ _ _

private abbrev gainSignature : Signature :=
  Reg.Support.UniverseSingleReadout.signature Params.{u,v}
    (fun ⟨a, b, fa, da, fb, db, _⟩ => @DensityState (a × b) (@instFintypeProd _ _ fa fb)
      (@instDecidableEqProd _ _ da db)) (fun _ => ℝ)

private def gainActual : Realization gainSignature.{u,v} :=
  realize gainSignature (fun _ ⟨a, b, fa, da, fb, db, U⟩ ρ => @basisGain a b fa da fb db ρ U)
    (fun e => nomatch e)

private def gainRejected : Realization gainSignature.{u,v} :=
  realize gainSignature (fun _ ⟨a, b, fa, da, fb, db, U⟩ ρ => @basisGain a b fa da fb db ρ U - 1)
    (fun e => nomatch e)

private abbrev Qubit := ULift.{u} (Fin 2)
private abbrev Scalar := ULift.{v} Unit

private theorem sumQubit {R : Type*} [AddCommMonoid R] (f : Qubit.{u} × Scalar.{v} → R) :
    ∑ i, f i = f (⟨0⟩, ⟨()⟩) + f (⟨1⟩, ⟨()⟩) := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  rw [← (Equiv.ulift.symm : Fin 2 ≃ Qubit.{u}).sum_comp]
  exact Fin.sum_univ_two _

private def flatVector : Qubit.{u} × Scalar.{v} → ℂ := fun _ => (Real.sqrt (1/2) : ℝ)

private theorem flatSquare : (Real.sqrt (1/2) : ℂ) * star (Real.sqrt (1/2) : ℂ) = 1/2 := by
  rw [Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (show (0 : ℝ) ≤ 1/2 by norm_num)]
  norm_num

private theorem flatNorm : star (flatVector.{u,v}) ⬝ᵥ flatVector.{u,v} = 1 := by
  simp only [dotProduct, Pi.star_apply, flatVector, sumQubit, mul_comm (star _) _, flatSquare]
  norm_num

private def uniform : DensityState (Qubit.{u} × Scalar.{v}) :=
  diagonalDensity (fun _ => (1/2 : ℝ)) (fun _ => by norm_num) (by rw [sumQubit]; norm_num)

private theorem localProj_one (j : Fin (Fintype.card Qubit.{u})) :
    (localPVM (b := Scalar.{v}) (1 : Matrix.unitaryGroup Qubit.{u} ℂ)).proj j =
      (coordinatePVM (fun i : Qubit.{u} × Scalar.{v} =>
        Fintype.equivFin Qubit.{u} i.1)).proj j := by
  change
    (Unitary.conjStarAlgAut ℂ _ (1 : Matrix.unitaryGroup Qubit.{u} ℂ)
      ((coordinatePVM (Fintype.equivFin Qubit.{u})).proj j)) ⊗ₖ
        (1 : Matrix Scalar.{v} Scalar.{v} ℂ) = _
  rw [Unitary.conjStarAlgAut_apply]
  simp only [OneMemClass.coe_one, star_one, one_mul, mul_one]
  ext ⟨i,k⟩ ⟨l,m⟩
  have hkm : k = m := Subsingleton.elim _ _
  subst m
  by_cases hil : i = l
  · subst l
    simp [coordinatePVM]
  · simp [coordinatePVM, Matrix.diagonal_apply_ne _ hil,
      Matrix.diagonal_apply_ne _ (show (i,k) ≠ (l,k) from fun h => hil (congrArg Prod.fst h))]

private theorem flatPinch :
    pinch (localPVM (1 : Matrix.unitaryGroup Qubit.{u} ℂ))
      (pureState flatVector.{u,v} flatNorm) = uniform.{u,v} := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change CStarMatrix.ofMatrix.symm
    ((pinchingChannel (localPVM (1 : Matrix.unitaryGroup Qubit.{u} ℂ))).toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (rankOneDensity flatVector.{u,v}))) =
    Matrix.diagonal (fun _ => (↑(1/2 : ℝ) : ℂ))
  rw [pinchingChannel_apply]
  simp only [unreadState, localProj_one, coordinatePVM, Matrix.mul_diagonal]
  ext i j
  simp only [Matrix.sum_apply, Matrix.of_apply, rankOneDensity, Matrix.vecMulVec_apply,
    Pi.star_apply, flatVector, flatSquare]
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq, Finset.sum_eq_single (Fintype.equivFin Qubit.{u} i.1)]
    · simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, if_pos rfl,
        one_mul, mul_one, Matrix.vecMulVec_apply, Pi.star_apply, flatVector, flatSquare]
      norm_num
    · intro k _ hk
      simp [Ne.symm hk]
    · simp
  · have hfst : Fintype.equivFin Qubit.{u} i.1 ≠ Fintype.equivFin Qubit.{u} j.1 := by
      intro h
      exact hij (Prod.ext ((Fintype.equivFin Qubit.{u}).injective h) (Subsingleton.elim _ _))
    rw [Matrix.diagonal_apply_ne _ hij]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hi : Fintype.equivFin Qubit.{u} i.1 = k
    · have hj : Fintype.equivFin Qubit.{u} j.1 ≠ k := fun h => hfst (hi.trans h.symm)
      simp [hj]
    · simp [hi]

private theorem uniformPinch :
    pinch (localPVM (1 : Matrix.unitaryGroup Qubit.{u} ℂ)) uniform.{u,v} = uniform := by
  let p := localPVM (b := Scalar.{v}) (1 : Matrix.unitaryGroup Qubit.{u} ℂ)
  let ρ := pureState flatVector.{u,v} flatNorm
  rw [← flatPinch]
  change pinch p (pinch p ρ) = pinch p ρ
  have action (σ : DensityState (Qubit.{u} × Scalar.{v})) :
      CStarMatrix.ofMatrix.symm (pinch p σ).1 =
        unreadState p.proj (CStarMatrix.ofMatrix.symm σ.1) := pinchingChannel_apply p _
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  rw [action (pinch p ρ), action ρ]
  exact unreadState_idempotent
    ⟨fun j => by simpa only [Matrix.star_eq_conjTranspose] using (p.hermitian j).eq,
      p.idempotent, p.orthogonal, p.complete⟩ _

private theorem gainDependence : ObservationalDependence gainSignature.{u,v} gainActual := by
  intro _
  let p : Params.{u,v} :=
    ⟨Qubit, Scalar, inferInstance, inferInstance, inferInstance, inferInstance, 1⟩
  refine ⟨p, pureState flatVector flatNorm, uniform, ?_⟩
  change basisGain (pureState flatVector flatNorm) 1 ≠ basisGain uniform 1
  rw [basisGain, basisGain, flatPinch, uniformPinch, pure_entropy, sub_zero, sub_self]
  have hp := Real.binEntropy_pos (p := (1/2 : ℝ)) (by norm_num) (by norm_num)
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub] at hp
  unfold uniform
  rw [diagonalEntropy, sumQubit]
  norm_num at hp ⊢
  exact ne_of_gt hp

private abbrev MeasuredSingleton := ULift.{u} Unit

private theorem singletonState {n : Type*} [Fintype n] [DecidableEq n]
    [Subsingleton n] [Inhabited n] (ρ σ : DensityState n) : ρ = σ := by
  let : Unique n := ⟨inferInstance, fun i => Subsingleton.elim i default⟩
  apply Subtype.ext
  ext i j
  have hρ := ρ.trace_eq_one
  have hσ := σ.trace_eq_one
  change (∑ k, ρ.val k k) = 1 at hρ
  change (∑ k, σ.val k k) = 1 at hσ
  rw [Fintype.sum_unique] at hρ hσ
  rw [Unique.eq_default i, Unique.eq_default j, hρ, hσ]

private def singletonInput : DensityState (MeasuredSingleton.{u} × Scalar.{v}) :=
  diagonalDensity (fun _ => 1) (fun _ => by norm_num) (by simp)

private def singletonChannel : QuantumChannel MeasuredSingleton.{u} MeasuredSingleton.{u} :=
  pinchingChannel (coordinatePVM (fun _ => (0 : Fin 1)))

private theorem singletonCQ : PreservesCQ (localChannel (b := Scalar.{v}) singletonChannel.{u}) :=
  fun _ _ => ⟨1, singletonState _ _⟩

private theorem singletonGain (ρ : DensityState (MeasuredSingleton.{u} × Scalar.{v}))
    (U : Matrix.unitaryGroup MeasuredSingleton.{u} ℂ) : basisGain ρ U = 0 := by
  unfold basisGain
  rw [singletonState (pinch (localPVM U) ρ) ρ, sub_self]

private abbrev attainedArena : Arena where
  signature := gainSignature.{u,v}
  Law r := ∀ {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] [Nonempty b] (Λ : QuantumChannel a a) (_hCQ : PreservesCQ (localChannel (b := b) Λ))
    (ρ : DensityState (a × b)),
    let R := (localChannel (b := b) Λ).mapState ρ
    ∃ U V : Matrix.unitaryGroup a ℂ,
      Eligible ρ U ∧ Eligible R V ∧
      IsMinOn (basisGain ρ) {W | Eligible ρ W} U ∧
      IsMinOn (basisGain R) {W | Eligible R W} V ∧
      basisGain R V ≤ r.readout () ⟨a, b, inferInstance, inferInstance, inferInstance, inferInstance, U⟩ ρ

private theorem attainedRejected : ¬ attainedArena.{u,v}.Law gainRejected := by
  intro h
  obtain ⟨U, V, _, _, _, _, hbound⟩ := h singletonChannel singletonCQ singletonInput
  change basisGain _ V ≤ basisGain singletonInput U - 1 at hbound
  rw [singletonGain, singletonGain] at hbound
  linarith

def attainedSource :
    Registration attainedArena.{u,v} (type_of% @diagonalDiscord_localChannel_mono_attained.{u,v}) where
  actual := gainActual
  bridge := Iff.rfl
  variation := ⟨@diagonalDiscord_localChannel_mono_attained, gainRejected, attainedRejected⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ attainedRejected
  dependence := gainDependence

private abbrev transferArena : Arena where
  signature := gainSignature.{u,v}
  Law r := ∀ {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] [Nonempty b] (Λ : QuantumChannel a a) (_hCQ : PreservesCQ (localChannel (b := b) Λ))
    (ρ : DensityState (a × b)) (U : Matrix.unitaryGroup a ℂ) (_hU : Eligible ρ U),
    let T := localChannel (b := b) Λ
    let R := T.mapState ρ
    let τ := T.mapState (pinch (localPVM U) ρ)
    ∃ V : Matrix.unitaryGroup a ℂ,
      Eligible R V ∧ pinch (localPVM V) τ = τ ∧
      SupportContained (pinch (localPVM V) R) τ ∧
      0 ≤ finiteTraceLogRelativeEntropy (pinch (localPVM V) R) τ ∧
      basisGain R V + finiteTraceLogRelativeEntropy (pinch (localPVM V) R) τ ≤
        r.readout () ⟨a, b, inferInstance, inferInstance, inferInstance, inferInstance, U⟩ ρ

private theorem transferRejected : ¬ transferArena.{u,v}.Law gainRejected := by
  intro h
  have hU : Eligible singletonInput.{u,v} 1 :=
    fun i j hij => False.elim (hij (Subsingleton.elim i j))
  obtain ⟨V, _, _, _, hres, hbound⟩ := h singletonChannel singletonCQ singletonInput 1 hU
  change basisGain _ V + _ ≤ basisGain singletonInput 1 - 1 at hbound
  rw [singletonGain, singletonGain] at hbound
  linarith

def transferSource :
    Registration transferArena.{u,v} (type_of% @pointwise_transfer.{u,v}) where
  actual := gainActual
  bridge := Iff.rfl
  variation := ⟨@pointwise_transfer, gainRejected, transferRejected⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ transferRejected
  dependence := gainDependence


def attainedRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@diagonalDiscord_localChannel_mono_attained.{u,v}) (Realization gainSignature.{u,v})
      (type_of% @DensityState.{max u v}) Unit := {
  unitName := .str ``attainedSource "unit"
  realizationName := ``attainedSource
  realizationSource := none
  generated := false
  arena := .source ⟨attainedArena.{u,v}⟩
  objectArena := .source ⟨attainedArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source attainedArena.{u,v} ⟨attainedSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gainSignature
    (fun _ ⟨a, b, fa, da, fb, db, U⟩ ρ => @basisGain a b fa da fb db ρ U)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity
    definition := none
    coordinates := #[0, 1, 12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
          "body", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def transferRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@pointwise_transfer.{u,v}) (Realization gainSignature.{u,v})
      (type_of% @DensityState.{max u v}) Unit := {
  unitName := .str ``transferSource "unit"
  realizationName := ``transferSource
  realizationSource := none
  generated := false
  arena := .source ⟨transferArena.{u,v}⟩
  objectArena := .source ⟨transferArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source transferArena.{u,v} ⟨transferSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gainSignature
    (fun _ ⟨a, b, fa, da, fb, db, U⟩ ρ => @basisGain a b fa da fb db ρ U)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity
    definition := none
    coordinates := #[0, 1, 11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
          "body", "body", "body", "body", "body", "body", "arg", "body",
          "arg", "arg", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end BasisGainAudit

end
end Reg.D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity
