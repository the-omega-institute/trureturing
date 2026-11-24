import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity
import Reg.D5.S3.Quantum.Information.PartialTraceMutualInformation
import Reg.Support.UniverseSingleReadout
import D5.S3.Quantum.Measurement.Auric.CoordinatePinchingEntropy

/-! Source-bound audits for pinching entropy and the diagonal discord comparison. -/

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
    (fun p => @DensityState (p.1 × p.2.1)
      (@instFintypeProd _ _ p.2.2.1 p.2.2.2.2.1)
      (@instDecidableEqProd _ _ p.2.2.2.1 p.2.2.2.2.2.1)) (fun _ => ℝ)

private def gainActual : Realization gainSignature.{u,v} :=
  realize gainSignature (fun _ p ρ =>
      @basisGain p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
        ρ p.2.2.2.2.2.2)
    (fun e => nomatch e)

private def gainRejected : Realization gainSignature.{u,v} :=
  realize gainSignature (fun _ p ρ =>
      @basisGain p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
        ρ p.2.2.2.2.2.2 - 1)
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

private theorem flatGain_ne_uniform :
    basisGain (pureState flatVector.{u,v} flatNorm) 1 ≠ basisGain uniform.{u,v} 1 := by
  rw [basisGain, basisGain, flatPinch, uniformPinch, pure_entropy, sub_zero, sub_self]
  have hp := Real.binEntropy_pos (p := (1/2 : ℝ)) (by norm_num) (by norm_num)
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub] at hp
  unfold uniform
  rw [diagonalEntropy, sumQubit]
  norm_num at hp ⊢
  exact ne_of_gt hp

private theorem gainDependence : ObservationalDependence gainSignature.{u,v} gainActual := by
  intro _
  let p : Params.{u,v} :=
    ⟨Qubit, Scalar, inferInstance, inferInstance, inferInstance, inferInstance, 1⟩
  exact ⟨p, pureState flatVector flatNorm, uniform, flatGain_ne_uniform⟩

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

private abbrev attainedStatement := type_of% @diagonalDiscord_localChannel_mono_attained.{u,v}

private theorem attainedBridge : attainedStatement.{u,v} ↔ attainedArena.{u,v}.Law gainActual :=
  Iff.rfl

private theorem attainedVariation : Variation attainedArena.{u,v} gainActual :=
  ⟨@diagonalDiscord_localChannel_mono_attained, gainRejected, attainedRejected⟩

private theorem attainedSensitivity : Sensitivity attainedArena.{u,v} gainActual :=
  Reg.Support.UniverseSingleReadout.sensitivity attainedArena.Law _ _ attainedRejected

def attainedSource : Registration attainedArena.{u,v} attainedStatement.{u,v} where
  actual := gainActual
  bridge := attainedBridge
  variation := attainedVariation
  sensitivity := attainedSensitivity
  dependence := gainDependence

private def transferLaw (r : Realization gainSignature.{u,v}) : Prop :=
  ∀ {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] [Nonempty b] (Λ : QuantumChannel a a)
    (_hCQ : PreservesCQ (localChannel (b := b) Λ))
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

private abbrev transferArena : Arena where
  signature := gainSignature.{u,v}
  Law := transferLaw

private theorem transferRejected : ¬ transferArena.{u,v}.Law gainRejected := by
  intro h
  have hU : Eligible singletonInput.{u,v} 1 :=
    fun i j hij => False.elim (hij (Subsingleton.elim i j))
  obtain ⟨V, _, _, _, hres, hbound⟩ := h singletonChannel singletonCQ singletonInput 1 hU
  change basisGain _ V + _ ≤ basisGain singletonInput 1 - 1 at hbound
  rw [singletonGain, singletonGain] at hbound
  linarith

private abbrev transferStatement := type_of% @pointwise_transfer.{u,v}

private theorem transferBridge : transferStatement.{u,v} ↔ transferArena.{u,v}.Law gainActual :=
  Iff.rfl

private theorem transferVariation : Variation transferArena.{u,v} gainActual :=
  ⟨@pointwise_transfer, gainRejected, transferRejected⟩

private theorem transferSensitivity : Sensitivity transferArena.{u,v} gainActual :=
  Reg.Support.UniverseSingleReadout.sensitivity transferArena.Law _ _ transferRejected

def transferSource : Registration transferArena.{u,v} transferStatement.{u,v} where
  actual := gainActual
  bridge := transferBridge
  variation := transferVariation
  sensitivity := transferSensitivity
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
    (fun _ p ρ =>
      @basisGain p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
        ρ p.2.2.2.2.2.2)
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
    (fun _ p ρ =>
      @basisGain p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
        ρ p.2.2.2.2.2.2)
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

private abbrev minimumArena : Arena where
  signature := gainSignature.{u,v}
  Law r := ∀ {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ρ : DensityState (a × b)),
    ∃ U : Matrix.unitaryGroup a ℂ,
      Eligible ρ U ∧ IsMinOn (basisGain ρ) {V | Eligible ρ V} U ∧
      diagonalDiscord ρ =
        r.readout () ⟨a, b, inferInstance, inferInstance, inferInstance, inferInstance, U⟩ ρ

private theorem minimumRejected : ¬ minimumArena.{u,v}.Law gainRejected := by
  intro h
  obtain ⟨U, _, _, hbad⟩ := h singletonInput.{u,v}
  obtain ⟨V, _, _, hactual⟩ := diagonalDiscord_attained singletonInput.{u,v}
  change diagonalDiscord singletonInput = basisGain singletonInput U - 1 at hbad
  rw [singletonGain] at hbad hactual
  linarith

def minimumSource :
    Registration minimumArena.{u,v} (type_of% @diagonalDiscord_attained.{u,v}) where
  actual := gainActual
  bridge := Iff.rfl
  variation := ⟨@diagonalDiscord_attained, gainRejected, minimumRejected⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ minimumRejected
  dependence := gainDependence

def minimumRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@diagonalDiscord_attained.{u,v}) (Realization gainSignature.{u,v})
      (type_of% @DensityState.{max u v}) Unit := {
  unitName := .str ``minimumSource "unit"
  realizationName := ``minimumSource
  realizationSource := none
  generated := false
  arena := .source ⟨minimumArena.{u,v}⟩
  objectArena := .source ⟨minimumArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source minimumArena.{u,v} ⟨minimumSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gainSignature
    (fun _ p ρ =>
      @basisGain p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 ρ p.2.2.2.2.2.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity
    definition := none
    coordinates := #[0, 1, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


private abbrev PythagorasParams :=
  Σ n : Type u, Σ _ : Fintype n, Σ _ : DecidableEq n, DensityState n

private abbrev pythagorasSignature : Signature :=
  Reg.Support.UniverseSingleReadout.signature PythagorasParams.{u}
    (fun p => @DensityState p.1 p.2.1 p.2.2.1) (fun _ => WithTop ℝ)

private def referenceDivergence : ∀ (_ : Unit) (p : PythagorasParams.{u}),
    pythagorasSignature.State p → WithTop ℝ :=
  fun _ p ρ => @extendedQuantumRelativeEntropy p.1 p.2.1 p.2.2.1 ρ
    p.2.2.2

private def pythagorasActual : Realization pythagorasSignature.{u} :=
  realize pythagorasSignature referenceDivergence (fun e => nomatch e)

private def pythagorasRejected : Realization pythagorasSignature.{u} :=
  realize pythagorasSignature (fun _ _ _ => ⊤) (fun e => nomatch e)

private abbrev pythagorasArena : Arena where
  signature := pythagorasSignature.{u}
  Law r := ∀ {n : Type u} [Fintype n] [DecidableEq n] {k : ℕ} [Nonempty n]
    (p : CompletePVM n k) (ρ τ : DensityState n)
    (_hτ : pinch p τ = τ) (_h : SupportContained ρ τ),
    r.readout () ⟨n, inferInstance, inferInstance, τ⟩ ρ =
      extendedQuantumRelativeEntropy ρ (pinch p ρ) +
        extendedQuantumRelativeEntropy (pinch p ρ) τ

private theorem pythagorasRejected_law : ¬ pythagorasArena.{u}.Law pythagorasRejected := by
  intro h
  let p := localPVM (b := Scalar.{0}) (1 : Matrix.unitaryGroup Qubit.{u} ℂ)
  have he := h p uniform uniform uniformPinch (supportContained_refl uniform)
  change (⊤ : WithTop ℝ) = extendedQuantumRelativeEntropy uniform.{u,0} (pinch p uniform) +
    extendedQuantumRelativeEntropy (pinch p uniform) uniform at he
  rw [show pinch p uniform = uniform from uniformPinch,
    extendedQuantumRelativeEntropy_self] at he
  simp at he

private theorem pythagorasDependence :
    ObservationalDependence pythagorasSignature.{u} pythagorasActual := by
  intro _
  let p := localPVM (b := Scalar.{0}) (1 : Matrix.unitaryGroup Qubit.{u} ℂ)
  let flat := pureState flatVector.{u,0} flatNorm
  refine ⟨⟨Qubit.{u} × Scalar.{0}, inferInstance, inferInstance, uniform⟩, flat, uniform, ?_⟩
  change extendedQuantumRelativeEntropy flat uniform ≠ extendedQuantumRelativeEntropy uniform uniform
  have read_eq (ρ : DensityState (Qubit.{u} × Scalar.{0})) (h : pinch p ρ = uniform) :
      extendedQuantumRelativeEntropy ρ uniform = (basisGain ρ 1 : WithTop ℝ) := by
    rw [← h, extendedQuantumRelativeEntropy_eq_coe_of_support (supportContained_pinch p ρ),
      finiteTraceLogRelativeEntropy_pinch]
    rfl
  rw [read_eq flat flatPinch, read_eq uniform uniformPinch]
  exact fun e => flatGain_ne_uniform (WithTop.coe_injective e)

def pythagorasSource : Registration pythagorasArena.{u}
    (type_of% @extendedQuantumRelativeEntropy_pinch_pythagoras.{u}) where
  actual := pythagorasActual
  bridge := Iff.rfl
  variation := ⟨@extendedQuantumRelativeEntropy_pinch_pythagoras, pythagorasRejected,
    pythagorasRejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ pythagorasRejected_law
  dependence := pythagorasDependence

def pythagorasRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@extendedQuantumRelativeEntropy_pinch_pythagoras.{u})
      (Realization pythagorasSignature.{u}) (type_of% @DensityState.{u}) Unit := {
  unitName := .str ``pythagorasSource "unit"
  realizationName := ``pythagorasSource
  realizationSource := none
  generated := false
  arena := .source ⟨pythagorasArena.{u}⟩
  objectArena := .source ⟨pythagorasArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pythagorasArena.{u} ⟨pythagorasSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pythagorasSignature referenceDivergence (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity
    definition := none
    coordinates := #[0, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

namespace Optimized

open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
  (marginalRight partialTraceRight)

private abbrev PairQubit := ULift.{v} (Fin 2)

private theorem sumTwo {R : Type*} [AddCommMonoid R] (f : Qubit.{u} → R) :
    ∑ i, f i = f ⟨0⟩ + f ⟨1⟩ := by
  rw [← (Equiv.ulift.symm : Fin 2 ≃ Qubit.{u}).sum_comp]
  exact Fin.sum_univ_two _

private def amplitude (i : Fin 2) : ℂ := if i = 0 then 3/5 else 4/5
private def mass (i : Fin 2) : ℝ := if i = 0 then 9/25 else 16/25

private def schmidtVector (i : Qubit.{u} × PairQubit.{v}) : ℂ :=
  if i.1.down = i.2.down then amplitude i.1.down else 0

private def pinchedMass (i : Qubit.{u} × PairQubit.{v}) : ℝ :=
  if i.1.down = i.2.down then mass i.1.down else 0

private theorem schmidtNorm : star schmidtVector.{u,v} ⬝ᵥ schmidtVector.{u,v} = 1 := by
  simp only [dotProduct, Pi.star_apply, Fintype.sum_prod_type, sumTwo]
  norm_num [schmidtVector, amplitude, Complex.star_def]

private theorem pinchedMass_nonneg (i : Qubit.{u} × PairQubit.{v}) : 0 ≤ pinchedMass i := by
  unfold pinchedMass mass
  split_ifs <;> norm_num

private theorem pinchedMass_sum : ∑ i, pinchedMass.{u,v} i = 1 := by
  simp only [Fintype.sum_prod_type, sumTwo]
  norm_num [pinchedMass, mass]

private def schmidtState : DensityState (Qubit.{u} × PairQubit.{v}) :=
  pureState schmidtVector schmidtNorm

private def pinchedState : DensityState (Qubit.{u} × PairQubit.{v}) :=
  diagonalDensity pinchedMass pinchedMass_nonneg pinchedMass_sum

private theorem schmidtMarginal :
    CStarMatrix.ofMatrix.symm (marginalRight schmidtState.{u,v}).1 =
      Matrix.diagonal (fun i : Qubit.{u} => (mass i.down : ℂ)) := by
  ext ⟨i⟩ ⟨j⟩
  change (∑ k : PairQubit.{v}, rankOneDensity schmidtVector.{u,v} (⟨i⟩, k) (⟨j⟩, k)) = _
  fin_cases i <;> fin_cases j <;>
    norm_num [sumTwo, rankOneDensity, Matrix.vecMulVec_apply, Pi.star_apply,
      schmidtVector, amplitude, mass, Complex.star_def, map_ofNat, Matrix.diagonal_apply]

private theorem massInjective :
    Function.Injective (fun i : Qubit.{u} => (mass i.down : ℂ)) := by
  intro ⟨i⟩ ⟨j⟩ h
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [mass] at h

/-- A rank-one local pinching in an eigenbasis of a simple diagonal marginal
keeps exactly the matrix entries within each measured coordinate block. -/
private theorem simpleMarginalPinch {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ : DensityState (a × b)) (U : Matrix.unitaryGroup a ℂ)
    (hU : Eligible ρ U) (d : a → ℂ) (hd : Function.Injective d)
    (hm : CStarMatrix.ofMatrix.symm (marginalRight ρ).1 = Matrix.diagonal d) (i j : a × b) :
    CStarMatrix.ofMatrix.symm (pinch (localPVM U) ρ).1 i j =
      if i.1 = j.1 then CStarMatrix.ofMatrix.symm ρ.1 i j else 0 := by
  let f := Unitary.conjStarAlgAut ℂ (Matrix a a ℂ) U
  let E := coordinatePVM (Fintype.equivFin a)
  let Q := fun k => f (E.proj k)
  let p := localPVM (b := b) U
  have hdiag : (f.symm (Matrix.diagonal d)).IsDiag := by
    change (f.symm (CStarMatrix.ofMatrix.symm (marginalRight ρ).1)).IsDiag at hU
    rwa [hm] at hU
  have hQ (k) : (Q k).IsDiag := by
    have hcomm : Commute (f.symm (Matrix.diagonal d)) (E.proj k) := by
      rw [← hdiag.diagonal_diag]
      exact Matrix.commute_diagonal _ _
    have he := congrArg f hcomm.eq
    simp only [map_mul, StarAlgEquiv.apply_symm_apply] at he
    intro s t hst
    have hentry := congrArg (fun M : Matrix a a ℂ => M s t) he
    change (Matrix.diagonal d * Q k) s t = (Q k * Matrix.diagonal d) s t at hentry
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm (Q k s t)] at hentry
    have hz : (d s - d t) * Q k s t = 0 := by rw [sub_mul, hentry, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (fun h => hst (hd h)))
  have hQentry (k) (s t : a) :
      Q k s t = U.val s ((Fintype.equivFin a).symm k) *
        star (U.val t ((Fintype.equivFin a).symm k)) := by
    change (U.val * (E.proj k) * U.valᴴ) s t = _
    rw [Matrix.mul_apply, Finset.sum_eq_single ((Fintype.equivFin a).symm k)]
    · simp [E, coordinatePVM, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    · intro l _ hl
      have h : Fintype.equivFin a l ≠ k :=
        fun he => hl ((Fintype.equivFin a).injective
          (he.trans ((Fintype.equivFin a).apply_symm_apply k).symm))
      simp [E, coordinatePVM, Matrix.mul_diagonal, h]
    · simp
  have hpDiag (k) : (p.proj k).IsDiag :=
    (hQ k).kronecker Matrix.isDiag_one
  have hpEntry (k) (z : a × b) : p.proj k z z = Q k z.1 z.1 := by
    change (Q k ⊗ₖ (1 : Matrix b b ℂ)) z z = _
    simp [Matrix.kroneckerMap_apply]
  have hcompress (k) :
      (p.proj k * CStarMatrix.ofMatrix.symm ρ.1 * p.proj k) i j =
        p.proj k i i * CStarMatrix.ofMatrix.symm ρ.1 i j * p.proj k j j := by
    conv_lhs => rw [← (hpDiag k).diagonal_diag]
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rfl
  change CStarMatrix.ofMatrix.symm
    ((pinchingChannel p).toCompletelyPositiveMap (CStarMatrix.ofMatrix (CStarMatrix.ofMatrix.symm ρ.1)))
      i j = _
  rw [pinchingChannel_apply, unreadState, Matrix.sum_apply]
  by_cases hij : i.1 = j.1
  · rw [ite_eq_left hij]
    have hsum : (∑ k, p.proj k i i) = 1 := by
      simpa only [Matrix.sum_apply, Matrix.one_apply_eq] using
        congrArg (fun M : Matrix (a × b) (a × b) ℂ => M i i) p.complete
    calc
      _ = ∑ k, p.proj k i i * CStarMatrix.ofMatrix.symm ρ.1 i j := by
        apply Finset.sum_congr rfl
        intro k _
        have hsame : p.proj k j j = p.proj k i i := by rw [hpEntry, hpEntry, hij]
        have hid := congrArg (fun M : Matrix (a × b) (a × b) ℂ => M i i) (p.idempotent k)
        change (p.proj k * p.proj k) i i = p.proj k i i at hid
        conv at hid =>
          lhs
          rw [← (hpDiag k).diagonal_diag]
        rw [Matrix.diagonal_mul, Matrix.diagonal_apply_eq] at hid
        rw [hcompress, hsame, mul_right_comm]
        exact congrArg (fun z => z * CStarMatrix.ofMatrix.symm ρ.1 i j) hid
      _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]
  · rw [ite_eq_right hij]
    apply Finset.sum_eq_zero
    intro k _
    have hz := mul_eq_zero.mp ((hQentry k i.1 j.1).symm.trans (hQ k hij))
    rw [hcompress, hpEntry, hpEntry, hQentry, hQentry]
    rcases hz with hz | hz
    · rw [hz, zero_mul, zero_mul, zero_mul]
    · rw [hz, mul_zero, mul_zero]

private theorem schmidtPinch (U : Matrix.unitaryGroup Qubit.{u} ℂ)
    (hU : Eligible schmidtState.{u,v} U) :
    pinch (localPVM U) schmidtState.{u,v} = pinchedState.{u,v} := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  ext ⟨⟨i⟩, ⟨k⟩⟩ ⟨⟨j⟩, ⟨l⟩⟩
  rw [simpleMarginalPinch schmidtState U hU _ massInjective schmidtMarginal]
  change (if (⟨i⟩ : Qubit.{u}) = ⟨j⟩ then
      rankOneDensity schmidtVector.{u,v} (⟨i⟩, ⟨k⟩) (⟨j⟩, ⟨l⟩) else 0) =
    Matrix.diagonal (fun z => (pinchedMass.{u,v} z : ℂ)) (⟨i⟩, ⟨k⟩) (⟨j⟩, ⟨l⟩)
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [rankOneDensity, Matrix.vecMulVec_apply, Pi.star_apply, schmidtVector,
      amplitude, pinchedMass, mass, Complex.star_def, Matrix.diagonal_apply]

private theorem schmidtDiscord_pos : 0 < diagonalDiscord schmidtState.{u,v} := by
  obtain ⟨U, hU, _, he⟩ := diagonalDiscord_attained schmidtState.{u,v}
  rw [he, basisGain, schmidtPinch U hU]
  change 0 < vonNeumannEntropy pinchedState.{u,v} - vonNeumannEntropy (pureState _ schmidtNorm)
  rw [pure_entropy, sub_zero, pinchedState, diagonalEntropy, Fintype.sum_prod_type]
  simp only [sumTwo]
  norm_num [pinchedMass, mass, Real.negMulLog]
  have h9 : Real.log (9/25) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have h16 : Real.log (16/25) < 0 := Real.log_neg (by norm_num) (by norm_num)
  linarith

/-- The product of the two maximally mixed qubit states. -/
private def mixedProduct : DensityState (Qubit.{u} × PairQubit.{v}) :=
  diagonalDensity (fun _ => 1/4) (fun _ => by norm_num)
    (by simp only [Fintype.sum_prod_type, sumTwo]; norm_num)

private theorem mixedProductPinch (U : Matrix.unitaryGroup Qubit.{u} ℂ) :
    pinch (localPVM U) mixedProduct.{u,v} = mixedProduct.{u,v} := by
  let p := localPVM (b := PairQubit.{v}) U
  have hm : CStarMatrix.ofMatrix.symm mixedProduct.{u,v}.1 =
      (1/4 : ℂ) • (1 : Matrix (Qubit.{u} × PairQubit.{v}) _ ℂ) := by
    rw [Matrix.smul_one_eq_diagonal]
    change Matrix.diagonal (fun _ => (↑(1/4 : ℝ) : ℂ)) = _
    simp
  have hp : CStarMatrix.ofMatrix.symm (pinch p mixedProduct).1 =
      unreadState p.proj (CStarMatrix.ofMatrix.symm mixedProduct.1) :=
    pinchingChannel_apply p _
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  rw [hp, hm, unreadState]
  simp_rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, p.idempotent,
    ← Finset.smul_sum, p.complete]

private theorem mixedProductDiscord : diagonalDiscord mixedProduct.{u,v} = 0 := by
  obtain ⟨U, _, _, he⟩ := diagonalDiscord_attained mixedProduct.{u,v}
  rw [he, basisGain, mixedProductPinch, sub_self]

private abbrev Carriers :=
  Σ a : Type u, Σ b : Type v, Σ _ : Fintype a, Σ _ : DecidableEq a,
    Σ _ : Fintype b, DecidableEq b

private abbrev discordSignature : Signature :=
  Reg.Support.UniverseSingleReadout.signature Carriers.{u,v}
    (fun p => @DensityState (p.1 × p.2.1)
      (@instFintypeProd _ _ p.2.2.1 p.2.2.2.2.1)
      (@instDecidableEqProd _ _ p.2.2.2.1 p.2.2.2.2.2)) (fun _ => ℝ)

private def readDiscord : ∀ (_ : Unit) (p : Carriers.{u,v}), discordSignature.State p → ℝ :=
  fun _ p ρ =>
    @diagonalDiscord p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 ρ

private def discordActual : Realization discordSignature.{u,v} :=
  realize discordSignature readDiscord (fun e => nomatch e)

private def discordRejected : Realization discordSignature.{u,v} :=
  realize discordSignature (fun _ p ρ => readDiscord () p ρ - 1) (fun e => nomatch e)

private theorem discordDependence :
    ObservationalDependence discordSignature.{u,v} discordActual := by
  intro _
  let p : Carriers.{u,v} :=
    ⟨Qubit, PairQubit, inferInstance, inferInstance, inferInstance, inferInstance⟩
  refine ⟨p, schmidtState, mixedProduct, ?_⟩
  change diagonalDiscord schmidtState.{u,v} ≠ diagonalDiscord mixedProduct.{u,v}
  rw [mixedProductDiscord]
  exact ne_of_gt schmidtDiscord_pos

private def discordLaw (r : Realization discordSignature.{u,v}) : Prop :=
  ∀ {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] [Nonempty b] (Λ : QuantumChannel a a)
    (_hCQ : PreservesCQ (localChannel (b := b) Λ)) (ρ : DensityState (a × b)),
    diagonalDiscord ((localChannel Λ).mapState ρ) ≤
      r.readout () ⟨a, b, inferInstance, inferInstance, inferInstance, inferInstance⟩ ρ

private abbrev discordArena : Arena where
  signature := discordSignature.{u,v}
  Law := discordLaw

private theorem singletonDiscord (ρ : DensityState (MeasuredSingleton.{u} × Scalar.{v})) :
    diagonalDiscord ρ = 0 := by
  obtain ⟨U, _, _, he⟩ := diagonalDiscord_attained ρ
  exact he.trans (singletonGain ρ U)

private theorem discordRejected_law : ¬ discordArena.{u,v}.Law discordRejected := by
  intro h
  have hbad := h singletonChannel singletonCQ singletonInput.{u,v}
  change diagonalDiscord _ ≤ diagonalDiscord singletonInput.{u,v} - 1 at hbad
  rw [singletonDiscord, singletonDiscord] at hbad
  linarith

private abbrev discordStatement := type_of% @diagonalDiscord_localChannel_mono.{u,v}

private theorem discordBridge : discordStatement.{u,v} ↔ discordArena.{u,v}.Law discordActual :=
  Iff.rfl

private theorem discordVariation : Variation discordArena.{u,v} discordActual :=
  ⟨@diagonalDiscord_localChannel_mono, discordRejected, discordRejected_law⟩

private theorem discordSensitivity : Sensitivity discordArena.{u,v} discordActual :=
  Reg.Support.UniverseSingleReadout.sensitivity _ _ _ discordRejected_law

def discordSource : Registration discordArena.{u,v} discordStatement.{u,v} where
  actual := discordActual
  bridge := discordBridge
  variation := discordVariation
  sensitivity := discordSensitivity
  dependence := discordDependence

def discordRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@diagonalDiscord_localChannel_mono.{u,v}) (Realization discordSignature.{u,v})
      (type_of% @DensityState.{max u v}) Unit := {
  unitName := .str ``discordSource "unit"
  realizationName := ``discordSource
  realizationSource := none
  generated := false
  arena := .source ⟨discordArena.{u,v}⟩
  objectArena := .source ⟨discordArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source discordArena.{u,v} ⟨discordSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize discordSignature readDiscord (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Optimized
end BasisGainAudit

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
