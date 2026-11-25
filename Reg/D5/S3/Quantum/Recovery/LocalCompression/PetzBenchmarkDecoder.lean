import Batteries.Tactic.OpenPrivate
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Quantum.Recovery.LocalCompression.PetzBenchmarkDecoder
import Reg.D5.S3.Quantum.Recovery.LocalCompression.PetzFixedMarginalNoise

/-! Source-bound interventions on the sequential decoder, benchmark and score budget. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Quantum.Recovery.LocalCompression.PetzBenchmarkDecoder

open Matrix LeanInformationAudit
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Recovery.LocalCompression.PetzBenchmarkDecoder
open _root_.Reg.Support.UniverseSingleReadout (signature sensitivity)

namespace Transitivity

universe ua ub uc ui uj

set_option linter.checkUnivs false in
private abbrev Parameters :=
  Σ (A : Type ua) (B : Type ub) (C : Type uc) (I : Type ui) (J : Type uj)
    (_ : Fintype A) (_ : DecidableEq A) (_ : Fintype B) (_ : DecidableEq B)
    (_ : Fintype C) (_ : DecidableEq C) (_ : Fintype I) (_ : Fintype J)
    (_ : NormalizedKraus I B A) (_ : NormalizedKraus J C B), DensityState A

set_option linter.checkUnivs false in
private abbrev observation : Signature :=
  signature Parameters.{ua,ub,uc,ui,uj}
    (fun ⟨_, _, C, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ => Matrix C C ℂ)
    (fun ⟨A, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ => Matrix A A ℂ)

private def actual : Realization observation.{ua,ub,uc,ui,uj} :=
  realize observation (fun _ ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, K, L, σ⟩ X =>
    matrixAction (completedPetz K.1 K.2 σ)
      (matrixAction (completedPetz L.1 L.2 ((krausChannel K.1 K.2).mapState σ)) X))
    (fun e => nomatch e)

private def zeroReadout : Realization observation.{ua,ub,uc,ui,uj} :=
  realize observation (fun _ ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ _ => 0)
    (fun e => nomatch e)

set_option linter.checkUnivs false in
private abbrev arena : Arena where
  signature := observation.{ua,ub,uc,ui,uj}
  Law op := ∀ {A : Type ua} {B : Type ub} {C : Type uc} {I : Type ui} {J : Type uj}
      [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
      [Fintype I] [Fintype J]
      (K : NormalizedKraus I B A) (L : NormalizedKraus J C B)
      (σ : DensityState A) (X : Matrix C C ℂ),
    let sequential := op.readout () ⟨A, B, C, I, J, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      K, L, σ⟩ X
    matrixAction (compositePetz K.1 L.1 K.2 L.2 σ) X = sequential

private def oneKraus : PUnit.{ui+1} → Matrix PUnit.{ub+1} PUnit.{ua+1} ℂ := fun _ _ _ => 1

private theorem oneKraus_complete :
    (∑ i, (oneKraus.{ua,ub,ui} i)ᴴ * oneKraus.{ua,ub,ui} i) = 1 := by
  ext i j
  cases i
  cases j
  simp [oneKraus, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

private def singletonState : DensityState PUnit.{ua+1} :=
  ⟨CStarMatrix.ofMatrix 1, map_nonneg CStarMatrix.ofMatrixStarAlgEquiv zero_le_one, by
    change (1 : Matrix PUnit.{ua+1} PUnit.{ua+1} ℂ).trace = 1
    simp [Matrix.trace]⟩

private def parameters : Parameters.{ua,ub,uc,ui,uj} :=
  ⟨PUnit.{ua+1}, PUnit.{ub+1}, PUnit.{uc+1}, PUnit.{ui+1}, PUnit.{uj+1},
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ⟨oneKraus, oneKraus_complete⟩,
    ⟨oneKraus, oneKraus_complete⟩, singletonState⟩

private theorem trace_action {A : Type ua} {B : Type ub}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (N : QuantumChannel A B)
    (X : Matrix A A ℂ) : (matrixAction N X).trace = X.trace :=
  N.trace_preserving (CStarMatrix.ofMatrix X)

private theorem zero_fails : ¬ arena.{ua,ub,uc,ui,uj}.Law zeroReadout := by
  intro h
  have hit := h ⟨oneKraus.{ua,ub,ui}, oneKraus_complete⟩
    ⟨oneKraus.{ub,uc,uj}, oneKraus_complete⟩ singletonState
    (1 : Matrix PUnit.{uc+1} PUnit.{uc+1} ℂ)
  change matrixAction (compositePetz _ _ _ _ _) _ = 0 at hit
  have ht := congrArg Matrix.trace hit
  rw [trace_action, Matrix.trace_zero] at ht
  simp [Matrix.trace] at ht

def family : Registration arena.{ua,ub,uc,ui,uj}
    (type_of% @completed_petz_transitivity.{ua,ub,uc,ui,uj}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@completed_petz_transitivity.{ua,ub,uc,ui,uj}, zeroReadout, zero_fails⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual zeroReadout zero_fails
  dependence := by
    intro _
    refine ⟨parameters, (0 : Matrix PUnit.{uc+1} PUnit.{uc+1} ℂ),
      (1 : Matrix PUnit.{uc+1} PUnit.{uc+1} ℂ), ?_⟩
    intro h
    let K := oneKraus.{ua,ub,ui}
    let L := oneKraus.{ub,uc,uj}
    let D := (completedPetz K oneKraus_complete singletonState).comp
      (completedPetz L oneKraus_complete
        ((krausChannel K oneKraus_complete).mapState singletonState))
    change matrixAction D 0 = matrixAction D 1 at h
    have ht := congrArg Matrix.trace h
    rw [trace_action, trace_action, Matrix.trace_zero] at ht
    simp [Matrix.trace] at ht

set_option linter.style.longLine false in
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completed_petz_transitivity.{ua,ub,uc,ui,uj})
    (Realization observation.{ua,ub,uc,ui,uj}) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.LocalCompression.PetzBenchmarkDecoder.completed_petz_transitivity.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.LocalCompression.PetzBenchmarkDecoder.Transitivity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize observation (fun _ ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, K, L, σ⟩ X =>
    matrixAction (completedPetz K.1 K.2 σ)
      (matrixAction (completedPetz L.1 L.2 ((krausChannel K.1 K.2).mapState σ)) X))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.LocalCompression.PetzBenchmarkDecoder
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 13, 14, 15]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 16
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Transitivity

open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
  (marginalRight partialTraceRight)
open _root_.D5.S3.Quantum.Divergence.CanonicalChannelDPI (actual_kraus_representation)
open _root_.D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_nonneg)
open _root_.D5.S3.Quantum.Recovery.LocalCompression.PetzFixedMarginalNoise (loss)
open private krausChannel_apply completedPetz_reference krausErasure_apply from
  D5.S3.Quantum.Recovery.LocalCompression.PetzBenchmarkDecoder
open private Retained Environment source reference marginal_one source_loss_pos
  source_reference_ne from
  Reg.D5.S3.Quantum.Recovery.LocalCompression.PetzFixedMarginalNoise

universe u ui

private abbrev Joint := Retained.{u} × Environment.{u}

private def identityKraus : PUnit.{ui+1} → Matrix Joint.{u} Joint.{u} ℂ := fun _ => 1

private theorem identity_complete :
    (∑ i, (identityKraus.{u,ui} i)ᴴ * identityKraus.{u,ui} i) = 1 := by
  simp [identityKraus]

private theorem identity_retained (X : Matrix Joint.{u} Joint.{u} ℂ) :
    partialTraceRight (matrixAction (krausChannel identityKraus.{u,ui} identity_complete) X) =
      partialTraceRight X := by
  rw [krausChannel_apply]
  simp [identityKraus]

private theorem singleton_benchmark (ρ σ : DensityState Joint.{u}) : benchmark ρ σ = σ := by
  let L := actual_kraus_representation (retainedErasure (R := Retained) (E := Environment))
  have h := completedPetz_reference L.kraus L.hkraus σ
  have hmarg : raw (marginalRight ρ) = raw ((krausChannel L.kraus L.hkraus).mapState σ) := by
    change partialTraceRight (raw ρ) = matrixAction (krausChannel L.kraus L.hkraus) (raw σ)
    have hσ : matrixAction (krausChannel L.kraus L.hkraus) (raw σ) =
        partialTraceRight (raw σ) := krausErasure_apply (raw σ)
    rw [hσ, marginal_one, marginal_one]
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change matrixAction (completedPetz L.kraus L.hkraus σ) (raw (marginalRight ρ)) = raw σ
  rwa [hmarg]

private abbrev ReferenceParams :=
  Σ (R : Type u) (E : Type u) (_ : Fintype R) (_ : DecidableEq R)
    (_ : Fintype E) (_ : DecidableEq E), DensityState (R × E)

namespace Benchmark

private abbrev observation : Signature :=
  signature ReferenceParams.{u}
    (fun ⟨R, E, _, _, _, _, _⟩ => DensityState (R × E))
    (fun ⟨R, E, _, _, _, _, _⟩ => DensityState (R × E))

private def actual : Realization observation.{u} :=
  realize observation (fun _ ⟨_, _, _, _, _, _, ρ⟩ σ => benchmark ρ σ) (fun e => nomatch e)

private def sourceReadout : Realization observation.{u} :=
  realize observation (fun _ ⟨_, _, _, _, _, _, ρ⟩ _ => ρ) (fun e => nomatch e)

set_option linter.checkUnivs false in
private abbrev arena : Arena where
  signature := observation.{u}
  Law op := ∀ {I : Type ui} [Fintype I] {R E F : Type u}
      [Fintype R] [DecidableEq R] [Nonempty R]
      [Fintype E] [DecidableEq E] [Nonempty E] [Fintype F] [DecidableEq F] [Nonempty F]
      (K : I → Matrix (R × F) (R × E) ℂ) (hK : (∑ i, (K i)ᴴ * K i) = 1)
      (_ : ∀ X, partialTraceRight (matrixAction (krausChannel K hK) X) = partialTraceRight X)
      (ρ σ : DensityState (R × E)),
    let N := krausChannel K hK
    let original := op.readout ()
      ⟨R, E, inferInstance, inferInstance, inferInstance, inferInstance, ρ⟩ σ
    (completedPetz K hK σ).mapState (benchmark (N.mapState ρ) (N.mapState σ)) = original

private theorem source_fails : ¬ arena.{u,ui}.Law sourceReadout := by
  intro h
  have bad := h identityKraus.{u,ui} identity_complete identity_retained source.{u} reference.{u}
  have good := compression_recovers_benchmark identityKraus.{u,ui} identity_complete identity_retained
    source.{u} reference.{u}
  change _ = source.{u} at bad
  change _ = benchmark source.{u} reference.{u} at good
  exact source_reference_ne (congrArg raw (bad.symm.trans
    (good.trans (singleton_benchmark source.{u} reference.{u}))))

def family : Registration arena.{u,ui} (type_of% @compression_recovers_benchmark.{u,ui}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@compression_recovers_benchmark.{u,ui}, sourceReadout, source_fails⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual sourceReadout source_fails
  dependence := by
    intro _
    refine ⟨⟨Retained, Environment, inferInstance, inferInstance, inferInstance, inferInstance, source⟩,
      source, reference, ?_⟩
    change benchmark source.{u} source.{u} ≠ benchmark source.{u} reference.{u}
    rw [singleton_benchmark, singleton_benchmark]
    exact fun h => source_reference_ne (congrArg raw h)

set_option linter.style.longLine false in
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@compression_recovers_benchmark.{u,ui}) (Realization observation.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.LocalCompression.PetzBenchmarkDecoder.compression_recovers_benchmark.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.LocalCompression.PetzBenchmarkDecoder.Benchmark.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize observation (fun _ ⟨_, _, _, _, _, _, ρ⟩ σ => benchmark ρ σ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.LocalCompression.PetzBenchmarkDecoder
    definition := none
    coordinates := #[2, 3, 17]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body",
        "value"]
      stateBinder := 18
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Benchmark

namespace Score

private abbrev Parameters :=
  Σ (R : Type u) (E : Type u) (_ : Fintype R) (_ : DecidableEq R)
    (_ : Fintype E) (_ : DecidableEq E) (_ : DensityState (R × E)), DensityState (R × E)

private abbrev observation : Signature :=
  signature Parameters.{u} (fun _ => ℝ) (fun _ => ℝ)

private def actual : Realization observation.{u} :=
  realize observation (fun _ ⟨_, _, _, _, _, _, ρ, σ⟩ threshold =>
    Real.sqrt (threshold * loss ρ σ)) (fun e => nomatch e)

private def negativeReadout : Realization observation.{u} :=
  realize observation (fun _ _ _ => -1) (fun e => nomatch e)

set_option linter.checkUnivs false in
private abbrev arena : Arena where
  signature := observation.{u}
  Law op := ∀ {I : Type ui} [Fintype I] {R E F : Type u}
      [Fintype R] [DecidableEq R] [Nonempty R]
      [Fintype E] [DecidableEq E] [Nonempty E] [Fintype F] [DecidableEq F] [Nonempty F]
      (K : I → Matrix (R × F) (R × E) ℂ) (hK : (∑ i, (K i)ᴴ * K i) = 1)
      (_ : ∀ X, partialTraceRight (matrixAction (krausChannel K hK) X) = partialTraceRight X)
      (ρ σ : DensityState (R × E)) (_ : SupportContained ρ σ)
      (threshold : ℝ) (_ : 0 ≤ threshold) (ε : ℝ),
    let N := krausChannel K hK
    let ρ' := N.mapState ρ
    let σ' := N.mapState σ
    let decoded := (completedPetz K hK σ).mapState ρ'
    let budget := op.readout ()
      ⟨R, E, inferInstance, inferInstance, inferInstance, inferInstance, ρ, σ⟩ threshold
    traceNorm (raw ρ - raw decoded) ≤ ε →
    ε + budget < traceNorm (raw ρ - raw (benchmark ρ σ)) →
    0 < loss ρ' σ' ∧ threshold < compressionScore ρ' σ'

private theorem negative_fails : ¬ arena.{u,ui}.Law negativeReadout := by
  intro h
  let σ := reference.{u}
  let N := krausChannel identityKraus.{u,ui} identity_complete
  let D := completedPetz identityKraus.{u,ui} identity_complete σ
  have hrec : raw (D.mapState (N.mapState σ)) = raw σ :=
    completedPetz_reference identityKraus.{u,ui} identity_complete σ
  have hres : traceNorm (raw σ - raw (D.mapState (N.mapState σ))) ≤ 0 := by
    rw [hrec, sub_self]
    simp [_root_.D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm]
  have hmargin : 0 + (-1 : ℝ) < traceNorm (raw σ - raw (benchmark σ σ)) := by
    exact (by norm_num : (0 : ℝ) + -1 < 0).trans_le (traceNorm_nonneg _)
  have bad := h identityKraus.{u,ui} identity_complete identity_retained σ σ
    (fun _ hv => hv) 0 le_rfl 0 hres hmargin
  have hp : 0 < loss (N.mapState σ) (N.mapState σ) := bad.1
  rw [loss, finiteTraceLogRelativeEntropy_self (N.mapState σ),
    finiteTraceLogRelativeEntropy_self (marginalRight (N.mapState σ)), sub_self] at hp
  exact (lt_irrefl 0) hp

def family : Registration arena.{u,ui} (type_of% @strict_score_of_decoder_residual.{u,ui}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@strict_score_of_decoder_residual.{u,ui}, negativeReadout, negative_fails⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual negativeReadout negative_fails
  dependence := by
    intro _
    refine ⟨⟨Retained, Environment, inferInstance, inferInstance, inferInstance, inferInstance,
      source, reference⟩, (0 : ℝ), (1 : ℝ), ?_⟩
    change √(0 * loss source.{u} reference.{u}) ≠ √(1 * loss source.{u} reference.{u})
    simpa only [zero_mul, one_mul, Real.sqrt_zero] using
      (ne_of_lt (Real.sqrt_pos.2 source_loss_pos.{u}))

set_option linter.style.longLine false in
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@strict_score_of_decoder_residual.{u,ui}) (Realization observation.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.LocalCompression.PetzBenchmarkDecoder.strict_score_of_decoder_residual.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.LocalCompression.PetzBenchmarkDecoder.Score.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize observation (fun _ ⟨_, _, _, _, _, _, ρ, σ⟩ threshold => Real.sqrt (threshold * loss ρ σ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.LocalCompression.PetzBenchmarkDecoder
    definition := none
    coordinates := #[2, 3, 17, 18]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "value"]
      stateBinder := 20
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Score

end Reg.D5.S3.Quantum.Recovery.LocalCompression.PetzBenchmarkDecoder
