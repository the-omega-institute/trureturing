import Batteries.Tactic.OpenPrivate
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.PetzFixedMarginalNoise
import D5.S3.Quantum.Divergence.FibonacciQutritBenchmark
import D5.S3.Quantum.ProcessReconstruction.EdgeRecordQuantum
import D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
import D5.S3.Quantum.Schatten.TraceNorm
import Reg.Support.UniverseSingleReadout

/-! Source-bound identity-noise interventions for the contraction and score laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix LeanInformationAudit
open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_nonneg)
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceRight trace_partialTraceRight marginalRight density_posSemidef)
open _root_.D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open _root_.D5.S3.Quantum.Recovery.PetzFixedMarginalNoise
open _root_.D5.S3.Quantum.Recovery.BKMFlagRefinement (partialTracePetz lift)
open _root_.D5.S3.Quantum.Matrix.SpectralPower (mpow)
open _root_.D5.S3.Quantum.Schatten.TraceNorm (traceNormUINorm)
open _root_.D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance
  (traceNorm_submatrix_equiv)
open _root_.Reg.Support.UniverseSingleReadout (signature sensitivity)

open private diagonalState from D5.S3.Quantum.ProcessReconstruction.EdgeRecordQuantum
open private traceLog diagReal diagonal_traceLog from D5.S3.Quantum.Divergence.FibonacciQutritBenchmark
open private raw finiteTraceLog_eq_raw noiseWithEnvironment from D5.S3.Quantum.Recovery.PetzFixedMarginalNoise

namespace Reg.D5.S3.Quantum.Recovery.PetzFixedMarginalNoise

universe u

private abbrev Retained := ULift.{u} (Fin 1)
private abbrev Environment := ULift.{u} (Fin 3)
private abbrev Joint := Retained.{u} × Environment.{u}

private def sourceWeights (i : Joint.{u}) : ℝ := if i.2.down = 0 then 1 else 0
private def referenceWeights (i : Joint.{u}) : ℝ := if i.2.down = 2 then 0 else 1 / 2

private theorem sumJoint {A : Type*} [AddCommMonoid A] (f : Joint.{u} → A) :
    (∑ i, f i) = ∑ j : Fin 3, f (ULift.up 0, ULift.up j) := by
  rw [Fintype.sum_prod_type, Fintype.sum_unique]
  exact ((Equiv.ulift : Environment.{u} ≃ Fin 3).symm.sum_comp _).symm

private def source : DensityState Joint.{u} :=
  diagonalState sourceWeights (by intro i; unfold sourceWeights; split <;> norm_num)
    (by rw [sumJoint]; norm_num [Fin.sum_univ_three, sourceWeights])

private def reference : DensityState Joint.{u} :=
  diagonalState referenceWeights (by intro i; unfold referenceWeights; split <;> norm_num)
    (by rw [sumJoint]; norm_num [Fin.sum_univ_three, referenceWeights])

private theorem marginal_one (W : DensityState Joint.{u}) :
    partialTraceRight (raw W) = (1 : Matrix Retained.{u} Retained.{u} ℂ) := by
  have h : (partialTraceRight (raw W)).trace = 1 :=
    (trace_partialTraceRight _).trans W.2.2
  ext i j
  have hij : i = j := Subsingleton.elim _ _
  subst j
  rw [Matrix.trace, Finset.sum_eq_single i
    (fun k _ hk => (hk (Subsingleton.elim _ _)).elim) (by
      intro hm
      exact (hm (Finset.mem_univ i)).elim)] at h
  simpa using h

private theorem reference_marginal_faithful :
    (partialTraceRight (raw reference.{u})).PosDef := by
  rw [marginal_one]
  exact Matrix.PosDef.one

private theorem source_supported : SupportContained source.{u} reference.{u} := by
  intro v hv
  change diagonal (fun i => (referenceWeights i : ℂ)) *ᵥ v = 0 at hv
  change diagonal (fun i => (sourceWeights i : ℂ)) *ᵥ v = 0
  funext i
  have h := congrFun hv i
  simp only [Matrix.mulVec_diagonal, Pi.zero_apply] at h ⊢
  by_cases hi : i.2.down = 0
  · have hneq : i.2.down ≠ 2 := by rw [hi]; decide
    norm_num [referenceWeights, hneq] at h
    simp [sourceWeights, hi, h]
  · simp [sourceWeights, hi]

private theorem reference_singular : ¬ (raw reference.{u}).PosDef := by
  intro h
  change (diagonal (fun i : Joint.{u} => (referenceWeights i : ℂ))).PosDef at h
  have hi := Matrix.posDef_diagonal_iff.mp h ((ULift.up 0, ULift.up 2) : Joint.{u})
  simp [referenceWeights] at hi

private theorem source_loss_pos : 0 < loss source.{u} reference.{u} := by
  have hmarg : marginalRight source.{u} = marginalRight reference.{u} := by
    apply Subtype.ext
    exact CStarMatrix.ofMatrix.symm.injective
      ((marginal_one source.{u}).trans (marginal_one reference.{u}).symm)
  rw [loss, hmarg, finiteTraceLogRelativeEntropy_self, sub_zero, finiteTraceLog_eq_raw]
  change 0 < traceLog (diagReal sourceWeights) (diagReal referenceWeights)
  rw [diagonal_traceLog, sumJoint]
  have hlog : Real.log (1 / 2 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  simpa [Fin.sum_univ_three, sourceWeights, referenceWeights] using hlog

private theorem source_reference_ne : raw source.{u} ≠ raw reference.{u} := by
  intro heq
  let i : Joint.{u} := (ULift.up 0, ULift.up 0)
  have h := congrArg (fun A : Matrix Joint.{u} Joint.{u} ℂ => A i i) heq
  change diagonal (fun j : Joint.{u} => (sourceWeights j : ℂ)) i i =
    diagonal (fun j : Joint.{u} => (referenceWeights j : ℂ)) i i at h
  norm_num [i, sourceWeights, referenceWeights] at h

private theorem source_error_pos : 0 < errorSq source.{u} reference.{u} := by
  have hPetz : partialTracePetz (raw reference.{u}) (partialTraceRight (raw source.{u})) =
      raw reference.{u} := by
    have hhalf : mpow (raw reference.{u}) (1 / 2) = CFC.sqrt (raw reference.{u}) := by
      rw [CFC.sqrt_eq_real_sqrt _ (density_posSemidef reference.{u}).nonneg,
        cfcₙ_eq_cfc (a := raw reference.{u}) Real.continuous_sqrt.continuousOn Real.sqrt_zero]
      simp only [mpow, Real.sqrt_eq_rpow]
    rw [partialTracePetz, marginal_one source.{u}, marginal_one reference.{u}, hhalf]
    simp [mpow, lift, CFC.sqrt_mul_sqrt_self _ (density_posSemidef reference.{u}).nonneg]
  rw [errorSq, hPetz]
  let A := raw source.{u} - raw reference.{u}
  have hA : 0 < traceNorm A := by
    let e := (Fintype.equivFin Joint.{u}).symm
    rw [← traceNorm_submatrix_equiv A e e]
    exact lt_of_le_of_ne (traceNorm_nonneg _) (Ne.symm (fun hz => by
      have hzero := (traceNormUINorm (Fintype.card Joint.{u})).eq_zero_iff _ |>.mp hz
      apply source_reference_ne.{u}
      apply sub_eq_zero.mp
      ext i j
      simpa [A, e] using congrFun (congrFun hzero (Fintype.equivFin Joint.{u} i))
        (Fintype.equivFin Joint.{u} j)))
  exact pow_pos hA 2

private theorem noise_zero {R E : Type u} [Fintype R] [DecidableEq R]
    [Fintype E] [DecidableEq E] (X : DensityState (R × E)) : noise X 0 = X := by
  classical
  by_cases h : Nonempty E
  · apply Subtype.ext
    simp [noise, h, noiseWithEnvironment]
  · simp [noise, h]

private abbrev ReferenceParams :=
  Σ R : Type u, Σ E : Type u, Σ _ : Fintype R, Σ _ : DecidableEq R,
    Σ _ : Fintype E, Σ _ : DecidableEq E, DensityState (R × E)

private abbrev StatePairParams :=
  Σ R : Type u, Σ E : Type u, Σ _ : Fintype R, Σ _ : DecidableEq R,
    Σ _ : Fintype E, Σ _ : DecidableEq E, Σ _ : DensityState (R × E), DensityState (R × E)

namespace Contraction

abbrev observation : Signature := signature StatePairParams.{u} (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization observation.{u} :=
  realize observation (fun _ ⟨_, _, _, _, _, _, X, Y⟩ e => loss (noise X e) (noise Y e))
    (fun e => nomatch e)

def identity : Realization observation.{u} :=
  realize observation (fun _ ⟨_, _, _, _, _, _, X, Y⟩ _ => loss X Y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := observation.{u}
  Law op := ∀ {R E : Type u} [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype E] [DecidableEq E] [Nonempty E]
    (X Y : DensityState (R × E)) (_ : SupportContained X Y)
    (_ : (partialTraceRight (raw Y)).PosDef) {e : ℝ} (_ : e ∈ Set.Icc (0 : ℝ) 1),
    let noisyLoss := op.readout () ⟨R, E, inferInstance, inferInstance,
      inferInstance, inferInstance, X, Y⟩ e
    0 ≤ noisyLoss ∧ noisyLoss ≤ (1-e) * loss X Y

private def parameters : StatePairParams.{u} :=
  ⟨Retained, Environment, inferInstance, inferInstance, inferInstance, inferInstance, source, reference⟩

private theorem identity_fails : ¬ arena.{u}.Law identity := by
  intro h
  have bad := (h source.{u} reference.{u} source_supported reference_marginal_faithful
    (e := 1) (by exact ⟨zero_le_one, le_rfl⟩)).2
  exact (not_le_of_gt source_loss_pos.{u}) (by
    change loss source.{u} reference.{u} ≤ (1 - 1) * loss source.{u} reference.{u} at bad
    simpa using bad)

def family : Registration arena.{u} (type_of% @noise_loss_contract.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@noise_loss_contract.{u}, identity, identity_fails⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual identity identity_fails
  dependence := by
    intro _
    refine ⟨parameters, 0, 1, ?_⟩
    change loss (noise source.{u} 0) (noise reference.{u} 0) ≠
      loss (noise source.{u} 1) (noise reference.{u} 1)
    rw [noise_zero, noise_zero]
    have h := noise_loss_contract source.{u} reference.{u} source_supported
      reference_marginal_faithful (e := 1) ⟨zero_le_one, le_rfl⟩
    have hz : loss (noise source.{u} 1) (noise reference.{u} 1) ≤ 0 := by
      simpa using h.2
    exact ne_of_gt (hz.trans_lt source_loss_pos)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@noise_loss_contract.{u}) (Realization observation.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzFixedMarginalNoise.noise_loss_contract.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzFixedMarginalNoise.Contraction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize observation (fun _ ⟨_, _, _, _, _, _, X, Y⟩ e =>
    loss (noise X e) (noise Y e)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzFixedMarginalNoise
    definition := none
    coordinates := #[0, 1, 8, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "value"]
      stateBinder := 12
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Contraction

namespace StrictScore

abbrev observation : Signature := signature ReferenceParams.{u} (fun _ => ℝ)
  (fun ⟨R, E, _, _, _, _, _⟩ => DensityState (R × E))

def actual : Realization observation.{u} :=
  realize observation (fun _ ⟨_, _, _, _, _, _, Y⟩ e => noise Y e) (fun e => nomatch e)

def identity : Realization observation.{u} :=
  realize observation (fun _ ⟨_, _, _, _, _, _, Y⟩ _ => Y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := observation.{u}
  Law op := ∀ {R E : Type u} [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype E] [DecidableEq E] [Nonempty E]
    (X Y : DensityState (R × E)) (_ : SupportContained X Y)
    (_ : (partialTraceRight (raw Y)).PosDef) (_ : 0 < loss X Y)
    {C : ℝ} (_ : C < errorSq X Y / loss X Y), ∃ e : ℝ,
      let Ynoisy := op.readout () ⟨R, E, inferInstance, inferInstance,
        inferInstance, inferInstance, Y⟩ e
      0 < e ∧ e < 1 ∧
      marginalRight (noise X e) = marginalRight X ∧
      marginalRight Ynoisy = marginalRight Y ∧
      (raw Ynoisy).PosDef ∧
      ((partialTraceRight (raw X)).PosDef → (raw (noise X e)).PosDef) ∧
      SupportContained (noise X e) Ynoisy ∧
      0 < loss (noise X e) Ynoisy ∧
      loss (noise X e) Ynoisy ≤ (1-e) * loss X Y ∧
      C < errorSq (noise X e) Ynoisy / loss (noise X e) Ynoisy

private def parameters : ReferenceParams.{u} :=
  ⟨Retained, Environment, inferInstance, inferInstance, inferInstance, inferInstance, reference⟩

private theorem identity_fails : ¬ arena.{u}.Law identity := by
  intro h
  obtain ⟨_, _, _, _, _, hfaithful, _⟩ :=
    h source.{u} reference.{u} source_supported reference_marginal_faithful
      source_loss_pos (C := 0) (div_pos source_error_pos source_loss_pos)
  exact reference_singular.{u} hfaithful

def family : Registration arena.{u} (type_of% @exists_strict_score_noise.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_strict_score_noise.{u}, identity, identity_fails⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual identity identity_fails
  dependence := by
    intro _
    obtain ⟨e, _, _, _, _, hfaithful, _⟩ :=
      exists_strict_score_noise source.{u} reference.{u} source_supported reference_marginal_faithful
        source_loss_pos (C := 0) (div_pos source_error_pos source_loss_pos)
    refine ⟨parameters, 0, e, ?_⟩
    change noise reference.{u} 0 ≠ noise reference.{u} e
    rw [noise_zero]
    intro h
    exact reference_singular.{u} (h ▸ hfaithful)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_strict_score_noise.{u}) (Realization observation.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzFixedMarginalNoise.exists_strict_score_noise.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzFixedMarginalNoise.StrictScore.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize observation (fun _ ⟨_, _, _, _, _, _, Y⟩ e => noise Y e) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzFixedMarginalNoise
    definition := none
    coordinates := #[0, 1, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "body", "value"]
      stateBinder := 15
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end StrictScore

end Reg.D5.S3.Quantum.Recovery.PetzFixedMarginalNoise
