/- GID: D5/S3/Quantum/Fibers/OriginalReferenceOperational
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/OriginalReferenceOperational
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete original quantum output and arbitrary-reference operational supremum. -/

import D5.S3.Quantum.Fibers.OriginalReferenceRepeatedMass

/-! Complete original classical--quantum outputs retain the whole reference. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace BigOperators Matrix TensorProduct
open Set Filter Topology MeasureTheory intervalIntegral TraceClassFiniteBlocks
namespace D5.S3.Quantum.Fibers.OriginalReferenceOperational
open OriginalControlMarkedJump OriginalReferenceKraus OriginalReferenceOutputMeasure
open OriginalReferenceRepeatedMass OriginalRepeatedPrefix OriginalControlComposition OriginalMarkedConcatenation
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! The complete classical--quantum output uses the literal Kraus success
branch as well as every retained mode/time failure density. -/

private def diagonalAction {m : ℕ} (d : Fin m → ℂ) :
    Blocks (Fin m) H →L[ℂ] Blocks (Fin m) H :=
  ∑ i, d i • embedding (ContinuousLinearMap.id ℂ H) i

private theorem diagonalAction_apply {m : ℕ} (d : Fin m → ℂ)
    (x : Blocks (Fin m) H) (i : Fin m) : diagonalAction d x i = d i • x i := by
  change coordinate i (diagonalAction d x) = _
  simp [diagonalAction, embedding, ContinuousLinearMap.comp_apply, coordinate, PiLp.single_apply]

/-- The original constant-phase successful Kraus, amplified by the unchanged reference. -/
def referenceSuccess (c a k S : ℝ) : Blocks (Fin 5) H →L[ℂ] Blocks (Fin 5) H :=
  diagonalAction (fun i => (Real.sqrt S : ℂ) * (Real.sqrt (p c k i / p c a i) : ℂ))

/-- The actual successful trace-class output; no normalization or dephasing. -/
def successOutput (c a k S : ℝ) (rho : TraceClass (Blocks (Fin 5) H)) :
    TraceClass (Blocks (Fin 5) H) :=
  TraceClass.ofOperator
    (referenceSuccess c a k S * rho.1 * (referenceSuccess c a k S).adjoint)
    (isTraceClass_mul_mul (TraceClass.isTraceClass_coe rho))

private theorem tensor_diagonal {m : ℕ} (d : Fin m → ℂ)
    (z : EuclideanSpace ℂ (Fin m) ⊗[ℂ] H) :
    diagonalAction d (tensorCoordinates z) = tensorCoordinates
      (TensorProduct.map (diagonalAction (H := ℂ) d).toLinearMap
        (LinearMap.id : H →ₗ[ℂ] H) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u x =>
    apply PiLp.ext
    intro i
    simp [diagonalAction_apply, tensorCoordinates_tmul, TensorProduct.map_tmul,
      smul_smul]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

private theorem terminal_success (B : Band) (n : ℕ) (hn : 1 ≤ n) (e : Bool) :
    let k := if e then B.early n hn else B.late n hn
    referenceSuccess (H := H) B.c B.a (k 2) (survival B.c k 2) =
      (Real.sqrt (B.q^(n+1)) : ℂ) • ContinuousLinearMap.id ℂ _ := by
  have hf := early_late_native_survival B n hn 0
  have he : (if e then B.early n hn else B.late n hn) 2 = B.a := by
    cases e <;> simp_all
  have hs : survival B.c (if e then B.early n hn else B.late n hn) 2 = B.q^(n+1) := by
    cases e <;> simp_all
  dsimp only
  rw [he, hs]
  ext x i
  simp [referenceSuccess, diagonalAction_apply, div_self (p_pos B.c B.a B.c_lt
    ⟨B.a_pos, B.ab.trans B.bc⟩ i).ne']

/-- The fixed absorbing successor and the unchanged reference, with exact time and mode. -/
def liveFailure (c a : ℝ) (k : ℝ → ℝ) (i : Fin 5)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) (t : ℝ) :
    TraceClass (Blocks (Fin 6) H) :=
  (modeCoefficient c a k i t : ℂ) • TraceClass.ofOperator
    (embedding (compression rho.1 i) (5 : Fin 6))
    (embedding_traceClass (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)
      (compression_nonneg hpos i) (5 : Fin 6))

private theorem liveFailure_diff_norm (c a : ℝ) (k l : ℝ → ℝ) (i : Fin 5)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) (t : ℝ) :
    ‖liveFailure c a k i rho hpos t - liveFailure c a l i rho hpos t‖ =
      ‖modeOutput c a k i rho hpos t - modeOutput c a l i rho hpos t‖ := by
  simp only [liveFailure, modeOutput, ← sub_smul, norm_smul, TraceClass.norm_eq_traceNorm]
  congr 1
  exact (embedding_trace_norm (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)
    (compression_nonneg hpos i) (5 : Fin 6)).2

private theorem liveFailure_actual (c a : ℝ) (k : ℝ → ℝ) (i : Fin 5)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) (t : ℝ) :
    (liveFailure c a k i rho hpos t).1 =
      (absorbingJump c a (k t) (survival c k t) (jumpRate c k t) i).comp
        (rho.1.comp (absorbingJump c a (k t) (survival c k t) (jumpRate c k t) i).adjoint) := by
  have he := congrArg (fun A : H →L[ℂ] H =>
    (insertion (5 : Fin 6)).comp (A.comp (coordinate (5 : Fin 6))))
    (actual_raw_jump_operator c a (k t) (survival c k t) (jumpRate c k t) i rho.1)
  change (modeCoefficient c a k i t : ℂ) • embedding (compression rho.1 i) (5 : Fin 6) = _
  simpa only [modeCoefficient, absorbingJump,
    ContinuousLinearMap.adjoint_comp, insertion, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc, embedding, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul] using he.symm

/-- IS.7 on the complete five-live-mode output, including the absorbing successor. -/
def liveDistance (c a T : ℝ) (k l : ℝ → ℝ)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) : ℝ :=
  (‖successOutput c a (k T) (survival c k T) rho -
      successOutput c a (l T) (survival c l T) rho‖ +
    ∑ i : Fin 5, ∫ t in Ioc (0 : ℝ) T,
      ‖liveFailure c a k i rho hpos t - liveFailure c a l i rho hpos t‖) / 2

/-- The successful tensor Kraus is common, and the complete IS.7 distance
has the asserted value for every positive joint input, without normalization. -/
theorem repeated_live_operational (B : Band) (n : ℕ) (hn : 1 ≤ n)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) :
    (∀ (c a k S : ℝ) (z : EuclideanSpace ℂ (Fin 5) ⊗[ℂ] H),
      referenceSuccess c a k S (tensorCoordinates z) = tensorCoordinates
        (TensorProduct.map (referenceSuccess (H := ℂ) c a k S).toLinearMap
          (LinearMap.id : H →ₗ[ℂ] H) z)) ∧
    (∀ (c a k S : ℝ) (x : EuclideanSpace ℂ (Fin 5)) (i : Fin 5),
      referenceSuccess (H := ℂ) c a k S x i =
        (successfulKraus c a k S *ᵥ x) i) ∧
    (∀ (c a : ℝ) (k : ℝ → ℝ) (i : Fin 5) (t : ℝ),
      (liveFailure c a k i rho hpos t).1 =
        (absorbingJump c a (k t) (survival c k t) (jumpRate c k t) i).comp
          (rho.1.comp (absorbingJump c a (k t) (survival c k t) (jumpRate c k t) i).adjoint)) ∧
    (∀ e : Bool, let k := if e then B.early n hn else B.late n hn
      referenceSuccess (H := H) B.c B.a (k 2) (survival B.c k 2) =
        (Real.sqrt (B.q^(n+1)) : ℂ) • ContinuousLinearMap.id ℂ _) ∧
    liveDistance B.c B.a 2 (B.early n hn) (B.late n hn) rho hpos =
      B.q^n*(1-B.q)*‖rho‖ := by
  refine ⟨fun c a k S z => tensor_diagonal _ z, ?_,
    fun c a k i t => liveFailure_actual c a k i rho hpos t,
    terminal_success B n hn, ?_⟩
  · intro c a k S x i
    simp [referenceSuccess, diagonalAction_apply, successfulKraus, Matrix.mulVec]
  have he : successOutput B.c B.a (B.early n hn 2)
      (survival B.c (B.early n hn) 2) rho =
      successOutput B.c B.a (B.late n hn 2)
        (survival B.c (B.late n hn) 2) rho := by
    apply Subtype.ext
    change _ * rho.1 * _ = _ * rho.1 * _
    have hs : referenceSuccess (H := H) B.c B.a (B.early n hn 2)
        (survival B.c (B.early n hn) 2) = referenceSuccess B.c B.a (B.late n hn 2)
          (survival B.c (B.late n hn) 2) :=
      by
        have hE := terminal_success (H := H) B n hn true
        have hL := terminal_success (H := H) B n hn false
        dsimp only at hE hL
        exact hE.trans hL.symm
    exact congrArg (fun K : Blocks (Fin 5) H →L[ℂ] Blocks (Fin 5) H => K * rho.1 * K.adjoint) hs
  simp_rw [liveDistance, liveFailure_diff_norm]
  rw [he, sub_self, norm_zero, zero_add,
    (repeated_reference_distance B n hn rho hpos).2]
  ring

private def sixBlock (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1)
    (i : Fin 6) : TraceClass H :=
  TraceClass.ofOperator (compression rho.1 i)
    (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)

/-- Initial live weight, with all six-coordinate coherences still present in the input. -/
def liveWeight (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1) : ℝ :=
  ∑ i : Fin 5, ‖sixBlock rho hpos i.castSucc‖

private def diagonalLive (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1) :
    TraceClass (Blocks (Fin 5) H) :=
  ∑ i : Fin 5, TraceClass.ofOperator (embedding (sixBlock rho hpos i.castSucc).1 i)
    (embedding_traceClass (TraceClass.isTraceClass_coe _) (compression_nonneg hpos _) i)

private theorem diagonalLive_pos (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1) :
    0 ≤ (diagonalLive rho hpos).1 := by
  change 0 ≤ ∑ i : Fin 5, embedding (compression rho.1 i.castSucc) i
  apply Finset.sum_nonneg
  intro i _
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  simpa only [embedding, insertion, ContinuousLinearMap.comp_assoc] using
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (compression_nonneg hpos i.castSucc)).adjoint_conj
      (coordinate i)

private theorem diagonalLive_compression (rho : TraceClass (Blocks (Fin 6) H))
    (hpos : 0 ≤ rho.1) (i : Fin 5) :
    compression (diagonalLive rho hpos).1 i = compression rho.1 i.castSucc := by
  ext x
  change coordinate i ((∑ j : Fin 5, embedding (compression rho.1 j.castSucc) j)
    (insertion i x)) = _
  simp [embedding, ContinuousLinearMap.comp_apply, coordinate, PiLp.single_apply]

private theorem diagonalLive_mass (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1) :
    ‖diagonalLive rho hpos‖ = liveWeight rho hpos := by
  rw [← actual_output_mass_partition _ (diagonalLive_pos rho hpos)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Subtype.ext
  exact diagonalLive_compression rho hpos i

private theorem liveWeight_partition (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1) :
    liveWeight rho hpos + ‖sixBlock rho hpos 5‖ = ‖rho‖ := by
  have ht := congrArg (Complex.reCLM : ℂ → ℝ)
    (trace_compression_sum (TraceClass.isTraceClass_coe rho) hpos)
  have hi (i : Fin 6) : ‖sixBlock rho hpos i‖ =
      (trace (compression rho.1 i) (compression_traceClass
        (TraceClass.isTraceClass_coe rho) hpos i)).re :=
    QuantumLogEnergy.traceNorm_eq_re_trace _ (compression_nonneg hpos i)
  have hn : ‖rho‖ = (trace rho.1 (TraceClass.isTraceClass_coe rho)).re :=
    QuantumLogEnergy.traceNorm_eq_re_trace _ hpos
  have ht' : (∑ i : Fin 6, (trace (compression rho.1 i)
      (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)).re) =
      (trace rho.1 (TraceClass.isTraceClass_coe rho)).re := by
    simpa only [map_sum, Complex.reCLM_apply] using ht
  rw [hn, ← ht']
  simp_rw [← hi]
  rw [Fin.sum_univ_castSucc]
  rfl

/-- OC.19a/OC.28: the no-new-failure Kraus is K direct-sum the stopped identity. -/
def stoppedSuccess (c a k S : ℝ) : Blocks (Fin 6) H →L[ℂ] Blocks (Fin 6) H :=
  diagonalAction (Fin.lastCases 1
    (fun i => (Real.sqrt S : ℂ) * (Real.sqrt (p c k i / p c a i) : ℂ)))

def stoppedSuccessOutput (c a k S : ℝ) (rho : TraceClass (Blocks (Fin 6) H)) :
    TraceClass (Blocks (Fin 6) H) :=
  TraceClass.ofOperator (stoppedSuccess c a k S * rho.1 * (stoppedSuccess c a k S).adjoint)
    (isTraceClass_mul_mul (TraceClass.isTraceClass_coe rho))

/-- OC.19b extended by zero on the already stopped input. -/
def stoppedJump (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5) :
    Blocks (Fin 6) H →L[ℂ] Blocks (Fin 6) H :=
  (insertion (5 : Fin 6)).comp (amplitude c a k S g i • coordinate i.castSucc)

private theorem tensor_stoppedJump (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5)
    (z : EuclideanSpace ℂ (Fin 6) ⊗[ℂ] H) :
    stoppedJump c a k S g i (tensorCoordinates z) = tensorCoordinates
      (TensorProduct.map (stoppedJump (H := ℂ) c a k S g i).toLinearMap
        (LinearMap.id : H →ₗ[ℂ] H) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u x =>
    apply PiLp.ext
    intro j
    change coordinate j (stoppedJump c a k S g i (tensorCoordinates (u ⊗ₜ[ℂ] x))) = _
    simp [stoppedJump, ContinuousLinearMap.comp_apply, tensorCoordinates_tmul,
      TensorProduct.map_tmul, coordinate, PiLp.single_apply, apply_ite, smul_smul]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

def stoppedFailure (c a : ℝ) (k : ℝ → ℝ) (i : Fin 5)
    (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1) (t : ℝ) :
    TraceClass (Blocks (Fin 6) H) :=
  (modeCoefficient c a k i t : ℂ) • TraceClass.ofOperator
    (embedding (compression rho.1 i.castSucc) (5 : Fin 6))
    (embedding_traceClass (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos _)
      (compression_nonneg hpos _) (5 : Fin 6))

/-- IS.7 for the supplier's six-dimensional carrier, on the original input. -/
def stoppedDistance (c a T : ℝ) (k l : ℝ → ℝ)
    (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1) : ℝ :=
  (‖stoppedSuccessOutput c a (k T) (survival c k T) rho -
      stoppedSuccessOutput c a (l T) (survival c l T) rho‖ +
    ∑ i : Fin 5, ∫ t in Ioc (0 : ℝ) T,
      ‖stoppedFailure c a k i rho hpos t - stoppedFailure c a l i rho hpos t‖) / 2

private theorem stoppedFailure_live (c a : ℝ) (k : ℝ → ℝ) (i : Fin 5)
    (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1) (t : ℝ) :
    stoppedFailure c a k i rho hpos t =
      liveFailure c a k i (diagonalLive rho hpos) (diagonalLive_pos rho hpos) t := by
  apply Subtype.ext
  change _ • embedding _ _ = _ • embedding _ _
  rw [diagonalLive_compression]

private theorem stoppedFailure_actual (c a : ℝ) (k : ℝ → ℝ) (i : Fin 5)
    (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1) (t : ℝ) :
    (stoppedFailure c a k i rho hpos t).1 =
      (stoppedJump c a (k t) (survival c k t) (jumpRate c k t) i).comp
        (rho.1.comp (stoppedJump c a (k t) (survival c k t) (jumpRate c k t) i).adjoint) := by
  change (modeCoefficient c a k i t : ℂ) •
    embedding (compression rho.1 i.castSucc) (5 : Fin 6) = _
  ext x : 1
  simp only [stoppedJump, modeCoefficient, embedding, compression,
    ContinuousLinearMap.adjoint_comp, map_smulₛₗ, insertion,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_apply,
    smul_apply, map_smul, smul_smul, RingHom.id_apply]
  change (Complex.normSq (amplitude c a (k t) (survival c k t) (jumpRate c k t) i) : ℂ) • _ =
    (star (amplitude c a (k t) (survival c k t) (jumpRate c k t) i) *
      amplitude c a (k t) (survival c k t) (jumpRate c k t) i) • _
  rw [mul_comm (star _) _, Complex.star_def, Complex.mul_conj]

private theorem stopped_terminal (B : Band) (n : ℕ) (hn : 1 ≤ n) (e : Bool) :
    let k := if e then B.early n hn else B.late n hn
    stoppedSuccess (H := H) B.c B.a (k 2) (survival B.c k 2) =
      diagonalAction (Fin.lastCases 1 (fun _ : Fin 5 => (Real.sqrt (B.q^(n+1)) : ℂ))) := by
  have hf := early_late_native_survival B n hn 0
  have he : (if e then B.early n hn else B.late n hn) 2 = B.a := by
    cases e <;> simp_all
  have hs : survival B.c (if e then B.early n hn else B.late n hn) 2 = B.q^(n+1) := by
    cases e <;> simp_all
  dsimp only
  rw [he, hs]
  unfold stoppedSuccess
  apply congrArg (diagonalAction (H := H))
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rfl
  · simp [div_self (p_pos B.c B.a B.c_lt ⟨B.a_pos, B.ab.trans B.bc⟩ i).ne']

/-- Arbitrary initially stopped mass and live/stopped coherences are retained.
The complete output distance equals the live weight times the original scalar. -/
theorem repeated_stopped_operational (B : Band) (n : ℕ) (hn : 1 ≤ n)
    (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1) :
    (∀ (c a k S : ℝ) (z : EuclideanSpace ℂ (Fin 6) ⊗[ℂ] H),
      stoppedSuccess c a k S (tensorCoordinates z) = tensorCoordinates
        (TensorProduct.map (stoppedSuccess (H := ℂ) c a k S).toLinearMap
          (LinearMap.id : H →ₗ[ℂ] H) z)) ∧
    (∀ (c a : ℝ) (k : ℝ → ℝ) (i : Fin 5) (t : ℝ),
      (stoppedFailure c a k i rho hpos t).1 =
        (stoppedJump c a (k t) (survival c k t) (jumpRate c k t) i).comp
          (rho.1.comp (stoppedJump c a (k t) (survival c k t) (jumpRate c k t) i).adjoint)) ∧
    (∀ (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5) (x : H),
      stoppedJump c a k S g i (insertion (5 : Fin 6) x) = 0) ∧
    stoppedSuccessOutput B.c B.a (B.early n hn 2) (survival B.c (B.early n hn) 2) rho =
      stoppedSuccessOutput B.c B.a (B.late n hn 2) (survival B.c (B.late n hn) 2) rho ∧
    stoppedDistance B.c B.a 2 (B.early n hn) (B.late n hn) rho hpos =
      B.q^n*(1-B.q)*liveWeight rho hpos ∧
    (‖rho‖ = 1 → stoppedDistance B.c B.a 2 (B.early n hn) (B.late n hn) rho hpos ≤
      B.q^n*(1-B.q)) ∧
    (∀ (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5)
      (z : EuclideanSpace ℂ (Fin 6) ⊗[ℂ] H),
      stoppedJump c a k S g i (tensorCoordinates z) = tensorCoordinates
        (TensorProduct.map (stoppedJump (H := ℂ) c a k S g i).toLinearMap
          (LinearMap.id : H →ₗ[ℂ] H) z)) ∧
    (∀ (c a k S : ℝ) (x : Blocks (Fin 6) H),
      (∀ i : Fin 5, stoppedSuccess c a k S x i.castSucc =
        ((Real.sqrt S : ℂ) * (Real.sqrt (p c k i / p c a i) : ℂ)) • x i.castSucc) ∧
      stoppedSuccess c a k S x 5 = x 5) := by
  have he : stoppedSuccessOutput B.c B.a (B.early n hn 2)
      (survival B.c (B.early n hn) 2) rho =
      stoppedSuccessOutput B.c B.a (B.late n hn 2)
        (survival B.c (B.late n hn) 2) rho := by
    apply Subtype.ext
    change _ * rho.1 * _ = _ * rho.1 * _
    have hE := stopped_terminal (H := H) B n hn true
    have hL := stopped_terminal (H := H) B n hn false
    dsimp only at hE hL
    exact congrArg (fun K : Blocks (Fin 6) H →L[ℂ] Blocks (Fin 6) H => K * rho.1 * K.adjoint) (hE.trans hL.symm)
  have hd : stoppedDistance B.c B.a 2 (B.early n hn) (B.late n hn) rho hpos =
      B.q^n*(1-B.q)*liveWeight rho hpos := by
    have hl := (repeated_live_operational B n hn (diagonalLive rho hpos)
      (diagonalLive_pos rho hpos)).2.2.2.2
    rw [diagonalLive_mass] at hl
    rw [stoppedDistance, he, sub_self, norm_zero, zero_add]
    simp_rw [stoppedFailure_live]
    rw [liveDistance] at hl
    have hE := terminal_success (H := H) B n hn true
    have hL := terminal_success (H := H) B n hn false
    dsimp only at hE hL
    have hs := hE.trans hL.symm
    have ho : successOutput B.c B.a (B.early n hn 2) (survival B.c (B.early n hn) 2)
        (diagonalLive rho hpos) = successOutput B.c B.a (B.late n hn 2)
          (survival B.c (B.late n hn) 2) (diagonalLive rho hpos) := by
      apply Subtype.ext
      change _ * _ * _ = _ * _ * _
      exact congrArg (fun K : Blocks (Fin 5) H →L[ℂ] Blocks (Fin 5) H =>
        K * (diagonalLive rho hpos).1 * K.adjoint) hs
    simpa only [ho, sub_self, norm_zero, zero_add] using hl
  refine ⟨fun c a k S z => tensor_diagonal _ z,
    fun c a k i t => stoppedFailure_actual c a k i rho hpos t, ?_, he, hd, ?_,
    tensor_stoppedJump, ?_⟩
  · intro c a k S g i x
    have hi : i.castSucc ≠ (5 : Fin 6) := i.castSucc_ne_last
    simp [stoppedJump, ContinuousLinearMap.comp_apply, coordinate, PiLp.single_apply, hi]
  · intro hnorm
    rw [hd]
    have hw : liveWeight rho hpos ≤ 1 := by
      have hp := liveWeight_partition rho hpos
      rw [hnorm] at hp
      linarith [norm_nonneg (sixBlock rho hpos 5)]
    have hq := early_late_native_survival B n hn 0
    exact (mul_le_mul_of_nonneg_left hw
      (mul_nonneg (pow_nonneg hq.1.le _) (sub_nonneg.mpr hq.2.1.le))).trans_eq (mul_one _)
  · intro c a k S x
    constructor
    · intro i
      simp [stoppedSuccess, diagonalAction_apply]
    · change diagonalAction _ x (Fin.last 5) = x (Fin.last 5)
      simp [diagonalAction_apply]

universe v

/-- A normalized joint input with a reference in any fixed universe. -/
structure JointState (m : ℕ) where
  Ref : Type v
  [normed : NormedAddCommGroup Ref]
  [inner : InnerProductSpace ℂ Ref]
  [complete : CompleteSpace Ref]
  rho : TraceClass (Blocks (Fin m) Ref)
  positive : 0 ≤ rho.1
  normalized : ‖rho‖ = 1

attribute [instance] JointState.normed JointState.inner JointState.complete

/-- The genuine IS.7 supremum, indexed by all normalized inputs and references
in the chosen universe; its definition contains no proposed scalar value. -/
def operationalDistance (c a T : ℝ) (k l : ℝ → ℝ) : ℝ :=
  sSup {x : ℝ | ∃ s : JointState.{v} 6,
    x = stoppedDistance c a T k l s.rho s.positive}

private abbrev witnessReference := EuclideanSpace ℂ (ULift.{v} Unit)

private def witnessBase : TraceClass witnessReference.{v} :=
  TraceClass.ofOperator (ContinuousLinearMap.id ℂ _)
    (isTraceClass_of_finiteDimensional _)

private theorem witnessBase_pos : 0 ≤ witnessBase.{v}.1 := by
  change (0 : witnessReference.{v} →L[ℂ] witnessReference.{v}) ≤ 1
  exact zero_le_one

private theorem witnessBase_norm : ‖witnessBase.{v}‖ = 1 := by
  rw [TraceClass.norm_eq_traceNorm, QuantumLogEnergy.traceNorm_eq_re_trace _ witnessBase_pos]
  have ht : trace witnessBase.{v}.1 (TraceClass.isTraceClass_coe _) = 1 := by
    have hf : HasFiniteMultiplicity (1 : witnessReference.{v} →L[ℂ] witnessReference.{v}) :=
      ⟨.one _, isTraceClass_of_finiteDimensional _⟩
    have hv := hf.trace_eq_finrank_range
    have hr : LinearMap.range (1 : witnessReference.{v} →L[ℂ] witnessReference.{v}).toLinearMap = ⊤ := by
      ext x
      simp
    rw [hr] at hv
    simpa using hv
  exact congrArg Complex.re ht

private def fullyLive : TraceClass (Blocks (Fin 6) witnessReference.{v}) :=
  TraceClass.ofOperator (embedding witnessBase.{v}.1 (0 : Fin 6))
    (embedding_traceClass (TraceClass.isTraceClass_coe _) witnessBase_pos _)

private theorem fullyLive_pos : 0 ≤ fullyLive.{v}.1 := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  simpa only [fullyLive, TraceClass.ofOperator_coe, embedding, insertion,
    ContinuousLinearMap.comp_assoc] using
    (ContinuousLinearMap.nonneg_iff_isPositive.mp witnessBase_pos).adjoint_conj
      (coordinate (0 : Fin 6))

private theorem fullyLive_norm : ‖fullyLive.{v}‖ = 1 :=
  (embedding_trace_norm (TraceClass.isTraceClass_coe _) witnessBase_pos (0 : Fin 6)).2.trans
    witnessBase_norm

private theorem fullyLive_weight : liveWeight fullyLive.{v} fullyLive_pos = 1 := by
  have hp := liveWeight_partition fullyLive.{v} fullyLive_pos
  have hz : sixBlock fullyLive.{v} fullyLive_pos 5 = 0 := by
    apply Subtype.ext
    ext x : 1
    change coordinate (5 : Fin 6)
      (embedding witnessBase.{v}.1 (0 : Fin 6) (insertion 5 x)) = 0
    simp [embedding, ContinuousLinearMap.comp_apply, coordinate, PiLp.single_apply]
  simpa [hz, fullyLive_norm] using hp

/-- Every universe admits a fully live attaining state. The independently
defined supremum equals the original complete marked-law supplier. -/
theorem repeated_operational_supremum (B : Band) (n : ℕ) (hn : 1 ≤ n) :
    (∀ (s : JointState.{v} 5),
      liveDistance B.c B.a 2 (B.early n hn) (B.late n hn) s.rho s.positive =
        B.q^n*(1-B.q)) ∧
    (∃ s : JointState.{v} 6, liveWeight s.rho s.positive = 1 ∧
      stoppedDistance B.c B.a 2 (B.early n hn) (B.late n hn) s.rho s.positive =
        B.q^n*(1-B.q)) ∧
    operationalDistance.{v} B.c B.a 2 (B.early n hn) (B.late n hn) = B.q^n*(1-B.q) ∧
    (∀ (beta : ℝ) (m : ℤ) (theta : Fin 5 → ℝ),
      OriginalRepeatedMarkedLaw.eventTV
        (markedLaw B.c B.a beta 2 m theta (B.early n hn))
        (markedLaw B.c B.a beta 2 m theta (B.late n hn)) =
      operationalDistance.{v} B.c B.a 2 (B.early n hn) (B.late n hn)) := by
  have hbound (s : JointState.{v} 6) :
      stoppedDistance B.c B.a 2 (B.early n hn) (B.late n hn) s.rho s.positive ≤
        B.q^n*(1-B.q) :=
    (repeated_stopped_operational B n hn s.rho s.positive).2.2.2.2.2.1 s.normalized
  let witness : JointState.{v} 6 :=
    ⟨witnessReference.{v}, fullyLive.{v}, fullyLive_pos, fullyLive_norm⟩
  have hw : liveWeight witness.rho witness.positive = 1 := fullyLive_weight
  have ha : stoppedDistance B.c B.a 2 (B.early n hn) (B.late n hn)
      witness.rho witness.positive = B.q^n*(1-B.q) := by
    rw [(repeated_stopped_operational B n hn witness.rho witness.positive).2.2.2.2.1, hw, mul_one]
  have hop : operationalDistance.{v} B.c B.a 2 (B.early n hn) (B.late n hn) =
      B.q^n*(1-B.q) := by
    apply le_antisymm
    · apply csSup_le
      · exact ⟨_, witness, rfl⟩
      · rintro x ⟨s, rfl⟩
        exact hbound s
    · apply le_csSup
      · exact ⟨_, by rintro x ⟨s, rfl⟩; exact hbound s⟩
      · exact ⟨witness, ha.symm⟩
  refine ⟨?_, ⟨witness, hw, ha⟩, hop, ?_⟩
  · intro s
    simpa only [s.normalized, mul_one] using
      (repeated_live_operational B n hn s.rho s.positive).2.2.2.2
  · intro beta m theta
    rw [hop]
    exact (OriginalRepeatedMarkedLaw.native_marked_tv B n hn beta m theta).2.2.2

end D5.S3.Quantum.Fibers.OriginalReferenceOperational
