/- GID: D5/S3/Quantum/Fibers/OriginalDownstreamOutput
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/OriginalDownstreamOutput
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common mass-nonincreasing joint execution on the actual original cq output. -/

import D5.S3.Quantum.Fibers.OriginalCompleteOutputStability
import D5.S3.Quantum.Analysis.TraceClass.RecordedOutput

/-! The retained joint output, its actual execution, and independent permissions. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
open Set MeasureTheory TraceClassFiniteBlocks TraceClassRecordedOutput

namespace D5.S3.Quantum.Fibers.OriginalDownstreamOutput
open OriginalControlMarkedJump OriginalReferenceKraus OriginalReferenceOutputMeasure
open OriginalReferenceRepeatedMass OriginalControlComposition OriginalCompleteOutputStability

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev Carrier (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : ℝ) := Output (Blocks (Fin 5) H) (Blocks (Fin 6) H) (Fin 5)
      (volume.restrict (Ioc (0 : ℝ) T))

private def absorbingBlock (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1)
    (i : Fin 5) : TraceClass (Blocks (Fin 6) H) :=
  TraceClass.ofOperator (embedding (compression rho.1 i) (5 : Fin 6))
    (embedding_traceClass (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)
      (compression_nonneg hpos i) (5 : Fin 6))

private theorem coefficient_integrable (c a T : ℝ) (k chi : ℝ → ℝ)
    (hc : c < 1 / 2) (ha : a ∈ Ioo 0 c)
    (hk : OriginalControl (c, c, 1 - 2 * c) T k chi) (i : Fin 5) :
    IntegrableOn (modeCoefficient c a k i) (Ioc (0 : ℝ) T) :=
  (native_mode_balance c a T k hc ha (height_control c T k chi hk) i 0 T
    ⟨le_rfl,hk.1⟩ ⟨hk.1,le_rfl⟩ hk.1).1

private theorem failure_integrable (c a T : ℝ) (k chi : ℝ → ℝ)
    (hc : c < 1 / 2) (ha : a ∈ Ioo 0 c)
    (hk : OriginalControl (c, c, 1 - 2 * c) T k chi)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) (i : Fin 5) :
    IntegrableOn (fun t => phasedFailure c a k chi t i rho hpos) (Ioc (0 : ℝ) T) := by
  simp only [phasedFailure_eq]
  exact (coefficient_integrable c a T k chi hc ha hk i).ofReal.smul_const _

/-- The literal success output and all five exact-time absorbing failure densities. -/
def output (c a T : ℝ) (k chi : ℝ → ℝ)
    (hc : c < 1 / 2) (ha : a ∈ Ioo 0 c)
    (hk : OriginalControl (c, c, 1 - 2 * c) T k chi)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) : Carrier H T :=
  pack _ (terminalOutput c a k chi T rho)
    (fun i t => phasedFailure c a k chi t i rho hpos)
    (failure_integrable c a T k chi hc ha hk rho hpos)

private theorem terminal_positive (c a T : ℝ) (k chi : ℝ → ℝ)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) :
    0 ≤ (terminalOutput c a k chi T rho).1 := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  simpa only [terminalOutput,TraceClass.ofOperator_coe,ContinuousLinearMap.mul_def,
    ContinuousLinearMap.adjoint_adjoint,ContinuousLinearMap.comp_assoc] using
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hpos).adjoint_conj
      (terminalKraus (H := H) c a k chi T).adjoint

private theorem difference_pack (c a T : ℝ) (k chi l psi : ℝ → ℝ)
    (hc : c < 1 / 2) (ha : a ∈ Ioo 0 c)
    (hk : OriginalControl (c, c, 1 - 2 * c) T k chi)
    (hl : OriginalControl (c, c, 1 - 2 * c) T l psi)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) :
    output c a T k chi hc ha hk rho hpos - output c a T l psi hc ha hl rho hpos =
      pack _ (terminalOutput c a k chi T rho - terminalOutput c a l psi T rho)
        (fun i t => (modeCoefficient c a k i t - modeCoefficient c a l i t) •
          absorbingBlock rho hpos i)
        (fun i => ((coefficient_integrable c a T k chi hc ha hk i).sub
          (coefficient_integrable c a T l psi hc ha hl i)).smul_const _) := by
  apply (WithLp.equiv 1 _).injective
  apply Prod.ext
  · rfl
  · apply (WithLp.equiv 1 _).injective
    funext i
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub
        ((failure_integrable c a T k chi hc ha hk rho hpos i).toL1 _)
        ((failure_integrable c a T l psi hc ha hl rho hpos i).toL1 _),
      (failure_integrable c a T k chi hc ha hk rho hpos i).coeFn_toL1,
      (failure_integrable c a T l psi hc ha hl rho hpos i).coeFn_toL1,
      (((coefficient_integrable c a T k chi hc ha hk i).sub
        (coefficient_integrable c a T l psi hc ha hl i)).smul_const
          (absorbingBlock rho hpos i)).coeFn_toL1] with t he hk' hl' hd
    change (((failure_integrable c a T k chi hc ha hk rho hpos i).toL1 _) -
      ((failure_integrable c a T l psi hc ha hl rho hpos i).toL1 _)) t = _
    rw [he,Pi.sub_apply,hk',hl']
    change _ = (((((coefficient_integrable c a T k chi hc ha hk i).sub
      (coefficient_integrable c a T l psi hc ha hl i)).smul_const
        (absorbingBlock rho hpos i)).toL1 _) t)
    rw [hd,phasedFailure_eq,phasedFailure_eq]
    apply Subtype.ext
    change (modeCoefficient c a k i t : ℂ) • embedding (compression rho.1 i) (5 : Fin 6) -
      (modeCoefficient c a l i t : ℂ) • embedding (compression rho.1 i) (5 : Fin 6) =
        (((modeCoefficient c a k i t - modeCoefficient c a l i t : ℝ) : ℂ)) •
          embedding (compression rho.1 i) (5 : Fin 6)
    rw [Complex.ofReal_sub,sub_smul]

/-- The genuine additive cq norm is exactly twice the delivered complete distance IS.7. -/
theorem output_distance (c a T : ℝ) (k chi l psi : ℝ → ℝ)
    (hc : c < 1 / 2) (ha : a ∈ Ioo 0 c)
    (hk : OriginalControl (c, c, 1 - 2 * c) T k chi)
    (hl : OriginalControl (c, c, 1 - 2 * c) T l psi)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) :
    ‖output c a T k chi hc ha hk rho hpos - output c a T l psi hc ha hl rho hpos‖ / 2 =
      completeDistance c a T k chi l psi rho hpos := by
  rw [WithLp.prod_norm_eq_of_L1,PiLp.norm_eq_of_L1]
  unfold completeDistance
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub
      ((failure_integrable c a T k chi hc ha hk rho hpos i).toL1 _)
      ((failure_integrable c a T l psi hc ha hl rho hpos i).toL1 _),
    (failure_integrable c a T k chi hc ha hk rho hpos i).coeFn_toL1,
    (failure_integrable c a T l psi hc ha hl rho hpos i).coeFn_toL1] with t he hk' hl'
  change ‖((((failure_integrable c a T k chi hc ha hk rho hpos i).toL1 _) -
    ((failure_integrable c a T l psi hc ha hl rho hpos i).toL1 _)) t)‖ = _
  rw [he,Pi.sub_apply,hk',hl']

/-- A target carries its actual positive norm/mass law and its complete output distance. -/
structure Target (W : Type*) [SeminormedAddCommGroup W] [NormedSpace ℝ W] where
  positive : W → Prop
  mass : W →L[ℝ] ℝ
  positive_norm : ∀ w, positive w → ‖w‖ = mass w
  distance : W → W → ℝ
  distance_eq : ∀ x y, distance x y = ‖x - y‖ / 2

/-- The same four source context fields are used in the two executions. -/
structure Context (Policy Reference Permission External : Type*) where
  policy : Policy
  reference : Reference
  permission : Permission
  external : External

/-- A lawful semantic realization agrees with the independently specified complete execution.
Permissions are independent of the quantitative conclusion. No round bound or program grammar
is imposed. The map laws hold on all joint positive inputs, including the norming parts. -/
structure Realization {W Program Policy Reference Permission External : Type*}
    [SeminormedAddCommGroup W] [NormedSpace ℝ W] {T : ℝ}
    (target : Target W)
    (run : Program → Context Policy Reference Permission External → Carrier H T → W)
    (allowed : Program → Context Policy Reference Permission External → Prop)
    (program : Program) (context : Context Policy Reference Permission External) where
  permitted : allowed program context
  action : Carrier H T →ₗ[ℝ] W
  agrees : ∀ q, action q = run program context q
  positive : ∀ q, Positive q → target.positive (action q)
  mass_nonincreasing : ∀ q, Positive q → target.mass (action q) ≤ mass q

/-- Every common lawful realized protocol contracts the actual original complete output.
The estimate is unnormalized and concerns all declared failure/abort successors in run. -/
theorem downstream_distance_le
    {W Program Policy Reference Permission External : Type*}
    [SeminormedAddCommGroup W] [NormedSpace ℝ W]
    (c a T : ℝ) (k chi l psi : ℝ → ℝ)
    (hc : c < 1 / 2) (ha : a ∈ Ioo 0 c)
    (hk : OriginalControl (c, c, 1 - 2 * c) T k chi)
    (hl : OriginalControl (c, c, 1 - 2 * c) T l psi)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1)
    (target : Target W)
    (run : Program → Context Policy Reference Permission External → Carrier H T → W)
    (allowed : Program → Context Policy Reference Permission External → Prop)
    (program : Program) (context : Context Policy Reference Permission External)
    (R : Realization target run allowed program context) :
    target.distance (run program context (output c a T k chi hc ha hk rho hpos))
      (run program context (output c a T l psi hc ha hl rho hpos)) ≤
        completeDistance c a T k chi l psi rho hpos := by
  rw [target.distance_eq,← R.agrees,← R.agrees,← map_sub,
    ← output_distance c a T k chi l psi hc ha hk hl rho hpos]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rw [difference_pack]
  refine fixed_block_contracts _ _ ?_ (absorbingBlock rho hpos) ?_
    (fun i t => modeCoefficient c a k i t - modeCoefficient c a l i t)
    (fun i => (coefficient_integrable c a T k chi hc ha hk i).sub
      (coefficient_integrable c a T l psi hc ha hl i))
    target.positive target.mass target.positive_norm R.action ?_
  · change IsSelfAdjoint ((terminalOutput c a k chi T rho).1 -
      (terminalOutput c a l psi T rho).1)
    exact (IsSelfAdjoint.of_nonneg (terminal_positive c a T k chi rho hpos)).sub
      (IsSelfAdjoint.of_nonneg (terminal_positive c a T l psi rho hpos))
  · intro i
    exact embedding_nonneg (compression_nonneg hpos i) (5 : Fin 6)
  · intro q hq
    exact ⟨R.positive q hq,R.mass_nonincreasing q hq⟩

universe v w

/-- Uniformly over the same joint-input supremum, realized common downstream executions
obey the already proved IS.27 error bound, including arbitrary unchanged references. -/
theorem downstream_operational_bound
    {Program Policy Reference Permission External : Type*}
    (c a T : ℝ) (k chi l psi : ℝ → ℝ)
    (hc : c < 1 / 2) (ha : a ∈ Ioo 0 c)
    (hk : OriginalControl (c, c, 1 - 2 * c) T k chi)
    (hl : OriginalControl (c, c, 1 - 2 * c) T l psi)
    (hk0 : k 0 = a) (hl0 : l 0 = a)
    (W : JointState.{v} 5 → Type w)
    [∀ s, SeminormedAddCommGroup (W s)] [∀ s, NormedSpace ℝ (W s)]
    (target : ∀ s, Target (W s))
    (run : ∀ s : JointState.{v} 5,
      Program → Context Policy Reference Permission External → Carrier s.Ref T → W s)
    (allowed : Program → Context Policy Reference Permission External → Prop)
    (program : Program) (context : Context Policy Reference Permission External)
    (R : ∀ s, Realization (target s) (run s) allowed program context) :
    sSup {x : ℝ | ∃ s : JointState.{v} 5, x =
      (target s).distance
        (run s program context (output c a T k chi hc ha hk s.rho s.positive))
        (run s program context (output c a T l psi hc ha hl s.rho s.positive))} ≤
      krausError c a T k chi l psi +
        (Finset.univ.sup' Finset.univ_nonempty (densityError c a T k l)) / 2 := by
  have hb : BddAbove {x : ℝ | ∃ s : JointState.{v} 5,
      x = completeDistance c a T k chi l psi s.rho s.positive} := by
    refine ⟨krausError c a T k chi l psi +
      (Finset.univ.sup' Finset.univ_nonempty (densityError c a T k l)) / 2,?_⟩
    rintro x ⟨s,rfl⟩
    simpa only [s.normalized,mul_one] using
      complete_output_bound c a T k chi l psi hc ha hk hl hk0 hl0 s.rho s.positive
        (Finset.univ.sup' Finset.univ_nonempty (densityError c a T k l))
        (fun i => Finset.le_sup' _ (Finset.mem_univ i))
  apply le_trans _ (complete_operational_bound.{v} c a T k chi l psi hc ha hk hl hk0 hl0)
  apply csSup_le
  · exact ⟨_,normalizedLive.{v},rfl⟩
  · rintro x ⟨s,rfl⟩
    exact (downstream_distance_le c a T k chi l psi hc ha hk hl s.rho s.positive
      (target s) (run s) allowed program context (R s)).trans (le_csSup hb ⟨s,rfl⟩)

end D5.S3.Quantum.Fibers.OriginalDownstreamOutput
