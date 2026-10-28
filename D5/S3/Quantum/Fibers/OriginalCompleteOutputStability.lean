/- GID: D5/S3/Quantum/Fibers/OriginalCompleteOutputStability
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/OriginalCompleteOutputStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stability of the actual original complete quantum output on an unchanged reference. -/

import D5.S3.Quantum.Fibers.OriginalReferenceRepeatedMass
import D5.S3.TotalVariation.Hellinger

/-! The terminal congruence and all five time densities use one common joint input. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace BigOperators Matrix TensorProduct
open Set Filter Topology MeasureTheory intervalIntegral TraceClassFiniteBlocks

namespace D5.S3.Quantum.Fibers.OriginalCompleteOutputStability
open OriginalControlMarkedJump OriginalReferenceKraus OriginalReferenceOutputMeasure
open OriginalReferenceRepeatedMass OriginalControlComposition OriginalMarkedConcatenation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Forgetting the phase coordinate preserves original admissibility of the height. -/
theorem height_control (c T : ℝ) (k chi : ℝ → ℝ)
    (hk : OriginalControl (c,c,1-2*c) T k chi) :
    OriginalControl (c,c,1-2*c) T k (fun _ => (0 : ℝ)) := by
  refine ⟨hk.1,hk.2.1,continuousOn_const,hk.2.2.2.1,?_,Or.inl ⟨(original_ac _ _ _ _ hk).1,?_⟩⟩
  · exact (LipschitzWith.const (0 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval.boundedVariationOn
  · exact (LipschitzWith.const (0 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval

/-- The transported terminal character retains the original real phase integral. -/
def character (c : ℝ) (k chi : ℝ → ℝ) (t : ℝ) (i : Fin 5) : ℂ :=
  Complex.exp (-(∫ u in (0 : ℝ)..t,
    FiniteRectangleTransport.phaseWeight (c,c,1-2*c) (k u) i * deriv chi u) * Complex.I)

/-- The genuine successful diagonal, with its terminal phase, on every reference block. -/
def terminalDiagonal (c a : ℝ) (k chi : ℝ → ℝ) (t : ℝ) (i : Fin 5) : ℂ :=
  (Real.sqrt (survival c k t) : ℂ) *
    (Real.sqrt (p c (k t) i / p c a i) : ℂ) * character c k chi t i

def terminalKraus (c a : ℝ) (k chi : ℝ → ℝ) (t : ℝ) :
    Blocks (Fin 5) H →L[ℂ] Blocks (Fin 5) H :=
  diagonalAction (terminalDiagonal c a k chi t)

def terminalOutput (c a : ℝ) (k chi : ℝ → ℝ) (t : ℝ)
    (rho : TraceClass (Blocks (Fin 5) H)) : TraceClass (Blocks (Fin 5) H) :=
  TraceClass.ofOperator
    (terminalKraus c a k chi t * rho.1 * (terminalKraus c a k chi t).adjoint)
    (isTraceClass_mul_mul (TraceClass.isTraceClass_coe rho))

/-- The literal failure Kraus with the transported phase, on the same input blocks. -/
def phasedJump (c a : ℝ) (k chi : ℝ → ℝ) (t : ℝ) (i : Fin 5) :
    Blocks (Fin 5) H →L[ℂ] Blocks (Fin 6) H :=
  (absorbingJump c a (k t) (survival c k t) (jumpRate c k t) i).comp
    (diagonalAction (character c k chi t))

private theorem phasedJump_scalar (c a : ℝ) (k chi : ℝ → ℝ) (t : ℝ) (i : Fin 5) :
    phasedJump (H := H) c a k chi t i = character c k chi t i •
      absorbingJump c a (k t) (survival c k t) (jumpRate c k t) i := by
  apply ContinuousLinearMap.ext
  intro x
  rw [phasedJump,absorbingJump,referenceJump_factor]
  change insertion (5 : Fin 6)
      (amplitude c a (k t) (survival c k t) (jumpRate c k t) i •
        diagonalAction (character c k chi t) x i) =
    character c k chi t i • insertion (5 : Fin 6)
      (amplitude c a (k t) (survival c k t) (jumpRate c k t) i • x i)
  rw [diagonalAction_apply]
  simp only [map_smul,smul_smul,mul_comm]

/-- The failure density is the genuine phased Kraus congruence; its phase cancels. -/
theorem phased_failure_actual (c a : ℝ) (k chi : ℝ → ℝ) (t : ℝ) (i : Fin 5)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) :
    (liveFailure c a k i rho hpos t).1 =
      (phasedJump c a k chi t i).comp
        (rho.1.comp (phasedJump c a k chi t i).adjoint) := by
  rw [phasedJump_scalar,ContinuousLinearMap.adjoint_smul]
  simp only [ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul,smul_smul]
  have hz : character c k chi t i * star (character c k chi t i) = 1 := by
    rw [Complex.star_def,Complex.mul_conj']
    simp [character,Complex.norm_exp_ofReal_mul_I]
  rw [hz,one_smul]
  exact liveFailure_actual c a k i rho hpos t

/-- The actual phased Kraus density, before integration over any recorded time event. -/
def phasedFailure (c a : ℝ) (k chi : ℝ → ℝ) (t : ℝ) (i : Fin 5)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) :
    TraceClass (Blocks (Fin 6) H) :=
  TraceClass.ofOperator
    ((phasedJump c a k chi t i).comp (rho.1.comp (phasedJump c a k chi t i).adjoint))
    (by rw [← phased_failure_actual c a k chi t i rho hpos]
        exact TraceClass.isTraceClass_coe _)

private theorem phasedFailure_eq (c a : ℝ) (k chi : ℝ → ℝ) (t : ℝ) (i : Fin 5)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) :
    phasedFailure c a k chi t i rho hpos = liveFailure c a k i rho hpos t :=
  Subtype.ext (phased_failure_actual c a k chi t i rho hpos).symm

/-- The same complete output norm as IS.7, with no time integration before the norm. -/
def completeDistance (c a T : ℝ) (k chi l psi : ℝ → ℝ)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) : ℝ :=
  (‖terminalOutput c a k chi T rho - terminalOutput c a l psi T rho‖ +
    ∑ i : Fin 5, ∫ t in Ioc (0 : ℝ) T,
      ‖phasedFailure c a k chi t i rho hpos - phasedFailure c a l psi t i rho hpos‖) / 2

/-- Every actual Borel failure event is a Bochner integral on the retained reference. -/
theorem native_failure_bochner (c a T : ℝ) (k chi : ℝ → ℝ)
    (hc : c < 1/2) (ha : a ∈ Ioo 0 c)
    (hk : OriginalControl (c,c,1-2*c) T k chi)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1)
    (i : Fin 5) (E : Set ℝ) (_hE : MeasurableSet E) :
    IntegrableOn (fun t => phasedFailure c a k chi t i rho hpos) ((Ioc 0 T) ∩ E) := by
  have hi := (native_mode_balance c a T k hc ha (height_control c T k chi hk)
    i 0 T ⟨le_rfl,hk.1⟩ ⟨hk.1,le_rfl⟩ hk.1).1
  simp_rw [phasedFailure_eq]
  exact (hi.ofReal.smul_const _).mono_set inter_subset_left

/-- A trace-class congruence, also for nonpositive mixed terms in a difference. -/
def congruence (A : H →L[ℂ] H) (rho : TraceClass H) : TraceClass H :=
  TraceClass.ofOperator (A * rho.1 * A.adjoint)
    (isTraceClass_mul_mul (TraceClass.isTraceClass_coe rho))

private theorem congruence_difference (A B : H →L[ℂ] H) (rho : TraceClass H) :
    ‖congruence A rho - congruence B rho‖ ≤
      (‖A‖ + ‖B‖) * ‖A-B‖ * ‖rho‖ := by
  let X : TraceClass H := TraceClass.ofOperator ((A-B) * rho.1 * A.adjoint)
    (isTraceClass_mul_mul (TraceClass.isTraceClass_coe rho))
  let Y : TraceClass H := TraceClass.ofOperator (B * rho.1 * (A-B).adjoint)
    (isTraceClass_mul_mul (TraceClass.isTraceClass_coe rho))
  have he : congruence A rho - congruence B rho = X + Y := by
    apply Subtype.ext
    change A * rho.1 * A.adjoint - B * rho.1 * B.adjoint =
      (A-B) * rho.1 * A.adjoint + B * rho.1 * (A-B).adjoint
    rw [ContinuousLinearMap.adjoint_sub]
    noncomm_ring
  have hx : ‖X‖ ≤ ‖A-B‖ * ‖rho‖ * ‖A‖ := by
    change traceNorm _ _ ≤ ‖A-B‖ * traceNorm rho.1 _ * ‖A‖
    simpa only [ContinuousLinearMap.adjoint.norm_map] using
      (traceNorm_mul_mul_le (TraceClass.isTraceClass_coe rho)
        (isTraceClass_mul_mul (A := A-B) (B := A.adjoint) (TraceClass.isTraceClass_coe rho)))
  have hy : ‖Y‖ ≤ ‖B‖ * ‖rho‖ * ‖A-B‖ := by
    change traceNorm _ _ ≤ ‖B‖ * traceNorm rho.1 _ * ‖A-B‖
    simpa only [ContinuousLinearMap.adjoint.norm_map] using
      (traceNorm_mul_mul_le (TraceClass.isTraceClass_coe rho)
        (isTraceClass_mul_mul (A := B) (B := (A-B).adjoint) (TraceClass.isTraceClass_coe rho)))
  rw [he]
  exact (norm_add_le X Y).trans ((add_le_add hx hy).trans_eq (by ring))

private theorem diagonal_norm_le {m : ℕ} (d : Fin m → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hd : ∀ i, ‖d i‖ ≤ C) :
    ‖diagonalAction (H := H) d‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [diagonalAction_apply,norm_smul,mul_pow]
  exact mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ (norm_nonneg _) hC).mpr (hd i)) (sq_nonneg _)

/-- Native mode balance makes every actual surviving diagonal a contraction. -/
theorem native_mass_le (c a T : ℝ) (k chi : ℝ → ℝ)
    (hc : c < 1/2) (ha : a ∈ Ioo 0 c)
    (hk : OriginalControl (c,c,1-2*c) T k chi) (h0 : k 0 = a)
    (t : ℝ) (ht : t ∈ Icc 0 T) (i : Fin 5) :
    survival c k t * p c (k t) i ≤ p c a i := by
  have h := (native_mode_balance c a T k hc ha (height_control c T k chi hk)
    i 0 t ⟨le_rfl,hk.1⟩ ht ht.1).2
  have hn : 0 ≤ ∫ u in Ioc (0 : ℝ) t, modeCoefficient c a k i u :=
    integral_nonneg (fun _ => Complex.normSq_nonneg _)
  rw [h,h0] at hn
  simp only [OriginalControlSurvivalInstability.survival,integral_same,neg_zero,Real.exp_zero,one_mul] at hn
  apply sub_nonneg.mp
  rw [← div_mul_cancel₀ (p c a i-survival c k t*p c (k t) i) (p_pos c a hc ha i).ne']
  exact mul_nonneg hn (p_pos c a hc ha i).le

private theorem terminal_norm (c a T : ℝ) (k chi : ℝ → ℝ)
    (hc : c < 1/2) (ha : a ∈ Ioo 0 c)
    (hk : OriginalControl (c,c,1-2*c) T k chi) (h0 : k 0 = a) :
    ‖terminalKraus (H := H) c a k chi T‖ ≤ 1 := by
  apply diagonal_norm_le _ _ zero_le_one
  intro i
  have hp := p_pos c (k T) hc
    (OriginalRepeatedMarkedLaw.native_bounds c T 0 k (height_control c T k chi hk) T ⟨hk.1,le_rfl⟩) i
  have hd := p_pos c a hc ha i
  have hs := (Real.exp_pos (-(∫ u in (0 : ℝ)..T,hazard c k u))).le
  have hb := native_mass_le c a T k chi hc ha hk h0 T ⟨hk.1,le_rfl⟩ i
  change ‖(Real.sqrt (survival c k T) : ℂ) *
    (Real.sqrt (p c (k T) i / p c a i) : ℂ) * character c k chi T i‖ ≤ 1
  rw [norm_mul,norm_mul,show ‖character c k chi T i‖ = 1 by
    simp [character,Complex.norm_exp_ofReal_mul_I],mul_one,
    Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (Real.sqrt_nonneg _),
    ← Real.sqrt_mul hs]
  apply Real.sqrt_le_one.mpr
  rw [← mul_div_assoc]
  exact (div_le_one hd).mpr hb

private theorem diagonal_sub {m : ℕ} (d e : Fin m → ℂ) :
    diagonalAction (H := H) d - diagonalAction e = diagonalAction (fun i => d i-e i) := by
  ext x i
  simp [diagonalAction_apply,sub_smul]

private theorem diagonal_scalar_lower {m : ℕ} (d : Fin m → ℂ) (i : Fin m) :
    ‖d i‖ ≤ ‖diagonalAction (H := ℂ) d‖ := by
  let x : Blocks (Fin m) ℂ := PiLp.single 2 i 1
  have hx : ‖x‖ = 1 := by simp [x]
  have he : diagonalAction (H := ℂ) d x = PiLp.single 2 i (d i) := by
    ext j
    simp [diagonalAction_apply,x,PiLp.single_apply]
    split_ifs with h
    · subst j; simp
    · simp
  have h := (diagonalAction (H := ℂ) d).le_opNorm x
  simpa [he,hx] using h

private theorem amplified_difference_le (d e : Fin 5 → ℂ) :
    ‖diagonalAction (H := H) d-diagonalAction e‖ ≤
      ‖diagonalAction (H := ℂ) d-diagonalAction e‖ := by
  rw [diagonal_sub,diagonal_sub]
  exact diagonal_norm_le _ _ (norm_nonneg _) (diagonal_scalar_lower _)

/-- The terminal error is the operator norm on the original five-dimensional system. -/
def krausError (c a T : ℝ) (k chi l psi : ℝ → ℝ) : ℝ :=
  ‖terminalKraus (H := ℂ) c a k chi T-terminalKraus c a l psi T‖

/-- Source-family density, with its original unnormalized initial mode weight. -/
def lossDensity (c a : ℝ) (k : ℝ → ℝ) (i : Fin 5) (t : ℝ) : ℝ :=
  modeCoefficient c a k i t * p c a i

def densityError (c a T : ℝ) (k l : ℝ → ℝ) (i : Fin 5) : ℝ :=
  (∫ t in Ioc (0 : ℝ) T, |lossDensity c a k i t-lossDensity c a l i t|) / p c a i

private theorem densityError_eq (c a T : ℝ) (k l : ℝ → ℝ)
    (hc : c < 1/2) (ha : a ∈ Ioo 0 c) (i : Fin 5) :
    densityError c a T k l i =
      ∫ t in Ioc (0 : ℝ) T, |modeCoefficient c a k i t-modeCoefficient c a l i t| := by
  simp only [densityError,lossDensity,← sub_mul,abs_mul,
    abs_of_pos (p_pos c a hc ha i),integral_mul_const]
  exact mul_div_cancel_right₀ _ (p_pos c a hc ha i).ne'

private theorem actual_failure_error (c a T : ℝ) (k chi l psi : ℝ → ℝ)
    (hc : c < 1/2) (ha : a ∈ Ioo 0 c) (i : Fin 5)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) :
    (∫ t in Ioc (0 : ℝ) T,
      ‖phasedFailure c a k chi t i rho hpos-phasedFailure c a l psi t i rho hpos‖) =
      densityError c a T k l i *
        ‖TraceClass.ofOperator (compression rho.1 i)
          (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)‖ := by
  rw [densityError_eq c a T k l hc ha i]
  simp_rw [phasedFailure_eq,liveFailure_diff_norm,modeOutput,← sub_smul,← Complex.ofReal_sub,
    norm_smul,Complex.norm_real,Real.norm_eq_abs]
  rw [integral_mul_const]

/-- Complete-output stability on every positive joint input, retaining the same reference. -/
theorem complete_output_bound (c a T : ℝ) (k chi l psi : ℝ → ℝ)
    (hc : c < 1/2) (ha : a ∈ Ioo 0 c)
    (hk : OriginalControl (c,c,1-2*c) T k chi)
    (hl : OriginalControl (c,c,1-2*c) T l psi) (hk0 : k 0=a) (hl0 : l 0=a)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1)
    (b : ℝ) (hb : ∀ i : Fin 5, densityError c a T k l i ≤ b) :
    completeDistance c a T k chi l psi rho hpos ≤
      (krausError c a T k chi l psi + b/2) * ‖rho‖ := by
  have hterminal : ‖terminalOutput c a k chi T rho-terminalOutput c a l psi T rho‖ ≤
      2 * krausError c a T k chi l psi * ‖rho‖ := by
    have h := congruence_difference (terminalKraus c a k chi T)
      (terminalKraus c a l psi T) rho
    change ‖terminalOutput c a k chi T rho-terminalOutput c a l psi T rho‖ ≤ _ at h
    have hk1 := terminal_norm (H := H) c a T k chi hc ha hk hk0
    have hl1 := terminal_norm (H := H) c a T l psi hc ha hl hl0
    have he : ‖terminalKraus (H := H) c a k chi T-terminalKraus c a l psi T‖ ≤
        krausError c a T k chi l psi := amplified_difference_le _ _
    calc
      _ ≤ (‖terminalKraus (H := H) c a k chi T‖+
        ‖terminalKraus (H := H) c a l psi T‖) *
        ‖terminalKraus (H := H) c a k chi T-terminalKraus c a l psi T‖ * ‖rho‖ := h
      _ ≤ (1+1) * krausError c a T k chi l psi * ‖rho‖ := by
        gcongr
      _ = _ := by ring
  have hfail : (∑ i : Fin 5, ∫ t in Ioc (0 : ℝ) T,
      ‖phasedFailure c a k chi t i rho hpos-phasedFailure c a l psi t i rho hpos‖) ≤ b*‖rho‖ := by
    simp_rw [actual_failure_error c a T k chi l psi hc ha]
    rw [← actual_output_mass_partition rho hpos,Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _))
  dsimp only [completeDistance]
  nlinarith [norm_nonneg rho]

universe v

/-- The supremum over every normalized live input and every unchanged Hilbert reference. -/
def completeOperationalDistance (c a T : ℝ) (k chi l psi : ℝ → ℝ) : ℝ :=
  sSup {x : ℝ | ∃ s : JointState.{v} 5,
    x = completeDistance c a T k chi l psi s.rho s.positive}

private def normalizedLive : JointState.{v} 5 := by
  let rho : TraceClass (Blocks (Fin 5) witnessReference.{v}) :=
    TraceClass.ofOperator (embedding witnessBase.{v}.1 (0 : Fin 5))
      (embedding_traceClass (TraceClass.isTraceClass_coe _) witnessBase_pos _)
  have hp : 0 ≤ rho.1 := by
    apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
    simpa only [rho,TraceClass.ofOperator_coe,embedding,insertion,
      ContinuousLinearMap.comp_assoc] using
      (ContinuousLinearMap.nonneg_iff_isPositive.mp witnessBase_pos).adjoint_conj
        (coordinate (0 : Fin 5))
  have hn : ‖rho‖ = 1 :=
    (embedding_trace_norm (TraceClass.isTraceClass_coe _) witnessBase_pos (0 : Fin 5)).2.trans
      witnessBase_norm
  exact ⟨witnessReference.{v},rho,hp,hn⟩

/-- IS.27, uniformly over arbitrary, possibly entangled or nonseparable, references. -/
theorem complete_operational_bound (c a T : ℝ) (k chi l psi : ℝ → ℝ)
    (hc : c < 1/2) (ha : a ∈ Ioo 0 c)
    (hk : OriginalControl (c,c,1-2*c) T k chi)
    (hl : OriginalControl (c,c,1-2*c) T l psi) (hk0 : k 0=a) (hl0 : l 0=a) :
    completeOperationalDistance.{v} c a T k chi l psi ≤
      krausError c a T k chi l psi +
        (Finset.univ.sup' Finset.univ_nonempty (densityError c a T k l))/2 := by
  apply csSup_le
  · exact ⟨_,normalizedLive.{v},rfl⟩
  · rintro x ⟨s,rfl⟩
    have h := complete_output_bound c a T k chi l psi hc ha hk hl hk0 hl0
      s.rho s.positive _ (fun i => Finset.le_sup' _ (Finset.mem_univ i))
    simpa only [s.normalized,mul_one] using h

theorem complete_operational_nonneg (c a T : ℝ) (k chi l psi : ℝ → ℝ)
    (hc : c < 1/2) (ha : a ∈ Ioo 0 c)
    (hk : OriginalControl (c,c,1-2*c) T k chi)
    (hl : OriginalControl (c,c,1-2*c) T l psi) (hk0 : k 0=a) (hl0 : l 0=a) :
    0 ≤ completeOperationalDistance.{v} c a T k chi l psi := by
  let b := Finset.univ.sup' Finset.univ_nonempty (densityError c a T k l)
  have hb : BddAbove {x : ℝ | ∃ s : JointState.{v} 5,
      x = completeDistance c a T k chi l psi s.rho s.positive} := by
    refine ⟨krausError c a T k chi l psi+b/2,?_⟩
    rintro x ⟨s,rfl⟩
    simpa only [s.normalized,mul_one] using
      complete_output_bound c a T k chi l psi hc ha hk hl hk0 hl0 s.rho s.positive b
        (fun i => Finset.le_sup' _ (Finset.mem_univ i))
  apply le_csSup_of_le hb ⟨normalizedLive.{v},rfl⟩
  exact div_nonneg (add_nonneg (norm_nonneg _) (Finset.sum_nonneg
    (fun _ _ => integral_nonneg (fun _ => norm_nonneg _)))) (by norm_num)

theorem survival_le_one (c T : ℝ) (k chi : ℝ → ℝ)
    (hk : OriginalControl (c,c,1-2*c) T k chi) (t : ℝ) (ht : t ∈ Icc 0 T) :
    survival c k t ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  apply neg_nonpos.mpr
  apply intervalIntegral.integral_nonneg ht.1
  intro u hu
  have hb := OriginalRepeatedMarkedLaw.native_bounds c T 0 k
    (height_control c T k chi hk) u ⟨hu.1,hu.2.trans ht.2⟩
  exact add_nonneg (div_nonneg (le_max_right _ _) hb.1.le)
    (div_nonneg (le_max_right _ _) (sub_pos.mpr hb.2).le)

theorem probability_le_one (c x : ℝ) (hc : c < 1/2)
    (hx : x ∈ Ioo 0 c) (i : Fin 5) : p c x i ≤ 1 := by
  rw [← p_sum c x hc hx]
  exact Finset.single_le_sum (fun j _ => (p_pos c x hc hx j).le) (Finset.mem_univ i)

theorem probability_difference (c x y : ℝ) (i : Fin 5) :
    |p c x i-p c y i| ≤ |x-y| := by
  rw [p_explicit,p_explicit]
  fin_cases i <;> simp [abs_sub_comm]

private theorem terminal_mass_error (c a T B delta : ℝ) (k chi l psi : ℝ → ℝ)
    (hc : c < 1/2) (hk : OriginalControl (c,c,1-2*c) T k chi)
    (hl : OriginalControl (c,c,1-2*c) T l psi)
    (hS : |survival c k T-survival c l T| ≤ B) (hd : |k T-l T| ≤ delta)
    (i : Fin 5) :
    |survival c k T*p c (k T) i-survival c l T*p c (l T) i| ≤ B+delta := by
  have hp := p_pos c (k T) hc (OriginalRepeatedMarkedLaw.native_bounds c T 0 k
    (height_control c T k chi hk) T ⟨hk.1,le_rfl⟩) i
  have hp1 := probability_le_one c (k T) hc (OriginalRepeatedMarkedLaw.native_bounds c T 0 k
    (height_control c T k chi hk) T ⟨hk.1,le_rfl⟩) i
  have hs0 : 0 ≤ survival c l T := (Real.exp_pos _).le
  have hs1 := survival_le_one c T l psi hl T ⟨hl.1,le_rfl⟩
  have hb0 := (abs_nonneg _).trans hS
  have hd0 := (abs_nonneg _).trans hd
  calc
    _ = |(survival c k T-survival c l T)*p c (k T) i+
        survival c l T*(p c (k T) i-p c (l T) i)| := by congr 1; ring
    _ ≤ |survival c k T-survival c l T|*p c (k T) i+
        survival c l T*|p c (k T) i-p c (l T) i| := by
      simpa only [abs_mul,abs_of_nonneg hp.le,abs_of_nonneg hs0] using abs_add_le
        ((survival c k T-survival c l T)*p c (k T) i)
        (survival c l T*(p c (k T) i-p c (l T) i))
    _ ≤ B*1+1*delta := by gcongr; exact (probability_difference c _ _ i).trans hd
    _ = _ := by ring

private theorem root_character_bound (x y : ℝ) (z w : ℂ)
    (hy : Real.sqrt y ≤ 1) (hz : ‖z‖ = 1) :
    ‖(Real.sqrt x : ℂ)*z-(Real.sqrt y : ℂ)*w‖ ≤
      Real.sqrt |x-y|+‖z-w‖ := by
  have hr : |Real.sqrt x-Real.sqrt y| ≤ Real.sqrt |x-y| :=
    Real.abs_le_sqrt (D5.S3.TotalVariation.Hellinger.sq_sqrt_sub_sqrt_le_abs_sub x y)
  calc
    _ = ‖((Real.sqrt x-Real.sqrt y : ℝ) : ℂ)*z+
        (Real.sqrt y : ℂ)*(z-w)‖ := by congr 1; push_cast; ring
    _ ≤ ‖((Real.sqrt x-Real.sqrt y : ℝ) : ℂ)*z‖+
        ‖(Real.sqrt y : ℂ)*(z-w)‖ := norm_add_le _ _
    _ = |Real.sqrt x-Real.sqrt y|+Real.sqrt y*‖z-w‖ := by
      rw [norm_mul,norm_mul,hz,mul_one,Complex.norm_real,Complex.norm_real,
        Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ Real.sqrt |x-y|+1*‖z-w‖ := by gcongr
    _ = _ := by ring

/-- IS.29 keeps the terminal phase-character certificate separate from height errors. -/
theorem terminal_error_bound (c a T B delta : ℝ) (k chi l psi : ℝ → ℝ)
    (hc : c < 1/2) (ha : a ∈ Ioo 0 c)
    (hk : OriginalControl (c,c,1-2*c) T k chi)
    (hl : OriginalControl (c,c,1-2*c) T l psi) (hk0 : k 0=a) (hl0 : l 0=a)
    (hS : |survival c k T-survival c l T| ≤ B) (hd : |k T-l T| ≤ delta) :
    krausError c a T k chi l psi ≤
      (Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 5 => Real.sqrt ((B+delta)/p c a i)))+
      (Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin 5 => ‖character c k chi T i-character c l psi T i‖)) := by
  let C := Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 5 => Real.sqrt ((B+delta)/p c a i))
  let E := Finset.univ.sup' Finset.univ_nonempty
    (fun i : Fin 5 => ‖character c k chi T i-character c l psi T i‖)
  have hC : 0 ≤ C := (Real.sqrt_nonneg _).trans (Finset.le_sup' _ (Finset.mem_univ (0 : Fin 5)))
  have hE : 0 ≤ E := (norm_nonneg _).trans (Finset.le_sup' _ (Finset.mem_univ (0 : Fin 5)))
  change ‖diagonalAction (H := ℂ) _-diagonalAction _‖ ≤ C+E
  rw [diagonal_sub]
  apply diagonal_norm_le _ _ (add_nonneg hC hE)
  intro i
  have hd0 := (p_pos c a hc ha i).le
  have hdpos := p_pos c a hc ha i
  have hkm := OriginalRepeatedMarkedLaw.native_bounds c T 0 k
    (height_control c T k chi hk) T ⟨hk.1,le_rfl⟩
  have hlm := OriginalRepeatedMarkedLaw.native_bounds c T 0 l
    (height_control c T l psi hl) T ⟨hl.1,le_rfl⟩
  have hs : 0 ≤ survival c k T := (Real.exp_pos _).le
  have ht : 0 ≤ survival c l T := (Real.exp_pos _).le
  have hroot (q : ℝ → ℝ) :
      (Real.sqrt (survival c q T) : ℂ)*(Real.sqrt (p c (q T) i/p c a i) : ℂ) =
        (Real.sqrt (survival c q T*p c (q T) i/p c a i) : ℂ) := by
    rw [← Complex.ofReal_mul,← Real.sqrt_mul (show 0 ≤ survival c q T from (Real.exp_pos _).le),
      ← mul_div_assoc]
  have h1 : Real.sqrt (survival c l T*p c (l T) i/p c a i) ≤ 1 :=
    Real.sqrt_le_one.mpr ((div_le_one hdpos).mpr
      (native_mass_le c a T l psi hc ha hl hl0 T ⟨hl.1,le_rfl⟩ i))
  have heq : |survival c k T*p c (k T) i/p c a i-
      survival c l T*p c (l T) i/p c a i| =
      |survival c k T*p c (k T) i-survival c l T*p c (l T) i|/p c a i := by
    rw [← sub_div,abs_div,abs_of_pos hdpos]
  have hmass := terminal_mass_error c a T B delta k chi l psi hc hk hl hS hd i
  have he : Real.sqrt |survival c k T*p c (k T) i/p c a i-
      survival c l T*p c (l T) i/p c a i| ≤ Real.sqrt ((B+delta)/p c a i) := by
    rw [heq]
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hmass hd0)
  simp only [terminalDiagonal,hroot]
  exact (root_character_bound _ _ _ _ h1 (by simp [character,Complex.norm_exp_ofReal_mul_I])).trans
    ((add_le_add he le_rfl).trans (add_le_add
      (Finset.le_sup' _ (Finset.mem_univ i)) (Finset.le_sup' _ (Finset.mem_univ i))))

end D5.S3.Quantum.Fibers.OriginalCompleteOutputStability
