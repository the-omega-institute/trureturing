/- GID: D5/S3/Quantum/Analysis/TraceClass/LogRegularization
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TraceClass/LogRegularization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive trace pairing and continuous bounded logarithmic regularizations on genuine trace-class references. -/

import D5.S3.Quantum.Analysis.TraceClass.Pairing
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Bounded logarithmic trace energies

The trace and trace norm are the analytic, basis-independent quantities adopted
from Tom Ole Diem's Apache-2.0 Physlib trace-class development. The logarithm and
its noncommutative monotonicity are Mathlib's real continuous functional calculus.
Only bounded regularizations occur here; no totalized logarithm at a singular
reference is interpreted as an unbounded energy.
-/

noncomputable section
open scoped ComplexOrder InnerProductSpace ENNReal

namespace QuantumLogEnergy

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The inclusion uses the trace norm on its domain and the operator norm on its range. -/
def operatorCLM : TraceClass H →L[ℂ] (H →L[ℂ] H) :=
  ({ toFun := fun T => T.1
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : TraceClass H →ₗ[ℂ] (H →L[ℂ] H)).mkContinuous 1
    (fun T => by
      change ‖T.1‖ ≤ 1 * ‖T‖
      rw [one_mul, TraceClass.norm_eq_traceNorm]
      exact opNorm_le_traceNorm (TraceClass.isTraceClass_coe T))

/-- Positive trace-class operators have nonnegative real trace. -/
theorem re_trace_nonneg {T : H →L[ℂ] H} (hT : IsTraceClass T) (hpos : 0 ≤ T) :
    0 ≤ (trace T hT).re := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  rw [trace_eq_of_hilbertBasis hT b]
  change 0 ≤ Complex.reCLM (∑' i : w, ⟪b i, T (b i)⟫_ℂ)
  rw [Complex.reCLM.map_tsum (summable_trace_diagonal_of_isTraceClass hT b)]
  exact tsum_nonneg fun i => (T.nonneg_iff_isPositive.mp hpos).re_inner_nonneg_right (b i)

/-- Positivity of the trace pairing requires no commutation between its two arguments.
The cyclicity is applied to the trace-class product `sqrt A * rho`, not to `sqrt rho`. -/
theorem tracePairing_nonneg {A : H →L[ℂ] H} (hA : 0 ≤ A) (rho : TraceClass H)
    (hrho : 0 ≤ rho.1) : 0 ≤ (TraceClass.tracePairing A rho).re := by
  let R : H →L[ℂ] H := CFC.sqrt A
  have hR : IsSelfAdjoint R := .of_nonneg (CFC.sqrt_nonneg A)
  have hRR : R * R = A := CFC.sqrt_mul_sqrt_self A hA
  have hRrho : IsTraceClass (R * rho.1) := TraceClass.isTraceClass_mul_coe R rho
  have hcycle := trace_mul_cycle (A := R) hRrho
  have hconj : 0 ≤ R * rho.1 * R := by
    simpa only [hR.star_eq] using star_left_conjugate_nonneg hrho R
  have heq : R * (R * rho.1) = A * rho.1 := by rw [← mul_assoc, hRR]
  have htrace : TraceClass.tracePairing A rho =
      trace (R * rho.1 * R) (isTraceClass_mul_mul (TraceClass.isTraceClass_coe rho)) := by
    calc
      TraceClass.tracePairing A rho = trace (R * (R * rho.1))
          (isTraceClass_mul_mul (A := R) (B := 1) hRrho) :=
        TraceClass.trace_transport heq.symm _
      _ = _ := hcycle
  rw [htrace]
  exact re_trace_nonneg _ hconj

/-- Positive trace-class operators test the Loewner order, including noncommuting observables. -/
theorem tracePairing_mono {A B : H →L[ℂ] H} (hAB : A ≤ B) (rho : TraceClass H)
    (hrho : 0 ≤ rho.1) :
    (TraceClass.tracePairing A rho).re ≤ (TraceClass.tracePairing B rho).re := by
  have h := tracePairing_nonneg (sub_nonneg.mpr hAB) rho hrho
  change 0 ≤ (TraceClass.tracePairingContinuousLinearMap (B - A) rho).re at h
  rw [map_sub, sub_apply, Complex.sub_re] at h
  exact sub_nonneg.mp h

/-- On the positive cone the trace norm is the real trace. -/
theorem traceNorm_eq_re_trace {T : H →L[ℂ] H} (hT : IsTraceClass T) (hpos : 0 ≤ T) :
    traceNorm T hT = (trace T hT).re := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  rw [traceNorm_eq_of_hilbertBasis hT b, CFC.abs_of_nonneg T hpos,
    trace_eq_of_hilbertBasis hT b]
  exact (Complex.reCLM.map_tsum (summable_trace_diagonal_of_isTraceClass hT b)).symm

/-- Normalization and positivity imply the genuine operator inequality `rho ≤ 1`. -/
theorem density_le_one (rho : TraceClass H) (hrho : 0 ≤ rho.1)
    (htrace : (trace rho.1 (TraceClass.isTraceClass_coe rho)).re = 1) : rho.1 ≤ 1 := by
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg rho.1 hrho).mp
  calc
    ‖rho.1‖ ≤ traceNorm rho.1 (TraceClass.isTraceClass_coe rho) :=
      opNorm_le_traceNorm (TraceClass.isTraceClass_coe rho)
    _ = 1 := (traceNorm_eq_re_trace _ hrho).trans htrace

/-- A positive trace-class contraction, with the topology induced by the genuine trace norm. -/
abbrev Reference (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  {T : TraceClass H // 0 ≤ T.1 ∧ T.1 ≤ 1}

/-- `log(1+epsilon) I - log(T+epsilon I)` is bounded even when `T` has a kernel. -/
def logRegularization (epsilon : ℝ) (T : H →L[ℂ] H) : H →L[ℂ] H :=
  algebraMap ℝ (H →L[ℂ] H) (Real.log (1 + epsilon)) -
    CFC.log (T + algebraMap ℝ (H →L[ℂ] H) epsilon)

theorem shift_strictlyPositive {epsilon : ℝ} (he : 0 < epsilon)
    {T : H →L[ℂ] H} (hT : 0 ≤ T) :
    IsStrictlyPositive (T + algebraMap ℝ (H →L[ℂ] H) epsilon) :=
  IsStrictlyPositive.nonneg_add hT (isStrictlyPositive_algebraMap he)

/-- Real functional calculus acts on every actual eigenvector, including the zero vector.
No compactness, eigenbasis, or invertibility is assumed. -/
theorem cfc_apply_eigenvector (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (s : ℝ) (v : H) (hv : T v = (s : ℂ) • v) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ T)) :
    cfc f T v = (f s : ℂ) • v := by
  by_cases hv0 : v = 0
  · simp [hv0]
  have hsC : (s : ℂ) ∈ spectrum ℂ T := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact (Module.End.hasEigenvalue_of_hasEigenvector
      (show Module.End.HasEigenvector T.toLinearMap (s : ℂ) v from
        ⟨Module.End.mem_eigenspace_iff.mpr hv, hv0⟩)).mem_spectrum
  have hs : s ∈ spectrum ℝ T := spectrum.of_algebraMap_mem ℂ hsC
  let x : spectrum ℝ T := ⟨s, hs⟩
  let p : C(spectrum ℝ T, ℝ) → Prop := fun g =>
    (cfcHom hT g) v = (g x : ℂ) • v
  have hclosed : IsClosed {g | p g} := by
    exact isClosed_eq
      ((cfcHom_continuous hT).clm_apply continuous_const)
      ((Complex.continuous_ofReal.comp (ContinuousMap.evalCLM (R := ℝ) x).continuous).smul
        continuous_const)
  have hp (g : C(spectrum ℝ T, ℝ)) : p g := by
    induction g using ContinuousMap.induction_on_of_compact with
    | const r =>
        change (cfcHom hT (algebraMap ℝ C(spectrum ℝ T, ℝ) r)) v = _
        rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one]
        simp [x, Complex.coe_smul]
    | id => simpa [p, x, cfcHom_id] using hv
    | star_id => simpa only [star_trivial] using (show p _ from by
        simpa [p, x, cfcHom_id] using hv)
    | add g h hg hh =>
        change (cfcHom hT (g + h)) v = _
        rw [map_add, ContinuousLinearMap.add_apply, hg, hh]
        simp [add_smul]
    | mul g h hg hh =>
        change (cfcHom hT (g * h)) v = _
        rw [map_mul, ContinuousLinearMap.mul_apply, hh, map_smul, hg]
        simp only [ContinuousMap.mul_apply, Complex.ofReal_mul, mul_smul]
        exact smul_comm _ _ _
    | frequently g hg =>
        exact hg.mem_of_closed hclosed
  rw [cfc_apply f T hT hf]
  exact hp _

private theorem continuousOn_log_shift {epsilon : ℝ} (he : 0 < epsilon)
    {T : H →L[ℂ] H} (hT : 0 ≤ T) :
    ContinuousOn (fun x : ℝ => Real.log (x + epsilon)) (spectrum ℝ T) := by
  apply ContinuousOn.log (continuousOn_id.add continuousOn_const)
  intro x hx
  exact ne_of_gt (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hT hx) he)

private theorem logRegularization_eq_cfc {epsilon : ℝ} (he : 0 < epsilon)
    {T : H →L[ℂ] H} (hT : 0 ≤ T) :
    logRegularization epsilon T =
      cfc (fun x : ℝ => Real.log (1 + epsilon) - Real.log (x + epsilon)) T := by
  have hsa : IsSelfAdjoint T := .of_nonneg hT
  have hc := continuousOn_log_shift he hT
  rw [cfc_sub _ _ T continuousOn_const hc, cfc_const _ T hsa]
  unfold logRegularization CFC.log
  congr 1
  have hid : cfc (fun x : ℝ => x + epsilon) T =
      T + algebraMap ℝ (H →L[ℂ] H) epsilon := by
    simpa only [cfc_id' ℝ T hsa] using
      (cfc_add_const epsilon (fun x : ℝ => x) T continuousOn_id hsa)
  have hlog : ContinuousOn Real.log ((fun x : ℝ => x + epsilon) '' spectrum ℝ T) := by
    apply ContinuousOn.log continuousOn_id
    rintro y ⟨x, hx, rfl⟩
    exact ne_of_gt (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hT hx) he)
  rw [← hid, ← cfc_comp' Real.log (fun x : ℝ => x + epsilon) T hlog
    (continuousOn_id.add continuousOn_const) hsa]

/-- The bounded logarithmic observable acts by its scalar regularization on each
actual eigenvector, including eigenvalue zero. -/
theorem logRegularization_apply_eigenvector {epsilon : ℝ} (he : 0 < epsilon)
    {T : H →L[ℂ] H} (hT : 0 ≤ T) (s : ℝ) (v : H)
    (hv : T v = (s : ℂ) • v) :
    logRegularization epsilon T v =
      (Real.log (1 + epsilon) - Real.log (s + epsilon) : ℂ) • v := by
  rw [logRegularization_eq_cfc he hT]
  simpa only [Complex.ofReal_sub] using
    cfc_apply_eigenvector T (.of_nonneg hT) s v hv
      (fun x : ℝ => Real.log (1 + epsilon) - Real.log (x + epsilon))
      (continuousOn_const.sub (continuousOn_log_shift he hT))

/-- Decreasing a positive regularization parameter increases the actual operator.
The comparison is made on the spectrum of the same positive contraction. -/
theorem logRegularization_parameter_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {T : H →L[ℂ] H} (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    logRegularization b T ≤ logRegularization a T := by
  have hb : 0 < b := ha.trans_le hab
  rw [logRegularization_eq_cfc hb hT, logRegularization_eq_cfc ha hT]
  apply (cfc_le_iff _ _ T
    (continuousOn_const.sub (continuousOn_log_shift hb hT))
    (continuousOn_const.sub (continuousOn_log_shift ha hT)) (.of_nonneg hT)).mpr
  intro x hx
  have hx0 := spectrum_nonneg_of_nonneg hT hx
  have hx1 : x ≤ 1 := (CFC.le_one_iff (R := ℝ) T (.of_nonneg hT)).mp hT1 x hx
  change Real.log (1 + b) - Real.log (x + b) ≤ Real.log (1 + a) - Real.log (x + a)
  rw [← Real.log_div (by positivity) (by positivity),
    ← Real.log_div (by positivity) (by positivity)]
  apply Real.log_le_log (by positivity)
  apply (div_le_div_iff₀ (by positivity : 0 < x + b) (by positivity : 0 < x + a)).mpr
  nlinarith

/-- The bounded regularization is positive for every positive contraction. -/
theorem logRegularization_nonneg {epsilon : ℝ} (he : 0 < epsilon)
    {T : H →L[ℂ] H} (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    0 ≤ logRegularization epsilon T := by
  apply sub_nonneg.mpr
  have h := CFC.log_le_log (show T + algebraMap ℝ (H →L[ℂ] H) epsilon ≤
      1 + algebraMap ℝ (H →L[ℂ] H) epsilon from add_le_add hT1 le_rfl)
    (shift_strictlyPositive he hT)
  have hid : (1 : H →L[ℂ] H) + algebraMap ℝ (H →L[ℂ] H) epsilon =
      algebraMap ℝ (H →L[ℂ] H) (1 + epsilon) := by simp only [map_add, map_one]
  rw [hid, CFC.log_algebraMap] at h
  exact h

/-- Each bounded regularization reverses the operator order without a commutativity assumption. -/
theorem logRegularization_antitone {epsilon : ℝ} (he : 0 < epsilon)
    {P Q : H →L[ℂ] H} (hP : 0 ≤ P) (hPQ : P ≤ Q) :
    logRegularization epsilon Q ≤ logRegularization epsilon P := by
  unfold logRegularization
  apply sub_le_sub_left
  exact CFC.log_le_log (add_le_add hPQ le_rfl) (shift_strictlyPositive he hP)

/-- The bounded trace energy is paired with an actual trace-class operator. -/
def regularizedEnergy (epsilon : ℝ) (T : H →L[ℂ] H) (rho : TraceClass H) : ℝ :=
  (TraceClass.tracePairing (logRegularization epsilon T) rho).re

/-- Regularized energies are nonnegative, also for singular references. -/
theorem regularizedEnergy_nonneg {epsilon : ℝ} (he : 0 < epsilon)
    (T : Reference H) (rho : TraceClass H) (hrho : 0 ≤ rho.1) :
    0 ≤ regularizedEnergy epsilon T.1.1 rho :=
  tracePairing_nonneg (logRegularization_nonneg he T.2.1 T.2.2) rho hrho

/-- Noncommuting order domination holds at every positive regularization parameter. -/
theorem regularizedEnergy_antitone {epsilon : ℝ} (he : 0 < epsilon)
    {P Q : H →L[ℂ] H} (hP : 0 ≤ P) (hPQ : P ≤ Q)
    (rho : TraceClass H) (hrho : 0 ≤ rho.1) :
    regularizedEnergy epsilon Q rho ≤ regularizedEnergy epsilon P rho :=
  tracePairing_mono (logRegularization_antitone he hP hPQ) rho hrho

/-- The observable inclusion is continuous for the genuine trace norm. -/
private theorem continuous_reference_operator : Continuous (fun T : Reference H => T.1.1) :=
  operatorCLM.continuous.comp continuous_subtype_val

/-- Fixed positive regularization is continuous in the reference's trace norm. -/
theorem continuous_regularizedEnergy {epsilon : ℝ} (he : 0 < epsilon) (rho : TraceClass H) :
    Continuous (fun T : Reference H => regularizedEnergy epsilon T.1.1 rho) := by
  have hshift : Continuous (fun T : Reference H =>
      T.1.1 + algebraMap ℝ (H →L[ℂ] H) epsilon) :=
    continuous_reference_operator.add continuous_const
  have hlog : Continuous (fun T : Reference H =>
      CFC.log (T.1.1 + algebraMap ℝ (H →L[ℂ] H) epsilon)) :=
    CFC.continuousOn_log.comp_continuous hshift fun T =>
      let h := shift_strictlyPositive he T.2.1
      ⟨h.isSelfAdjoint, h.isUnit⟩
  have hreg : Continuous (fun T : Reference H => logRegularization epsilon T.1.1) :=
    continuous_const.sub hlog
  exact Complex.continuous_re.comp
    ((TraceClass.tracePairingContinuousLinearMap.continuous.comp hreg).clm_apply continuous_const)

/-- An auxiliary operator-defined supremum. Its identification with the singular
spectral energy requires a complete spectral basis theorem. -/
def regularizedSupremum (T : Reference H) (rho : TraceClass H) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (regularizedEnergy ((n : ℝ) + 1)⁻¹ T.1.1 rho)

/-- The supremum of actual regularized trace pairings is lower semicontinuous
in the reference's trace norm. This does not yet identify it with a spectral sum. -/
theorem lowerSemicontinuous_regularizedSupremum (rho : TraceClass H) :
    LowerSemicontinuous (fun T : Reference H => regularizedSupremum T rho) := by
  apply lowerSemicontinuous_iSup
  intro n
  exact (ENNReal.continuous_ofReal.comp
    (continuous_regularizedEnergy (by positivity : 0 < ((n : ℝ) + 1)⁻¹) rho)).lowerSemicontinuous

/-- The same operator-defined supremum reverses noncommuting reference order. -/
theorem regularizedSupremum_antitone (P Q : Reference H) (hPQ : P.1.1 ≤ Q.1.1)
    (rho : TraceClass H) (hrho : 0 ≤ rho.1) :
    regularizedSupremum Q rho ≤ regularizedSupremum P rho := by
  apply iSup_mono
  intro n
  exact ENNReal.ofReal_le_ofReal
    (regularizedEnergy_antitone (by positivity : 0 < ((n : ℝ) + 1)⁻¹) P.2.1 hPQ rho hrho)

/-- The real trace expectation increases along the inverse-natural grid. -/
theorem monotone_regularizedEnergy (T : Reference H) (rho : TraceClass H)
    (hrho : 0 ≤ rho.1) :
    Monotone (fun n : ℕ => regularizedEnergy ((n : ℝ) + 1)⁻¹ T.1.1 rho) := by
  intro m n hmn
  apply tracePairing_mono _ rho hrho
  apply logRegularization_parameter_antitone (by positivity) _ T.2.1 T.2.2
  exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)

/-- Finite nonnegative mixtures in the trace-class argument preserve the actual
operator-defined extended supremum, including zero coefficients and infinite energies. -/
theorem regularizedSupremum_nonneg_linear (T : Reference H) (rho gamma : TraceClass H)
    (hrho : 0 ≤ rho.1) (hgamma : 0 ≤ gamma.1) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    regularizedSupremum T ((a : ℂ) • rho + (b : ℂ) • gamma) =
      ENNReal.ofReal a * regularizedSupremum T rho +
        ENNReal.ofReal b * regularizedSupremum T gamma := by
  have hlin (e : ℝ) : regularizedEnergy e T.1.1 ((a : ℂ) • rho + (b : ℂ) • gamma) =
      a * regularizedEnergy e T.1.1 rho + b * regularizedEnergy e T.1.1 gamma := by
    unfold regularizedEnergy TraceClass.tracePairing
    simp only [map_add, map_smul, Complex.add_re, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hf : Monotone (fun n : ℕ => ENNReal.ofReal a *
      ENNReal.ofReal (regularizedEnergy ((n : ℝ) + 1)⁻¹ T.1.1 rho)) :=
    fun m n h => mul_le_mul_right (ENNReal.ofReal_le_ofReal
      (monotone_regularizedEnergy T rho hrho h)) _
  have hg : Monotone (fun n : ℕ => ENNReal.ofReal b *
      ENNReal.ofReal (regularizedEnergy ((n : ℝ) + 1)⁻¹ T.1.1 gamma)) :=
    fun m n h => mul_le_mul_right (ENNReal.ofReal_le_ofReal
      (monotone_regularizedEnergy T gamma hgamma h)) _
  have hpoint (n : ℕ) : ENNReal.ofReal (regularizedEnergy ((n : ℝ) + 1)⁻¹ T.1.1
      ((a : ℂ) • rho + (b : ℂ) • gamma)) =
      ENNReal.ofReal a * ENNReal.ofReal (regularizedEnergy ((n : ℝ) + 1)⁻¹ T.1.1 rho) +
      ENNReal.ofReal b * ENNReal.ofReal (regularizedEnergy ((n : ℝ) + 1)⁻¹ T.1.1 gamma) := by
    rw [hlin, ENNReal.ofReal_add
      (mul_nonneg ha (regularizedEnergy_nonneg (by positivity) T rho hrho))
      (mul_nonneg hb (regularizedEnergy_nonneg (by positivity) T gamma hgamma)),
      ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]
  simp_rw [regularizedSupremum, hpoint]
  rw [ENNReal.mul_iSup, ENNReal.mul_iSup, ENNReal.iSup_add_iSup_of_monotone hf hg]

/-- Multiplication by a scalar in `(0,1]` gives an actual positive trace-class contraction. -/
def scaleReference (T : Reference H) (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1) : Reference H :=
  ⟨(w : ℂ) • T.1, by
    change 0 ≤ (w : ℂ) • T.1.1 ∧ (w : ℂ) • T.1.1 ≤ 1
    rw [Complex.coe_smul]
    exact ⟨smul_nonneg hw.le T.2.1,
      (smul_le_smul_of_nonneg_left T.2.2 hw.le).trans (by simpa using
        (smul_le_smul_of_nonneg_right hw1 (show (0 : H →L[ℂ] H) ≤ 1 from zero_le_one)))⟩⟩

private theorem logRegularization_smul {e w : ℝ} (he : 0 < e) (hw : 0 < w)
    {T : H →L[ℂ] H} (hT : 0 ≤ T) :
    logRegularization e (w • T) = logRegularization (e / w) T +
      algebraMap ℝ (H →L[ℂ] H) (Real.log ((1 + e) / (w + e))) := by
  have hshift : w • T + algebraMap ℝ (H →L[ℂ] H) e =
      w • (T + algebraMap ℝ (H →L[ℂ] H) (e / w)) := by
    rw [smul_add, Algebra.smul_def w (algebraMap ℝ (H →L[ℂ] H) (e / w)),
      ← map_mul, mul_div_cancel₀ e hw.ne']
  rw [logRegularization, hshift, CFC.log_smul' _ hw
    (shift_strictlyPositive (div_pos he hw) hT), logRegularization]
  have hc : Real.log (1 + e) - Real.log w - Real.log (1 + e / w) =
      Real.log ((1 + e) / (w + e)) := by
    rw [Real.log_div (by positivity) (by positivity)]
    have hd : 1 + e / w = (w + e) / w := by field_simp
    rw [hd, Real.log_div (by positivity) hw.ne']
    ring
  rw [← hc, map_sub, map_sub]
  abel

private theorem regularizedEnergy_smul {e w : ℝ} (he : 0 < e) (hw : 0 < w)
    {T : H →L[ℂ] H} (hT : 0 ≤ T) (rho : TraceClass H) :
    regularizedEnergy e (w • T) rho = regularizedEnergy (e / w) T rho +
      (trace rho.1 (TraceClass.isTraceClass_coe rho)).re *
        Real.log ((1 + e) / (w + e)) := by
  unfold regularizedEnergy
  rw [logRegularization_smul he hw hT]
  change (TraceClass.tracePairingContinuousLinearMap (_ + _) rho).re = _
  rw [map_add, ContinuousLinearMap.add_apply, Complex.add_re]
  congr 1
  rw [Algebra.algebraMap_eq_smul_one]
  have hs : (Real.log ((1 + e) / (w + e))) • (1 : H →L[ℂ] H) =
      (Real.log ((1 + e) / (w + e)) : ℂ) • (1 : H →L[ℂ] H) := by
    rw [Complex.coe_smul]
  rw [hs, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [TraceClass.tracePairingContinuousLinearMap_apply, TraceClass.tracePairing_apply]
  simp only [one_mul]
  ring

private theorem grid_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) := by
  simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

private theorem regularizedEnergy_le_supremum (T : Reference H) (rho : TraceClass H)
    (hrho : 0 ≤ rho.1) {e : ℝ} (he : 0 < e) :
    ENNReal.ofReal (regularizedEnergy e T.1.1 rho) ≤ regularizedSupremum T rho := by
  obtain ⟨n, hn⟩ := (grid_tendsto_zero.eventually (gt_mem_nhds he)).exists
  exact le_trans (ENNReal.ofReal_le_ofReal (tracePairing_mono
    (logRegularization_parameter_antitone (by positivity) hn.le T.2.1 T.2.2) rho hrho))
    (le_iSup (fun n : ℕ => ENNReal.ofReal (regularizedEnergy ((n : ℝ) + 1)⁻¹ T.1.1 rho)) n)

private theorem regularizedSupremum_eq_cofinal (T : Reference H) (rho : TraceClass H)
    (hrho : 0 ≤ rho.1) (e : ℕ → ℝ) (he : ∀ n, 0 < e n)
    (ht : Filter.Tendsto e Filter.atTop (nhds 0)) :
    regularizedSupremum T rho = ⨆ n, ENNReal.ofReal (regularizedEnergy (e n) T.1.1 rho) := by
  apply le_antisymm
  · apply iSup_le
    intro m
    obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (by positivity : 0 < ((m : ℝ) + 1)⁻¹))).exists
    exact le_iSup_of_le n (ENNReal.ofReal_le_ofReal (tracePairing_mono
      (logRegularization_parameter_antitone (he n) hn.le T.2.1 T.2.2) rho hrho))
  · exact iSup_le fun n => regularizedEnergy_le_supremum T rho hrho (he n)

private theorem scaleCorrection_nonneg {e w : ℝ} (he : 0 < e) (hw : 0 < w) (hw1 : w ≤ 1) :
    0 ≤ Real.log ((1 + e) / (w + e)) := by
  apply Real.log_nonneg
  exact (le_div_iff₀ (by positivity : 0 < w + e)).mpr (by linarith)

private theorem scaleCorrection_antitone {a b w : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hw : 0 < w) (hw1 : w ≤ 1) :
    Real.log ((1 + b) / (w + b)) ≤ Real.log ((1 + a) / (w + a)) := by
  have hb := ha.trans_le hab
  apply Real.log_le_log (by positivity)
  apply (div_le_div_iff₀ (by positivity : 0 < w + b) (by positivity : 0 < w + a)).mpr
  nlinarith

/-- Scaling a singular reference adds its logarithmic normalization cost times the
actual, unnormalized real trace mass. No logarithm is applied to an unshifted singular operator. -/
theorem regularizedSupremum_scaleReference (T : Reference H) (rho : TraceClass H)
    (hrho : 0 ≤ rho.1) (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1) :
    regularizedSupremum (scaleReference T w hw hw1) rho = regularizedSupremum T rho +
      ENNReal.ofReal (trace rho.1 (TraceClass.isTraceClass_coe rho)).re *
        ENNReal.ofReal (-Real.log w) := by
  let e : ℕ → ℝ := fun n => w * ((n : ℝ) + 1)⁻¹
  have he (n : ℕ) : 0 < e n := mul_pos hw (by positivity)
  have ht : Filter.Tendsto e Filter.atTop (nhds 0) := by
    simpa [e] using grid_tendsto_zero.const_mul w
  have hmass := re_trace_nonneg (TraceClass.isTraceClass_coe rho) hrho
  have hcoeff : Monotone (fun n : ℕ => ENNReal.ofReal
      (Real.log ((1 + e n) / (w + e n)))) := by
    intro m n hmn
    apply ENNReal.ofReal_le_ofReal
    exact scaleCorrection_antitone (he n)
      (mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hmn 1)) hw.le) hw hw1
  have hcoefflim : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal
      (Real.log ((1 + e n) / (w + e n)))) Filter.atTop
      (nhds (ENNReal.ofReal (-Real.log w))) := by
    have hreal := ((Filter.Tendsto.const_add 1 ht).div (Filter.Tendsto.const_add w ht)
      (by simpa using hw.ne')).log (by positivity : (1 + 0) / (w + 0) ≠ 0)
    simpa only [Function.comp_def, Pi.div_apply, add_zero, one_div, Real.log_inv] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  rw [regularizedSupremum_eq_cofinal (scaleReference T w hw hw1) rho hrho e he ht]
  have hterm (n : ℕ) : regularizedEnergy (e n) (scaleReference T w hw hw1).1.1 rho =
      regularizedEnergy ((n : ℝ) + 1)⁻¹ T.1.1 rho +
        (trace rho.1 (TraceClass.isTraceClass_coe rho)).re *
          Real.log ((1 + e n) / (w + e n)) := by
    change regularizedEnergy (e n) ((w : ℂ) • T.1.1) rho = _
    rw [Complex.coe_smul, regularizedEnergy_smul (he n) hw T.2.1 rho]
    congr 2
    dsimp [e]
    field_simp
  have hpoint (n : ℕ) : ENNReal.ofReal
      (regularizedEnergy (e n) (scaleReference T w hw hw1).1.1 rho) =
      ENNReal.ofReal (regularizedEnergy ((n : ℝ) + 1)⁻¹ T.1.1 rho) +
        ENNReal.ofReal (trace rho.1 (TraceClass.isTraceClass_coe rho)).re *
          ENNReal.ofReal (Real.log ((1 + e n) / (w + e n))) := by
    rw [hterm, ENNReal.ofReal_add (regularizedEnergy_nonneg (by positivity) T rho hrho)
      (mul_nonneg hmass (scaleCorrection_nonneg (he n) hw hw1)), ENNReal.ofReal_mul hmass]
  simp_rw [hpoint]
  rw [← ENNReal.iSup_add_iSup_of_monotone
    (fun m n h => ENNReal.ofReal_le_ofReal (monotone_regularizedEnergy T rho hrho h))
    (fun m n h => mul_le_mul_right (hcoeff h) _), ← ENNReal.mul_iSup,
    iSup_eq_of_tendsto hcoeff hcoefflim]
  rfl

#print axioms regularizedSupremum_scaleReference

#print axioms cfc_apply_eigenvector
#print axioms logRegularization_parameter_antitone
#print axioms regularizedSupremum_nonneg_linear

#print axioms tracePairing_nonneg
#print axioms density_le_one
#print axioms continuous_regularizedEnergy
#print axioms lowerSemicontinuous_regularizedSupremum
#print axioms regularizedSupremum_antitone

end QuantumLogEnergy
