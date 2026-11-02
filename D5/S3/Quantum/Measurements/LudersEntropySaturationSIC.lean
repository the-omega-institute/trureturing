/- GID: D5/S3/Quantum/Measurements/LudersEntropySaturationSIC
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/LudersEntropySaturationSIC
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Entropy saturation of a Lüders MIC channel forces the source SIC structure. -/

import D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
import D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy
import D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Inner
import D5.S3.Quantum.Matrix.TwoPointFunctionalCalculus
import D5.S3.Quantum.Measurements.UnitaryPureProjectorSpan
import D5.S3.Quantum.Measurements.HaarPureProjectorMoment
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-! DeBrota--Stacey's saturation implication for Lüders MIC channels. -/

open scoped BigOperators CStarAlgebra ComplexOrder Matrix MatrixOrder
open MeasureTheory TopologicalSpace

noncomputable section

namespace D5.S3.Quantum.Measurements.LudersEntropySaturationSIC

open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false

def IsMIC (d : ℕ)
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ i, (e i).PosSemidef) ∧
    (∑ i, e i = 1) ∧ LinearIndependent ℂ e

def IsSIC (d : ℕ)
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  IsMIC d e ∧
    (∀ i, ∃ c : ℝ, ∃ p : Matrix (Fin d) (Fin d) ℂ,
      p.IsHermitian ∧ p * p = p ∧ p.trace = 1 ∧ e i = (c : ℂ) • p) ∧
    ∃ a b : ℂ, ∀ i j, (e i * e j).trace = if i = j then a else b

def ludersChannel {d : ℕ}
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (x : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ i, CFC.sqrt (e i) * x * CFC.sqrt (e i)

private def baseProjector {d : ℕ} [NeZero d] : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.single 0 0 1

private def inputProjector {d : ℕ} [NeZero d]
    (u : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  u.1 * baseProjector * u.1ᴴ

private theorem base_projector_psd {d : ℕ} [NeZero d] :
    (baseProjector : Matrix (Fin d) (Fin d) ℂ).PosSemidef := by
  change (Matrix.single (0 : Fin d) 0 (1 : ℂ)).PosSemidef
  rw [← Matrix.diagonal_single]
  apply Matrix.PosSemidef.diagonal
  intro j
  by_cases hj : j = 0 <;> simp [baseProjector, Matrix.single, hj]

private theorem base_projector_trace {d : ℕ} [NeZero d] :
    (baseProjector : Matrix (Fin d) (Fin d) ℂ).trace = 1 := by
  simp [baseProjector]

private theorem input_projector_psd {d : ℕ} [NeZero d]
    (u : Matrix.unitaryGroup (Fin d) ℂ) :
    (inputProjector u).PosSemidef := by
  exact base_projector_psd.mul_mul_conjTranspose_same u.1

private theorem input_projector_trace {d : ℕ} [NeZero d]
    (u : Matrix.unitaryGroup (Fin d) ℂ) :
    (inputProjector u).trace = 1 := by
  rw [inputProjector, Matrix.trace_mul_cycle]
  have hu : u.1ᴴ * u.1 = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp u.2
  rw [hu, Matrix.one_mul]
  exact base_projector_trace

private theorem input_projector_idempotent {d : ℕ} [NeZero d]
    (u : Matrix.unitaryGroup (Fin d) ℂ) :
    inputProjector u * inputProjector u = inputProjector u := by
  have hu : u.1ᴴ * u.1 = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp u.2
  have hb : (baseProjector : Matrix (Fin d) (Fin d) ℂ) * baseProjector = baseProjector := by
    simp [baseProjector, Matrix.single_mul_single_same]
  simp only [inputProjector, Matrix.mul_assoc, ← Matrix.mul_assoc u.1ᴴ u.1, hu,
    Matrix.one_mul, ← Matrix.mul_assoc baseProjector baseProjector, hb]

private noncomputable def ludersState {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (u : Matrix.unitaryGroup (Fin d) ℂ) :
    DensityState (Fin d) := by
  classical
  by_cases he : IsMIC d e
  · refine ⟨ludersChannel e (inputProjector u), ?_, ?_⟩
    · change 0 ≤ CStarMatrix.ofMatrix (ludersChannel e (inputProjector u))
      refine map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
        (Matrix.nonneg_iff_posSemidef.mpr ?_)
      rw [ludersChannel]
      apply Matrix.posSemidef_sum Finset.univ
      intro i hi
      have hx : (inputProjector u).PosSemidef := input_projector_psd u
      have hterm := hx.conjTranspose_mul_mul_same (B := CFC.sqrt (e i))
      have hs : (CFC.sqrt (e i))ᴴ = CFC.sqrt (e i) := by
        simpa [Matrix.star_eq_conjTranspose] using
          (CFC.sqrt_nonneg (e i)).isSelfAdjoint.star_eq
      simpa [hs, Matrix.mul_assoc] using hterm
    · change Matrix.trace (ludersChannel e (inputProjector u)) = 1
      rw [show ludersChannel e (inputProjector u) =
          ∑ i, CFC.sqrt (e i) * inputProjector u * CFC.sqrt (e i) by rfl,
        Matrix.trace_sum]
      calc
        (∑ i, Matrix.trace
            (CFC.sqrt (e i) * inputProjector u * CFC.sqrt (e i))) =
            ∑ i, Matrix.trace (inputProjector u * e i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Matrix.trace_mul_cycle,
            CFC.sqrt_mul_sqrt_self (e i) (he.1 i).nonneg]
          exact Matrix.trace_mul_comm _ _
        _ = Matrix.trace (inputProjector u * ∑ i, e i) := by
          rw [← Matrix.trace_sum, Matrix.mul_sum]
        _ = Matrix.trace (inputProjector u * 1) := by rw [he.2.1]
        _ = 1 := by simpa [Matrix.mul_one] using input_projector_trace u
  · refine ⟨baseProjector, ?_, ?_⟩
    · change 0 ≤ CStarMatrix.ofMatrix baseProjector
      exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv base_projector_psd.nonneg
    · change Matrix.trace baseProjector = 1
      exact base_projector_trace

private noncomputable def sigmaState {d : ℕ} [NeZero d]
    (u : Matrix.unitaryGroup (Fin d) ℂ) : DensityState (Fin d) := by
  let p : Matrix (Fin d) (Fin d) ℂ := inputProjector u
  let q : Matrix (Fin d) (Fin d) ℂ :=
    ((1 / (d + 1 : ℝ)) : ℝ) • ((1 : Matrix (Fin d) (Fin d) ℂ) + p)
  have hp : p.PosSemidef := input_projector_psd u
  have hq0 : q.PosSemidef := by
    apply Matrix.PosSemidef.smul
    · exact Matrix.PosSemidef.add Matrix.PosSemidef.one hp
    · positivity
  refine ⟨CStarMatrix.ofMatrix q, map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hq0.nonneg, ?_⟩
  change Matrix.trace q = 1
  dsimp [q, p]
  rw [Matrix.trace_smul, Matrix.trace_add, input_projector_trace]
  simp [Matrix.trace, Finset.sum_const]
  field_simp

noncomputable def typicalEntropy (d : ℕ) [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∫ u : Matrix.unitaryGroup (Fin d) ℂ,
    vonNeumannEntropy (ludersState e u) ∂
      (Measure.haarMeasure
        (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ)))

private theorem luders_state_density {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (u : Matrix.unitaryGroup (Fin d) ℂ) (he : IsMIC d e) :
    (ludersState e u).1 = ludersChannel e (inputProjector u) := by
  simp [ludersState, he]
  rfl

private theorem sigma_log {d : ℕ} [NeZero d]
    (u : Matrix.unitaryGroup (Fin d) ℂ) :
    CFC.log (sigmaState u).1 = CStarMatrix.ofMatrix
      ((-Real.log (d + 1)) • (1 : Matrix (Fin d) (Fin d) ℂ) +
        Real.log 2 • inputProjector u) := by
  haveI : Nontrivial (CStarMatrix (Fin d) (Fin d) ℂ) := inferInstance
  haveI : ContinuousFunctionalCalculus ℝ (CStarMatrix (Fin d) (Fin d) ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus
  let k : ℝ := 1 / (d + 1)
  let p := inputProjector u
  let h : Matrix (Fin d) (Fin d) ℂ := (2 : ℝ) • p - 1
  have hp : p.IsHermitian := (input_projector_psd u).isHermitian
  have hpp : p * p = p := input_projector_idempotent u
  have hh : IsSelfAdjoint h :=
    (hp.smul (isSelfAdjoint_iff.mpr (by simp) : IsSelfAdjoint (2 : ℝ))).sub
      Matrix.isHermitian_one
  have hhh : h * h = 1 := by
    dsimp [h]
    simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, mul_one, one_mul,
      hpp, smul_smul]
    module
  have hk : 0 < k := by dsimp [k]; positivity
  have hcalc := QuantumTwoPointFunctionalCalculus.two_point_cfc
    Real.log (3 * k / 2) (k / 2) h hh hhh
  have harg : (3 * k / 2) • (1 : Matrix (Fin d) (Fin d) ℂ) + (k / 2) • h =
      k • (1 + p) := by
    dsimp [h]
    module
  rw [harg, show 3 * k / 2 + k / 2 = 2 * k by ring,
    show 3 * k / 2 - k / 2 = k by ring,
    Real.log_mul (by norm_num) (ne_of_gt hk)] at hcalc
  have hlog : Real.log k = -Real.log (d + 1) := by simp [k]
  have hq : (k • (1 + p) : Matrix (Fin d) (Fin d) ℂ).IsHermitian := by
    exact (Matrix.isHermitian_one.add hp).smul (by simp [isSelfAdjoint_iff])
  have hmap := StarAlgHomClass.map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    CStarMatrix.ofMatrixStarAlgEquiv Real.log
    (k • (1 + p) : Matrix (Fin d) (Fin d) ℂ)
    ((k • (1 + p) : Matrix (Fin d) (Fin d) ℂ).finite_real_spectrum.continuousOn _)
    CStarMatrix.ofMatrixL.continuous hq (by exact hq)
  change CStarMatrix.ofMatrix (cfc Real.log (k • (1 + p))) = CFC.log (sigmaState u).1 at hmap
  rw [← hmap, hcalc, hlog]
  congr 1
  dsimp [h, p]
  module

private theorem entropy_gap {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (u : Matrix.unitaryGroup (Fin d) ℂ) (he : IsMIC d e) :
    Real.log (d + 1) - 2 / (d + 1) * Real.log 2 -
        vonNeumannEntropy (ludersState e u) =
      quantumRelativeEntropy (ludersState e u) (sigmaState u) +
        ((Matrix.trace (inputProjector u * ludersChannel e (inputProjector u))).re -
          2 / (d + 1)) * Real.log 2 := by
  rw [quantum_relative_entropy_eq_neg_entropy_sub_cross, sigma_log]
  have hr := (ludersState e u).2.2
  change Matrix.trace (CStarMatrix.ofMatrix.symm (ludersState e u).1) = 1 at hr
  change _ = -vonNeumannEntropy (ludersState e u) -
    (Matrix.trace (CStarMatrix.ofMatrix.symm (ludersState e u).1 *
      ((-Real.log (d + 1)) • (1 : Matrix (Fin d) (Fin d) ℂ) +
        Real.log 2 • inputProjector u))).re + _
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hr]
  simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.one_re,
    Complex.one_im, mul_one]
  have hv : CStarMatrix.ofMatrix.symm (ludersState e u).1 =
      ludersChannel e (inputProjector u) := luders_state_density e u he
  rw [Matrix.trace_mul_comm, hv]
  ring

private theorem haar_second_moment {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ) (he : IsMIC d e) :
    (∫ u : Matrix.unitaryGroup (Fin d) ℂ,
        (Matrix.trace (inputProjector u * ludersChannel e (inputProjector u))).re ∂
          (Measure.haarMeasure
            (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ)))) =
      ((∑ i, (Matrix.trace (CFC.sqrt (e i))).re ^ 2) + d) /
        (d * (d + 1)) := by
  classical
  let mu := Measure.haarMeasure
    (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ))
  have hp : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ => inputProjector u) :=
    (continuous_subtype_val.matrix_mul continuous_const).matrix_mul
      continuous_subtype_val.matrix_conjTranspose
  have hc (i : Fin (d ^ 2)) : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
      (inputProjector u * CFC.sqrt (e i) * inputProjector u * CFC.sqrt (e i)).trace) :=
    (((hp.matrix_mul continuous_const).matrix_mul hp).matrix_mul continuous_const).matrix_trace
  have hi (i : Fin (d ^ 2)) :=
    (hc i).integrable_of_hasCompactSupport (μ := mu) (HasCompactSupport.of_compactSpace _)
  have hm (i : Fin (d ^ 2)) :
      (∫ u : Matrix.unitaryGroup (Fin d) ℂ,
        (inputProjector u * CFC.sqrt (e i) * inputProjector u * CFC.sqrt (e i)).trace.re
          ∂mu) = ((CFC.sqrt (e i)).trace.re ^ 2 + (e i).trace.re) / (d * (d + 1)) := by
    have ha := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (e i))
    have ht : ((CFC.sqrt (e i)).trace.re : ℂ) = (CFC.sqrt (e i)).trace :=
      Complex.ext rfl (by simpa using (Complex.nonneg_iff.mp ha.trace_nonneg).2)
    have het : ((e i).trace.re : ℂ) = (e i).trace :=
      Complex.ext rfl (by simpa using (Complex.nonneg_iff.mp (he.1 i).trace_nonneg).2)
    have hh := HaarPureProjectorMoment.pure_quadratic (CFC.sqrt (e i))
    change (∫ u, (inputProjector u * CFC.sqrt (e i) * inputProjector u *
      CFC.sqrt (e i)).trace ∂mu) = _ at hh
    rw [CFC.sqrt_mul_sqrt_self (e i) (he.1 i).nonneg, ← ht, ← het] at hh
    have hr : (∫ u, (inputProjector u * CFC.sqrt (e i) * inputProjector u *
        CFC.sqrt (e i)).trace ∂mu) =
        ((((CFC.sqrt (e i)).trace.re ^ 2 + (e i).trace.re) /
          (d * (d + 1) : ℝ) : ℝ) : ℂ) := by
      rw [hh]
      push_cast
      rfl
    calc
      _ = Complex.re (∫ u, (inputProjector u * CFC.sqrt (e i) * inputProjector u *
          CFC.sqrt (e i)).trace ∂mu) := integral_re (hi i)
      _ = _ := congrArg Complex.re hr
  change (∫ u, _ ∂mu) = _
  simp only [ludersChannel, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum,
    ← Matrix.mul_assoc]
  have hir (i : Fin (d ^ 2)) : Integrable (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
      (inputProjector u * CFC.sqrt (e i) * inputProjector u * CFC.sqrt (e i)).trace.re) mu :=
    (Complex.continuous_re.comp (hc i)).integrable_of_hasCompactSupport
      (μ := mu) (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum Finset.univ (fun i _ => hir i)]
  simp_rw [hm]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have ht : ∑ i, (e i).trace.re = (d : ℝ) := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, he.2.1]
    simp
  rw [ht]

private theorem rank_one_forcing {d : ℕ}
    (a : Matrix (Fin d) (Fin d) ℂ) (ha : a.PosSemidef) :
    (a.trace.re) ^ 2 ≥ (a * a).trace.re := by
  let h : HermitianMat (Fin d) ℂ := ⟨a, ha.isHermitian⟩
  have hh : 0 ≤ h := HermitianMat.zero_le_iff.mpr ha
  have hi := HermitianMat.inner_le_mul_trace hh hh
  rw [HermitianMat.inner_eq_re_trace, HermitianMat.trace_eq_re_trace] at hi
  change (a * a).trace.re ≤ a.trace.re * a.trace.re at hi
  simpa [pow_two] using hi

private theorem rank_one_from_equality {d : ℕ}
    (a : Matrix (Fin d) (Fin d) ℂ) (ha : a.PosSemidef) (ha0 : a ≠ 0)
    (heq : (a.trace.re) ^ 2 = (a * a).trace.re) :
    ∃ c : ℝ, ∃ p : Matrix (Fin d) (Fin d) ℂ,
      p.IsHermitian ∧ p * p = p ∧ p.trace = 1 ∧ a = (c : ℂ) • p := by
  let h : HermitianMat (Fin d) ℂ := ⟨a, ha.isHermitian⟩
  have hh : 0 ≤ h := HermitianMat.zero_le_iff.mpr ha
  have ht : (a.trace.re : ℂ) = a.trace :=
    Complex.ext rfl (by simpa using (Complex.nonneg_iff.mp ha.trace_nonneg).2)
  have ht0 : a.trace.re ≠ 0 := by
    intro hz
    apply ha0
    apply ha.trace_eq_zero_iff.mp
    rw [← ht, hz, Complex.ofReal_zero]
  have hinner : inner ℝ h (h.trace • 1 - h) = 0 := by
    rw [inner_sub_right, inner_smul_right, HermitianMat.inner_one,
      HermitianMat.inner_eq_re_trace, HermitianMat.trace_eq_re_trace]
    change a.trace.re * a.trace.re - (a * a).trace.re = 0
    nlinarith [heq]
  have hker := (HermitianMat.inner_zero_iff hh
    (sub_nonneg.mpr (HermitianMat.le_trace_smul_one hh))).mp hinner
  have hmul : (h.trace • (1 : HermitianMat (Fin d) ℂ) - h).mat * a = 0 := by
    apply Matrix.toEuclideanLin.injective
    have hc := LinearMap.range_le_ker_iff.mp hker
    change Matrix.toEuclideanLin _ ∘ₗ Matrix.toEuclideanLin a = 0 at hc
    calc
      _ = Matrix.toEuclideanLin (h.trace • (1 : HermitianMat (Fin d) ℂ) - h).mat ∘ₗ
          Matrix.toEuclideanLin a := by
        ext v
        simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, Matrix.toEuclideanLin]
      _ = 0 := hc
      _ = Matrix.toEuclideanLin 0 := (map_zero Matrix.toEuclideanLin).symm
  have hsquare : a * a = (a.trace.re : ℂ) • a := by
    change ((a.trace.re : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ) - a) * a = 0 at hmul
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_eq_zero] at hmul
    simpa only [← Complex.coe_smul] using hmul.symm
  refine ⟨a.trace.re, (a.trace.re : ℂ)⁻¹ • a, ?_, ?_, ?_, ?_⟩
  · exact ha.isHermitian.smul (by simp [isSelfAdjoint_iff])
  · rw [Matrix.smul_mul, Matrix.mul_smul, hsquare, smul_smul, smul_smul]
    congr 1
    field_simp
  · rw [Matrix.trace_smul, ← ht]
    exact inv_mul_cancel₀ (by exact_mod_cast ht0)
  · rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast ht0), one_smul]

private theorem relative_entropy_hs_bound {d : ℕ} [NeZero d]
    (rho sigma : DensityState (Fin d))
    (hsigma : (CStarMatrix.ofMatrix.symm sigma.1).PosDef) :
    ((CStarMatrix.ofMatrix.symm rho.1 - CStarMatrix.ofMatrix.symm sigma.1)ᴴ *
      (CStarMatrix.ofMatrix.symm rho.1 - CStarMatrix.ofMatrix.symm sigma.1)).trace.re / 2 ≤
        quantumRelativeEntropy rho sigma := by
  haveI : ContinuousFunctionalCalculus ℝ (CStarMatrix (Fin d) (Fin d) ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus
  have hpsd (s : DensityState (Fin d)) : (CStarMatrix.ofMatrix.symm s.1).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm s.2.1)
  have htrace (s : DensityState (Fin d)) :
      (CStarMatrix.ofMatrix.symm s.1).trace.re = 1 := by
    exact congrArg Complex.re s.2.2
  have hceiling (s : DensityState (Fin d)) :
      CStarMatrix.ofMatrix.symm s.1 ≤ (1 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    have heig : ∑ i, (hpsd s).1.eigenvalues i = 1 := by
      have ht := congrArg Complex.re (hpsd s).1.trace_eq_sum_eigenvalues
      simpa [htrace s] using ht.symm
    apply (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff (hpsd s).1 (1 : ℝ)).mp
    intro i
    rw [← heig]
    exact Finset.single_le_sum (fun j _ => (hpsd s).eigenvalues_nonneg j) (Finset.mem_univ i)
  have hsupport : ∀ v, CStarMatrix.ofMatrix.symm sigma.1 *ᵥ v = 0 →
      CStarMatrix.ofMatrix.symm rho.1 *ᵥ v = 0 := by
    intro v hv
    have hv0 : v = 0 := hsigma.mulVec_injective (by simpa using hv)
    rw [hv0, Matrix.mulVec_zero]
  have h := actual_matrix_spectral_ceiling_strong_klein
      _ _ (hpsd rho) (hpsd sigma) 1 (by norm_num) (hceiling rho) (hceiling sigma) hsupport
  have hlog (s : DensityState (Fin d)) :
      CStarMatrix.ofMatrix (cfc Real.log (CStarMatrix.ofMatrix.symm s.1)) = CFC.log s.1 :=
    StarAlgHomClass.map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint)
      CStarMatrix.ofMatrixStarAlgEquiv Real.log _
      ((CStarMatrix.ofMatrix.symm s.1).finite_real_spectrum.continuousOn _)
      CStarMatrix.ofMatrixL.continuous (hpsd s).1 (by exact (hpsd s).1)
  rw [htrace rho, htrace sigma] at h
  have hcross : (CStarMatrix.ofMatrix.symm rho.1 *
      (cfc Real.log (CStarMatrix.ofMatrix.symm rho.1) -
        cfc Real.log (CStarMatrix.ofMatrix.symm sigma.1))).trace.re =
      quantumRelativeEntropy rho sigma := by
    unfold quantumRelativeEntropy
    rw [← hlog rho, ← hlog sigma]
    rfl
  rw [hcross] at h
  simpa using h

private theorem continuous_luders_state {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ) (he : IsMIC d e) :
    Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ => (ludersState e u).1) := by
  have hp : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ => inputProjector u) :=
    (continuous_subtype_val.matrix_mul continuous_const).matrix_mul
      continuous_subtype_val.matrix_conjTranspose
  have hl : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
      ludersChannel e (inputProjector u)) := by
    apply continuous_finsetSum
    intro i hi
    exact (continuous_const.matrix_mul hp).matrix_mul continuous_const
  have hv : (fun u : Matrix.unitaryGroup (Fin d) ℂ => (ludersState e u).1) =
      (fun u => CStarMatrix.ofMatrix (ludersChannel e (inputProjector u))) :=
    funext (fun u => luders_state_density e u he)
  rw [hv]
  exact CStarMatrix.ofMatrixL.continuous.comp hl

private theorem continuous_output_entropy {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ) (he : IsMIC d e) :
    Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
      vonNeumannEntropy (ludersState e u)) := by
  haveI : ContinuousFunctionalCalculus ℝ (CStarMatrix (Fin d) (Fin d) ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus
  have hc : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
      cfc (fun x : ℝ => x * Real.log x) (ludersState e u).1) :=
    Continuous.cfc_of_mem_nhdsSet _ (s := Set.univ) (by simp)
      (continuous_luders_state e he) (fun u => (ludersState e u).2.1.isSelfAdjoint)
      Real.continuous_mul_log.continuousOn
  have hid (s : DensityState (Fin d)) :
      vonNeumannEntropy s =
        -(Matrix.trace (CStarMatrix.ofMatrix.symm
          (cfc (fun x : ℝ => x * Real.log x) s.1))).re := by
    let m := CStarMatrix.ofMatrix.symm s.1
    have hm : m.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm s.2.1)).1
    have hmap (f : ℝ → ℝ) : CStarMatrix.ofMatrix (cfc f m) = cfc f s.1 :=
      StarAlgHomClass.map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint)
        CStarMatrix.ofMatrixStarAlgEquiv f m (m.finite_real_spectrum.continuousOn _)
        CStarMatrix.ofMatrixL.continuous hm (by exact hm)
    have hlog : CStarMatrix.ofMatrix (cfc Real.log m) = CFC.log s.1 := by
      exact StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log m
        (m.finite_real_spectrum.continuousOn _) CStarMatrix.ofMatrixL.continuous hm
        (by exact hm)
    unfold vonNeumannEntropy
    rw [← hlog, ← hmap (fun x : ℝ => x * Real.log x)]
    change -(Matrix.trace (m * cfc Real.log m)).re = -(cfc (fun x : ℝ => x * Real.log x) m).trace.re
    have hmprod : m * cfc Real.log m = cfc (fun x : ℝ => x * Real.log x) m := by
      conv_lhs => lhs; rw [← cfc_id ℝ m hm]
      exact (cfc_mul id Real.log m (m.finite_real_spectrum.continuousOn _)
        (m.finite_real_spectrum.continuousOn _)).symm
    rw [hmprod]
  simp_rw [hid]
  exact (Complex.continuous_re.comp
    (CStarMatrix.ofMatrixL.symm.continuous.comp hc).matrix_trace).neg

private theorem saturation_remainders {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ) (he : IsMIC d e)
    (hsat : typicalEntropy d e = Real.log (d + 1) - 2 / (d + 1) * Real.log 2) :
    (∑ i, (Matrix.trace (CFC.sqrt (e i))).re ^ 2) = d ∧
      ∀ᵐ u ∂(Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ))),
        quantumRelativeEntropy (ludersState e u) (sigmaState u) = 0 := by
  let mu := Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ))
  let t := ∑ i, (Matrix.trace (CFC.sqrt (e i))).re ^ 2
  let a := ∫ u : Matrix.unitaryGroup (Fin d) ℂ,
    (inputProjector u * ludersChannel e (inputProjector u)).trace.re ∂mu
  let b := Real.log (d + 1) - 2 / (d + 1) * Real.log 2
  have hp : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ => inputProjector u) :=
    (continuous_subtype_val.matrix_mul continuous_const).matrix_mul
      continuous_subtype_val.matrix_conjTranspose
  have hl := CStarMatrix.ofMatrixL.symm.continuous.comp (continuous_luders_state e he)
  change Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
    CStarMatrix.ofMatrix.symm (ludersState e u).1) at hl
  have hlv : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
      ludersChannel e (inputProjector u)) := by
    have hv (u : Matrix.unitaryGroup (Fin d) ℂ) :
        CStarMatrix.ofMatrix.symm (ludersState e u).1 = ludersChannel e (inputProjector u) :=
      luders_state_density e u he
    simpa only [Function.comp_def, hv] using hl
  have hc : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
      (inputProjector u * ludersChannel e (inputProjector u)).trace.re) :=
    Complex.continuous_re.comp (hp.matrix_mul hlv).matrix_trace
  have hs := continuous_output_entropy e he
  have hdc : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
      quantumRelativeEntropy (ludersState e u) (sigmaState u)) := by
    have hc0 : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
        b - vonNeumannEntropy (ludersState e u) -
          ((inputProjector u * ludersChannel e (inputProjector u)).trace.re -
            2 / (d + 1)) * Real.log 2) :=
      (continuous_const.sub hs).sub ((hc.sub continuous_const).mul continuous_const)
    convert hc0 using 1
    funext u
    linarith [entropy_gap e u he]
  have hsi := hs.integrable_of_hasCompactSupport (μ := mu) (HasCompactSupport.of_compactSpace _)
  have hci := hc.integrable_of_hasCompactSupport (μ := mu) (HasCompactSupport.of_compactSpace _)
  have hdi := hdc.integrable_of_hasCompactSupport (μ := mu) (HasCompactSupport.of_compactSpace _)
  have hnonneg (u : Matrix.unitaryGroup (Fin d) ℂ) :
      0 ≤ quantumRelativeEntropy (ludersState e u) (sigmaState u) := by
    have hpd : (CStarMatrix.ofMatrix.symm (sigmaState u).1).PosDef := by
      change ((1 / (d + 1 : ℝ)) • (1 + inputProjector u)).PosDef
      exact (Matrix.PosDef.one.add_posSemidef (input_projector_psd u)).smul
        (by positivity : (0 : ℝ) < 1 / (d + 1 : ℝ))
    have hk := relative_entropy_hs_bound (ludersState e u) (sigmaState u) hpd
    have hn := (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self
      (CStarMatrix.ofMatrix.symm (ludersState e u).1 -
        CStarMatrix.ofMatrix.symm (sigmaState u).1)).trace_nonneg).1
    linarith
  have hdn : 0 ≤ ∫ u, quantumRelativeEntropy (ludersState e u) (sigmaState u) ∂mu :=
    integral_nonneg hnonneg
  have hsum : (d : ℝ) ≤ t := by
    calc
      (d : ℝ) = ∑ i, (e i).trace.re := by
        rw [← Complex.re_sum, ← Matrix.trace_sum, he.2.1]
        simp
      _ ≤ t := by
        apply Finset.sum_le_sum
        intro i hi
        have h := rank_one_forcing (CFC.sqrt (e i))
          (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (e i)))
        rwa [CFC.sqrt_mul_sqrt_self (e i) (he.1 i).nonneg] at h
  have ha : a = (t + d) / (d * (d + 1)) := haar_second_moment e he
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hac : 2 / (d + 1 : ℝ) ≤ a := by
    rw [ha]
    apply (le_div_iff₀ (by positivity)).mpr
    field_simp
    nlinarith
  have heq : 0 = (∫ u, quantumRelativeEntropy (ludersState e u) (sigmaState u) ∂mu) +
      (a - 2 / (d + 1)) * Real.log 2 := by
    have hki : Integrable (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
        ((inputProjector u * ludersChannel e (inputProjector u)).trace.re -
          2 / (d + 1)) * Real.log 2) mu :=
      (hci.sub (integrable_const (2 / (d + 1 : ℝ)))).mul_const (Real.log 2)
    have hid := integral_congr_ae (μ := mu)
      (Filter.Eventually.of_forall (fun u => entropy_gap e u he))
    rw [integral_sub (integrable_const b) hsi,
      integral_add hdi hki, integral_mul_const,
      integral_sub hci (integrable_const (2 / (d + 1 : ℝ)))] at hid
    simp only [integral_const, probReal_univ, one_smul] at hid
    change b - typicalEntropy d e = _ at hid
    rw [hsat, sub_self] at hid
    exact hid
  have haeq : a = 2 / (d + 1 : ℝ) := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  constructor
  · have hnum := (div_eq_iff (by positivity : (d : ℝ) * (d + 1) ≠ 0)).mp
      (ha.symm.trans haeq)
    field_simp at hnum
    nlinarith
  · rw [haeq, sub_self, zero_mul, add_zero] at heq
    exact (integral_eq_zero_iff_of_nonneg hnonneg hdi).mp heq.symm

private theorem saturation_forces_rank_one {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (he : IsMIC d e)
    (hsat : typicalEntropy d e = Real.log (d + 1) -
      2 / (d + 1) * Real.log 2) :
    ∀ i, ∃ c : ℝ, ∃ p : Matrix (Fin d) (Fin d) ℂ,
      p.IsHermitian ∧ p * p = p ∧ p.trace = 1 ∧ e i = (c : ℂ) • p := by
  have ht := (saturation_remainders e he hsat).1
  have hsumtrace : ∑ i, (e i).trace.re = (d : ℝ) := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, he.2.1]
    simp
  have hgap (i : Fin (d ^ 2)) : 0 ≤
      (CFC.sqrt (e i)).trace.re ^ 2 - (e i).trace.re := by
    have h := rank_one_forcing (CFC.sqrt (e i))
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (e i)))
    rw [CFC.sqrt_mul_sqrt_self (e i) (he.1 i).nonneg] at h
    linarith
  have hzero : ∑ i, ((CFC.sqrt (e i)).trace.re ^ 2 - (e i).trace.re) = 0 := by
    rw [Finset.sum_sub_distrib, ht, hsumtrace, sub_self]
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hgap j)).mp hzero i
    (Finset.mem_univ i)
  have ha0 : CFC.sqrt (e i) ≠ 0 := by
    intro hz
    have hei := CFC.sqrt_mul_sqrt_self (e i) (he.1 i).nonneg
    rw [hz, zero_mul] at hei
    exact he.2.2.ne_zero i hei.symm
  have haeq : (CFC.sqrt (e i)).trace.re ^ 2 =
      (CFC.sqrt (e i) * CFC.sqrt (e i)).trace.re := by
    rw [CFC.sqrt_mul_sqrt_self (e i) (he.1 i).nonneg]
    linarith
  obtain ⟨c, p, hp, hpp, htr, hmat⟩ := rank_one_from_equality (CFC.sqrt (e i))
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (e i))) ha0 haeq
  refine ⟨c ^ 2, p, hp, hpp, htr, ?_⟩
  rw [← CFC.sqrt_mul_sqrt_self (e i) (he.1 i).nonneg, hmat,
    Matrix.smul_mul, Matrix.mul_smul, hpp, smul_smul]
  simp [pow_two]

private theorem saturation_ae_luders_eq_sigma {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (he : IsMIC d e)
    (hsat : typicalEntropy d e = Real.log (d + 1) -
      2 / (d + 1) * Real.log 2) :
    ∀ᵐ u ∂(Measure.haarMeasure
      (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ))),
      ludersChannel e (inputProjector u) = (sigmaState u).1 := by
  filter_upwards [(saturation_remainders e he hsat).2] with u hu
  have hpd : (CStarMatrix.ofMatrix.symm (sigmaState u).1).PosDef := by
    change ((1 / (d + 1 : ℝ)) • (1 + inputProjector u)).PosDef
    exact (Matrix.PosDef.one.add_posSemidef (input_projector_psd u)).smul
      (by positivity : (0 : ℝ) < 1 / (d + 1 : ℝ))
  have hk := relative_entropy_hs_bound (ludersState e u) (sigmaState u) hpd
  rw [hu] at hk
  let x := CStarMatrix.ofMatrix.symm (ludersState e u).1 -
    CStarMatrix.ofMatrix.symm (sigmaState u).1
  have hn := Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self x).trace_nonneg
  have htr : (xᴴ * x).trace = 0 :=
    Complex.ext (by dsimp [x]; linarith) (by simpa using hn.2.symm)
  have hx : x = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htr
  have heq := sub_eq_zero.mp hx
  have hv : CStarMatrix.ofMatrix.symm (ludersState e u).1 =
      ludersChannel e (inputProjector u) := luders_state_density e u he
  rw [hv] at heq
  exact heq

private theorem saturation_everywhere_luders_eq_sigma {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (he : IsMIC d e)
    (hsat : typicalEntropy d e = Real.log (d + 1) -
      2 / (d + 1) * Real.log 2) :
    ∀ u : Matrix.unitaryGroup (Fin d) ℂ,
      ludersChannel e (inputProjector u) = (sigmaState u).1 := by
  have hp : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ => inputProjector u) :=
    (continuous_subtype_val.matrix_mul continuous_const).matrix_mul
      continuous_subtype_val.matrix_conjTranspose
  have hl : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
      ludersChannel e (inputProjector u)) := by
    apply continuous_finsetSum
    intro i hi
    exact (continuous_const.matrix_mul hp).matrix_mul continuous_const
  have hs : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
      ((sigmaState u).1 : Matrix (Fin d) (Fin d) ℂ)) := by
    change Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
      (1 / (d + 1 : ℝ)) • (1 + inputProjector u))
    exact (continuous_const.add hp).const_smul (1 / (d + 1 : ℝ))
  exact congrFun ((hl.ae_eq_iff_eq _ hs).mp
    (saturation_ae_luders_eq_sigma e he hsat))

private theorem depolarizing_identity {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (he : IsMIC d e)
    (hsat : typicalEntropy d e = Real.log (d + 1) -
      2 / (d + 1) * Real.log 2) :
    ∀ x : Matrix (Fin d) (Fin d) ℂ,
      ludersChannel e x =
        (1 / (d + 1 : ℂ)) • (x + Matrix.trace x • (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  let f : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
    { toFun := ludersChannel e
      map_add' := by
        intro x y
        simp only [ludersChannel, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp only [ludersChannel, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum,
          RingHom.id_apply] }
  let g : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
    (1 / (d + 1 : ℂ)) •
      (LinearMap.id + (Matrix.traceLinearMap (Fin d) ℂ ℂ).smulRight 1)
  have hfg : f = g := by
    apply D5.S3.Quantum.Measurements.UnitaryPureProjectorSpan.unitary_pure_ext
    intro u
    change ludersChannel e (inputProjector u) =
      (1 / (d + 1 : ℂ)) • (inputProjector u + (inputProjector u).trace • 1)
    rw [saturation_everywhere_luders_eq_sigma e he hsat u, input_projector_trace]
    change (1 / (d + 1 : ℝ)) • (1 + inputProjector u) = _
    rw [← Complex.coe_smul]
    simp [add_comm]
  intro x
  exact LinearMap.congr_fun hfg x

private theorem sic_coefficients {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (he : IsMIC d e)
    (hrank : ∀ i, ∃ c : ℝ, ∃ p : Matrix (Fin d) (Fin d) ℂ,
      p.IsHermitian ∧ p * p = p ∧ p.trace = 1 ∧ e i = (c : ℂ) • p)
    (hdepol : ∀ x : Matrix (Fin d) (Fin d) ℂ,
      ludersChannel e x =
        (1 / (d + 1 : ℂ)) • (x + Matrix.trace x • (1 : Matrix (Fin d) (Fin d) ℂ))) :
    IsSIC d e := by
  classical
  have hrank0 := hrank
  choose c p hp hpp htr heq using hrank
  have hc (i : Fin (d ^ 2)) : 0 ≤ c i := by
    have ht := Complex.nonneg_iff.mp (he.1 i).trace_nonneg
    simpa [heq i, Matrix.trace_smul, htr i] using ht.1
  have hpsd (i : Fin (d ^ 2)) : (p i).PosSemidef := by
    have hh := Matrix.posSemidef_conjTranspose_mul_self (p i)
    rwa [(hp i).eq, hpp i] at hh
  have hsqrt (i : Fin (d ^ 2)) :
      CFC.sqrt (e i) = (Real.sqrt (c i) : ℂ) • p i := by
    apply (CFC.sqrt_eq_iff _ _ (he.1 i).nonneg
      (by exact_mod_cast (hpsd i).smul (Real.sqrt_nonneg (c i)) |>.nonneg)).mpr
    rw [Matrix.smul_mul, Matrix.mul_smul, hpp i, smul_smul, heq i]
    congr 1
    norm_cast
    exact Real.mul_self_sqrt (hc i)
  have hexp (x : Matrix (Fin d) (Fin d) ℂ) :
      ludersChannel e x = ∑ i, (p i * x).trace • e i := by
    unfold ludersChannel
    apply Finset.sum_congr rfl
    intro i hi
    simp only [hsqrt, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [D5.S3.Quantum.Measurements.UnitaryPureProjectorSpan.trace_one_sandwich
        (p i) x (hpp i) (htr i), heq i, smul_smul, smul_smul]
    congr 1
    have hsq : (Real.sqrt (c i) : ℂ) * (Real.sqrt (c i) : ℂ) = (c i : ℂ) := by
      norm_cast
      exact Real.mul_self_sqrt (hc i)
    rw [hsq]
    ring
  have hcoeff (j i : Fin (d ^ 2)) :
      (p i * e j).trace = (1 / (d + 1 : ℂ)) *
        ((if i = j then 1 else 0) + (c j : ℂ)) := by
    have hsum := hdepol (e j)
    rw [hexp, heq j, Matrix.trace_smul, htr j, smul_eq_mul, mul_one] at hsum
    rw [← heq j] at hsum
    have hrhs : (1 / (d + 1 : ℂ)) • (e j + (c j : ℂ) • 1) =
        ∑ k, ((1 / (d + 1 : ℂ)) *
          ((if k = j then 1 else 0) + (c j : ℂ))) • e k := by
      simp only [add_smul, mul_smul, Finset.sum_add_distrib,
        ← Finset.smul_sum, ← he.2.1]
      congr 1
      simp
    rw [hrhs] at hsum
    have hz : ∑ k, ((p k * e j).trace - (1 / (d + 1 : ℂ)) *
        ((if k = j then 1 else 0) + (c j : ℂ))) • e k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, hsum, sub_self]
    exact sub_eq_zero.mp ((Fintype.linearIndependent_iff.mp he.2.2) _ hz i)
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have hden : (d + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show d + 1 ≠ 0 by omega)
  have hcval (j : Fin (d ^ 2)) : (c j : ℂ) = 1 / (d : ℂ) := by
    have hdiag := hcoeff j j
    rw [heq j, Matrix.mul_smul, hpp j, Matrix.trace_smul, htr j] at hdiag
    simp at hdiag
    field_simp at hdiag ⊢
    linear_combination hdiag
  refine ⟨he, hrank0, (1 / (d : ℂ)) ^ 2,
    (1 / (d : ℂ)) ^ 2 / (d + 1 : ℂ), ?_⟩
  intro i j
  rw [heq i, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, hcoeff, hcval i,
    hcval j]
  by_cases hij : i = j
  · subst j
    simp
    <;> field_simp [hd, hden]
    <;> ring
  · simp only [if_neg hij]
    ring


def claim : Prop :=
  ∀ (d : ℕ) [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ),
    IsMIC d e →
    typicalEntropy d e = Real.log (d + 1) - 2 / (d + 1) * Real.log 2 →
    ∃ f : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ, IsSIC d f

private theorem route_result_from
    (_hstate : ∀ {d : ℕ} [NeZero d]
      (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
      (u : Matrix.unitaryGroup (Fin d) ℂ), IsMIC d e →
      (ludersState e u).1 = ludersChannel e (inputProjector u))
    (_hgap : ∀ {d : ℕ} [NeZero d]
      (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
      (u : Matrix.unitaryGroup (Fin d) ℂ), IsMIC d e →
      Real.log (d + 1) - 2 / (d + 1) * Real.log 2 -
          vonNeumannEntropy (ludersState e u) =
        quantumRelativeEntropy (ludersState e u) (sigmaState u) +
          ((Matrix.trace (inputProjector u * ludersChannel e (inputProjector u))).re -
            2 / (d + 1)) * Real.log 2)
    (_hmoment : ∀ {d : ℕ} [NeZero d]
      (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ), IsMIC d e →
      (∫ u : Matrix.unitaryGroup (Fin d) ℂ,
          (Matrix.trace (inputProjector u * ludersChannel e (inputProjector u))).re ∂(Measure.haarMeasure
              (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ)))) =
        ((∑ i, (Matrix.trace (CFC.sqrt (e i))).re ^ 2) + d) /
          (d * (d + 1)))
    (_hforce : ∀ {d : ℕ} (a : Matrix (Fin d) (Fin d) ℂ), a.PosSemidef →
      (a.trace.re) ^ 2 ≥ (a * a).trace.re)
    (_hequality : ∀ {d : ℕ} (a : Matrix (Fin d) (Fin d) ℂ), a.PosSemidef →
      a ≠ 0 → (a.trace.re) ^ 2 = (a * a).trace.re →
      ∃ c : ℝ, ∃ p : Matrix (Fin d) (Fin d) ℂ,
        p.IsHermitian ∧ p * p = p ∧ p.trace = 1 ∧ a = (c : ℂ) • p)
    (hrank : ∀ {d : ℕ} [NeZero d]
      (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ), IsMIC d e →
      typicalEntropy d e = Real.log (d + 1) - 2 / (d + 1) * Real.log 2 →
      ∀ i, ∃ c : ℝ, ∃ p : Matrix (Fin d) (Fin d) ℂ,
        p.IsHermitian ∧ p * p = p ∧ p.trace = 1 ∧ e i = (c : ℂ) • p)
    (_hae : ∀ {d : ℕ} [NeZero d]
      (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ), IsMIC d e →
      typicalEntropy d e = Real.log (d + 1) - 2 / (d + 1) * Real.log 2 →
      ∀ᵐ u ∂(Measure.haarMeasure
        (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ))),
        ludersChannel e (inputProjector u) = (sigmaState u).1)
    (_hevery : ∀ {d : ℕ} [NeZero d]
      (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ), IsMIC d e →
      typicalEntropy d e = Real.log (d + 1) - 2 / (d + 1) * Real.log 2 →
      ∀ u : Matrix.unitaryGroup (Fin d) ℂ,
        ludersChannel e (inputProjector u) = (sigmaState u).1)
    (hdepol : ∀ {d : ℕ} [NeZero d]
      (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ), IsMIC d e →
      typicalEntropy d e = Real.log (d + 1) - 2 / (d + 1) * Real.log 2 →
      ∀ x : Matrix (Fin d) (Fin d) ℂ,
        ludersChannel e x =
          (1 / (d + 1 : ℂ)) • (x + Matrix.trace x • (1 : Matrix (Fin d) (Fin d) ℂ)))
    (hsic : ∀ {d : ℕ} [NeZero d]
      (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ), IsMIC d e →
      (∀ i, ∃ c : ℝ, ∃ p : Matrix (Fin d) (Fin d) ℂ,
        p.IsHermitian ∧ p * p = p ∧ p.trace = 1 ∧ e i = (c : ℂ) • p) →
      (∀ x : Matrix (Fin d) (Fin d) ℂ,
        ludersChannel e x =
          (1 / (d + 1 : ℂ)) • (x + Matrix.trace x • (1 : Matrix (Fin d) (Fin d) ℂ))) →
      IsSIC d e) : claim := by
  intro d inst e he hsat
  have hrank' := hrank e he hsat
  have hdepol' := hdepol e he hsat
  exact ⟨e, hsic e he hrank' hdepol'⟩

private theorem route_result : claim :=
  route_result_from luders_state_density entropy_gap haar_second_moment
    rank_one_forcing rank_one_from_equality saturation_forces_rank_one
    saturation_ae_luders_eq_sigma saturation_everywhere_luders_eq_sigma
    depolarizing_identity sic_coefficients

theorem result : claim := route_result

end D5.S3.Quantum.Measurements.LudersEntropySaturationSIC
