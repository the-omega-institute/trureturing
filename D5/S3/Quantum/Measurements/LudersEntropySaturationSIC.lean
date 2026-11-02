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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-! DeBrota--Stacey's saturation implication for Lüders MIC channels. -/

open scoped BigOperators CStarAlgebra ComplexOrder Matrix MatrixOrder
open MeasureTheory TopologicalSpace

noncomputable section

namespace D5.S3.Quantum.Measurements.LudersEntropySaturationSIC

open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching

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
  sorry

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

private theorem saturation_forces_rank_one {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (he : IsMIC d e)
    (hsat : typicalEntropy d e = Real.log (d + 1) -
      2 / (d + 1) * Real.log 2) :
    ∀ i, ∃ c : ℝ, ∃ p : Matrix (Fin d) (Fin d) ℂ,
      p.IsHermitian ∧ p * p = p ∧ p.trace = 1 ∧ e i = (c : ℂ) • p := by
  sorry

private theorem saturation_ae_luders_eq_sigma {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (he : IsMIC d e)
    (hsat : typicalEntropy d e = Real.log (d + 1) -
      2 / (d + 1) * Real.log 2) :
    ∀ᵐ u ∂(Measure.haarMeasure
      (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ))),
      ludersChannel e (inputProjector u) = (sigmaState u).1 := by
  sorry

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
        (x + Matrix.trace x • (1 : Matrix (Fin d) (Fin d) ℂ)) / (d + 1) := by
  sorry

private theorem sic_coefficients {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (he : IsMIC d e)
    (hrank : ∀ i, ∃ c : ℝ, ∃ p : Matrix (Fin d) (Fin d) ℂ,
      p.IsHermitian ∧ p * p = p ∧ p.trace = 1 ∧ e i = (c : ℂ) • p)
    (hdepol : ∀ x : Matrix (Fin d) (Fin d) ℂ,
      ludersChannel e x =
        (x + Matrix.trace x • (1 : Matrix (Fin d) (Fin d) ℂ)) / (d + 1)) :
    IsSIC d e := by
  sorry

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
          (x + Matrix.trace x • (1 : Matrix (Fin d) (Fin d) ℂ)) / (d + 1))
    (hsic : ∀ {d : ℕ} [NeZero d]
      (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ), IsMIC d e →
      (∀ i, ∃ c : ℝ, ∃ p : Matrix (Fin d) (Fin d) ℂ,
        p.IsHermitian ∧ p * p = p ∧ p.trace = 1 ∧ e i = (c : ℂ) • p) →
      (∀ x : Matrix (Fin d) (Fin d) ℂ,
        ludersChannel e x =
          (x + Matrix.trace x • (1 : Matrix (Fin d) (Fin d) ℂ)) / (d + 1)) →
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
