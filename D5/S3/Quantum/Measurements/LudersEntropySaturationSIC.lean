/- GID: D5/S3/Quantum/Measurements/LudersEntropySaturationSIC
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/LudersEntropySaturationSIC
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Entropy saturation of a Lüders MIC channel forces the source SIC structure. -/

import D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.States.Mixed.MState.Basic
import D5.S3.Quantum.Matrix.TwoPointFunctionalCalculus
import D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
import D5.S3.Quantum.Information.OrthogonalRecordEntropy

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

private theorem unitary_pure_ext {d : ℕ} [NeZero d]
    (f g : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ u : Matrix.unitaryGroup (Fin d) ℂ,
      f (u.1 * Matrix.single 0 0 1 * u.1ᴴ) =
        g (u.1 * Matrix.single 0 0 1 * u.1ᴴ)) : f = g := by
  have hs (u : Matrix.unitaryGroup (Fin d) ℂ) (i : Fin d) :
      f (u.1 * Matrix.single i i 1 * u.1ᴴ) =
        g (u.1 * Matrix.single i i 1 * u.1ᴴ) := by
    let p := (Equiv.swap (0 : Fin d) i).permMatrix ℂ
    let v : Matrix.unitaryGroup (Fin d) ℂ :=
      u * D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.permutationUnitary (Equiv.swap 0 i)
    have hsingle : p * Matrix.single 0 0 1 * pᴴ = Matrix.single i i 1 := by
      dsimp [p]
      rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul,
        PEquiv.mul_toMatrix_toPEquiv]
      simp [Matrix.submatrix_single_equiv]
    have hv : v.1 * Matrix.single 0 0 1 * v.1ᴴ =
        u.1 * Matrix.single i i 1 * u.1ᴴ := by
      change (u.1 * p) * Matrix.single 0 0 1 * (u.1 * p)ᴴ = _
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc p (Matrix.single 0 0 1),
        ← Matrix.mul_assoc (p * Matrix.single 0 0 1), hsingle]
    simpa only [hv] using h v
  have hh (x : Matrix (Fin d) (Fin d) ℂ) (hx : x.IsHermitian) : f x = g x := by
    let u := hx.eigenvectorUnitary
    have hdec : x = ∑ i, (hx.eigenvalues i : ℂ) •
        ((u : Matrix (Fin d) (Fin d) ℂ) * Matrix.single i i 1 *
          (u : Matrix (Fin d) (Fin d) ℂ)ᴴ) := by
      let a : HermitianMat (Fin d) ℂ := ⟨x, hx⟩
      have hs := a.cfc_toMat_eq_sum_smul_proj id
      rw [HermitianMat.cfc_id] at hs
      change x = ∑ i, hx.eigenvalues i •
        (hx.eigenvectorUnitary.val * Matrix.single i i 1 * hx.eigenvectorUnitary.valᴴ) at hs
      simpa only [id_eq, Complex.coe_smul] using hs
    rw [hdec, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul, map_smul, hs u i]
  apply LinearMap.ext
  intro x
  rw [← realPart_add_I_smul_imaginaryPart x, map_add, map_add,
    map_smul, map_smul, hh _ (realPart x).2, hh _ (imaginaryPart x).2]

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

private def inputProjector {d : ℕ} [NeZero d]
    (u : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  u.1 * Matrix.single 0 0 1 * u.1ᴴ

private theorem input_projector_psd {d : ℕ} [NeZero d]
    (u : Matrix.unitaryGroup (Fin d) ℂ) :
    (inputProjector u).PosSemidef := by
  exact ((Matrix.PosSemidef.stdBasisMatrix_iff_eq 0 0
    (by norm_num : (0 : ℂ) < 1)).mpr rfl).mul_mul_conjTranspose_same u.1

private theorem input_projector_trace {d : ℕ} [NeZero d]
    (u : Matrix.unitaryGroup (Fin d) ℂ) :
    (inputProjector u).trace = 1 :=
  (Matrix.trace_units_conj (Unitary.toUnits u) (Matrix.single 0 0 1)).trans
    (Matrix.trace_single_eq_same _ _)

private theorem input_projector_idempotent {d : ℕ} [NeZero d]
    (u : Matrix.unitaryGroup (Fin d) ℂ) :
    inputProjector u * inputProjector u = inputProjector u := by
  have hb : IsIdempotentElem (Matrix.single (0 : Fin d) (0 : Fin d) (1 : ℂ)) := by
    change Matrix.single (0 : Fin d) 0 (1 : ℂ) * Matrix.single 0 0 1 = Matrix.single 0 0 1
    simpa only [mul_one] using
      Matrix.single_mul_single_same (1 : ℂ) (0 : Fin d) (0 : Fin d) (0 : Fin d) 1
  change (u.1 * Matrix.single 0 0 1 * u.1ᴴ) * (u.1 * Matrix.single 0 0 1 * u.1ᴴ) =
    u.1 * Matrix.single 0 0 1 * u.1ᴴ
  simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
    (hb.map (Unitary.conjStarAlgAut ℂ _ u)).eq

private noncomputable def ludersState {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (u : Matrix.unitaryGroup (Fin d) ℂ) :
    DensityState (Fin d) := by
  classical
  by_cases he : IsMIC d e
  · refine ⟨D5.S3.Observer.Conditioning.unreadState
      (fun i => CFC.sqrt (e i)) (inputProjector u), ?_, ?_⟩
    · change 0 ≤ CStarMatrix.ofMatrix (D5.S3.Observer.Conditioning.unreadState
        (fun i => CFC.sqrt (e i)) (inputProjector u))
      refine map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
        (Matrix.nonneg_iff_posSemidef.mpr ?_)
      rw [D5.S3.Observer.Conditioning.unreadState]
      apply Matrix.posSemidef_sum Finset.univ
      intro i hi
      have hx : (inputProjector u).PosSemidef := input_projector_psd u
      have hterm := hx.conjTranspose_mul_mul_same (B := CFC.sqrt (e i))
      have hs : (CFC.sqrt (e i))ᴴ = CFC.sqrt (e i) := by
        simpa (config := { congrConsts := false }) [Matrix.star_eq_conjTranspose] using
          (CFC.sqrt_nonneg (e i)).isSelfAdjoint.star_eq
      simpa (config := { congrConsts := false }) [hs, Matrix.mul_assoc] using hterm
    · rw [show D5.S3.Observer.Conditioning.unreadState
          (fun i => CFC.sqrt (e i)) (inputProjector u) =
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
        _ = 1 := by
          simpa (config := { congrConsts := false }) [Matrix.mul_one]
            using input_projector_trace u
  · exact D5.S3.Quantum.Information.OrthogonalRecordEntropy.pointerState (0 : Fin d)

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
  simp (config := { congrConsts := false }) [Matrix.trace, Finset.sum_const]
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
    (ludersState e u).1 = D5.S3.Observer.Conditioning.unreadState
      (fun i => CFC.sqrt (e i)) (inputProjector u) := by
  rw [ludersState]
  simp (config := { congrConsts := false }) [he]
  rfl

private theorem sigma_log {d : ℕ} [NeZero d]
    (u : Matrix.unitaryGroup (Fin d) ℂ) :
    CFC.log (sigmaState u).1 = CStarMatrix.ofMatrix
      ((-Real.log (d + 1)) • (1 : Matrix (Fin d) (Fin d) ℂ) +
        Real.log 2 • inputProjector u) := by
  have : Nontrivial (CStarMatrix (Fin d) (Fin d) ℂ) := inferInstance
  have : ContinuousFunctionalCalculus ℝ (CStarMatrix (Fin d) (Fin d) ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus
  let k : ℝ := 1 / (d + 1)
  let p := inputProjector u
  let h : Matrix (Fin d) (Fin d) ℂ := (2 : ℝ) • p - 1
  have hp : p.IsHermitian := (input_projector_psd u).isHermitian
  have hpp : p * p = p := input_projector_idempotent u
  have hh : IsSelfAdjoint h :=
    (hp.smul (isSelfAdjoint_iff.mpr (by simp (config := { congrConsts := false })) :
      IsSelfAdjoint (2 : ℝ))).sub
      Matrix.isHermitian_one
  have hhh : h * h = 1 := by
    dsimp [h]
    simp (config := { congrConsts := false }) only [sub_mul, mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, mul_one, one_mul, hpp, smul_smul]
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
  have hlog : Real.log k = -Real.log (d + 1) := by simp (config := { congrConsts := false }) [k]
  have hq : (k • (1 + p) : Matrix (Fin d) (Fin d) ℂ).IsHermitian := by
    exact (Matrix.isHermitian_one.add hp).smul
      (by simp (config := { congrConsts := false }) [isSelfAdjoint_iff])
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
        ((Matrix.trace (inputProjector u * D5.S3.Observer.Conditioning.unreadState
          (fun i => CFC.sqrt (e i)) (inputProjector u))).re -
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
  simp (config := { congrConsts := false }) only [Complex.add_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_one]
  have hv : CStarMatrix.ofMatrix.symm (ludersState e u).1 =
      D5.S3.Observer.Conditioning.unreadState (fun i => CFC.sqrt (e i)) (inputProjector u) :=
    luders_state_density e u he
  rw [Matrix.trace_mul_comm, hv]
  ring

private theorem haar_second_moment {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ) (he : IsMIC d e) :
    (∫ u : Matrix.unitaryGroup (Fin d) ℂ,
        (Matrix.trace (inputProjector u * D5.S3.Observer.Conditioning.unreadState
          (fun i => CFC.sqrt (e i)) (inputProjector u))).re ∂
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
      ha.isHermitian.re_trace_eq_trace
    have het : ((e i).trace.re : ℂ) = (e i).trace :=
      (he.1 i).isHermitian.re_trace_eq_trace
    have hh := D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.pure_quadratic (CFC.sqrt (e i))
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
  simp (config := { congrConsts := false }) only [D5.S3.Observer.Conditioning.unreadState,
    Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, ← Matrix.mul_assoc]
  have hir (i : Fin (d ^ 2)) : Integrable (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
      (inputProjector u * CFC.sqrt (e i) * inputProjector u * CFC.sqrt (e i)).trace.re) mu :=
    (Complex.continuous_re.comp (hc i)).integrable_of_hasCompactSupport
      (μ := mu) (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum Finset.univ (fun i _ => hir i)]
  simp_rw (config := { congrConsts := false }) [hm]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have ht : ∑ i, (e i).trace.re = (d : ℝ) := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, he.2.1]
    simp (config := { congrConsts := false })
  rw [ht]

private theorem rank_one_forcing {d : ℕ}
    (a : Matrix (Fin d) (Fin d) ℂ) (ha : a.PosSemidef) :
    (a.trace.re) ^ 2 ≥ (a * a).trace.re := by
  let h : HermitianMat (Fin d) ℂ := ⟨a, ha.isHermitian⟩
  have hh : 0 ≤ h := HermitianMat.zero_le_iff.mpr ha
  have hi := HermitianMat.inner_le_mul_trace hh hh
  rw [HermitianMat.inner_eq_re_trace, HermitianMat.trace_eq_re_trace] at hi
  change (a * a).trace.re ≤ a.trace.re * a.trace.re at hi
  simpa (config := { congrConsts := false }) [pow_two] using hi

private theorem rank_one_from_equality {d : ℕ}
    (a : Matrix (Fin d) (Fin d) ℂ) (ha : a.PosSemidef) (ha0 : a ≠ 0)
    (heq : (a.trace.re) ^ 2 = (a * a).trace.re) :
    ∃ c : ℝ, ∃ p : Matrix (Fin d) (Fin d) ℂ,
      p.IsHermitian ∧ p * p = p ∧ p.trace = 1 ∧ a = (c : ℂ) • p := by
  let h : HermitianMat (Fin d) ℂ := ⟨a, ha.isHermitian⟩
  have hh : 0 ≤ h := HermitianMat.zero_le_iff.mpr ha
  have ht : (a.trace.re : ℂ) = a.trace :=
    ha.isHermitian.re_trace_eq_trace
  have ht0 : a.trace.re ≠ 0 := by
    intro hz
    apply ha0
    apply ha.trace_eq_zero_iff.mp
    rw [← ht, hz, Complex.ofReal_zero]
  let rho : MState (Fin d) := ⟨a.trace.re⁻¹ • h,
    smul_nonneg (inv_nonneg.mpr (HermitianMat.trace_nonneg hh)) hh, by
      rw [HermitianMat.trace_smul, HermitianMat.trace_eq_re_trace]
      exact inv_mul_cancel₀ ht0⟩
  have hpurity : rho.purity = 1 := by
    apply Subtype.ext
    change inner ℝ (a.trace.re⁻¹ • h) (a.trace.re⁻¹ • h) = (1 : ℝ)
    rw [HermitianMat.inner_smul_left, HermitianMat.inner_smul_right,
      HermitianMat.inner_eq_re_trace]
    change a.trace.re⁻¹ * (a.trace.re⁻¹ * (a * a).trace.re) = 1
    rw [← heq]
    field_simp
  obtain ⟨ψ, hψ⟩ := (MState.pure_iff_purity_one rho).mpr hpurity
  refine ⟨a.trace.re, rho.m, rho.Hermitian, ?_, rho.tr', ?_⟩
  · rw [hψ]
    exact MState.pure_mul_self ψ
  · change a = (a.trace.re : ℂ) • (a.trace.re⁻¹ • a)
    rw [Complex.coe_smul, smul_smul, mul_inv_cancel₀ ht0, one_smul]

private theorem relative_entropy_hs_bound {d : ℕ} [NeZero d]
    (rho sigma : DensityState (Fin d))
    (hsigma : (CStarMatrix.ofMatrix.symm sigma.1).PosDef) :
    ((CStarMatrix.ofMatrix.symm rho.1 - CStarMatrix.ofMatrix.symm sigma.1)ᴴ *
      (CStarMatrix.ofMatrix.symm rho.1 - CStarMatrix.ofMatrix.symm sigma.1)).trace.re / 2 ≤
        quantumRelativeEntropy rho sigma := by
  have : ContinuousFunctionalCalculus ℝ (CStarMatrix (Fin d) (Fin d) ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus
  have hpsd (s : DensityState (Fin d)) : (CStarMatrix.ofMatrix.symm s.1).PosSemidef :=
    D5.S3.Quantum.Information.PartialTraceMutualInformation.density_posSemidef s
  have htrace (s : DensityState (Fin d)) :
      (CStarMatrix.ofMatrix.symm s.1).trace.re = 1 := by
    exact congrArg Complex.re s.2.2
  have hceiling (s : DensityState (Fin d)) :
      CStarMatrix.ofMatrix.symm s.1 ≤ (1 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    let h : HermitianMat (Fin d) ℂ := ⟨_, (hpsd s).isHermitian⟩
    have hb := HermitianMat.le_trace_smul_one
      (HermitianMat.zero_le_iff.mpr (hpsd s) : 0 ≤ h)
    change CStarMatrix.ofMatrix.symm s.1 ≤
      (CStarMatrix.ofMatrix.symm s.1).trace.re • (1 : Matrix (Fin d) (Fin d) ℂ) at hb
    simpa only [htrace s, one_smul] using hb
  have hsupport : ∀ v, CStarMatrix.ofMatrix.symm sigma.1 *ᵥ v = 0 →
      CStarMatrix.ofMatrix.symm rho.1 *ᵥ v = 0 := by
    intro v hv
    have hv0 : v = 0 := hsigma.mulVec_injective
      (by simpa (config := { congrConsts := false }) using hv)
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
  simpa (config := { congrConsts := false }) using h

private theorem continuous_luders_state {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ) (he : IsMIC d e) :
    Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ => (ludersState e u).1) := by
  have hp : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ => inputProjector u) :=
    (continuous_subtype_val.matrix_mul continuous_const).matrix_mul
      continuous_subtype_val.matrix_conjTranspose
  have hl : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
      D5.S3.Observer.Conditioning.unreadState (fun i => CFC.sqrt (e i)) (inputProjector u)) := by
    apply continuous_finsetSum
    intro i hi
    exact (continuous_const.matrix_mul hp).matrix_mul continuous_const
  have hv : (fun u : Matrix.unitaryGroup (Fin d) ℂ => (ludersState e u).1) =
      (fun u => CStarMatrix.ofMatrix (D5.S3.Observer.Conditioning.unreadState
        (fun i => CFC.sqrt (e i)) (inputProjector u))) :=
    funext (fun u => luders_state_density e u he)
  rw [hv]
  exact CStarMatrix.ofMatrixL.continuous.comp hl

private theorem continuous_output_entropy {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ) (he : IsMIC d e) :
    Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
      vonNeumannEntropy (ludersState e u)) := by
  have : ContinuousFunctionalCalculus ℝ (CStarMatrix (Fin d) (Fin d) ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus
  have hc : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
      cfc (fun x : ℝ => x * Real.log x) (ludersState e u).1) :=
    Continuous.cfc_of_mem_nhdsSet _ (s := Set.univ) (by simp (config := { congrConsts := false }))
      (continuous_luders_state e he) (fun u => (ludersState e u).2.1.isSelfAdjoint)
      Real.continuous_mul_log.continuousOn
  have hid (s : DensityState (Fin d)) :
      vonNeumannEntropy s =
        -(Matrix.trace (CStarMatrix.ofMatrix.symm
          (cfc (fun x : ℝ => x * Real.log x) s.1))).re := by
    rw [D5.S3.Quantum.Information.OrthogonalRecordEntropy.entropy_eq_trace_cfc]
    change (Matrix.trace (CStarMatrix.ofMatrix.symm (cfc Real.negMulLog s.1))).re = _
    rw [show Real.negMulLog = fun x : ℝ => -(x * Real.log x) by
      funext x; simp only [Real.negMulLog, neg_mul],
      cfc_neg (fun x : ℝ => x * Real.log x) s.1]
    change (Matrix.trace (-CStarMatrix.ofMatrix.symm
      (cfc (fun x : ℝ => x * Real.log x) s.1))).re = _
    rw [Matrix.trace_neg, Complex.neg_re]
  simp_rw (config := { congrConsts := false }) [hid]
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
    (inputProjector u * D5.S3.Observer.Conditioning.unreadState
      (fun i => CFC.sqrt (e i)) (inputProjector u)).trace.re ∂mu
  let b := Real.log (d + 1) - 2 / (d + 1) * Real.log 2
  have hp : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ => inputProjector u) :=
    (continuous_subtype_val.matrix_mul continuous_const).matrix_mul
      continuous_subtype_val.matrix_conjTranspose
  have hl := CStarMatrix.ofMatrixL.symm.continuous.comp (continuous_luders_state e he)
  change Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
    CStarMatrix.ofMatrix.symm (ludersState e u).1) at hl
  have hlv : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
      D5.S3.Observer.Conditioning.unreadState (fun i => CFC.sqrt (e i)) (inputProjector u)) := by
    have hv (u : Matrix.unitaryGroup (Fin d) ℂ) :
        CStarMatrix.ofMatrix.symm (ludersState e u).1 = D5.S3.Observer.Conditioning.unreadState
          (fun i => CFC.sqrt (e i)) (inputProjector u) :=
      luders_state_density e u he
    simpa (config := { congrConsts := false }) only [Function.comp_def, hv] using hl
  have hc : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
      (inputProjector u * D5.S3.Observer.Conditioning.unreadState
        (fun i => CFC.sqrt (e i)) (inputProjector u)).trace.re) :=
    Complex.continuous_re.comp (hp.matrix_mul hlv).matrix_trace
  have hs := continuous_output_entropy e he
  have hdc : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
      quantumRelativeEntropy (ludersState e u) (sigmaState u)) := by
    have hc0 : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
        b - vonNeumannEntropy (ludersState e u) -
          ((inputProjector u * D5.S3.Observer.Conditioning.unreadState
            (fun i => CFC.sqrt (e i)) (inputProjector u)).trace.re -
            2 / (d + 1)) * Real.log 2) :=
      (continuous_const.sub hs).sub ((hc.sub continuous_const).mul continuous_const)
    convert hc0 using 1
    funext u
    exact eq_sub_of_add_eq (entropy_gap e u he).symm
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
    exact (div_nonneg hn (by norm_num)).trans hk
  have hdn : 0 ≤ ∫ u, quantumRelativeEntropy (ludersState e u) (sigmaState u) ∂mu :=
    integral_nonneg hnonneg
  have hsum : (d : ℝ) ≤ t := by
    calc
      (d : ℝ) = ∑ i, (e i).trace.re := by
        rw [← Complex.re_sum, ← Matrix.trace_sum, he.2.1]
        simp (config := { congrConsts := false })
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
    nlinarith only [hsum]
  have heq : 0 = (∫ u, quantumRelativeEntropy (ludersState e u) (sigmaState u) ∂mu) +
      (a - 2 / (d + 1)) * Real.log 2 := by
    have hki : Integrable (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
        ((inputProjector u * D5.S3.Observer.Conditioning.unreadState
          (fun i => CFC.sqrt (e i)) (inputProjector u)).trace.re -
          2 / (d + 1)) * Real.log 2) mu :=
      (hci.sub (integrable_const (2 / (d + 1 : ℝ)))).mul_const (Real.log 2)
    have hid := integral_congr_ae (μ := mu)
      (Filter.Eventually.of_forall (fun u => entropy_gap e u he))
    rw [integral_sub (integrable_const b) hsi,
      integral_add hdi hki, integral_mul_const,
      integral_sub hci (integrable_const (2 / (d + 1 : ℝ)))] at hid
    simp (config := { congrConsts := false }) only [integral_const, probReal_univ, one_smul] at hid
    change b - typicalEntropy d e = _ at hid
    rw [hsat, sub_self] at hid
    exact hid
  have haeq : a = 2 / (d + 1 : ℝ) := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hz := ((add_eq_zero_iff_of_nonneg hdn
      (mul_nonneg (sub_nonneg.mpr hac) hlog.le)).mp heq.symm).2
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (ne_of_gt hlog))
  constructor
  · have hnum := (div_eq_iff (by positivity : (d : ℝ) * (d + 1) ≠ 0)).mp
      (ha.symm.trans haeq)
    field_simp at hnum
    nlinarith only [hnum, hd]
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
    simp (config := { congrConsts := false })
  have hgap (i : Fin (d ^ 2)) : 0 ≤
      (CFC.sqrt (e i)).trace.re ^ 2 - (e i).trace.re := by
    have h := rank_one_forcing (CFC.sqrt (e i))
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (e i)))
    rw [CFC.sqrt_mul_sqrt_self (e i) (he.1 i).nonneg] at h
    exact sub_nonneg.mpr h
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
    exact sub_eq_zero.mp hi
  obtain ⟨c, p, hp, hpp, htr, hmat⟩ := rank_one_from_equality (CFC.sqrt (e i))
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (e i))) ha0 haeq
  refine ⟨c ^ 2, p, hp, hpp, htr, ?_⟩
  rw [← CFC.sqrt_mul_sqrt_self (e i) (he.1 i).nonneg, hmat,
    Matrix.smul_mul, Matrix.mul_smul, hpp, smul_smul]
  simp (config := { congrConsts := false }) [pow_two]

private theorem saturation_ae_luders_eq_sigma {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (he : IsMIC d e)
    (hsat : typicalEntropy d e = Real.log (d + 1) -
      2 / (d + 1) * Real.log 2) :
    ∀ᵐ u ∂(Measure.haarMeasure
      (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ))),
      D5.S3.Observer.Conditioning.unreadState (fun i => CFC.sqrt (e i)) (inputProjector u) =
        (sigmaState u).1 := by
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
  have hle : (xᴴ * x).trace.re ≤ 0 := by
    have hhk : (xᴴ * x).trace.re / 2 ≤ 0 := hk
    have hle0 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hhk
    simpa (config := { congrConsts := false }) only [zero_mul] using hle0
  have htr : (xᴴ * x).trace = 0 :=
    Complex.ext (le_antisymm hle hn.1) hn.2.symm
  have hx : x = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htr
  have heq := sub_eq_zero.mp hx
  have hv : CStarMatrix.ofMatrix.symm (ludersState e u).1 =
      D5.S3.Observer.Conditioning.unreadState (fun i => CFC.sqrt (e i)) (inputProjector u) :=
    luders_state_density e u he
  rw [hv] at heq
  exact heq

private theorem saturation_everywhere_luders_eq_sigma {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (he : IsMIC d e)
    (hsat : typicalEntropy d e = Real.log (d + 1) -
      2 / (d + 1) * Real.log 2) :
    ∀ u : Matrix.unitaryGroup (Fin d) ℂ,
      D5.S3.Observer.Conditioning.unreadState (fun i => CFC.sqrt (e i)) (inputProjector u) =
        (sigmaState u).1 := by
  have hp : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ => inputProjector u) :=
    (continuous_subtype_val.matrix_mul continuous_const).matrix_mul
      continuous_subtype_val.matrix_conjTranspose
  have hl : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
      D5.S3.Observer.Conditioning.unreadState (fun i => CFC.sqrt (e i)) (inputProjector u)) := by
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
      D5.S3.Observer.Conditioning.unreadState (fun i => CFC.sqrt (e i)) x =
        (1 / (d + 1 : ℂ)) • (x + Matrix.trace x • (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  let f : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
    { toFun := D5.S3.Observer.Conditioning.unreadState (fun i => CFC.sqrt (e i))
      map_add' := by
        intro x y
        simp (config := { congrConsts := false }) only [D5.S3.Observer.Conditioning.unreadState,
          Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp (config := { congrConsts := false }) only [D5.S3.Observer.Conditioning.unreadState,
          Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, RingHom.id_apply] }
  let g : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
    (1 / (d + 1 : ℂ)) •
      (LinearMap.id + (Matrix.traceLinearMap (Fin d) ℂ ℂ).smulRight 1)
  have hfg : f = g := by
    apply unitary_pure_ext
    intro u
    change D5.S3.Observer.Conditioning.unreadState (fun i => CFC.sqrt (e i)) (inputProjector u) =
      (1 / (d + 1 : ℂ)) • (inputProjector u + (inputProjector u).trace • 1)
    rw [saturation_everywhere_luders_eq_sigma e he hsat u, input_projector_trace]
    change (1 / (d + 1 : ℝ)) • (1 + inputProjector u) = _
    rw [← Complex.coe_smul]
    simp (config := { congrConsts := false }) [add_comm]
  intro x
  exact LinearMap.congr_fun hfg x

private theorem sic_coefficients {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (he : IsMIC d e)
    (hrank : ∀ i, ∃ c : ℝ, ∃ p : Matrix (Fin d) (Fin d) ℂ,
      p.IsHermitian ∧ p * p = p ∧ p.trace = 1 ∧ e i = (c : ℂ) • p)
    (hdepol : ∀ x : Matrix (Fin d) (Fin d) ℂ,
      D5.S3.Observer.Conditioning.unreadState (fun i => CFC.sqrt (e i)) x =
        (1 / (d + 1 : ℂ)) • (x + Matrix.trace x • (1 : Matrix (Fin d) (Fin d) ℂ))) :
    IsSIC d e := by
  classical
  have hrank0 := hrank
  choose c p hp hpp htr heq using hrank
  have hc (i : Fin (d ^ 2)) : 0 ≤ c i := by
    have ht := Complex.nonneg_iff.mp (he.1 i).trace_nonneg
    simpa (config := { congrConsts := false }) [heq i, Matrix.trace_smul, htr i] using ht.1
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
      D5.S3.Observer.Conditioning.unreadState (fun i => CFC.sqrt (e i)) x =
        ∑ i, (p i * x).trace • e i := by
    unfold D5.S3.Observer.Conditioning.unreadState
    apply Finset.sum_congr rfl
    intro i hi
    simp (config := { congrConsts := false }) only [hsqrt, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    rw [D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.trace_one_sandwich
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
      simp (config := { congrConsts := false }) only [add_smul, mul_smul, Finset.sum_add_distrib,
        ← Finset.smul_sum, ← he.2.1]
      congr 1
      simp (config := { congrConsts := false })
    rw [hrhs] at hsum
    have hz : ∑ k, ((p k * e j).trace - (1 / (d + 1 : ℂ)) *
        ((if k = j then 1 else 0) + (c j : ℂ))) • e k = 0 := by
      simp (config := { congrConsts := false }) only [sub_smul, Finset.sum_sub_distrib,
        hsum, sub_self]
    exact sub_eq_zero.mp ((Fintype.linearIndependent_iff.mp he.2.2) _ hz i)
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have hden : (d + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show d + 1 ≠ 0 by omega)
  have hcval (j : Fin (d ^ 2)) : (c j : ℂ) = 1 / (d : ℂ) := by
    have hdiag := hcoeff j j
    rw [heq j, Matrix.mul_smul, hpp j, Matrix.trace_smul, htr j] at hdiag
    simp (config := { congrConsts := false }) at hdiag
    field_simp at hdiag ⊢
    linear_combination hdiag
  refine ⟨he, hrank0, (1 / (d : ℂ)) ^ 2,
    (1 / (d : ℂ)) ^ 2 / (d + 1 : ℂ), ?_⟩
  intro i j
  rw [heq i, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, hcoeff, hcval i,
    hcval j]
  by_cases hij : i = j
  · subst j
    simp (config := { congrConsts := false })
    field_simp [hd, hden]
  · simp (config := { congrConsts := false }) only [ite_eq_right hij]
    ring


def claim : Prop :=
  ∀ (d : ℕ) [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ),
    IsMIC d e →
    typicalEntropy d e = Real.log (d + 1) - 2 / (d + 1) * Real.log 2 →
    ∃ f : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ, IsSIC d f

private theorem route_result_from
    (hrank : ∀ {d : ℕ} [NeZero d]
      (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ), IsMIC d e →
      typicalEntropy d e = Real.log (d + 1) - 2 / (d + 1) * Real.log 2 →
      ∀ i, ∃ c : ℝ, ∃ p : Matrix (Fin d) (Fin d) ℂ,
        p.IsHermitian ∧ p * p = p ∧ p.trace = 1 ∧ e i = (c : ℂ) • p)
    (hdepol : ∀ {d : ℕ} [NeZero d]
      (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ), IsMIC d e →
      typicalEntropy d e = Real.log (d + 1) - 2 / (d + 1) * Real.log 2 →
      ∀ x : Matrix (Fin d) (Fin d) ℂ,
        D5.S3.Observer.Conditioning.unreadState (fun i => CFC.sqrt (e i)) x =
          (1 / (d + 1 : ℂ)) • (x + Matrix.trace x • (1 : Matrix (Fin d) (Fin d) ℂ)))
    (hsic : ∀ {d : ℕ} [NeZero d]
      (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ), IsMIC d e →
      (∀ i, ∃ c : ℝ, ∃ p : Matrix (Fin d) (Fin d) ℂ,
        p.IsHermitian ∧ p * p = p ∧ p.trace = 1 ∧ e i = (c : ℂ) • p) →
      (∀ x : Matrix (Fin d) (Fin d) ℂ,
        D5.S3.Observer.Conditioning.unreadState (fun i => CFC.sqrt (e i)) x =
          (1 / (d + 1 : ℂ)) • (x + Matrix.trace x • (1 : Matrix (Fin d) (Fin d) ℂ))) →
      IsSIC d e) : claim := by
  intro d inst e he hsat
  have hrank' := hrank e he hsat
  have hdepol' := hdepol e he hsat
  exact ⟨e, hsic e he hrank' hdepol'⟩

private theorem route_result : claim :=
  route_result_from saturation_forces_rank_one depolarizing_identity sic_coefficients

theorem result : claim := route_result

end D5.S3.Quantum.Measurements.LudersEntropySaturationSIC
