/- GID: D5/S3/Quantum/Dynamics/PolygonalFourierCouplings
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/PolygonalFourierCouplings
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive polygonal couplings realize every discrete Fourier transform. -/

/-
admission_basis: open-problem-resolution (#13954; Proved).
utility: none: all statements are uniform analytical identities or constructions in N.
The auxiliary declarations below are consumed by result.
proof_shape: fourier, IsUnimodularDiagonal, IsPolygonalCoupling, claim: definitions;
  escape_witness: not applicable; consumers: claim and result.
proof_shape: chirpInt, chirp: definitions; escape_witness: not applicable;
  consumers: chirpInt_periodic, chirp_intCast, chirp_even, chirp_norm, chirp_sub.
proof_shape: transform, chirpMatrix: definitions; escape_witness: not applicable;
  consumers: transform_unitary, chirp_factorization, circulant_spectral,
  spectralKernel_matrix, circulant_unitary_spectrum, positive_polygonal_data, result.
proof_shape: spectralValue, spectralKernel: definitions; escape_witness: not applicable;
  consumers: circulant_spectral, spectralKernel_matrix,
  spectralKernel_real, spectralKernel_even, spectralKernel_bound,
  circulant_unitary_spectrum, positive_polygonal_data.
proof_shape: chirpInt_periodic: bind-only; escape_witness: none; consumer: chirp_intCast.
proof_shape: chirp_intCast: bind-only; escape_witness: none; consumers: chirp_even, chirp_sub.
proof_shape: chirp_even: bind-only; escape_witness: none; consumer: positive_polygonal_data.
proof_shape: chirp_norm: bind-only; escape_witness: none; consumer: positive_polygonal_data.
proof_shape: chirp_sub: bind-only; escape_witness: none; consumer: chirp_factorization.
proof_shape: transform_unitary: bind-only; escape_witness: none;
  consumers: circulant_unitary_spectrum, positive_polygonal_data.
proof_shape: chirp_factorization: bind-only; escape_witness: none;
  consumer: positive_polygonal_data.
proof_shape: circulant_spectral: bind-only; escape_witness: none;
  consumers: circulant_unitary_spectrum, positive_polygonal_data.
proof_shape: spectralKernel_apply: bind-only; escape_witness: none;
  consumers: spectralKernel_real, positive_polygonal_data.
proof_shape: spectralKernel_matrix: bind-only; escape_witness: none;
  consumer: positive_polygonal_data.
proof_shape: spectralKernel_real: bind-only; escape_witness: none;
  consumer: positive_polygonal_data.
proof_shape: spectralKernel_even: bind-only; escape_witness: none;
  consumers: spectralKernel_real, positive_polygonal_data.
proof_shape: spectralKernel_bound: bind-only; escape_witness: none;
  consumer: positive_polygonal_data.
proof_shape: diagonal_unitary: bind-only; escape_witness: none;
  consumer: positive_polygonal_data.
proof_shape: circulant_unitary_spectrum: bind-only; escape_witness: none;
  consumer: positive_polygonal_data.
proof_shape: positive_polygonal_data: bind-only; escape_witness: none; consumer: result.
proof_shape: result: bind-only; escape_witness: none;
  consumers: the polygonal Fourier question.
The construction instantiates character, unitary, exponential and argument identities,
then uses normalization; admission rests on the named question.
Direct frozen dependencies:
  D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.fourierRows
  statement_id sha256:47e2300a010cbecab6a48046a0d4f2986ff23e91fc66d4211049b13e1e317e3d.
  D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.fourierRows_gram
  statement_id sha256:af8daaa446b7f0b6f4b0e5bfe86d6dcebd00b3c1759affc95dc756e1c3aa1966.
  D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.hamiltonianPropagator
  statement_id sha256:cda9b54324a60c3d19d82ae43fd312bec7fd42bc7d2748ad663e34115d863ceb.
  D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.hamiltonianGenerator
  statement_id sha256:4c0ebd78b0aa0a551d6207706ae2d39b87a3d18687dc8dcb29e00bd4e58a735a.
  hamiltonianPropagator._proof_1 is generated implementation evidence of the propagator;
  the accepted record has no separate statement_id for that internal proof.
-/

import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Eigenspace.Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.Operator
open Matrix Complex
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow

namespace D5.S3.Quantum.Dynamics.PolygonalFourierCouplings

def fourier (N : ℕ) : Matrix (Fin N) (Fin N) ℂ := fun j k =>
  Complex.exp (-((2 : ℕ) * Real.pi * Complex.I * (j : ℕ) * (k : ℕ)) / N) / Real.sqrt N

def IsUnimodularDiagonal {N : ℕ} (Φ : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∃ z : Fin N → ℂ, (∀ x, ‖z x‖ = 1) ∧ Φ = Matrix.diagonal z

def IsPolygonalCoupling {N : ℕ} [NeZero N] (C : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∃ c : Fin N → ℝ, c 0 = 0 ∧ (∀ l, c (-l) = c l) ∧ ∀ i j, C i j = c (j - i)

def claim : Prop := ∀ (N : ℕ) [NeZero N], ∃ C : Matrix (Fin N) (Fin N) ℝ,
  IsPolygonalCoupling C ∧ (∀ i j, i ≠ j → 0 < C i j) ∧
  ∃ Φout Φin : Matrix (Fin N) (Fin N) ℂ,
    IsUnimodularDiagonal Φout ∧ IsUnimodularDiagonal Φin ∧
    Φout * hamiltonianPropagator (C.map (fun x : ℝ => (x : ℂ))) 1 * Φin = fourier N


private def chirpInt (N : ℕ) (r : ℤ) : ℂ :=
  Complex.exp (Real.pi * I * ((r : ℂ) ^ 2 / N - r))

private lemma chirpInt_periodic (N : ℕ) [NeZero N] (r m : ℤ) :
    chirpInt N (r + m * N) = chirpInt N r := by
  unfold chirpInt
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨m * r + N * (m * (m - 1) / 2), ?_⟩
  have hm : 2 * (m * (m - 1) / 2) = m * (m - 1) :=
    Int.mul_ediv_cancel' (even_iff_two_dvd.mp (Int.even_mul_pred_self m))
  have hmc : (2 : ℂ) * ((m * (m - 1) / 2 : ℤ) : ℂ) = (m : ℂ) * (m - 1) := by
    exact_mod_cast hm
  push_cast -congrConsts
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp (disch := exact hN)
  linear_combination -(Real.pi : ℂ) * I * (N : ℂ) ^ 2 * hmc

private def chirp (N : ℕ) [NeZero N] (r : ZMod N) : ℂ := chirpInt N r.val

private lemma chirp_intCast (N : ℕ) [NeZero N] (r : ℤ) :
    chirp N (r : ZMod N) = chirpInt N r := by
  unfold chirp
  rw [ZMod.val_intCast]
  have h : r % (N : ℤ) = r + (-(r / N)) * N := by
    linear_combination Int.emod_add_mul_ediv r N
  rw [h, chirpInt_periodic]

private lemma chirp_even (N : ℕ) [NeZero N] (r : ZMod N) : chirp N (-r) = chirp N r := by
  have h (t : ℤ) : chirpInt N (-t) = chirpInt N t := by
    unfold chirpInt
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨t, ?_⟩
    push_cast -congrConsts
    ring
  calc
    chirp N (-r) = chirp N ((-(r.val : ℤ) : ℤ) : ZMod N) := by
      rw [Int.cast_neg, Int.cast_natCast, ZMod.natCast_zmod_val]
    _ = chirpInt N (-(r.val : ℤ)) := chirp_intCast N _
    _ = chirpInt N r.val := h _
    _ = chirp N r := rfl

private lemma chirp_norm (N : ℕ) [NeZero N] (r : ZMod N) : ‖chirp N r‖ = 1 := by
  change ‖Complex.exp (Real.pi * I * (((r.val : ℤ) : ℂ) ^ 2 / N - (r.val : ℤ)))‖ = 1
  rw [show (Real.pi : ℂ) * I * (((r.val : ℤ) : ℂ) ^ 2 / N - (r.val : ℤ)) =
    ((Real.pi * (((r.val : ℤ) : ℝ) ^ 2 / N - (r.val : ℤ)) : ℝ) : ℂ) * I by
      push_cast -congrConsts; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma chirp_sub (N : ℕ) [NeZero N] (j k : ZMod N) :
    chirp N (j - k) = chirp N j * ZMod.stdAddChar (-(j * k)) * chirp N k := by
  have hj : ((j.val : ℤ) : ZMod N) = j := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hk : ((k.val : ℤ) : ZMod N) = k := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hsub : (((j.val : ℤ) - k.val : ℤ) : ZMod N) = j - k := by
    rw [Int.cast_sub, hj, hk]
  have hmul : ((-(j.val : ℤ) * k.val : ℤ) : ZMod N) = -(j * k) := by
    rw [Int.cast_mul, Int.cast_neg, hj, hk, neg_mul]
  rw [← hsub, chirp_intCast, ← hmul, ZMod.stdAddChar_coe]
  change chirpInt N ((j.val : ℤ) - k.val) = chirpInt N j.val *
    Complex.exp (2 * Real.pi * I * ((-(j.val : ℤ) * k.val : ℤ) : ℂ) / N) * chirpInt N k.val
  unfold chirpInt
  rw [← Complex.exp_add, ← Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨k.val, ?_⟩
  push_cast -congrConsts
  ring

private def transform (N : ℕ) [NeZero N] : Matrix (ZMod N) (ZMod N) ℂ :=
  fun j k => ZMod.stdAddChar (-(j * k)) / Real.sqrt N

private lemma transform_unitary (N : ℕ) [NeZero N] :
    transform N * (transform N)ᴴ = 1 := by
  classical
  let e := (ZMod.finEquiv N).toEquiv
  let T := Matrix.reindexAlgEquiv ℂ ℂ e
  let W := D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity.fourierRows N N (le_refl N)
  have hstar (M : Matrix (Fin N) (Fin N) ℂ) : T Mᴴ = (T M)ᴴ := rfl
  have hW := congrArg T
    (D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity.fourierRows_gram N N (le_refl N))
  rw [map_mul, hstar, map_smul, map_one] at hW
  let U := (starRingEnd ℂ).mapMatrix (T W)
  have hstar' (M : Matrix (ZMod N) (ZMod N) ℂ) :
      (starRingEnd ℂ).mapMatrix Mᴴ = ((starRingEnd ℂ).mapMatrix M)ᴴ := rfl
  have hU : U * Uᴴ = (N : ℂ) • 1 := by
    have h := congrArg (starRingEnd ℂ).mapMatrix hW
    rw [map_mul, hstar'] at h
    have hc : (starRingEnd ℂ).mapMatrix ((N : ℂ) • (1 : Matrix (ZMod N) (ZMod N) ℂ)) =
        (N : ℂ) • 1 := by
      ext i j
      change conj ((N : ℂ) * (if i = j then 1 else 0)) = _
      simp -congrConsts only [map_mul, map_natCast, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply]
      split_ifs <;> simp -congrConsts
    rw [hc] at h
    exact h
  have hentry : U = fun j k => ZMod.stdAddChar (-(j * k)) := by
    ext j k
    change conj (ZMod.stdAddChar
      ((ZMod.finEquiv N (e.symm k)) * (ZMod.finEquiv N (Fin.castLE (le_refl N) (e.symm j))))) = _
    simp -congrConsts only [Fin.castLE_refl]
    change conj (ZMod.stdAddChar (e (e.symm k) * e (e.symm j))) = _
    rw [e.apply_symm_apply, e.apply_symm_apply, ← AddChar.map_neg_eq_conj, mul_comm]
  have hs : (Real.sqrt N : ℂ) * Real.sqrt N = N := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg N)
  have hF : transform N = (Real.sqrt N : ℂ)⁻¹ • U := by
    rw [hentry]
    ext j k
    change ZMod.stdAddChar (-(j * k)) / (Real.sqrt N : ℂ) =
      (Real.sqrt N : ℂ)⁻¹ * ZMod.stdAddChar (-(j * k))
    rw [div_eq_mul_inv, mul_comm]
  rw [hF]
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hU, smul_smul]
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [← mul_inv, hs, inv_mul_cancel₀ (NeZero.ne (N : ℂ)), one_smul]

private def chirpMatrix (N : ℕ) [NeZero N] : Matrix (ZMod N) (ZMod N) ℂ :=
  Matrix.circulant (fun l => chirp N l / Real.sqrt N)

private lemma chirp_factorization (N : ℕ) [NeZero N] :
    chirpMatrix N = Matrix.diagonal (chirp N) * transform N * Matrix.diagonal (chirp N) := by
  ext j k
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  change chirp N (j - k) / (Real.sqrt N : ℂ) =
    chirp N j * (ZMod.stdAddChar (-(j * k)) / Real.sqrt N) * chirp N k
  rw [chirp_sub]
  ring

private def spectralValue (N : ℕ) [NeZero N] (b : ZMod N → ℂ) (k : ZMod N) : ℂ :=
  ZMod.dft b k

private lemma circulant_spectral (N : ℕ) [NeZero N] (b : ZMod N → ℂ) :
    transform N * Matrix.circulant b = Matrix.diagonal (spectralValue N b) * transform N := by
  ext i k
  rw [Matrix.mul_apply, Matrix.diagonal_mul]
  change (∑ j : ZMod N, (ZMod.stdAddChar (-(i * j)) / Real.sqrt N) * b (j - k)) =
    spectralValue N b i * (ZMod.stdAddChar (-(i * k)) / Real.sqrt N)
  have h := congr_fun (Fourier.fourierIntegral_comp_add_right ZMod.toCircle
    MeasureTheory.Measure.count b (-k)) i
  rw [← ZMod.dft_eq_fourier, ← ZMod.dft_eq_fourier] at h
  have hshift : ZMod.dft (fun j => b (j - k)) i =
      ZMod.stdAddChar (-(i * k)) * ZMod.dft b i := by
    rw [ZMod.stdAddChar_apply]
    simpa -congrConsts only [Function.comp_def, sub_eq_add_neg, Circle.smul_def,
      smul_eq_mul, neg_mul, mul_neg, mul_comm] using h
  calc
    _ = ZMod.dft (fun j => b (j - k)) i / (Real.sqrt N : ℂ) := by
      rw [ZMod.dft_apply, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      simp -congrConsts only [smul_eq_mul, mul_comm j i]
      ring
    _ = _ := by rw [hshift]; unfold spectralValue; ring

private def spectralKernel (N : ℕ) [NeZero N] (v : ZMod N → ℝ) : ZMod N → ℂ :=
  (ZMod.dft (N := N) (E := ℂ)).symm (fun k => (v k : ℂ))

private lemma spectralKernel_apply (N : ℕ) [NeZero N] (v : ZMod N → ℝ) (l : ZMod N) :
    spectralKernel N v l = (∑ k : ZMod N, (v k : ℂ) * ZMod.stdAddChar (l * k)) / N := by
  rw [spectralKernel, ZMod.invDFT_apply]
  simp -congrConsts only [smul_eq_mul, mul_comm l, mul_comm (ZMod.stdAddChar _), div_eq_mul_inv,
    mul_comm ((N : ℂ)⁻¹)]

private lemma spectralKernel_matrix (N : ℕ) [NeZero N] (v : ZMod N → ℝ) :
    (transform N)ᴴ * Matrix.diagonal (fun k => (v k : ℂ)) * transform N =
      Matrix.circulant (spectralKernel N v) := by
  have h := circulant_spectral N (spectralKernel N v)
  change transform N * Matrix.circulant (spectralKernel N v) =
    Matrix.diagonal (ZMod.dft ((ZMod.dft (N := N) (E := ℂ)).symm
      (fun k => (v k : ℂ)))) * transform N at h
  rw [LinearEquiv.apply_symm_apply] at h
  rw [Matrix.mul_assoc, ← h, ← Matrix.mul_assoc,
    mul_eq_one_comm.mp (transform_unitary N), Matrix.one_mul]

private lemma spectralKernel_even (N : ℕ) [NeZero N] (v : ZMod N → ℝ)
    (hv : ∀ k, v (-k) = v k) (l : ZMod N) :
    spectralKernel N v (-l) = spectralKernel N v l := by
  have h : (spectralKernel N v).Even := by
    apply ZMod.dft_even_iff.mp
    simpa -congrConsts only [spectralKernel, LinearEquiv.apply_symm_apply] using
      (show (fun k => (v k : ℂ)).Even from fun k => congrArg Complex.ofReal (hv k))
  exact h l

private lemma spectralKernel_real (N : ℕ) [NeZero N] (v : ZMod N → ℝ)
    (hv : ∀ k, v (-k) = v k) (l : ZMod N) :
    ((spectralKernel N v l).re : ℂ) = spectralKernel N v l := by
  apply Complex.conj_eq_iff_re.mp
  calc
    conj (spectralKernel N v l) = spectralKernel N v (-l) := by
      simp -congrConsts only [spectralKernel_apply, map_div₀, map_sum, map_mul, Complex.conj_ofReal,
        ← AddChar.map_neg_eq_conj, map_natCast, neg_mul]
    _ = spectralKernel N v l := spectralKernel_even N v hv l

private lemma spectralKernel_bound (N : ℕ) [NeZero N] (v : ZMod N → ℝ)
    (hv : ∀ k, |v k| ≤ Real.pi) (l : ZMod N) :
    ‖spectralKernel N v l‖ ≤ Real.pi := by
  have hn : (N : ℝ) > 0 := Nat.cast_pos.mpr (NeZero.pos N)
  change ‖(N : ℂ)⁻¹ • ZMod.dft (fun k => (v k : ℂ)) (-l)‖ ≤ Real.pi
  rw [norm_smul, norm_inv, Complex.norm_natCast, inv_mul_eq_div]
  apply (div_le_iff₀ hn).mpr
  have h := Fourier.norm_fourierIntegral_le_integral_norm ZMod.toCircle
    MeasureTheory.Measure.count (fun k => (v k : ℂ)) (-l)
  rw [← ZMod.dft_eq_fourier, MeasureTheory.integral_count] at h
  calc
    _ ≤ ∑ k : ZMod N, ‖(v k : ℂ)‖ := h
    _ ≤ ∑ _k : ZMod N, Real.pi := by
      apply Finset.sum_le_sum
      intro k _
      simpa -congrConsts only [Complex.norm_real, Real.norm_eq_abs] using hv k
    _ = Real.pi * N := by simp -congrConsts [mul_comm]

private lemma diagonal_unitary (N : ℕ) [NeZero N] (z : ZMod N → ℂ)
    (hz : ∀ k, ‖z k‖ = 1) :
    Matrix.diagonal z ∈ Matrix.unitaryGroup (ZMod N) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext k
  change z k * conj (z k) = 1
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  norm_num

open scoped Matrix.Norms.L2Operator in
private lemma circulant_unitary_spectrum (N : ℕ) [NeZero N] (b : ZMod N → ℂ)
    (hb : Matrix.circulant b ∈ Matrix.unitaryGroup (ZMod N) ℂ) :
    ∀ k, ‖spectralValue N b k‖ = 1 := by
  have hF : transform N ∈ Matrix.unitaryGroup (ZMod N) ℂ :=
    Matrix.mem_unitaryGroup_iff.mpr (transform_unitary N)
  have hF' : (transform N)ᴴ ∈ Matrix.unitaryGroup (ZMod N) ℂ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp (transform_unitary N)
  have hd : Matrix.diagonal (spectralValue N b) =
      transform N * Matrix.circulant b * (transform N)ᴴ := by
    rw [circulant_spectral, Matrix.mul_assoc, transform_unitary, Matrix.mul_one]
  have hu := Matrix.unitaryGroup (ZMod N) ℂ |>.mul_mem
    (Matrix.unitaryGroup (ZMod N) ℂ |>.mul_mem hF hb) hF'
  rw [← hd] at hu
  intro k
  apply spectrum.norm_eq_one_of_unitary hu
  rw [spectrum_diagonal]
  exact ⟨k, rfl⟩

private lemma positive_polygonal_data (N : ℕ) [NeZero N] :
    ∃ c : ZMod N → ℝ, c 0 = 0 ∧ (∀ l, c (-l) = c l) ∧ (∀ l, l ≠ 0 → 0 < c l) ∧
      ∃ z w : ZMod N → ℂ, (∀ l, ‖z l‖ = 1) ∧ (∀ l, ‖w l‖ = 1) ∧
        Matrix.diagonal z * NormedSpace.exp ((-I) •
          Matrix.circulant (fun l => (c l : ℂ))) * Matrix.diagonal w = transform N := by
  classical
  let b : ZMod N → ℂ := fun l => chirp N l / Real.sqrt N
  have hbmat : Matrix.circulant b = chirpMatrix N := rfl
  have hF : transform N ∈ Matrix.unitaryGroup (ZMod N) ℂ :=
    Matrix.mem_unitaryGroup_iff.mpr (transform_unitary N)
  have hD := diagonal_unitary N (chirp N) (chirp_norm N)
  have hB : Matrix.circulant b ∈ Matrix.unitaryGroup (ZMod N) ℂ := by
    rw [hbmat, chirp_factorization]
    exact (Matrix.unitaryGroup (ZMod N) ℂ).mul_mem
      ((Matrix.unitaryGroup (ZMod N) ℂ).mul_mem hD hF) hD
  let eig : ZMod N → ℂ := spectralValue N b
  have heignorm : ∀ k, ‖eig k‖ = 1 := circulant_unitary_spectrum N b hB
  have heigeven : ∀ k, eig (-k) = eig k := by
    intro k
    apply ZMod.dft_even_iff.mpr _ k
    intro l
    dsimp [b]
    rw [chirp_even]
  let t : ZMod N → ℝ := fun k => -(eig k).arg
  let a : ℝ := (∑ k : ZMod N, t k) / N
  let v : ZMod N → ℝ := fun k => t k - a - 2 * Real.pi +
    if k = 0 then 2 * Real.pi * N else 0
  have ht : ∀ k, t (-k) = t k := by intro k; dsimp [t]; rw [heigeven]
  have hv : ∀ k, v (-k) = v k := by
    intro k
    dsimp [v]
    simp -congrConsts only [ht, neg_eq_zero]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hsum : ∑ k : ZMod N, v k = 0 := by
    dsimp [v]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp -congrConsts only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    dsimp [a]
    field_simp (disch := exact hN)
    ring
  let c : ZMod N → ℝ := fun l => (spectralKernel N v l).re
  have hc : ∀ l, (c l : ℂ) = spectralKernel N v l := spectralKernel_real N v hv
  have hc0 : c 0 = 0 := by
    have hzero : spectralKernel N v 0 = 0 := by
      rw [spectralKernel_apply]
      simp -congrConsts only [zero_mul, AddChar.map_zero_eq_one, mul_one]
      rw [← Complex.ofReal_sum, hsum, Complex.ofReal_zero, zero_div]
    dsimp [c]
    rw [hzero]
    rfl
  have hceven : ∀ l, c (-l) = c l := by
    intro l
    dsimp [c]
    rw [spectralKernel_even N v hv]
  have hkernel : ∀ l : ZMod N, l ≠ 0 →
      spectralKernel N v l = spectralKernel N t l + (2 * Real.pi : ℝ) := by
    intro l hl
    have hvcast (k : ZMod N) : (v k : ℂ) =
        (t k : ℂ) - (a : ℂ) - 2 * (Real.pi : ℂ) +
          if k = 0 then (2 : ℂ) * (Real.pi : ℂ) * (N : ℂ) else (0 : ℂ) := by
      dsimp [v]
      split_ifs <;> push_cast -congrConsts <;> rfl
    rw [spectralKernel_apply, spectralKernel_apply]
    simp -congrConsts only [hvcast, add_mul, sub_mul, ite_mul, zero_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      mul_zero, AddChar.map_zero_eq_one, mul_one]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have hchar : (∑ k : ZMod N, ZMod.stdAddChar (l * k)) = 0 := by
      simpa -congrConsts only [mul_comm l, ZMod.card, if_neg hl, Nat.cast_zero] using
        AddChar.sum_mulShift l (ZMod.isPrimitive_stdAddChar N)
    rw [hchar]
    push_cast -congrConsts
    field_simp (disch := exact hNc)
    ring
  have hcpos : ∀ l, l ≠ 0 → 0 < c l := by
    intro l hl
    have hbound : ‖spectralKernel N t l‖ ≤ Real.pi :=
      spectralKernel_bound N t
        (fun k => by dsimp [t]; rw [abs_neg]; exact Complex.abs_arg_le_pi _) l
    have hre := (abs_le.mp (Complex.abs_re_le_norm (spectralKernel N t l))).1
    dsimp [c]
    rw [hkernel l hl, Complex.add_re, Complex.ofReal_re]
    linarith [Real.pi_pos]
  have hFleft : (transform N)ᴴ * transform N = 1 :=
    mul_eq_one_comm.mp (transform_unitary N)
  have hdecomp : Matrix.circulant b =
      (transform N)ᴴ * Matrix.diagonal eig * transform N := by
    calc
      Matrix.circulant b = (transform N)ᴴ * (transform N * Matrix.circulant b) := by
        rw [← Matrix.mul_assoc, hFleft, Matrix.one_mul]
      _ = (transform N)ᴴ * Matrix.diagonal eig * transform N := by
        rw [circulant_spectral, Matrix.mul_assoc]
  have hexpv : ∀ k, Complex.exp (-I * (v k : ℂ)) = Complex.exp (I * (a : ℂ)) * eig k := by
    intro k
    have he : Complex.exp ((eig k).arg * I) = eig k := by
      have h := Complex.norm_mul_exp_arg_mul_I (eig k)
      rw [heignorm k, Complex.ofReal_one, one_mul] at h
      exact h
    rw [← he, ← Complex.exp_add]
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨if k = 0 then 1 - (N : ℤ) else 1, ?_⟩
    dsimp [v, t]
    by_cases hk : k = 0
    · rw [if_pos hk, if_pos hk]
      push_cast -congrConsts
      ring
    · rw [if_neg hk, if_neg hk]
      push_cast -congrConsts
      ring
  have hC : Matrix.circulant (fun l => (c l : ℂ)) =
      (transform N)ᴴ * Matrix.diagonal (fun k => (v k : ℂ)) * transform N := by
    rw [spectralKernel_matrix]
    congr 1
    funext l
    exact hc l
  have hinv : (transform N)⁻¹ = (transform N)ᴴ :=
    Matrix.inv_eq_right_inv (transform_unitary N)
  have hgen : (-I) • Matrix.circulant (fun l => (c l : ℂ)) =
      (transform N)⁻¹ * Matrix.diagonal (fun k => -I * (v k : ℂ)) * transform N := by
    rw [hC, hinv]
    change (-I) • ((transform N)ᴴ * Matrix.diagonal (fun k => (v k : ℂ)) * transform N) =
      (transform N)ᴴ * Matrix.diagonal ((-I) • (fun k => (v k : ℂ))) * transform N
    rw [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hU : NormedSpace.exp ((-I) • Matrix.circulant (fun l => (c l : ℂ))) =
      Complex.exp (I * (a : ℂ)) • Matrix.circulant b := by
    rw [hgen, Matrix.exp_conj' _ _ (Unitary.isUnit_coe (U := ⟨transform N, hF⟩)),
      Matrix.exp_diagonal, hinv, hdecomp]
    have he : NormedSpace.exp (fun k => -I * (v k : ℂ)) =
        fun k => Complex.exp (I * (a : ℂ)) * eig k := by
      funext k
      rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
      exact hexpv k
    rw [he]
    change (transform N)ᴴ * Matrix.diagonal (Complex.exp (I * (a : ℂ)) • eig) * transform N =
      Complex.exp (I * (a : ℂ)) • ((transform N)ᴴ * Matrix.diagonal eig * transform N)
    rw [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  let z : ZMod N → ℂ := fun l => conj (chirp N l)
  let w : ZMod N → ℂ := fun l => Complex.exp (-I * (a : ℂ)) * z l
  have hz : ∀ l, ‖z l‖ = 1 := by intro l; dsimp [z]; rw [norm_conj, chirp_norm]
  have hw : ∀ l, ‖w l‖ = 1 := by
    intro l
    dsimp [w]
    rw [norm_mul, hz, mul_one, Complex.norm_exp]
    simp -congrConsts
  have hcancel : Matrix.diagonal z * Matrix.diagonal (chirp N) = 1 := by
    simpa -congrConsts only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Pi.star_def, Complex.star_def, z] using
      (diagonal_unitary N (chirp N) (chirp_norm N)).1
  have hcancel' : Matrix.diagonal (chirp N) * Matrix.diagonal z = 1 := by
    simpa -congrConsts only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Pi.star_def, Complex.star_def, z] using
      (diagonal_unitary N (chirp N) (chirp_norm N)).2
  refine ⟨c, hc0, hceven, hcpos, z, w, hz, hw, ?_⟩
  rw [hU, hbmat, chirp_factorization]
  have hphase : Matrix.diagonal w = Complex.exp (-I * (a : ℂ)) • Matrix.diagonal z := by
    rw [← Matrix.diagonal_smul]
    rfl
  rw [hphase]
  simp -congrConsts only [mul_smul_comm, smul_mul_assoc, smul_smul]
  have hscalar : Complex.exp (-I * (a : ℂ)) * Complex.exp (I * (a : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    simp -congrConsts
  rw [hscalar, one_smul]
  simp -congrConsts only [← Matrix.mul_assoc]
  rw [hcancel, Matrix.one_mul, Matrix.mul_assoc, hcancel', Matrix.mul_one]

theorem result : claim := by
  intro N instN
  let e : Fin N ≃+* ZMod N := ZMod.finEquiv N
  let T : Matrix (ZMod N) (ZMod N) ℂ ≃ₐ[ℂ] Matrix (Fin N) (Fin N) ℂ :=
    Matrix.reindexAlgEquiv ℂ ℂ e.symm.toEquiv
  obtain ⟨c, hc0, hceven, hcpos, z, w, hz, hw, hzw⟩ := positive_polygonal_data N
  let C : Matrix (Fin N) (Fin N) ℝ := fun i j => c (e (j - i))
  let zout : Fin N → ℂ := fun j => z (e j)
  let zin : Fin N → ℂ := fun j => w (e j)
  refine ⟨C, ?_, ?_, Matrix.diagonal zout, Matrix.diagonal zin,
    ⟨zout, fun j => hz (e j), rfl⟩, ⟨zin, fun j => hw (e j), rfl⟩, ?_⟩
  · refine ⟨fun l => c (e l), ?_, ?_, fun i j => rfl⟩
    · change c (e 0) = 0
      rw [map_zero]
      exact hc0
    · intro l
      change c (e (-l)) = c (e l)
      rw [map_neg]
      exact hceven _
  · intro i j hij
    apply hcpos
    rw [← e.map_zero]
    exact e.injective.ne (sub_ne_zero.mpr (Ne.symm hij))
  · have hdiag (u : ZMod N → ℂ) :
        T (Matrix.diagonal u) = Matrix.diagonal (fun j => u (e j)) := by
      ext i j
      change (Matrix.diagonal u) (e i) (e j) = (Matrix.diagonal (fun j => u (e j))) i j
      simp -congrConsts only [Matrix.diagonal_apply, e.injective.eq_iff]
    have hC : T (Matrix.circulant (fun l => (c l : ℂ))) = C.map (fun x : ℝ => (x : ℂ)) := by
      ext i j
      change (c (e i - e j) : ℂ) = c (e (j - i))
      rw [map_sub, ← neg_sub (e i) (e j), hceven]
    have hF : T (transform N) = fourier N := by
      ext j k
      change ZMod.stdAddChar (-(e j * e k)) / (Real.sqrt N : ℂ) =
        Complex.exp (-(2 * Real.pi * I * (j : ℕ) * (k : ℕ)) / N) / Real.sqrt N
      have he (x : Fin N) : e x = ((x : ℕ) : ZMod N) := by
        dsimp [e]
        cases N with
        | zero => exact (NeZero.ne 0 rfl).elim
        | succ n => exact (ZMod.natCast_zmod_val (n := n + 1) x).symm
      rw [he j, he k]
      have hcast : -(((j : ℕ) : ZMod N) * ((k : ℕ) : ZMod N)) =
          ((-((j : ℕ) : ℤ) * (k : ℕ) : ℤ) : ZMod N) := by push_cast -congrConsts; ring
      rw [hcast, ZMod.stdAddChar_coe]
      congr 2
      push_cast -congrConsts
      ring
    have hexp (X : Matrix (ZMod N) (ZMod N) ℂ) : T (NormedSpace.exp X) = NormedSpace.exp (T X) :=
      NormedSpace.map_exp T T.toLinearMap.continuous_of_finiteDimensional X
    have h := congrArg T hzw
    rw [map_mul, map_mul, hdiag, hdiag, hexp, map_smul, hC, hF] at h
    unfold hamiltonianPropagator hamiltonianGenerator
    rw [one_smul]
    exact h

end D5.S3.Quantum.Dynamics.PolygonalFourierCouplings
