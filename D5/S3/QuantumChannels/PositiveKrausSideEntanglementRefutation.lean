/- GID: D5/S3/QuantumChannels/PositiveKrausSideEntanglementRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/PositiveKrausSideEntanglementRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/PositiveKrausSideEntanglementRefutation.claim; result=D5/S3/QuantumChannels/PositiveKrausSideEntanglementRefutation.result; claim=D5/S3/QuantumChannels/PositiveKrausSideEntanglementRefutation.claim
   digest: Positive tetrahedral Kraus operators allow an entanglement advantage. -/

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#16535; Refuted)
Direct frozen dependencies (declaration statement_id; F labels below):
F1: D5/S3/Quantum/Foundation/FiniteKrausChannel.MatrixMap
  statement_id: sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
F2: D5/S3/Quantum/Foundation/FiniteKrausChannel.of_kraus
  statement_id: sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287
F3: D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.IsDensity
  statement_id: sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448
F4: D5/S3/Quantum/FiniteDimensional.QubitMatrix
  statement_id: sha256:e376bbe008ddbbc49fcf9763247304ed70ec54ac5cf49af3c6f7fb58fa626f30
F5: D5/S3/Quantum/FiniteDimensional.qubitX
  statement_id: sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7
F6: D5/S3/Quantum/FiniteDimensional.qubitZ
  statement_id: sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
F7: D5/S3/Weil/ZetaLinear/RankTrace.trace_mul_nonneg_of_posSemidef
  statement_id: sha256:fefc8a0805a2b6dd7fcf96418c2412c83986c84d51c5d1731ed8d1cea0a88ca3
F8: D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.density_le_one
  statement_id: sha256:42c930570f378656e0577ccfac3a3df3a5b93f7b2c18f1c68671e090562d035f
F9: D5/S3/QuantumBounds/CHSHWitness.bellDensity
  statement_id: sha256:e912835dc9088a23076f5ad7c742dd494605dd2e25b7beb587d4750a4f1efa84
F10: D5/S3/QuantumBounds/CHSHWitness.bellVector
  statement_id: sha256:ef8ab2c76767d0b6e0ead3d2869923996cafda705f450300e01195f336eadb8f
F11: D5/S3/Quantum/QubitWitnesses.bellCoefficients
  statement_id: sha256:e2b60dfaa8cf4c9859738273f0e38c061b7898ed8aba82a4f813fd80d5eb5fe8
F12: D5/S3/QuantumBounds/CHSHWitness.TwoQubitMatrix
  statement_id: sha256:2a939b5c081cb7f5071bf116c5a5967adc0c05361ef9b701465cb9cb84dc1c22
F13: D5/S3/Quantum/EnvironmentRecords.traceEnvironment
  statement_id: sha256:da04a9203d2fcd9cbdb7853beba00edf269232eeeb3ae8a2710d33d847198025
F14: D5/S3/Quantum/Entanglement/BellPureStateMixedMarginal.bell_pure_state_has_maximally_mixed_marginal
  statement_id: sha256:1852b851afdab783a70de9ace3043539b2e971391762da4b9ce2cab933c3ccea
F15: D5/S3/QuantumBounds/CHSHWitness.bell_density_is_state
  statement_id: sha256:f25b7239e34182d1cdaff8dfc1f1b67e43f85b40bdfbe3e850173bf7593427d5

Declaration classifications; every theorem helper is consumed bind-only:
kraus_action: proof_shape: bind-only; escape_witness: none;
  consumers: kraus_apply_formula, kraus_complete, success_un_formula, kraus_ext_entry, assisted_success; Direct frozen dependencies: F1, F2.
numerator_hermitian: proof_shape: bind-only; escape_witness: none;
  consumers: kraus_complete; Direct frozen dependencies: F4, F5, F6.
numerator_gram: proof_shape: bind-only; escape_witness: none;
  consumers: numerator_pos_def; Direct frozen dependencies: F4, F5, F6.
numerator_pos_def: proof_shape: bind-only; escape_witness: none;
  consumers: kraus_pos_def; Direct frozen dependencies: F4, F5, F6.
scale_pos: proof_shape: bind-only; escape_witness: none;
  consumers: kraus_pos_def; Direct frozen dependencies: none.
scale_sq: proof_shape: bind-only; escape_witness: none;
  consumers: kraus_apply_formula; Direct frozen dependencies: none.
kraus_pos_def: proof_shape: bind-only; escape_witness: none;
  consumers: result; Direct frozen dependencies: F4, F5, F6.
numerator_apply: proof_shape: bind-only; escape_witness: none;
  consumers: kraus_apply_formula; Direct frozen dependencies: F4, F5, F6.
kraus_apply_formula: proof_shape: bind-only; escape_witness: none;
  consumers: kraus_complete, success_un_formula, bell_output; Direct frozen dependencies: F1, F2, F4, F5, F6.
kraus_complete: proof_shape: bind-only; escape_witness: none;
  consumers: result; Direct frozen dependencies: F4, F5, F6, F1, F2.
effect_density_pairing: proof_shape: bind-only; escape_witness: none;
  consumers: unassisted_bound; Direct frozen dependencies: F3, F7, F8.
success_un_formula: proof_shape: bind-only; escape_witness: none;
  consumers: unassisted_bound; Direct frozen dependencies: F3, F4, F5, F6, F1, F2.
unassisted_bound: proof_shape: bind-only; escape_witness: none;
  consumers: result; Direct frozen dependencies: F3, F4, F5, F6, F1, F2, F7, F8.
bell_entries: proof_shape: bind-only; escape_witness: none;
  consumers: bell_output, assisted_success; Direct frozen dependencies: F9, F10, F11.
bell_square: proof_shape: bind-only; escape_witness: none;
  consumers: bell_effect, assisted_success; Direct frozen dependencies: F12, F9, F4, F13, F10, F14.
bell_effect: proof_shape: bind-only; escape_witness: none;
  consumers: result; Direct frozen dependencies: F9, F12, F15, F4, F13, F10, F14.
kraus_ext_entry: proof_shape: bind-only; escape_witness: none;
  consumers: bell_output; Direct frozen dependencies: F1, F2.
bell_output: proof_shape: bind-only; escape_witness: none;
  consumers: assisted_success; Direct frozen dependencies: F1, F2, F4, F5, F6, F9, F12, F10, F11.
assisted_success: proof_shape: bind-only; escape_witness: none;
  consumers: result; Direct frozen dependencies: F4, F5, F6, F9, F1, F2, F12, F10, F11, F13, F14.
result: proof_shape: bind-only; escape_witness: none;
  consumers: none; Direct frozen dependencies: F3, F4, F5, F6, F9, F1, F2, F15, F12, F13, F10, F14, F7, F8, F11.

The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
The Kraus sums and positive-semidefinite effect conditions are literal in the
public definitions and claim; proofs use the frozen of_kraus and Bell owners.
The frozen private density_le_one owner supplies the density-complement bound.
FiniteKrausRepresentation is unfrozen; its additional channel declarations are
not used. The frozen FiniteKrausChannel.of_kraus owner suffices here.
-/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Measurements.BroadcastingChannelExtremaRefutation
import D5.S3.Quantum.Entanglement.BellPureStateMixedMarginal
import D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound
import D5.S3.Quantum.EnvironmentRecords
import D5.S3.Quantum.FiniteDimensional
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.QubitWitnesses
import D5.S3.QuantumBounds.CHSHWitness
import D5.S3.Weil.ZetaLinear.RankTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Kronecker
namespace D5.S3.QuantumChannels.PositiveKrausSideEntanglementRefutation
open D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound (IsDensity)
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open D5.S3.QuantumBounds.CHSHWitness (bellDensity bellVector bell_density_is_state)
open D5.S3.Quantum.Entanglement.BellPureStateMixedMarginal
  (bell_pure_state_has_maximally_mixed_marginal)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap (of_kraus)
open D5.S3.Quantum.Measurements.BroadcastingChannelExtremaRefutation (density_le_one)

private theorem kraus_action {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m]
    (Ks : k → Matrix m m ℂ) (A : Matrix m m ℂ) :
    of_kraus Ks Ks A = ∑ i, Ks i * A * (Ks i)ᴴ := by
  simp only [of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]

def successUn {n : ℕ} (K1 K2 : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (rho M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (1/2 : ℝ) * ((M * (∑ i, K1 i * rho * (K1 i)ᴴ)).trace).re +
    (1/2 : ℝ) * (((1 - M) * (∑ i, K2 i * rho * (K2 i)ᴴ)).trace).re

def successAs {n : ℕ} (K1 K2 : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (rho M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ :=
  (1/2 : ℝ) * ((M * (∑ i, Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) (K1 i) * rho *
      (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) (K1 i))ᴴ)).trace).re +
    (1/2 : ℝ) * (((1 - M) * (∑ i, Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) (K2 i) * rho *
      (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) (K2 i))ᴴ)).trace).re

def claim : Prop :=
  ∀ (n : ℕ) (K1 K2 : Fin n → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ i, (K1 i).PosDef) → (∀ i, (K2 i).PosDef) →
    ∑ i, (K1 i)ᴴ * K1 i = 1 → ∑ i, (K2 i)ᴴ * K2 i = 1 →
    ∀ (rho M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ), IsDensity rho → (M.PosSemidef ∧ (1 - M).PosSemidef) →
    ∃ (sigma N : Matrix (Fin 2) (Fin 2) ℂ), IsDensity sigma ∧ (N.PosSemidef ∧ (1 - N).PosSemidef) ∧
      successAs K1 K2 rho M ≤ successUn K1 K2 sigma N


private def numerator (a : ℝ) : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![a • 1 + qubitX + Complex.I • (qubitX * qubitZ) + qubitZ,
    a • 1 + qubitX - Complex.I • (qubitX * qubitZ) - qubitZ,
    a • 1 - qubitX + Complex.I • (qubitX * qubitZ) - qubitZ,
    a • 1 - qubitX - Complex.I • (qubitX * qubitZ) + qubitZ]

private def scale (a : ℝ) : ℝ := 1 / (2 * Real.sqrt (a^2+3))
private def K (a : ℝ) (i : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ := scale a • numerator a i

private def lambda (a : ℝ) : ℂ := ((a^2-1)/(a^2+3) : ℝ)

private theorem numerator_hermitian (a : ℝ) (s : Fin 4) : (numerator a s).IsHermitian := by
  ext i j
  fin_cases s <;> fin_cases i <;> fin_cases j <;> simp [numerator, qubitX, qubitZ, Matrix.conjTranspose_apply] <;> ring

private theorem numerator_gram (a : ℝ) (ha : a ≠ 0) (s : Fin 4) :
    numerator a s = ((a^2-3)/(2*a) : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (1/(2*a) : ℝ) • ((numerator a s)ᴴ * numerator a s) := by
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  ext i j
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [numerator, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;>
    field_simp <;> (try simp [← Complex.ofReal_pow]) <;> ring

private theorem numerator_pos_def (a : ℝ) (ha : a = 2 ∨ a = 3) (s : Fin 4) :
    (numerator a s).PosDef := by
  have ha0 : a ≠ 0 := by rcases ha with rfl | rfl <;> norm_num
  rw [numerator_gram a ha0 s]
  apply Matrix.PosDef.add_posSemidef
  · exact (Matrix.PosDef.one (n := Fin 2) (R := ℂ)).smul
      (a := ((a^2-3)/(2*a) : ℝ)) (by rcases ha with rfl | rfl <;> norm_num)
  · exact (Matrix.posSemidef_conjTranspose_mul_self (numerator a s)).smul
      (a := (1/(2*a) : ℝ)) (by rcases ha with rfl | rfl <;> norm_num)

private theorem scale_pos (a : ℝ) : 0 < scale a := by
  unfold scale
  positivity

private theorem scale_sq (a : ℝ) : scale a ^ 2 = 1/(4*(a^2+3)) := by
  have hpos : 0 < a^2+3 := by positivity
  have hs := Real.sq_sqrt hpos.le
  have hn : Real.sqrt (a^2+3) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  unfold scale
  field_simp
  nlinarith

private theorem kraus_pos_def (a : ℝ) (ha : a = 2 ∨ a = 3) (s : Fin 4) :
    (K a s).PosDef := (numerator_pos_def a ha s).smul (scale_pos a)


private theorem numerator_apply (a : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ i, numerator a i * A * (numerator a i)ᴴ) =
      (4*(a^2-1) : ℝ) • A + (8*A.trace : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [numerator, qubitX, qubitZ, Matrix.one_apply, Fin.sum_univ_succ, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.trace,
      -Complex.ofReal_pow, Complex.mul_re, Complex.mul_im] <;> ring

private theorem kraus_apply_formula (a : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    of_kraus (K a) (K a) A = lambda a • A +
      (((1 - lambda a) / 2) * A.trace) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hsc : of_kraus (K a) (K a) A = (scale a^2) •
      (∑ i, numerator a i * A * (numerator a i)ᴴ) := by
    simp only [kraus_action, K, Matrix.conjTranspose_smul, star_trivial,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Finset.smul_sum, pow_two]
  rw [hsc, scale_sq, numerator_apply]
  have hn : a^2+3 ≠ 0 := ne_of_gt (by positivity : 0 < a^2+3)
  ext i j
  simp only [lambda, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_one,
    Complex.ofReal_ofNat]
  have hnc : (a : ℂ)^2+3 ≠ 0 := by exact_mod_cast hn
  field_simp
  ring

private theorem kraus_complete (a : ℝ) : ∑ i, (K a i)ᴴ * K a i = 1 := by
  have hh' : ∀ i, (K a i)ᴴ = K a i := by
    intro i
    simp only [K, Matrix.conjTranspose_smul, star_trivial, (numerator_hermitian a i).eq]
  simp_rw [hh']
  have he : (∑ i, K a i * K a i) = of_kraus (K a) (K a) 1 := by
    simp [kraus_action, hh']
  rw [he, kraus_apply_formula]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [lambda, Matrix.add_apply, Matrix.smul_apply, Matrix.trace,
      Fin.sum_univ_two, Matrix.diag_apply, Matrix.one_apply,
      smul_eq_mul, Complex.ofReal_div,
      Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_pow,
      Complex.ofReal_one, Complex.ofReal_ofNat]
  all_goals norm_num


private theorem effect_density_pairing (sigma N : Matrix (Fin 2) (Fin 2) ℂ) (hs : IsDensity sigma)
    (hN : (N.PosSemidef ∧ (1 - N).PosSemidef)) : ((N*sigma).trace).re - N.trace.re/2 ≤ 1/2 := by
  have h1 := RHLinalg.trace_mul_nonneg_of_posSemidef hN.2 hs.1
  have h2 := RHLinalg.trace_mul_nonneg_of_posSemidef hN.1 (density_le_one hs.1 hs.2)
  change 0 ≤ (((1 - N)*sigma).trace).re at h1
  change 0 ≤ ((N*(1 - sigma)).trace).re at h2
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, hs.2,
    Complex.sub_re, Complex.one_re] at h1
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re] at h2
  linarith

private theorem success_un_formula (sigma N : Matrix (Fin 2) (Fin 2) ℂ) (hs : IsDensity sigma) :
    successUn (K 3) (K 2) sigma N = 1/2 + (5/42 : ℝ) *
      (((N*sigma).trace).re - N.trace.re/2) := by
  unfold successUn
  rw [← kraus_action, ← kraus_action, kraus_apply_formula, kraus_apply_formula]
  norm_num [lambda, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_smul, hs.2, Matrix.sub_mul, Matrix.trace_sub,
    Matrix.one_mul, Complex.mul_re, Complex.mul_im, Complex.sub_re]
  ring

private theorem unassisted_bound (sigma N : Matrix (Fin 2) (Fin 2) ℂ) (hs : IsDensity sigma)
    (hN : (N.PosSemidef ∧ (1 - N).PosSemidef)) : successUn (K 3) (K 2) sigma N ≤ 47/84 := by
  rw [success_un_formula sigma N hs]
  have h := effect_density_pairing sigma N hs hN
  linarith

private theorem bell_entries (i j : Fin 2 × Fin 2) :
    bellDensity i j = if i.1 = i.2 ∧ j.1 = j.2 then (1/2 : ℂ) else 0 := by
  have hsq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    norm_num
  rcases i with ⟨i,k⟩; rcases j with ⟨j,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [bellDensity, bellVector, D5.S3.Quantum.QubitWitnesses.bellCoefficients,
      Matrix.vecMulVec_apply, hsq, ← pow_two]

private theorem bell_square : bellDensity * bellDensity = bellDensity := by
  exact bell_pure_state_has_maximally_mixed_marginal.2.2.2.2.1

private theorem bell_effect : (bellDensity.PosSemidef ∧ (1 - bellDensity).PosSemidef) := by
  refine ⟨bell_density_is_state.1, ?_⟩
  have he : (1-bellDensity)ᴴ * (1-bellDensity) = 1-bellDensity := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, bell_density_is_state.1.isHermitian.eq]
    simp [Matrix.sub_mul, Matrix.mul_sub, bell_square]
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self (1-bellDensity)

private theorem kraus_ext_entry {n : ℕ} (Ks : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (i j k l : Fin 2) :
    (of_kraus
      (fun r => Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) (Ks r))
      (fun r => Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) (Ks r)) B) (i,k) (j,l) =
      of_kraus Ks Ks (Matrix.of (fun p q => B (i,p) (j,q))) k l := by
  fin_cases i <;> fin_cases j <;>
    simp only [kraus_action, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Matrix.of_apply] <;> simp



private theorem bell_output (a : ℝ) : of_kraus
    (fun r => Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) (K a r))
    (fun r => Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) (K a r)) bellDensity =
    ((a^2-1)/(a^2+3) : ℝ) • bellDensity +
      ((1/(a^2+3) : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  rcases i with ⟨i,k⟩; rcases j with ⟨j,l⟩
  rw [kraus_ext_entry]
  have hf := congrArg (fun C : Matrix (Fin 2) (Fin 2) ℂ => C k l)
    (kraus_apply_formula a (Matrix.of (fun p q => bellDensity (i,p) (j,q))))
  rw [hf]
  have hn : a^2+3 ≠ 0 := ne_of_gt (by positivity : 0 < a^2+3)
  have hnc : (a : ℂ)^2+3 ≠ 0 := by exact_mod_cast hn
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp only [lambda, Matrix.add_apply, Matrix.smul_apply,
      Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, bell_entries, Matrix.one_apply, Matrix.of_apply,
      Complex.real_smul, smul_eq_mul, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat,
      Prod.mk.injEq, and_true, true_and, ite_true] <;> norm_num <;> field_simp <;> ring

private theorem assisted_success : successAs (K 3) (K 2) bellDensity bellDensity = 33/56 := by
  unfold successAs
  rw [← kraus_action, ← kraus_action, bell_output, bell_output]
  norm_num [Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.sub_mul, Matrix.one_mul, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_smul, bell_square, bell_density_is_state.2,
    bell_entries, Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem result : ¬ claim := by
  intro h
  obtain ⟨sigma,N,hs,hN,hle⟩ := h 4 (K 3) (K 2)
    (kraus_pos_def 3 (Or.inr rfl)) (kraus_pos_def 2 (Or.inl rfl))
    (kraus_complete 3) (kraus_complete 2) bellDensity bellDensity bell_density_is_state bell_effect
  rw [assisted_success] at hle
  have hbound := unassisted_bound sigma N hs hN
  norm_num at *
  linarith

end D5.S3.QuantumChannels.PositiveKrausSideEntanglementRefutation
