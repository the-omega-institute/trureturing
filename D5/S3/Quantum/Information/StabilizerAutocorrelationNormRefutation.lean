/- GID: D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.claim; result=D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.result; claim=D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.claim
   digest: The Fourier Clifford changes the Euclidean operator norm of MUB autocorrelations. -/

import D5.S3.Quantum.Magic.CepollaroPowerOfTwoZeroMagicGap
import D5.S3.Quantum.Measurement.FourierLDOILOCCRefutation
import D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity
import D5.S3.Quantum.QuantumChannels.TwirlingPhaseRetrievabilityCounterexample
import D5.S3.Quantum.Magic.QuquintWignerCriticalGeometry
import D5.S3.Arith.Lattices.Klartag.Walk.StepInputs2
import D5.S3.Observer.MatrixUnitCertificate

/-!
The native MUB spectral labels do not admit one common column permutation under every
Clifford unitary. A dimension-five Fourier transform separates the operator norms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
open Matrix
namespace D5.S3.Quantum.Information.StabilizerAutocorrelationNormRefutation

/-- The standard positive fifth root of unity. -/
def omega : ℂ := D5.S3.Observer.WindowRegister.windowRoot 5

/-- The phase convention for odd-dimensional displacements. -/
def tau : ℂ := D5.S3.Quantum.Magic.CepollaroPowerOfTwoZeroMagicGap.tau 5

/-- The cyclic shift, with `X |j⟩ = |j+1⟩`. -/
def shift : Matrix (Fin 5) (Fin 5) ℂ := D5.S3.Observer.WindowRegister.shiftMatrix 5

/-- The clock in the computational basis. -/
def clock : Matrix (Fin 5) (Fin 5) ℂ := D5.S3.Observer.WindowRegister.clockMatrix 5

/-- `D(p,q) = τ^(pq) X^p Z^q`. -/
def displacement (p q : Fin 5) : Matrix (Fin 5) (Fin 5) ℂ :=
  D5.S3.Quantum.Magic.CepollaroPowerOfTwoZeroMagicGap.paperDisplacement 5 (p, q)

/-- The native spectral labels of the six canonical Weyl--Heisenberg MUBs.
`none` denotes infinity, and `some m` denotes the line `(mr,r)`. -/
def projector (m : Option (Fin 5)) (j : Fin 5) : Matrix (Fin 5) (Fin 5) ℂ :=
  (1 / 5 : ℂ) • ∑ r : Fin 5, omega ^ ((-j * r : Fin 5).val) •
    (match m with
    | none => displacement r 0
    | some m => displacement (m * r) r)

/-- Born probabilities in the projector families, with the real expectation value. -/
def probability (ψ : Fin 5 → ℂ) (m : Option (Fin 5)) (j : Fin 5) : ℝ :=
  (star ψ ⬝ᵥ (projector m j *ᵥ ψ)).re

/-- Stacey's rectangular, real MUB autocorrelation matrix. -/
def autocorr (ψ : Fin 5 → ℂ) : Matrix (Option (Fin 5)) (Fin 5) ℝ :=
  fun m k => ∑ j, probability ψ m j * probability ψ m (j + k)

/-- Unitarity and normalization of both Weyl generators, up to unit phases. -/
def IsClifford (U : Matrix (Fin 5) (Fin 5) ℂ) : Prop :=
  Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
  (∃ (p q : Fin 5) (c : ℂ), ‖c‖ = 1 ∧ U * shift * Uᴴ = c • displacement p q) ∧
  (∃ (p q : Fin 5) (c : ℂ), ‖c‖ = 1 ∧ U * clock * Uᴴ = c • displacement p q)

/-- Clifford invariance of the ordinary Euclidean operator norm. -/
def claim : Prop :=
  ∀ (ψ : Fin 5 → ℂ), (∑ i, Complex.normSq (ψ i)) = 1 →
    ∀ U, IsClifford U → ‖autocorr (U *ᵥ ψ)‖ = ‖autocorr ψ‖

/-- The positive-exponent Fourier unitary. -/
def fourier : Matrix (Fin 5) (Fin 5) ℂ :=
  D5.S3.Quantum.Measurement.FourierLDOILOCCRefutation.fourier 5

/-- A two-coordinate pure state. -/
def psi : Fin 5 → ℂ := fun j => if j = 0 ∨ j = 1 then (Real.sqrt 2 : ℂ)⁻¹ else 0

private def s : ℝ := Real.sqrt 5
private def t : ℝ := D5.S3.Quantum.Magic.QuquintCertificateData.radical / 4

private lemma tau_eq : tau = omega ^ 3 := by
  unfold tau D5.S3.Quantum.Magic.CepollaroPowerOfTwoZeroMagicGap.tau omega
  rw [D5.S3.Observer.WindowRegister.windowRoot, ← Complex.exp_nat_mul]
  calc
    -Complex.exp ((Real.pi : ℂ) * Complex.I / 5) =
        Complex.exp ((Real.pi : ℂ) * Complex.I) *
          Complex.exp ((Real.pi : ℂ) * Complex.I / 5) := by
      rw [Complex.exp_pi_mul_I]
      ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring

private lemma s_sq : s ^ 2 = 5 := by norm_num [s]

private lemma t_sq : t ^ 2 = (5 + s) / 8 := by
  dsimp [t]
  rw [div_pow, D5.S3.Quantum.Magic.QuquintCertificateData.radical_sq]
  dsimp [s]
  ring

private lemma psi_normalized : (∑ i, Complex.normSq (psi i)) = 1 := by
  have hsum (z : ℂ) : (∑ i : Fin 5, Complex.normSq
      (if i = 0 ∨ i = 1 then z else 0)) = 2 * Complex.normSq z := by
    norm_num [Fin.sum_univ_succ]
    ring
  change (∑ i : Fin 5, Complex.normSq
    (if i = 0 ∨ i = 1 then (Real.sqrt 2 : ℂ)⁻¹ else 0)) = 1
  rw [hsum,
    D5.S3.Quantum.QuantumChannels.TwirlingPhaseRetrievabilityCounterexample.scale_normSq]
  norm_num

private lemma power_reduce {a b : ℝ} (h : a ^ 2 = b) (n : ℕ) :
    a ^ n = b ^ (n / 2) * (if n % 2 = 0 then 1 else a) := by
  have hn : n % 2 < 2 := Nat.mod_lt n (by norm_num)
  calc
    a ^ n = (a ^ 2) ^ (n / 2) * a ^ (n % 2) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    _ = _ := by
      rw [h]
      interval_cases hh : n % 2 <;> simp [hh]

private lemma s_power (n : ℕ) :
    s ^ n = (5 : ℝ) ^ (n / 2) * (if n % 2 = 0 then 1 else s) :=
  power_reduce s_sq n

private lemma t_power (n : ℕ) :
    t ^ n = ((5 + s) / 8) ^ (n / 2) * (if n % 2 = 0 then 1 else t) :=
  power_reduce t_sq n

macro "real_ring" : tactic => `(tactic|
  (ring_nf <;>
   (try simp only [s_power, t_power]) <;>
   norm_num <;>
   ring_nf <;>
   (try simp only [s_power]) <;>
   norm_num <;>
   ring))

private def rootTable : Fin 5 → ℂ :=
  ![1, ⟨(s - 1) / 4, t⟩, ⟨-(s + 1) / 4, (s - 1) / 2 * t⟩,
    ⟨-(s + 1) / 4, -(s - 1) / 2 * t⟩, ⟨(s - 1) / 4, -t⟩]

private lemma root_table (k : Fin 5) : omega ^ k.val = rootTable k := by
  change D5.S3.Quantum.Magic.QuquintWignerCriticalGeometry.zeta ^ k.val = _
  rw [D5.S3.Quantum.Magic.QuquintWignerCriticalGeometry.zeta_powers]
  have hr := D5.S3.Quantum.Magic.QuquintCertificateData.radical_sq
  change D5.S3.Quantum.Magic.QuquintCertificateData.radical ^ 2 = 10 + 2 * s at hr
  fin_cases k <;> apply Complex.ext <;>
    norm_num [D5.S3.Quantum.Magic.QuquintWignerCriticalGeometry.powerTable, rootTable, t]
  all_goals first | (rw [pow_succ, hr]; ring) | (rw [hr]; ring) | ring

private lemma omega_re : omega.re = (s - 1) / 4 := by
  simpa [rootTable] using congrArg Complex.re (root_table 1)

private lemma omega_im : omega.im = t := by
  simpa [rootTable] using congrArg Complex.im (root_table 1)

private lemma omega_mod (n : ℕ) : omega ^ (n % 5) = omega ^ n :=
  D5.S3.Quantum.Algebra.WeylPhaseArithmetic.windowRoot_pow_mod n

private lemma omega_table (n : ℕ) :
    omega ^ n = rootTable ⟨n % 5, Nat.mod_lt _ (by norm_num)⟩ := by
  rw [← omega_mod]
  exact root_table ⟨n % 5, Nat.mod_lt _ (by norm_num)⟩

lemma shift_power (p : Fin 5) (i j : Fin 5) :
    (shift ^ p.val) i j = if i = j + p then 1 else 0 := by
  have h (p i j : ZMod 5) :
      (shift ^ p.val) i j = if i = j + p then 1 else 0 := by
    simpa only [shift, ZMod.natCast_zmod_val, sub_eq_iff_eq_add'] using
      (D5.S3.Observer.MatrixUnitCertificate.shift_matrix_pow_apply (M := 5) p.val i j)
  exact h p i j

private lemma shift_eq : shift = fun i j => if i = j + 1 then 1 else 0 := by
  ext i j
  have h := shift_power 1 i j
  change (shift ^ 1) i j = _ at h
  simpa only [pow_one] using h

private lemma displacement_entry (p q i j : Fin 5) :
    displacement p q i j =
      if i = j + p then omega ^ (3 * p.val * q.val + q.val * j.val) else 0 := by
  have hentry : D5.S3.Quantum.Algebra.WeylDisplacement.displacement 5 p q i j =
      if i.val = (j.val + p.val) % 5 then omega ^ (q.val * j.val) else 0 := by
    exact D5.S3.Quantum.Magic.CepollaroPowerOfTwoZeroMagicGap.displacement_entry
      5 (show ZMod 5 from p) q i j
  have hindex : i.val = (j.val + p.val) % 5 ↔ i = j + p := by
    rw [← Fin.val_inj, Fin.val_add]
  change (tau ^ (p.val * q.val) •
    D5.S3.Quantum.Algebra.WeylDisplacement.displacement 5 p q) i j = _
  simp only [Matrix.smul_apply, hentry, hindex, tau_eq]
  split_ifs <;> simp only [smul_eq_mul, mul_zero]
  rw [← pow_mul, ← pow_add]
  congr 1
  ring

private lemma fourier_entry (i j : Fin 5) :
    fourier i j = (s / 5 : ℝ) * omega ^ ((i * j : Fin 5).val) := by
  have hi : (Real.sqrt 5 : ℂ)⁻¹ = (s / 5 : ℝ) := by
    exact_mod_cast (Real.sqrt_div_self (x := 5)).symm
  have hp : omega ^ ((i * j : Fin 5).val) =
      Complex.exp (2 * Real.pi * Complex.I * (i.val : ℂ) * (j.val : ℂ) / 5) := by
    rw [Fin.val_mul, omega_mod, omega, D5.S3.Observer.WindowRegister.windowRoot,
      ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  change Complex.exp (2 * Real.pi * Complex.I * (i.val : ℂ) * (j.val : ℂ) / 5) /
    (Real.sqrt 5 : ℂ) = _
  rw [← hp, div_eq_mul_inv, hi]
  ring

private def c : ℝ := D5.S3.Quantum.Measurement.FourierLDOILOCCRefutation.c

private lemma c_power (n : ℕ) :
    c ^ n = (1 / 2 : ℝ) ^ (n / 2) * (if n % 2 = 0 then 1 else c) :=
  power_reduce (by simpa only [c, pow_two] using
    D5.S3.Quantum.Measurement.FourierLDOILOCCRefutation.c_sq) n

private lemma psi_entry (j : Fin 5) : psi j = if j = 0 ∨ j = 1 then (c : ℂ) else 0 := by
  simp only [psi, c, D5.S3.Quantum.Measurement.FourierLDOILOCCRefutation.c,
    Complex.ofReal_inv]

private def phi : Fin 5 → ℂ :=
  fun i => (c * s / 5 : ℝ) * (1 + omega ^ i.val)

private lemma fourier_psi : fourier *ᵥ psi = phi := by
  funext i
  fin_cases i <;> apply Complex.ext <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, fourier_entry, psi_entry,
      phi, omega_table, omega_re, omega_im, rootTable, Complex.mul_re, Complex.mul_im] <;> ring

private lemma fourier_clifford : IsClifford fourier := by
  have clock_eq : clock = diagonal fun j => omega ^ j.val := rfl
  let W := D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity.fourierRows
    5 5 (le_refl 5)
  have hF : fourier = (Real.sqrt 5 : ℂ)⁻¹ • W := by
    ext i j
    have hi : (i.val : ZMod 5) = ZMod.finEquiv 5 i :=
      ZMod.natCast_zmod_val (show ZMod 5 from i)
    have hj : (j.val : ZMod 5) = ZMod.finEquiv 5 j :=
      ZMod.natCast_zmod_val (show ZMod 5 from j)
    have he : (ZMod.finEquiv 5 j) * (ZMod.finEquiv 5 i) =
        (((i.val : ℤ) * (j.val : ℤ) : ℤ) : ZMod 5) := by
      push_cast
      rw [hi, hj]
      ring
    unfold W D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity.fourierRows
    simp only [Fin.castLE_refl, Matrix.smul_apply, smul_eq_mul, he, ZMod.stdAddChar_coe,
      fourier, D5.S3.Quantum.Measurement.FourierLDOILOCCRefutation.fourier]
    push_cast
    rw [div_eq_mul_inv, mul_comm]
    congr 2
    ring
  have hh' : fourier * fourierᴴ = 1 := by
    have hs : (Real.sqrt 5 : ℂ) * Real.sqrt 5 = 5 := by
      exact_mod_cast Real.mul_self_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    rw [hF, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity.fourierRows_gram,
      smul_smul, star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, hs]
    norm_num
  have hh : fourierᴴ * fourier = 1 := _root_.mul_eq_one_comm.mp hh'
  refine ⟨hh, hh', ?_, ?_⟩
  · have hFX : fourier * shift = clock * fourier := by
      ext i j
      rw [clock_eq, Matrix.diagonal_mul]
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
        norm_num [fourier_entry, shift_eq, Matrix.mul_apply, Fin.sum_univ_succ,
          Complex.mul_re, Complex.mul_im, omega_table, omega_re, omega_im, rootTable] <;> real_ring
    have h01 : displacement 0 1 = clock := by
      change tau ^ (0 * 1) • (shift ^ 0 * clock ^ 1) = clock
      simp
    refine ⟨0, 1, 1, by norm_num, ?_⟩
    rw [hFX, Matrix.mul_assoc, hh', Matrix.mul_one, one_smul, h01]
  · have hFZ : fourier * clock = displacement 4 0 * fourier := by
      ext i j
      rw [clock_eq, Matrix.mul_diagonal]
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
        norm_num [fourier_entry, Matrix.mul_apply, Fin.sum_univ_succ, displacement_entry,
          Complex.mul_re, Complex.mul_im, omega_table, omega_re, omega_im, rootTable] <;> real_ring
    refine ⟨4, 0, 1, by norm_num, ?_⟩
    rw [hFZ, Matrix.mul_assoc, hh', Matrix.mul_one, one_smul]

private def inputProb : Option (Fin 5) → Fin 5 → ℝ
  | none => ![2/5, (3+s)/20, (3-s)/20, (3-s)/20, (3+s)/20]
  | some m =>
    ![![1/2, 1/2, 0, 0, 0],
      ![(3-s)/20, (3-s)/20, (3+s)/20, 2/5, (3+s)/20],
      ![(3+s)/20, (3+s)/20, (3-s)/20, 2/5, (3-s)/20],
      ![(3+s)/20, (3+s)/20, (3-s)/20, 2/5, (3-s)/20],
      ![(3-s)/20, (3-s)/20, (3+s)/20, 2/5, (3+s)/20]] m

private def outputProb : Option (Fin 5) → Fin 5 → ℝ
  | none => ![1/2, 0, 0, 0, 1/2]
  | some m =>
    ![![2/5, (3+s)/20, (3-s)/20, (3-s)/20, (3+s)/20],
      ![(3-s)/20, (3+s)/20, 2/5, (3+s)/20, (3-s)/20],
      ![(3+s)/20, (3-s)/20, (3-s)/20, (3+s)/20, 2/5],
      ![(3+s)/20, 2/5, (3+s)/20, (3-s)/20, (3-s)/20],
      ![(3-s)/20, (3-s)/20, (3+s)/20, 2/5, (3+s)/20]] m

macro "certificate_ring" : tactic => `(tactic|
  (ring_nf <;>
   (try simp only [c_power]) <;>
   norm_num <;>
   real_ring))

private lemma probability_psi (m : Option (Fin 5)) (j : Fin 5) :
    probability psi m j = inputProb m j := by
  fin_cases m <;> fin_cases j <;>
    norm_num [probability, projector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.smul_apply, Finset.sum_apply, smul_eq_mul, displacement_entry,
      psi_entry, inputProb, Fin.neg_def, omega_table, omega_re, omega_im, rootTable,
      Complex.mul_re, Complex.mul_im] <;> certificate_ring

private lemma probability_phi (m : Option (Fin 5)) (j : Fin 5) :
    probability phi m j = outputProb m j := by
  fin_cases m <;> fin_cases j <;>
    norm_num [probability, projector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.smul_apply, Finset.sum_apply, smul_eq_mul, displacement_entry,
      phi, outputProb, Fin.neg_def, omega_table, omega_re, omega_im, rootTable,
      Complex.mul_re, Complex.mul_im] <;> certificate_ring

private def rowA : Fin 5 → ℝ := ![1/2, 1/4, 0, 0, 1/4]
private def rowB : Fin 5 → ℝ := ![3/10, (7+s)/40, (7-s)/40, (7-s)/40, (7+s)/40]
private def rowC : Fin 5 → ℝ := ![3/10, (7-s)/40, (7+s)/40, (7+s)/40, (7-s)/40]

private def original : Matrix (Option (Fin 5)) (Fin 5) ℝ
  | none => rowB
  | some m => ![rowA, rowB, rowC, rowC, rowB] m

private def transformed : Matrix (Option (Fin 5)) (Fin 5) ℝ
  | none => rowA
  | some _ => rowB

private lemma autocorr_psi : autocorr psi = original := by
  ext m k
  simp only [autocorr, probability_psi]
  fin_cases m <;> fin_cases k <;>
    norm_num [inputProb, original, rowA, rowB, rowC, Fin.sum_univ_succ] <;> real_ring

private lemma autocorr_phi : autocorr phi = transformed := by
  ext m k
  simp only [autocorr, probability_phi]
  fin_cases m <;> fin_cases k <;>
    norm_num [outputProb, transformed, rowA, rowB, Fin.sum_univ_succ] <;> real_ring

private lemma norm_sq_le_sum_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖A‖ ^ 2 ≤ ∑ i, ∑ j, A i j ^ 2 := by
  have h := D5.S3.Arith.Lattices.Klartag.Walk.StepInputs2.opNorm_le_frobenius A
  rw [Matrix.l2_opNorm_toEuclideanCLM] at h
  have hQ : 0 ≤ ∑ i, ∑ j, A i j ^ 2 := by positivity
  have hs := (sq_le_sq₀ (norm_nonneg A) (Real.sqrt_nonneg _)).mpr h
  simpa only [Real.sq_sqrt hQ] using hs

private lemma original_certificate :
    (∑ i, ∑ j, ((originalᴴ * original) i j) ^ 2) = (2961 + 19*s)/1600 := by
  norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_option,
    Fin.sum_univ_succ, original, rowA, rowB, rowC]
  real_ring

private lemma test_norm :
    ‖(EuclideanSpace.equiv (Fin 5) ℝ).symm rowB‖ ^ 2 = 9/40 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  norm_num [rowB, Fin.sum_univ_succ]
  real_ring

private lemma test_image :
    ‖(EuclideanSpace.equiv (Option (Fin 5)) ℝ).symm (transformed *ᵥ rowB)‖ ^ 2 =
      (993 + 19*s)/3200 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  norm_num [Matrix.mulVec, dotProduct, Fintype.sum_option, Fin.sum_univ_succ,
    transformed, rowA, rowB]
  real_ring

private lemma norms_differ : ‖autocorr (fourier *ᵥ psi)‖ ≠ ‖autocorr psi‖ := by
  rw [fourier_psi, autocorr_phi, autocorr_psi]
  intro he
  have hs : 2 < s ∧ s < 3 := by
    have hn := Real.sqrt_nonneg (5 : ℝ)
    change 0 ≤ s at hn
    constructor <;> nlinarith [s_sq]
  have hu := norm_sq_le_sum_sq (originalᴴ * original)
  rw [Matrix.l2_opNorm_conjTranspose_mul_self, original_certificate] at hu
  have hl := Matrix.l2_opNorm_mulVec transformed
    ((EuclideanSpace.equiv (Fin 5) ℝ).symm rowB)
  have hl' := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hl
  change ‖(EuclideanSpace.equiv (Option (Fin 5)) ℝ).symm (transformed *ᵥ rowB)‖ ^ 2 ≤
    (‖transformed‖ * ‖(EuclideanSpace.equiv (Fin 5) ℝ).symm rowB‖) ^ 2 at hl'
  rw [mul_pow, test_norm, test_image, he] at hl'
  nlinarith [sq_nonneg (‖original‖ ^ 2 - 7/5)]

theorem result : ¬ claim := by
  intro h
  exact norms_differ (h psi psi_normalized fourier fourier_clifford)

#print axioms claim
#print axioms result

end D5.S3.Quantum.Information.StabilizerAutocorrelationNormRefutation
