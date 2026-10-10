/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.claim; result=D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.result; claim=D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.claim
   digest: Finite-Fock beam-splitter states need not be extreme Wigner-positive states. -/
/-
result:
  proof_shape: bind-only
  escape_witness: none
admission_basis: open-problem-resolution (#14447; Refuted)
Private helpers (each consumed on the result path):
  sparse_trace: proof_shape: bind-only; consumers: trace_familyS, trace_familyH.
  sparse_psd: proof_shape: bind-only; consumers: perturb_psd.
  sqrt6_times_sqrt24: proof_shape: bind-only; consumers: familyS_wigner, familyH_wigner.
  sparse_wigner: proof_shape: bind-only; consumers: familyS_wigner, familyH_wigner.
  wigner_add: proof_shape: bind-only; consumers: end_wigner.
  wigner_sub: proof_shape: bind-only; consumers: end_wigner.
  wigner_smul: proof_shape: bind-only; consumers: end_wigner.
  fockPair_apply: proof_shape: bind-only; consumers: fockExpansion_apply.
  balanced_fock: proof_shape: bind-only; consumers: balanced_input.
  balanced_input: proof_shape: bind-only; consumers: family_output.
  fockExpansion_apply: proof_shape: bind-only; consumers: family_output.
  sqrt_two_pow_six: proof_shape: bind-only; consumers: family_output.
  sqrt_two_pow_four: proof_shape: bind-only; consumers: family_output.
  psi_a_norm: proof_shape: bind-only; consumers: phi_a_norm, result.
  phi_a_norm: proof_shape: bind-only; consumers: result.
  family_output: proof_shape: bind-only; consumers: bsState_family.
  outputCoeff_above: proof_shape: bind-only; consumers: bsState_family.
  bsState_family: proof_shape: bind-only; consumers: family_not_extreme.
  familyS_wigner: proof_shape: bind-only; consumers: end_wigner.
  familyH_wigner: proof_shape: bind-only; consumers: end_wigner.
  eps_bounds: proof_shape: bind-only; consumers: end_mem_WPS, endpoint_bounds, perturb_psd, end_ne_state, family_not_extreme.
  perturb_sparse: proof_shape: bind-only; consumers: perturb_psd.
  perturb_psd: proof_shape: bind-only; consumers: end_psd.
  trace_familyS: proof_shape: bind-only; consumers: end_trace.
  trace_familyH: proof_shape: bind-only; consumers: end_trace.
  end_trace: proof_shape: bind-only; consumers: end_mem_WPS.
  trace_ratio_bounds: proof_shape: bind-only; consumers: end_mem_WPS, endpoint_bounds.
  endpoint_bounds: proof_shape: bind-only; consumers: end_mem_WPS, end_psd.
  end_psd: proof_shape: bind-only; consumers: end_mem_WPS.
  end_wigner: proof_shape: bind-only; consumers: end_mem_WPS.
  end_mem_WPS: proof_shape: bind-only; consumers: family_not_extreme.
  end_midpoint: proof_shape: bind-only; consumers: family_not_extreme.
  end_ne_state: proof_shape: bind-only; consumers: family_not_extreme.
  family_not_extreme: proof_shape: bind-only; consumers: result.
Direct frozen dependencies:
  D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity
  statement_id: sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3
  D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.beamSplitter
  statement_id: sha256:94b3c9f6bfb3a10e79519891f510d15a9586dc9b5d1cd64526949222e4877d2b
  D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.fockExpansion
  statement_id: sha256:a7e0e0fbddaa39e12dce64a7d4316e4e1fc965dd2ba066d3eb30e47644419627
  D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.beamUnitary_fock
  statement_id: sha256:d72910dcc446ec8de4cd2543c6419599d4345ea538916a185a2c8d693c01f7ce
  D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.tensor
  statement_id: sha256:e1c657f6d4440a647e61a871bf4435cb98f4cb6bc8fb729ae744a03270b69a9b
  D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.fockPair
  statement_id: sha256:d61de90cc28d6523a1fe07ed3c2b17777577f024e9a9fb298768e08905cdd7f7
  D5/S3/Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum.countablePartialTraceRight
  statement_id: sha256:c6846f133601aed0da4374874130871a2ce330b4ac1cf7e8d91254664f5ee81e
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter
import D5.S3.Observer.DefectModularFirstLaw.ThermofieldMarginalModularSpectrum

noncomputable section
open scoped BigOperators ComplexOrder Matrix
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.FiniteFockBeamSplitterNonExtremality
open D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter

def genLaguerre (k m : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), (-1 : ℝ)^i * ((m+k).choose (m-i) : ℝ) *
    x^i / (i.factorial : ℝ)

private def wignerFockUpper (m n : ℕ) (α : ℂ) : ℂ :=
  ((2 / Real.pi * (-1 : ℝ)^m * Real.sqrt ((m.factorial : ℝ) / (n.factorial : ℝ))) : ℂ) *
    (2 * α)^(n-m) * (genLaguerre (n-m) m (4 * ‖α‖^2) : ℂ) *
    (Real.exp (-2 * ‖α‖^2) : ℂ)

def wignerFock (m n : ℕ) (α : ℂ) : ℂ :=
  if m ≤ n then wignerFockUpper m n α else (starRingEnd ℂ) (wignerFockUpper n m α)

def wigner {K : ℕ} (A : Matrix (Fin (K+1)) (Fin (K+1)) ℂ) (α : ℂ) : ℂ :=
  ∑ m, ∑ n, A m n * wignerFock m.val n.val α

def WPS (K : ℕ) : Set (Matrix (Fin (K+1)) (Fin (K+1)) ℂ) :=
  {A | A.PosSemidef ∧ A.trace = 1 ∧ ∀ α, 0 ≤ wigner A α}

def IsExtremeWPS (K : ℕ) (σ : Matrix (Fin (K+1)) (Fin (K+1)) ℂ) : Prop :=
  σ ∈ WPS K ∧ ∀ x ∈ WPS K, ∀ y ∈ WPS K,
    σ = (1/2 : ℝ) • (x+y) → x = σ ∧ y = σ

def bsState {N : ℕ} (ψ φ : Fin (N+1) → ℂ) :
    Matrix (Fin (2*N+1)) (Fin (2*N+1)) ℂ :=
  let Ψ := beamSplitter (1/2) (by constructor <;> norm_num)
    (∑ j : Fin (N+1), ∑ k : Fin (N+1), (ψ j * φ k) • fockPair j.val k.val)
  (D5.S3.Observer.DefectModularFirstLaw.ThermofieldMarginalModularSpectrum.countablePartialTraceRight
    (D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity
      (fun idx : ℕ × ℕ => (Ψ idx.2) idx.1))).submatrix
    (fun m : Fin (2*N+1) => m.val) (fun n : Fin (2*N+1) => n.val)

def claim : Prop :=
  ∀ (N : ℕ) (ψ φ : Fin (N+1) → ℂ),
    (∑ i, ‖ψ i‖^2) = 1 → (∑ i, ‖φ i‖^2) = 1 →
    IsExtremeWPS (2*N) (bsState ψ φ)

private def sparse (d0 d1 d2 d4 c : ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.diagonal ![(d0 : ℂ), d1, d2, 0, d4] +
    Matrix.single 0 4 (c : ℂ) + Matrix.single 4 0 (c : ℂ)

private lemma sparse_trace (d0 d1 d2 d4 c : ℝ) :
    (sparse d0 d1 d2 d4 c).trace = ((d0+d1+d2+d4 : ℝ) : ℂ) := by
  simp [Matrix.trace, Matrix.single, sparse, Fin.sum_univ_succ]

  ring

private lemma sparse_psd (d0 d1 d2 d4 c : ℝ) (h0 : 0 < d0) (h1 : 0 ≤ d1)
    (h2 : 0 ≤ d2) (hdet : c^2 ≤ d0*d4) : (sparse d0 d1 d2 d4 c).PosSemidef := by
  let v : Fin 5 → ℂ := ![d0, 0, 0, 0, c]
  let D : Fin 5 → ℂ := ![0, d1, d2, 0, ((d4-c^2/d0 : ℝ) : ℂ)]
  have hd4 : 0 ≤ d4-c^2/d0 := by
    apply sub_nonneg.mpr
    exact (div_le_iff₀ h0).mpr (by nlinarith [hdet])
  have hD : (Matrix.diagonal D).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> dsimp [D]
    · exact le_refl 0
    · exact Complex.zero_le_real.mpr h1
    · exact Complex.zero_le_real.mpr h2
    · exact le_refl 0
    · exact Complex.zero_le_real.mpr hd4
  have hv := Matrix.posSemidef_vecMulVec_self_star v
  have hG := (hv.smul (show (0 : ℝ) ≤ 1/d0 by positivity)).add hD
  convert hG using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single, sparse, v, D, Matrix.vecMulVec, Matrix.diagonal,
      Complex.conj_ofReal, Matrix.add_apply]

  all_goals field_simp [h0.ne']
  all_goals norm_cast
  all_goals field_simp [h0.ne']
  all_goals ring

private lemma sqrt6_times_sqrt24 : Real.sqrt 6 * Real.sqrt (1/24) = 1/2 := by
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]
  norm_num

private lemma sparse_wigner (d0 d1 d2 d4 c : ℝ) (α : ℂ) :
    wigner (sparse d0 d1 d2 d4 c) α =
    (((2/Real.pi)*Real.exp (-2*‖α‖^2) *
      (d0 + d1*(4*Complex.normSq α-1) + d2*(1-8*Complex.normSq α+8*(Complex.normSq α)^2) +
       d4*(1-16*Complex.normSq α+48*(Complex.normSq α)^2-128/3*(Complex.normSq α)^3+32/3*(Complex.normSq α)^4) +
       32*c*Real.sqrt (1/24)*(α.re^4-6*α.re^2*α.im^2+α.im^4)) : ℝ) : ℂ) := by
  simp [-Complex.ofReal_exp, wigner, Matrix.single, sparse, Fin.sum_univ_succ, wignerFock, wignerFockUpper,
    genLaguerre, Finset.sum_range_succ]
  norm_num [-Complex.ofReal_exp, Nat.choose]
  simp only [← Complex.ofReal_pow, Complex.sq_norm]
  apply Complex.ext <;>
    simp [-Complex.ofReal_exp, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      pow_succ, Complex.normSq_apply]
  all_goals ring

private lemma wigner_add {K : ℕ} (M N : Matrix (Fin (K+1)) (Fin (K+1)) ℂ) (α : ℂ) :
    wigner (M+N) α = wigner M α + wigner N α := by
  simp [wigner, add_mul, Finset.sum_add_distrib]

private lemma wigner_sub {K : ℕ} (M N : Matrix (Fin (K+1)) (Fin (K+1)) ℂ) (α : ℂ) :
    wigner (M-N) α = wigner M α - wigner N α := by
  simp [wigner, sub_mul, Finset.sum_sub_distrib]

private lemma wigner_smul {K : ℕ} (t : ℝ) (M : Matrix (Fin (K+1)) (Fin (K+1)) ℂ) (α : ℂ) :
    wigner (t • M) α = (t : ℂ) * wigner M α := by
  simp [wigner, Matrix.smul_apply, mul_assoc, Finset.mul_sum]

private lemma fockPair_apply (m n p q : ℕ) :
    fockPair m n q p = if p = m ∧ q = n then (1:ℂ) else 0 := by
  simp [fockPair, tensor, lp.single_apply,
    Pi.single_apply]
  split_ifs <;> simp_all

private lemma balanced_fock (m n : ℕ) :
    beamSplitter (1/2) (by constructor <;> norm_num) (fockPair m n) =
      fockExpansion (Real.sqrt (1/2)) (Real.sqrt (1/2)) m n := by
  unfold beamSplitter
  convert beamUnitary_fock _ _ _ m n using 1; norm_num

private lemma balanced_input (N : ℕ) (ψ φ : Fin (N+1) → ℂ) :
    beamSplitter (1/2) (by constructor <;> norm_num)
      (∑ j : Fin (N+1), ∑ k : Fin (N+1), (ψ j * φ k) • fockPair j.val k.val) =
    ∑ j : Fin (N+1), ∑ k : Fin (N+1),
      (ψ j * φ k) • fockExpansion (Real.sqrt (1/2)) (Real.sqrt (1/2)) j.val k.val := by
  simp only [map_sum, map_smul, balanced_fock]

private lemma fockExpansion_apply (t r : ℝ) (m n p q : ℕ) :
    fockExpansion t r m n q p =
    ∑ i : Fin (m+1), ∑ j : Fin (n+1),
      (((m.choose i : ℝ) * (n.choose j : ℝ) * t ^ (i : ℕ) * r ^ (m-i) *
          (-r) ^ (j : ℕ) * t ^ (n-j) *
          Real.sqrt ((i+j : ℕ).factorial : ℝ) *
          Real.sqrt ((m-i+(n-j) : ℕ).factorial : ℝ) /
          (Real.sqrt (m.factorial : ℝ) * Real.sqrt (n.factorial : ℝ)) : ℝ) : ℂ) *
      (if p = i+j ∧ q = m-i+(n-j) then 1 else 0) := by
  simp only [fockExpansion, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, fockPair_apply]

private lemma sqrt_two_pow_six : Real.sqrt (2:ℝ)^6 = 8 := by
  calc
    Real.sqrt (2:ℝ)^6 = (Real.sqrt (2:ℝ)^2)^3 := by ring
    _ = 8 := by rw [Real.sq_sqrt (by norm_num)]; norm_num

private lemma sqrt_two_pow_four : Real.sqrt (2:ℝ)^4 = 4 := by
  calc
    Real.sqrt (2:ℝ)^4 = (Real.sqrt (2:ℝ)^2)^2 := by ring
    _ = 4 := by rw [Real.sq_sqrt (by norm_num)]; norm_num

private def psi_a (a : ℝ) : Fin 3 → ℂ :=
  ![((1 / Real.sqrt (1+a^2) : ℝ) : ℂ), 0, ((a / Real.sqrt (1+a^2) : ℝ) : ℂ)]
private def phi_a (a : ℝ) : Fin 3 → ℂ :=
  ![((1 / Real.sqrt (1+a^2) : ℝ) : ℂ), 0, ((-a / Real.sqrt (1+a^2) : ℝ) : ℂ)]

private def familyS (a : ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  sparse (1+3*a^4/8) (2*a^2) (a^4/4) (3*a^4/8) (-Real.sqrt 6*a^2/4)
private def familyH (a : ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  sparse (a^2/2) (a^2) (a^2/2) 0 (-Real.sqrt 6*a^2/4)
private def familyEps (a : ℝ) : ℝ :=
  min (1/2) (min (a^2/4) (3*a^4/(16*(3+a^2/2))))
private def familyState (a : ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  (1/(1+a^2)^2 : ℝ) • familyS a
private def familyEnd (a t : ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  (1/(1+a^2)^2 : ℝ) •
    (familyS a + t • (familyH a - (2*a^2/(1+a^2)^2 : ℝ) • familyS a))
private def familyR (a : ℝ) (α : ℂ) : ℝ :=
  1-a^2+4*a^2*Complex.normSq α-2*a^2*(Complex.normSq α)^2
private def outputCoeff (a : ℝ) (p q : ℕ) : ℂ :=
  if p = 0 ∧ q = 0 then (1/(1+a^2) : ℝ) else
  if p = 1 ∧ q = 1 then (Real.sqrt 2*a/(1+a^2) : ℝ) else
  if p = 2 ∧ q = 2 then (a^2/(2*(1+a^2)) : ℝ) else
  if p = 0 ∧ q = 4 then (-Real.sqrt 6*a^2/(4*(1+a^2)) : ℝ) else
  if p = 4 ∧ q = 0 then (-Real.sqrt 6*a^2/(4*(1+a^2)) : ℝ) else 0

private lemma psi_a_norm (a : ℝ) : (∑ i, ‖psi_a a i‖^2) = 1 := by
  have hp : 0 < 1+a^2 := by positivity
  simp [psi_a, Fin.sum_univ_succ, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt hp.le, sq_abs]
  field_simp
private lemma phi_a_norm (a : ℝ) : (∑ i, ‖phi_a a i‖^2) = 1 := by
  simpa only [psi_a, phi_a, neg_sq] using psi_a_norm (-a)

private def familyOutput (a : ℝ) := beamSplitter (1/2) (by constructor <;> norm_num)
  (∑ j : Fin 3, ∑ k : Fin 3, (psi_a a j * phi_a a k) • fockPair j.val k.val)

private lemma family_output (a : ℝ) (p q : ℕ) :
    familyOutput a q p = outputCoeff a p q := by
  rw [familyOutput, balanced_input]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  simp [psi_a, phi_a, Fin.sum_univ_succ, fockExpansion_apply]
  norm_num [Fin.sum_univ_succ, Nat.choose]
  have hd : 0 < 1+a^2 := by positivity
  have hds : Real.sqrt (1+a^2)^2 = 1+a^2 := Real.sq_sqrt hd.le
  have hdp : Real.sqrt (1+a^2) ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  have hhalf : (Real.sqrt (1/2:ℝ))^2 = 1/2 := Real.sq_sqrt (by norm_num)
  have h2 : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have h6 : (Real.sqrt (6:ℝ))^2 = 6 := Real.sq_sqrt (by norm_num)
  have h24 : Real.sqrt (24:ℝ) = 2*Real.sqrt 6 := by
    rw [show (24:ℝ) = 2^2*6 by norm_num, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  rw [h24]
  simp only [outputCoeff]
  split_ifs <;> simp_all

  all_goals field_simp
  all_goals norm_cast
  all_goals norm_num [← Complex.ofReal_pow, sqrt_two_pow_six, sqrt_two_pow_four]
  all_goals try ring_nf
  all_goals simp only [hds, Complex.ofReal_add, Complex.ofReal_one]
  all_goals field_simp


private lemma outputCoeff_above (a : ℝ) (p n : ℕ) (hn : 5 ≤ n) : outputCoeff a p n = 0 := by
  simp only [outputCoeff]
  split_ifs <;> simp_all

private lemma bsState_family (a : ℝ) : bsState (psi_a a) (phi_a a) = familyState a := by
  ext i j
  change (∑' n : ℕ, familyOutput a n i.val * (starRingEnd ℂ) (familyOutput a n j.val)) = familyState a i j
  simp only [family_output]
  rw [tsum_eq_sum (s := Finset.range 5) (by
    intro n hn
    have hn' : 5 ≤ n := by simpa using hn
    rw [outputCoeff_above _ _ _ hn']
    simp)]
  have hd : 1+a^2 ≠ 0 := by positivity
  fin_cases i <;> fin_cases j <;>
    norm_num [outputCoeff, familyState, familyS, Matrix.single, sparse, Finset.sum_range_succ,
      Matrix.smul_apply, smul_eq_mul, Complex.conj_ofReal]
  all_goals push_cast
  all_goals norm_cast
  all_goals norm_num [map_ofNat, map_inv₀]
  all_goals field_simp

  all_goals norm_num [← Complex.ofReal_pow, Real.sq_sqrt]
  all_goals ring

private lemma familyS_wigner (a : ℝ) (α : ℂ) : wigner (familyS a) α =
    ((2/Real.pi*Real.exp (-2*‖α‖^2)*
      (familyR a α^2+32*a^2*α.re^2*α.im^2) : ℝ) : ℂ) := by
  rw [familyS, sparse_wigner]
  congr 1
  unfold familyR
  simp only [Complex.normSq_apply]
  have h := sqrt6_times_sqrt24
  ring_nf
  simp only [mul_assoc, h]
  ring
private lemma familyH_wigner (a : ℝ) (α : ℂ) : wigner (familyH a) α =
    ((2/Real.pi*Real.exp (-2*‖α‖^2)*32*a^2*α.re^2*α.im^2 : ℝ) : ℂ) := by
  rw [familyH, sparse_wigner]
  congr 1
  simp only [Complex.normSq_apply]
  have h := sqrt6_times_sqrt24
  ring_nf
  simp only [mul_assoc, h]
  ring
private lemma eps_bounds (a : ℝ) (ha : 0 < a) :
    0 < familyEps a ∧ familyEps a ≤ 1/2 ∧ familyEps a ≤ a^2/4 ∧
    familyEps a ≤ 3*a^4/(16*(3+a^2/2)) := by
  unfold familyEps
  refine ⟨by positivity, min_le_left _ _, ?_, ?_⟩
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

private lemma perturb_sparse (a u : ℝ) : familyS a + u • familyH a =
    sparse (1+3*a^4/8+u*a^2/2) (2*a^2+u*a^2)
      (a^4/4+u*a^2/2) (3*a^4/8) (-Real.sqrt 6*a^2*(1+u)/4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [familyS, familyH, sparse, Matrix.single] <;> ring

private lemma perturb_psd (a : ℝ) (ha : 0 < a) (u : ℝ)
    (hu : |u| ≤ familyEps a) : (familyS a + u • familyH a).PosSemidef := by
  have he := eps_bounds a ha
  have hu0 := neg_abs_le u
  have hu1 := le_abs_self u
  have hu2 : |u| ≤ a^2/4 := hu.trans he.2.2.1
  have huh : |u| ≤ 1/2 := hu.trans he.2.1
  have hu3 : |u| *(3+a^2/2) ≤ 3*a^4/16 := by
    have hp : 0 < 3+a^2/2 := by positivity
    have h := hu.trans he.2.2.2
    have h' := (le_div_iff₀ (show 0 < 16*(3+a^2/2) by positivity)).mp h
    nlinarith
  have hquad : u^2 ≤ |u|/2 := by
    have h := mul_nonneg (abs_nonneg u) (sub_nonneg.mpr huh)
    nlinarith [sq_abs u]
  have hlin : -(a^2/2+2)*|u| ≤ (a^2/2-2)*u := by
    have h := mul_le_mul_of_nonneg_left hu0 (show 0 ≤ a^2/2 by positivity)
    nlinarith
  have hbr : 0 ≤ 3*a^4/8+(a^2/2-2)*u-u^2 := by
    nlinarith [sq_nonneg (a^2)]
  rw [perturb_sparse]
  apply sparse_psd
  · have h := mul_le_mul_of_nonneg_left hu0 (show 0 ≤ a^2/2 by positivity)
    nlinarith [sq_nonneg (a^2)]
  · have h := mul_le_mul_of_nonneg_left hu0 (show 0 ≤ a^2 by positivity)
    nlinarith
  · have h := mul_le_mul_of_nonneg_left hu0 (show 0 ≤ a^2/2 by positivity)
    nlinarith
  · have hs : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    have hid : (1+3*a^4/8+u*a^2/2)*(3*a^4/8) -
        (-Real.sqrt 6*a^2*(1+u)/4)^2 =
        (3*a^4/8)*(3*a^4/8+(a^2/2-2)*u-u^2) := by
      ring_nf
      rw [hs]
      ring
    have hnonneg := mul_nonneg (show 0 ≤ 3*a^4/8 by positivity) hbr
    linarith

private lemma trace_familyS (a : ℝ) : (familyS a).trace = (((1+a^2)^2 : ℝ) : ℂ) := by
  rw [familyS, sparse_trace]
  congr 1
  ring
private lemma trace_familyH (a : ℝ) : (familyH a).trace = ((2*a^2 : ℝ) : ℂ) := by
  rw [familyH, sparse_trace]
  congr 1
  ring

private lemma end_trace (a t : ℝ) : (familyEnd a t).trace = 1 := by
  have hd : 1+a^2 ≠ 0 := by positivity
  simp only [familyEnd, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sub,
    trace_familyS, trace_familyH, Complex.real_smul,
    ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_sub]
  norm_cast
  field_simp
  ring

private lemma trace_ratio_bounds (a : ℝ) :
    0 ≤ 2*a^2/(1+a^2)^2 ∧ 2*a^2/(1+a^2)^2 ≤ 1/2 := by
  constructor
  · positivity
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (a^2-1)]

private lemma endpoint_bounds (a : ℝ) (ha : 0 < a) (t : ℝ)
    (ht : |t| ≤ familyEps a/2) :
    1/2 ≤ 1-t*(2*a^2/(1+a^2)^2) ∧
    |t/(1-t*(2*a^2/(1+a^2)^2))| ≤ familyEps a := by
  have he := eps_bounds a ha
  have hq := trace_ratio_bounds a
  have hprod : t*(2*a^2/(1+a^2)^2) ≤ familyEps a/2 := by
    calc
      _ ≤ |t| *(2*a^2/(1+a^2)^2) := mul_le_mul_of_nonneg_right (le_abs_self t) hq.1
      _ ≤ |t| *1 := mul_le_mul_of_nonneg_left (by linarith : 2*a^2/(1+a^2)^2 ≤ 1) (abs_nonneg t)
      _ ≤ familyEps a/2 := by simpa using ht
  have hl : 1/2 ≤ 1-t*(2*a^2/(1+a^2)^2) := by linarith
  refine ⟨hl, ?_⟩
  rw [abs_div, abs_of_pos (by linarith : 0 < 1-t*(2*a^2/(1+a^2)^2))]
  apply (div_le_iff₀ (by linarith)).mpr
  nlinarith

private lemma end_psd (a : ℝ) (ha : 0 < a) (t : ℝ)
    (ht : |t| ≤ familyEps a/2) : (familyEnd a t).PosSemidef := by
  have hb := endpoint_bounds a ha t ht
  have hp : 0 < 1-t*(2*a^2/(1+a^2)^2) := by linarith [hb.1]
  have hd : 1+a^2 ≠ 0 := by positivity
  have hg := (perturb_psd a ha (t/(1-t*(2*a^2/(1+a^2)^2))) hb.2).smul
    (show 0 ≤ (1-t*(2*a^2/(1+a^2)^2))/(1+a^2)^2 by positivity)
  have hh : (1-t*(2*a^2/(1+a^2)^2))*(t/(1-t*(2*a^2/(1+a^2)^2))) = t := by
    exact mul_div_cancel₀ t hp.ne'
  have hlin : familyS a + t • (familyH a - (2*a^2/(1+a^2)^2) • familyS a) =
      (1-t*(2*a^2/(1+a^2)^2)) •
        (familyS a + (t/(1-t*(2*a^2/(1+a^2)^2))) • familyH a) := by
    simp only [smul_add, smul_sub, smul_smul, hh, sub_smul, one_smul]
    simp only [sub_eq_add_neg]
    ac_rfl
  convert hg using 1
  rw [familyEnd, hlin, smul_smul]
  congr 1
  ring

private lemma end_wigner (a t : ℝ) (α : ℂ) : wigner (familyEnd a t) α =
    ((2/Real.pi*Real.exp (-2*‖α‖^2)/(1+a^2)^2 *
      ((1-t*(2*a^2/(1+a^2)^2))*familyR a α^2+
       (1+t*(1-2*a^2/(1+a^2)^2))*32*a^2*α.re^2*α.im^2) : ℝ) : ℂ) := by
  rw [familyEnd, wigner_smul, wigner_add, wigner_smul, wigner_sub,
    wigner_smul, familyS_wigner, familyH_wigner]
  push_cast
  ring

private lemma end_mem_WPS (a : ℝ) (ha : 0 < a) (t : ℝ)
    (ht : |t| ≤ familyEps a/2) : familyEnd a t ∈ WPS 4 := by
  refine ⟨end_psd a ha t ht, end_trace a t, ?_⟩
  intro α
  rw [end_wigner, Complex.zero_le_real]
  have hb := endpoint_bounds a ha t ht
  have he := eps_bounds a ha
  have hq := trace_ratio_bounds a
  have ht0 := neg_abs_le t
  have hmul : -(familyEps a/2) ≤ t*(1-2*a^2/(1+a^2)^2) := by
    have hq0 : 0 ≤ 1-2*a^2/(1+a^2)^2 := by linarith
    have hq1 : 1-2*a^2/(1+a^2)^2 ≤ 1 := by linarith
    have h1 := mul_le_mul_of_nonneg_left hq1 (abs_nonneg t)
    have h2 := mul_le_mul_of_nonneg_right ht0 hq0
    nlinarith
  have hp1 : 0 ≤ 1+t*(1-2*a^2/(1+a^2)^2) := by linarith
  have hp0 : 0 ≤ 1-t*(2*a^2/(1+a^2)^2) := by linarith [hb.1]
  positivity

private lemma end_midpoint (a t : ℝ) :
    familyState a = (1/2 : ℝ) • (familyEnd a t + familyEnd a (-t)) := by
  ext i j
  simp [familyState, familyEnd, Matrix.smul_apply]
  ring

private lemma end_ne_state (a : ℝ) (ha : 0 < a) :
    familyEnd a (familyEps a/2) ≠ familyState a := by
  have he := (eps_bounds a ha).1
  have hd : 0 < 1+a^2 := by positivity
  intro h
  have h' := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℂ => (M 4 4).re) h
  have hk : 0 < familyEps a/2 * (2*a^2/(1+a^2)^2) * (3*a^4/8) := by positivity
  have hS : familyS a 4 4 = ((3*a^4/8 : ℝ) : ℂ) := by
    change familyS a ⟨4, by decide⟩ ⟨4, by decide⟩ = _
    simp [familyS, sparse, Matrix.single, Matrix.diagonal]
  have hH : familyH a 4 4 = 0 := by
    change familyH a ⟨4, by decide⟩ ⟨4, by decide⟩ = _
    simp [familyH, sparse, Matrix.single, Matrix.diagonal]
  simp only [familyEnd, familyState, Matrix.smul_apply, Matrix.add_apply,
    Matrix.sub_apply, hS, hH, Complex.smul_re, Complex.add_re, Complex.sub_re,
    Complex.ofReal_re, Complex.zero_re, smul_eq_mul] at h'
  have hc : (familyEps a/2)*(2*a^2/(1+a^2)^2)*(3*a^4/8) = 0 := by
    have hden : 0 < 1/(1+a^2)^2 := by positivity
    nlinarith
  exact hk.ne' hc

private theorem family_not_extreme (a : ℝ) (ha : 0 < a) :
    ¬ IsExtremeWPS 4 (bsState (psi_a a) (phi_a a)) := by
  rw [bsState_family]
  intro h
  have he := (eps_bounds a ha).1
  have hx := end_mem_WPS a ha (familyEps a/2) (by rw [abs_of_pos (by positivity)])
  have hy := end_mem_WPS a ha (-(familyEps a/2)) (by rw [abs_neg, abs_of_pos (by positivity)])
  have hm := end_midpoint a (familyEps a/2)
  exact end_ne_state a ha (h.2 _ hx _ hy hm).1

theorem result : ¬ claim := by
  intro h
  exact family_not_extreme (1/2) (by norm_num)
    (h 2 (psi_a (1/2)) (phi_a (1/2)) (psi_a_norm _) (phi_a_norm _))

#print axioms result
#print axioms family_not_extreme
#check wignerFockUpper
#check sparse
#check psi_a
#check phi_a
#check familyS
#check familyH
#check familyEps
#check familyState
#check familyEnd
#check familyR
#check outputCoeff
#check familyOutput

end D5.S3.Quantum.QuantumChannels.FockAttenuator.FiniteFockBeamSplitterNonExtremality
