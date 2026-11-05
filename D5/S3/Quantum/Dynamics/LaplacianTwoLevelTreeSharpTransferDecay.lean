/- GID: D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: none
   digest: Non-attained Pell phase supremum, unit tail constant, and 3/2 decay sharpness. -/

/-
admission_basis: escape-witness
Escape witnesses surviving the bypass test:
1. sharp_transfer_supremum_and_pell_approx:
   (a) Three-term complex phase-gap identity
       (c + A₀ + B₀)^2 - ‖c - A₀ e^{i a t} + B₀ e^{i b t}‖^2
         = 2 c A₀ (1 + cos(a t)) + 2 c B₀ (1 - cos(b t)) + 2 A₀ B₀ (1 + cos((a - b) t)) >= 0
       combined with the integer parity obstruction
       (4*v - 6*u - 3)^2 - 5*(2*u + 1)^2
         = 4*(2*(2*v^2 - 6*u*v - 3*v + 2*u^2 + 2*u) + 1) != 0,
       proving strict finite-time non-attainment n^(3/2) P_{k, l}(t) < C_* for all k >= 2, l >= 1.
   (b) Pell recurrence (p_{j+1}, m_{j+1}) = (9 p_j + 20 m_j, 4 p_j + 9 m_j) yielding
       p_j - sqrt(5) m_j = (2 - sqrt(5))*(9 - 4*sqrt(5))^j -> 0, Odd (3*m_j - p_j), and
       5^(3/2) P_{2, 1}(approxTime j) = (C_*/2)*(1 + cos(pi*delta_j)) -> C_*.
2. sharp_asymptotic_tail_decay:
   (a) Even-s family s = 2*(m + 1), l_s = s*(s + 1), k_s = l_s + 1 at t = pi satisfying
       cos(a_s*pi) = -1, cos(b_s*pi) = 1, and n_s^(3/2) P_{k_s, l_s}(pi) = envelopeH (2*s + 1) > 1.
   (b) Threshold discriminant lower bound tailThresholdD N <= specD k l via
       ((k - l)^2 + 4*l) - (2*(k + l + 1) - 3) = (k - l - 1)^2 >= 0, combined with
       envelopeG d^2 <= 128/d <= 1 < envelopeH d^2 <= 1 + 175/d for d >= 128, establishing
       tailBoundingSup -> 1, tailTransferSup -> 1, and failure of O(n^(-beta)) for all beta > 3/2.
Direct dependencies:
  D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound (treeOrder, leafTransferProb,
  leafBoundingEntry, specS, specD, specA, specB, optimalTransferConst, upperFeasibleA, envelopeG,
  envelopeH, twoLevelTree_leaf_dynamics_and_invariance, spectral_envelope_and_antitonicity,
  sharp_global_spectral_transfer_bound)
  D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees (lapPropagator, boundingEntry;
  sha256:eaa12760074ad3f2e25fbb0d69c7cc50dd9a77cb4cda1a9fa1cf193e798d8975)
Utility: none; universal Diophantine non-attainment, Pell limits, and asymptotic tail bounds.
proof_shape: three_phase_gap: bind-only;
  consumer: even_witness_at_pi, pell_props_and_eval, strict_nonattainment.
proof_shape: strict_nonattainment: bind-only;
  consumer: sharp_transfer_supremum_and_pell_approx.
proof_shape: pell_props_and_eval: bind-only;
  consumer: sharp_transfer_supremum_and_pell_approx.
proof_shape: even_witness_at_pi: bind-only; consumer: sharp_asymptotic_tail_decay.
proof_shape: envelope_large_bound: bind-only; consumer: sharp_asymptotic_tail_decay.
proof_shape: sharp_transfer_supremum_and_pell_approx: content;
  consumer: D5/B/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.
proof_shape: sharp_asymptotic_tail_decay: content;
  consumer: D5/B/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.
proof_shape: scaledTransferSet: not-applicable;
  consumer: sharp_transfer_supremum_and_pell_approx.
proof_shape: scaledTransferSet21: not-applicable;
  consumer: sharp_transfer_supremum_and_pell_approx.
proof_shape: pellPair: not-applicable; consumer: pellM, pellP, pell_props_and_eval.
proof_shape: pellP: not-applicable; consumer: pell_props_and_eval.
proof_shape: pellM: not-applicable;
  consumer: approxTime, pell_props_and_eval, sharp_transfer_supremum_and_pell_approx.
proof_shape: bStar: not-applicable;
  consumer: approxTime, pell_props_and_eval, sharp_transfer_supremum_and_pell_approx.
proof_shape: approxTime: not-applicable;
  consumer: pell_props_and_eval, sharp_transfer_supremum_and_pell_approx.
proof_shape: tailBoundingSet: not-applicable;
  consumer: sharp_asymptotic_tail_decay, tailBoundingSup.
proof_shape: tailTransferSet: not-applicable;
  consumer: sharp_asymptotic_tail_decay, tailTransferSup.
proof_shape: tailBoundingSup: not-applicable; consumer: sharp_asymptotic_tail_decay.
proof_shape: tailTransferSup: not-applicable; consumer: sharp_asymptotic_tail_decay.
proof_shape: tailThresholdD: not-applicable; consumer: sharp_asymptotic_tail_decay.
Escape registration:
  Reg/D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.lean (DTR-Declared).
-/

import D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSpectralBound

/-! # Sharp Root-to-Leaf Laplacian Transfer Supremum and Asymptotic Tail Decay -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSpectralBound
noncomputable section
namespace D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSharpTransferDecay

/-- Set of all scaled root-to-leaf transfer probabilities `n^(3/2) P_{k, l}(t)` for `k ≥ 2`,
`l ≥ 1`. -/
def scaledTransferSet : Set ℝ :=
  { y | ∃ (k l : ℕ), 2 ≤ k ∧ 1 ≤ l ∧
    ∃ (i : Fin k) (j : Fin l) (t : ℝ),
      y = ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * leafTransferProb k l i j t }

/-- Set of scaled root-to-leaf transfer probabilities `5^(3/2) P_{2, 1}(t)` on `T(2, 1)`. -/
def scaledTransferSet21 (i : Fin 2) (j : Fin 1) : Set ℝ :=
  { y | ∃ t : ℝ, y = ((5 : ℝ) ^ ((3 : ℝ) / 2)) * leafTransferProb 2 1 i j t }

/-- Pell-type integer sequence `(p_j, m_j)` approximating `(sqrt 5, 1)` by `(9 + 4 sqrt 5)^j`. -/
def pellPair : ℕ → ℕ × ℕ
  | 0 => (2, 1)
  | j + 1 => (9 * (pellPair j).1 + 20 * (pellPair j).2, 4 * (pellPair j).1 + 9 * (pellPair j).2)

/-- Numerator sequence `p_j = (pellPair j).1` in the Pell phase approximation. -/
def pellP (j : ℕ) : ℕ := (pellPair j).1

/-- Denominator sequence `m_j = (pellPair j).2` in the Pell phase approximation. -/
def pellM (j : ℕ) : ℕ := (pellPair j).2

/-- Upper positive root-supported Laplacian eigenvalue `b_* = (5 + sqrt 5) / 2` on `T(2, 1)`. -/
noncomputable def bStar : ℝ := (5 + Real.sqrt 5) / 2

/-- Explicit Pell phase-alignment times `t_j = 2 pi m_j / b_*` on `T(2, 1)`. -/
noncomputable def approxTime (j : ℕ) : ℝ := 2 * Real.pi * (pellM j : ℝ) / bStar

/-- Tail set of scaled spectral bounds `n^(3/2) B_{k, l}^2` over trees with `n ≥ N`. -/
def tailBoundingSet (N : ℝ) : Set ℝ :=
  { y | ∃ (k l : ℕ), 2 ≤ k ∧ 1 ≤ l ∧ N ≤ (treeOrder k l : ℝ) ∧
    ∃ (i : Fin k) (j : Fin l),
      y = ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * (leafBoundingEntry k l i j) ^ 2 }

/-- Tail set of scaled transfer probabilities `n^(3/2) P_{k, l}(t)` over trees with `n ≥ N`. -/
def tailTransferSet (N : ℝ) : Set ℝ :=
  { y | ∃ (k l : ℕ), 2 ≤ k ∧ 1 ≤ l ∧ N ≤ (treeOrder k l : ℝ) ∧
    ∃ (i : Fin k) (j : Fin l) (t : ℝ),
      y = ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * leafTransferProb k l i j t }

/-- Tail supremum `M_B(N) = sSup (tailBoundingSet N)` of scaled spectral bounds. -/
noncomputable def tailBoundingSup (N : ℝ) : ℝ := sSup (tailBoundingSet N)

/-- Tail supremum `M_P(N) = sSup (tailTransferSet N)` of scaled transfer probabilities. -/
noncomputable def tailTransferSup (N : ℝ) : ℝ := sSup (tailTransferSet N)

/-- Threshold discriminant `D_N = max(sqrt 5, sqrt(4 sqrt(N - 1) - 3))` for `n ≥ N`. -/
noncomputable def tailThresholdD (N : ℝ) : ℝ :=
  max (Real.sqrt 5) (Real.sqrt (4 * Real.sqrt (N - 1) - 3))

private lemma three_phase_gap (c A₀ B₀ a b t : ℝ) :
    (c + A₀ + B₀) ^ 2 -
      ‖(c : ℂ) - (A₀ : ℂ) * Complex.exp (Complex.I * (a : ℂ) * (t : ℂ)) +
        (B₀ : ℂ) * Complex.exp (Complex.I * (b : ℂ) * (t : ℂ))‖ ^ 2 =
      2 * c * A₀ * (1 + Real.cos (a * t)) + 2 * c * B₀ * (1 - Real.cos (b * t)) +
        2 * A₀ * B₀ * (1 + Real.cos ((a - b) * t)) := by
  have heuler : ∀ x : ℝ, Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) =
      (Real.cos (x * t) : ℂ) + (Real.sin (x * t) : ℂ) * Complex.I := fun x => by
    rw [show Complex.I * (x : ℂ) * (t : ℂ) = ((x * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [heuler a, heuler b, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.add_im, Complex.sub_im, Complex.mul_im,
    mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add]
  have hca := Real.cos_sq_add_sin_sq (a * t)
  have hcb := Real.cos_sq_add_sin_sq (b * t)
  have hcab : Real.cos ((a - b) * t) =
      Real.cos (a * t) * Real.cos (b * t) + Real.sin (a * t) * Real.sin (b * t) := by
    rw [sub_mul, Real.cos_sub]
  linear_combination -A₀ ^ 2 * hca - B₀ ^ 2 * hcb - 2 * A₀ * B₀ * hcab

private lemma strict_nonattainment (k l : ℕ) (hk : 2 ≤ k) (hl : 1 ≤ l)
    (i : Fin k) (j : Fin l) (t : ℝ) :
    ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * leafTransferProb k l i j t < optimalTransferConst := by
  have hglob := sharp_global_spectral_transfer_bound k l hk hl i j t
  have hn_pos : 0 < (treeOrder k l : ℝ) := by unfold treeOrder; positivity
  have hrpow_pos : 0 < (treeOrder k l : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hn_pos _
  have hle_b : ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * leafTransferProb k l i j t ≤
      ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * (leafBoundingEntry k l i j) ^ 2 :=
    mul_le_mul_of_nonneg_left hglob.2.2.2.2.2.1 hrpow_pos.le
  have hB_le_C : ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * (leafBoundingEntry k l i j) ^ 2 ≤
      optimalTransferConst := by
    have hm := mul_le_mul_of_nonneg_left hglob.2.2.2.2.2.2.1 hrpow_pos.le
    have hr : ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) *
        ((treeOrder k l : ℝ) ^ (-(3 : ℝ) / 2)) = 1 := by
      rw [← Real.rpow_add hn_pos]; norm_num
    calc ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * (leafBoundingEntry k l i j) ^ 2
        ≤ ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) *
            (optimalTransferConst * ((treeOrder k l : ℝ) ^ (-(3 : ℝ) / 2))) := hm
      _ = optimalTransferConst *
            (((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) *
              ((treeOrder k l : ℝ) ^ (-(3 : ℝ) / 2))) := by ring
      _ = optimalTransferConst := by rw [hr, mul_one]
  by_cases h21 : k = 2 ∧ l = 1
  · rcases h21 with ⟨rfl, rfl⟩
    have hBeq := hglob.2.2.2.2.2.2.2.mpr ⟨rfl, rfl⟩
    rw [← hBeq]; refine mul_lt_mul_of_pos_left (lt_of_le_of_ne hglob.2.2.2.2.2.1 ?_) hrpow_pos
    intro heq
    have hdyn := twoLevelTree_leaf_dynamics_and_invariance 2 1 hk hl i i j j t
    set q := Real.sqrt 5
    have hq_pos : 0 < q := Real.sqrt_pos.mpr (by norm_num)
    have hq_sq : q ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hd21 : specD 2 1 = q := by unfold specD; congr 1; norm_num
    have ha_eq : specA 2 1 = (5 - q) / 2 := by unfold specA specS; rw [hd21]; ring
    have hb_eq : specB 2 1 = (5 + q) / 2 := by unfold specB specS; rw [hd21]; ring
    have ha_pos : 0 < specA 2 1 := lt_trans zero_lt_one hglob.2.1
    have hb_pos : 0 < specB 2 1 := by rw [hb_eq]; positivity
    set c : ℝ := 1 / (treeOrder 2 1 : ℝ)
    set A₀ : ℝ := 1 / (specA 2 1 * specD 2 1)
    set B₀ : ℝ := 1 / (specB 2 1 * specD 2 1)
    have hc_pos : 0 < c := by dsimp [c]; unfold treeOrder; positivity
    have hA_pos : 0 < A₀ := by dsimp [A₀]; rw [hd21]; positivity
    have hB_pos : 0 < B₀ := by dsimp [B₀]; rw [hd21]; positivity
    have hsum : c + A₀ + B₀ = leafBoundingEntry 2 1 i j := by
      rw [hdyn.2.2.2.2.2.1]; dsimp [c, A₀, B₀]
      have hn5 : (treeOrder 2 1 : ℝ) = 5 := by unfold treeOrder; norm_num
      have hab5 : specA 2 1 * specB 2 1 = 5 := by
        rw [ha_eq, hb_eq]; linear_combination -hq_sq / 4
      have hsub_q : specB 2 1 - specA 2 1 = specD 2 1 := by rw [ha_eq, hb_eq, hd21]; ring
      have ha0 : specA 2 1 ≠ 0 := ha_pos.ne'; have hb0 : specB 2 1 ≠ 0 := hb_pos.ne'
      have hba : specB 2 1 - specA 2 1 ≠ 0 := by rw [hsub_q, hd21]; exact hq_pos.ne'
      rw [hn5, ← hab5, ← hsub_q]; field_simp; ring
    have hprob_eq : leafTransferProb 2 1 i j t =
        ‖(c : ℂ) - (A₀ : ℂ) * Complex.exp (Complex.I * (specA 2 1 : ℂ) * (t : ℂ)) +
          (B₀ : ℂ) * Complex.exp (Complex.I * (specB 2 1 : ℂ) * (t : ℂ))‖ ^ 2 := by
      unfold leafTransferProb; rw [hdyn.2.2.2.2.1]; dsimp [c, A₀, B₀]; push_cast; ring_nf
    have hgap := three_phase_gap c A₀ B₀ (specA 2 1) (specB 2 1) t
    rw [hsum, ← hprob_eq, heq, sub_self] at hgap
    have h1 : 0 ≤ 2 * c * A₀ * (1 + Real.cos (specA 2 1 * t)) :=
      mul_nonneg (by positivity) (by linarith [Real.neg_one_le_cos (specA 2 1 * t)])
    have h2 : 0 ≤ 2 * c * B₀ * (1 - Real.cos (specB 2 1 * t)) :=
      mul_nonneg (by positivity) (by linarith [Real.cos_le_one (specB 2 1 * t)])
    have h3 : 0 ≤ 2 * A₀ * B₀ * (1 + Real.cos ((specA 2 1 - specB 2 1) * t)) :=
      mul_nonneg (by positivity) (by linarith [Real.neg_one_le_cos ((specA 2 1 - specB 2 1) * t)])
    have hca : Real.cos (specA 2 1 * t) = -1 := by
      have hz : 2 * c * A₀ * (1 + Real.cos (specA 2 1 * t)) = 0 := by linarith
      linarith [(mul_eq_zero.mp hz).resolve_left (by positivity : 2 * c * A₀ ≠ 0)]
    have hcb : Real.cos (specB 2 1 * t) = 1 := by
      have hz : 2 * c * B₀ * (1 - Real.cos (specB 2 1 * t)) = 0 := by linarith
      linarith [(mul_eq_zero.mp hz).resolve_left (by positivity : 2 * c * B₀ ≠ 0)]
    obtain ⟨u, hu⟩ := Real.cos_eq_neg_one_iff.mp hca
    obtain ⟨v, hv⟩ := (Real.cos_eq_one_iff _).mp hcb
    have hmul_pi : (Real.pi + (u : ℝ) * (2 * Real.pi)) * specB 2 1 =
        ((v : ℝ) * (2 * Real.pi)) * specA 2 1 := by rw [hu, hv]; ring
    have hrel : (1 + 2 * (u : ℝ)) * ((5 + q) / 2) = 2 * (v : ℝ) * ((5 - q) / 2) := by
      rw [ha_eq, hb_eq] at hmul_pi
      exact mul_left_cancel₀ Real.pi_ne_zero (by linear_combination hmul_pi)
    have hqu : (2 * (u : ℝ) + 1) * q = 4 * (v : ℝ) - 6 * (u : ℝ) - 3 := by
      linear_combination ((5 + q) / 5) * hrel - ((1 + 2 * (u : ℝ) + 2 * (v : ℝ)) / 10) * hq_sq
    have hsqR : (4 * (v : ℝ) - 6 * (u : ℝ) - 3) ^ 2 = 5 * (2 * (u : ℝ) + 1) ^ 2 := by
      rw [← hqu]; linear_combination (2 * (u : ℝ) + 1) ^ 2 * hq_sq
    have hsqZ : (4 * v - 6 * u - 3) ^ 2 = 5 * (2 * u + 1) ^ 2 := by exact_mod_cast hsqR
    have hpar : (4 * v - 6 * u - 3) ^ 2 - 5 * (2 * u + 1) ^ 2 =
        4 * (2 * (2 * v ^ 2 - 6 * u * v - 3 * v + 2 * u ^ 2 + 2 * u) + 1) := by ring
    omega
  · exact lt_of_le_of_lt hle_b (lt_of_le_of_ne hB_le_C (mt hglob.2.2.2.2.2.2.2.mp h21))

private lemma pell_props_and_eval (j : ℕ) (i₀ : Fin 2) (j₀ : Fin 1) :
    1 ≤ pellM j ∧ pellM j < pellM (j + 1) ∧ 9 ^ j ≤ pellM j ∧
      (∃ k : ℤ, 3 * (pellM j : ℤ) - (pellP j : ℤ) = 2 * k + 1) ∧
      (pellP j : ℝ) - Real.sqrt 5 * (pellM j : ℝ) =
        (2 - Real.sqrt 5) * (9 - 4 * Real.sqrt 5) ^ j ∧
      ((5 : ℝ) ^ ((3 : ℝ) / 2)) * leafTransferProb 2 1 i₀ j₀ (approxTime j) =
        (optimalTransferConst / 2) *
          (1 + Real.cos (Real.pi * ((2 - Real.sqrt 5) * (9 - 4 * Real.sqrt 5) ^ j))) := by
  have hq_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hq_sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hind : ∀ n : ℕ, 1 ≤ pellM n ∧ pellM n < pellM (n + 1) ∧ 9 ^ n ≤ pellM n ∧
      (∃ k : ℤ, 3 * (pellM n : ℤ) - (pellP n : ℤ) = 2 * k + 1) ∧
      (pellP n : ℝ) - Real.sqrt 5 * (pellM n : ℝ) =
        (2 - Real.sqrt 5) * (9 - 4 * Real.sqrt 5) ^ n := by
    intro n; induction n with
    | zero =>
      refine ⟨by decide, by decide, by decide, ⟨0, by decide⟩, ?_⟩
      simp [pellP, pellM, pellPair]
    | succ n ih =>
      obtain ⟨hm1, _, h9, ⟨k, hk⟩, hdel⟩ := ih
      have hp_step : pellP (n + 1) = 9 * pellP n + 20 * pellM n := rfl
      have hm_step : pellM (n + 1) = 4 * pellP n + 9 * pellM n := rfl
      have hm_step2 : pellM (n + 2) = 4 * pellP (n + 1) + 9 * pellM (n + 1) := rfl
      refine ⟨by rw [hm_step]; omega, by rw [hm_step2, hm_step]; omega, ?_,
        ⟨k + 2 * (pellP n : ℤ) + 2 * (pellM n : ℤ), ?_⟩, ?_⟩
      · calc 9 ^ (n + 1) = 9 * 9 ^ n := by ring
          _ ≤ 9 * pellM n := Nat.mul_le_mul_left 9 h9
          _ ≤ 4 * pellP n + 9 * pellM n := by omega
      · rw [hp_step, hm_step]; push_cast; linarith
      · rw [hp_step, hm_step]; push_cast
        calc 9 * (pellP n : ℝ) + 20 * (pellM n : ℝ) -
              Real.sqrt 5 * (4 * (pellP n : ℝ) + 9 * (pellM n : ℝ))
            = (9 - 4 * Real.sqrt 5) * ((pellP n : ℝ) - Real.sqrt 5 * (pellM n : ℝ)) := by
              linear_combination -4 * (pellM n : ℝ) * hq_sq
          _ = (2 - Real.sqrt 5) * (9 - 4 * Real.sqrt 5) ^ (n + 1) := by rw [hdel]; ring
  obtain ⟨hm1, hmlt, h9, ⟨k, hk⟩, hdel⟩ := hind j
  refine ⟨hm1, hmlt, h9, ⟨k, hk⟩, hdel, ?_⟩
  have hk2 : 2 ≤ (2 : ℕ) := le_rfl; have hl1 : 1 ≤ (1 : ℕ) := le_rfl
  have hdyn := twoLevelTree_leaf_dynamics_and_invariance 2 1 hk2 hl1 i₀ i₀ j₀ j₀ (approxTime j)
  have hglob := sharp_global_spectral_transfer_bound 2 1 hk2 hl1 i₀ j₀ (approxTime j)
  have hn5 : (treeOrder 2 1 : ℝ) = 5 := by unfold treeOrder; norm_num
  have hd21 : specD 2 1 = Real.sqrt 5 := by unfold specD; congr 1; norm_num
  have ha_eq : specA 2 1 = (5 - Real.sqrt 5) / 2 := by unfold specA specS; rw [hd21]; ring
  have hb_eq : specB 2 1 = bStar := by unfold specB specS bStar; rw [hd21]; ring
  have hb_pos : 0 < bStar := by unfold bStar; positivity
  have ha_pos : 0 < specA 2 1 := lt_trans zero_lt_one hglob.2.1
  set c : ℝ := 1 / (treeOrder 2 1 : ℝ)
  set A₀ : ℝ := 1 / (specA 2 1 * specD 2 1)
  set B₀ : ℝ := 1 / (specB 2 1 * specD 2 1)
  have hab5 : specA 2 1 * specB 2 1 = 5 := by
    rw [ha_eq, hb_eq]; unfold bStar; linear_combination -hq_sq / 4
  have hcB_eq : c + B₀ = A₀ := by
    dsimp [c, A₀, B₀]; rw [hn5, ← hab5, hd21]
    have hsub : specB 2 1 - specA 2 1 = Real.sqrt 5 := by
      rw [ha_eq, hb_eq]; unfold bStar; ring
    have : specA 2 1 ≠ 0 := ha_pos.ne'; have : specB 2 1 ≠ 0 := by rw [hb_eq]; exact hb_pos.ne'
    have : specB 2 1 - specA 2 1 ≠ 0 := by rw [hsub]; exact hq_pos.ne'
    rw [← hsub]; field_simp; ring
  have hBnd_eq : leafBoundingEntry 2 1 i₀ j₀ = 2 * A₀ := by
    rw [hdyn.2.2.2.2.2.1]; dsimp [A₀]; ring
  have hsum : c + A₀ + B₀ = 2 * A₀ := by linarith
  have hprob_eq : leafTransferProb 2 1 i₀ j₀ (approxTime j) =
      ‖(c : ℂ) - (A₀ : ℂ) * Complex.exp (Complex.I * (specA 2 1 : ℂ) * (approxTime j : ℂ)) +
        (B₀ : ℂ) * Complex.exp (Complex.I * (specB 2 1 : ℂ) * (approxTime j : ℂ))‖ ^ 2 := by
    unfold leafTransferProb; rw [hdyn.2.2.2.2.1]; dsimp [c, A₀, B₀]; push_cast; ring_nf
  have hgap := three_phase_gap c A₀ B₀ (specA 2 1) (specB 2 1) (approxTime j)
  rw [hsum, ← hprob_eq] at hgap
  have hcos_int : ∀ (x : ℝ) (z : ℤ), Real.cos (x + (z : ℝ) * (2 * Real.pi)) = Real.cos x := by
    intro x z
    have hcz : Real.cos ((z : ℝ) * (2 * Real.pi)) = 1 := (Real.cos_eq_one_iff _).mpr ⟨z, rfl⟩
    have hsz : Real.sin ((z : ℝ) * (2 * Real.pi)) = 0 :=
      sq_eq_zero_iff.mp (by
        have hcs := Real.cos_sq_add_sin_sq ((z : ℝ) * (2 * Real.pi))
        rw [hcz] at hcs; linarith)
    rw [Real.cos_add, hcz, hsz]; ring
  have hbt : specB 2 1 * approxTime j = 0 + ((pellM j : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hb_eq]; unfold approxTime
    have : bStar ≠ 0 := hb_pos.ne'; push_cast; field_simp; ring
  have hcos_b : Real.cos (specB 2 1 * approxTime j) = 1 := by
    rw [hbt, hcos_int, Real.cos_zero]
  set δ : ℝ := (2 - Real.sqrt 5) * (9 - 4 * Real.sqrt 5) ^ j
  have hat : specA 2 1 * approxTime j =
      (Real.pi * δ + Real.pi) + (k : ℝ) * (2 * Real.pi) := by
    have hratio : specA 2 1 = ((3 - Real.sqrt 5) / 2) * bStar := by
      rw [ha_eq]; unfold bStar; linear_combination hq_sq / 4
    have hkR : 3 * (pellM j : ℝ) - (pellP j : ℝ) = 2 * (k : ℝ) + 1 := by exact_mod_cast hk
    unfold approxTime; rw [hratio]
    have : bStar ≠ 0 := hb_pos.ne'
    have hcancel : (3 - Real.sqrt 5) / 2 * bStar * (2 * Real.pi * (pellM j : ℝ) / bStar) =
        Real.pi * (3 * (pellM j : ℝ) - Real.sqrt 5 * (pellM j : ℝ)) := by field_simp
    have hdel' : (pellP j : ℝ) - Real.sqrt 5 * (pellM j : ℝ) = δ := hdel
    rw [hcancel]; linear_combination Real.pi * hkR + Real.pi * hdel'
  have hcos_a : Real.cos (specA 2 1 * approxTime j) = -Real.cos (Real.pi * δ) := by
    rw [hat, hcos_int, Real.cos_add, Real.cos_pi, Real.sin_pi]; ring
  have hcos_ab : Real.cos ((specA 2 1 - specB 2 1) * approxTime j) = -Real.cos (Real.pi * δ) := by
    have hab_t : (specA 2 1 - specB 2 1) * approxTime j =
        (Real.pi * δ + Real.pi) + ((k - (pellM j : ℤ) : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [sub_mul, hat, hbt]; push_cast; ring
    rw [hab_t, hcos_int, Real.cos_add, Real.cos_pi, Real.sin_pi]; ring
  rw [hcos_b, hcos_a, hcos_ab] at hgap
  have hP_eval : leafTransferProb 2 1 i₀ j₀ (approxTime j) =
      ((leafBoundingEntry 2 1 i₀ j₀) ^ 2 / 2) * (1 + Real.cos (Real.pi * δ)) := by
    rw [hBnd_eq]; linear_combination -hgap - 2 * A₀ * (1 - Real.cos (Real.pi * δ)) * hcB_eq
  have hBeq := hglob.2.2.2.2.2.2.2.mpr ⟨rfl, rfl⟩
  rw [hn5] at hBeq; rw [hP_eval]
  linear_combination ((1 + Real.cos (Real.pi * δ)) / 2) * hBeq

/-- Non-attained global supremum `C_*` on `T(2, 1)` and explicit Pell phase convergence. -/
theorem sharp_transfer_supremum_and_pell_approx (m : ℕ) :
    approxTime m < approxTime (m + 1) ∧
      scaledTransferSet.Nonempty ∧ BddAbove scaledTransferSet ∧
      IsLUB scaledTransferSet optimalTransferConst ∧
      sSup scaledTransferSet = optimalTransferConst ∧
      (∀ (i₀ : Fin 2) (j₀ : Fin 1),
        (scaledTransferSet21 i₀ j₀).Nonempty ∧ BddAbove (scaledTransferSet21 i₀ j₀) ∧
          IsLUB (scaledTransferSet21 i₀ j₀) optimalTransferConst ∧
          sSup scaledTransferSet = sSup (scaledTransferSet21 i₀ j₀) ∧
          sSup (scaledTransferSet21 i₀ j₀) = optimalTransferConst) ∧
      (∀ (k l : ℕ), 2 ≤ k → 1 ≤ l → ∀ (i : Fin k) (j : Fin l) (t : ℝ),
        ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * leafTransferProb k l i j t <
          optimalTransferConst) ∧
      Filter.Tendsto approxTime Filter.atTop Filter.atTop ∧
      (∀ (i₀ : Fin 2) (j₀ : Fin 1),
        Filter.Tendsto
          (fun j : ℕ => ((5 : ℝ) ^ ((3 : ℝ) / 2)) * leafTransferProb 2 1 i₀ j₀ (approxTime j))
          Filter.atTop (nhds optimalTransferConst)) := by
  have hb_pos : 0 < bStar := by
    unfold bStar; have : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num); positivity
  have hpi_pos : 0 < 2 * Real.pi := by positivity [Real.pi_pos]
  have htime_lt : approxTime m < approxTime (m + 1) := by
    unfold approxTime
    have hmlt : (pellM m : ℝ) < (pellM (m + 1) : ℝ) := by
      exact_mod_cast (pell_props_and_eval m 0 0).2.1
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hmlt hpi_pos) hb_pos
  have htime_top : Filter.Tendsto approxTime Filter.atTop Filter.atTop := by
    have h9 : Filter.Tendsto (fun j : ℕ => (2 * Real.pi / bStar) * (9 : ℝ) ^ j)
        Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop (div_pos hpi_pos hb_pos)
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 9))
    refine Filter.tendsto_atTop_mono (fun j => ?_) h9
    unfold approxTime
    have hj : (9 : ℝ) ^ j ≤ (pellM j : ℝ) := by exact_mod_cast (pell_props_and_eval j 0 0).2.2.1
    calc (2 * Real.pi / bStar) * (9 : ℝ) ^ j
        ≤ (2 * Real.pi / bStar) * (pellM j : ℝ) :=
          mul_le_mul_of_nonneg_left hj (div_nonneg hpi_pos.le hb_pos.le)
      _ = 2 * Real.pi * (pellM j : ℝ) / bStar := by ring
  have htend21 : ∀ (i₀ : Fin 2) (j₀ : Fin 1),
      Filter.Tendsto
        (fun j : ℕ => ((5 : ℝ) ^ ((3 : ℝ) / 2)) * leafTransferProb 2 1 i₀ j₀ (approxTime j))
        Filter.atTop (nhds optimalTransferConst) := fun i₀ j₀ => by
    have hq_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
    have hq_sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hr0 : 0 ≤ 9 - 4 * Real.sqrt 5 := by
      have : 4 * Real.sqrt 5 ≤ 9 :=
        (sq_le_sq₀ (by positivity) (by norm_num)).mp (by rw [mul_pow, hq_sq]; norm_num)
      linarith
    have hr1 : 9 - 4 * Real.sqrt 5 < 1 := by
      have : 8 < 4 * Real.sqrt 5 :=
        (sq_lt_sq₀ (by norm_num) (by positivity)).mp (by rw [mul_pow, hq_sq]; norm_num)
      linarith
    have hpow0 : Filter.Tendsto (fun j : ℕ => (9 - 4 * Real.sqrt 5) ^ j)
        Filter.atTop (nhds (0 : ℝ)) := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have harg0 : Filter.Tendsto
        (fun j : ℕ => Real.pi * ((2 - Real.sqrt 5) * (9 - 4 * Real.sqrt 5) ^ j))
        Filter.atTop (nhds (0 : ℝ)) := by
      simpa only [mul_assoc, mul_zero] using hpow0.const_mul (Real.pi * (2 - Real.sqrt 5))
    have hcos1 : Filter.Tendsto
        (fun j : ℕ => (optimalTransferConst / 2) *
          (1 + Real.cos (Real.pi * ((2 - Real.sqrt 5) * (9 - 4 * Real.sqrt 5) ^ j))))
        Filter.atTop (nhds optimalTransferConst) := by
      have hc := ((Real.continuous_cos.tendsto 0).comp harg0).const_add 1
      have hm := hc.const_mul (optimalTransferConst / 2)
      simpa only [Function.comp_def, Real.cos_zero,
        show (optimalTransferConst / 2) * (1 + 1) = optimalTransferConst by ring] using hm
    refine hcos1.congr' (Filter.Eventually.of_forall fun j => ?_)
    exact ((pell_props_and_eval j i₀ j₀).2.2.2.2.2).symm
  have hub_all : optimalTransferConst ∈ upperBounds scaledTransferSet := by
    rintro y ⟨k, l, hk, hl, i, j, t, rfl⟩
    exact (strict_nonattainment k l hk hl i j t).le
  have hsub21 : ∀ (i₀ : Fin 2) (j₀ : Fin 1), scaledTransferSet21 i₀ j₀ ⊆ scaledTransferSet := by
    rintro i₀ j₀ y ⟨t, hy⟩
    refine ⟨2, 1, le_rfl, le_rfl, i₀, j₀, t, ?_⟩
    have hn5 : (treeOrder 2 1 : ℝ) = 5 := by unfold treeOrder; norm_num
    rw [hn5, hy]
  have hlub21 : ∀ (i₀ : Fin 2) (j₀ : Fin 1),
      (scaledTransferSet21 i₀ j₀).Nonempty ∧ BddAbove (scaledTransferSet21 i₀ j₀) ∧
        IsLUB (scaledTransferSet21 i₀ j₀) optimalTransferConst := fun i₀ j₀ => by
    have hne : (scaledTransferSet21 i₀ j₀).Nonempty := ⟨_, 0, rfl⟩
    have hub : optimalTransferConst ∈ upperBounds (scaledTransferSet21 i₀ j₀) :=
      fun y hy => hub_all (hsub21 i₀ j₀ hy)
    refine ⟨hne, ⟨optimalTransferConst, hub⟩, ⟨hub, fun b hb => ?_⟩⟩
    exact le_of_tendsto' (htend21 i₀ j₀) (fun j => hb ⟨approxTime j, rfl⟩)
  have hne_all : scaledTransferSet.Nonempty := (hlub21 0 0).1.mono (hsub21 0 0)
  have hlub_all : IsLUB scaledTransferSet optimalTransferConst :=
    ⟨hub_all, fun b hb => (hlub21 0 0).2.2.2 (fun y hy => hb (hsub21 0 0 hy))⟩
  have hsup_all : sSup scaledTransferSet = optimalTransferConst := hlub_all.csSup_eq hne_all
  refine ⟨htime_lt, hne_all, ⟨optimalTransferConst, hub_all⟩, hlub_all, hsup_all,
    fun i₀ j₀ => ?_, strict_nonattainment, htime_top, htend21⟩
  have h := hlub21 i₀ j₀
  have hs21 : sSup (scaledTransferSet21 i₀ j₀) = optimalTransferConst := h.2.2.csSup_eq h.1
  exact ⟨h.1, h.2.1, h.2.2, by rw [hsup_all, hs21], hs21⟩

private lemma even_witness_at_pi (m : ℕ) :
    let s := 2 * (m + 1)
    let l := s * (s + 1)
    let k := l + 1
    2 ≤ k ∧ 1 ≤ l ∧ (m : ℝ) ≤ (treeOrder k l : ℝ) ∧
      ∃ (i : Fin k) (j : Fin l),
        ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * leafTransferProb k l i j Real.pi =
          envelopeH (2 * (s : ℝ) + 1) ∧
        ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * (leafBoundingEntry k l i j) ^ 2 =
          envelopeH (2 * (s : ℝ) + 1) ∧
        1 < envelopeH (2 * (s : ℝ) + 1) := by
  dsimp only
  set s : ℕ := 2 * (m + 1)
  set l : ℕ := s * (s + 1)
  set k : ℕ := l + 1
  have hs_ge : 2 ≤ s := by dsimp [s]; omega
  have hl_ge : 1 ≤ l := by dsimp [l]; nlinarith
  have hk_ge : 2 ≤ k := by dsimp [k]; omega
  have hm_le : (m : ℝ) ≤ (treeOrder k l : ℝ) := by
    have hml : m ≤ l + 1 := le_trans (by dsimp [s]; omega : m ≤ s)
      (le_trans (Nat.le_mul_of_pos_right s (by omega)) (Nat.le_succ l))
    have : m ≤ treeOrder k l := by
      unfold treeOrder
      exact le_trans hml (le_trans (Nat.le_mul_of_pos_left _ (by omega)) (Nat.le_add_left _ 1))
    exact_mod_cast this
  let i₀ : Fin k := ⟨0, by omega⟩
  let j₀ : Fin l := ⟨0, by omega⟩
  set d : ℝ := 2 * (s : ℝ) + 1
  have hd_pos : 0 < d := by dsimp [d]; positivity
  have hH_gt : 1 < envelopeH d :=
    (spectral_envelope_and_antitonicity d (d + 1) hd_pos (by linarith)).2.2.1
  have hdsq : ((k : ℝ) - (l : ℝ)) ^ 2 + 4 * (l : ℝ) = d ^ 2 := by
    dsimp [k, l, d]; push_cast; ring
  have hD_eq : specD k l = d := by unfold specD; rw [hdsq, Real.sqrt_sq hd_pos.le]
  have hS_eq : specS k l = 2 * (s : ℝ) * ((s : ℝ) + 1) + 3 := by
    unfold specS; dsimp [k, l]; push_cast; ring
  have hA_eq : specA k l = (s : ℝ) ^ 2 + 1 := by
    unfold specA; rw [hS_eq, hD_eq]; dsimp [d]; ring
  have hB_eq : specB k l = ((s : ℝ) + 1) ^ 2 + 1 := by
    unfold specB; rw [hS_eq, hD_eq]; dsimp [d]; ring
  have hdyn := twoLevelTree_leaf_dynamics_and_invariance k l hk_ge hl_ge i₀ i₀ j₀ j₀ Real.pi
  have hglob := sharp_global_spectral_transfer_bound k l hk_ge hl_ge i₀ j₀ Real.pi
  set c : ℝ := 1 / (treeOrder k l : ℝ)
  set A₀ : ℝ := 1 / (specA k l * specD k l)
  set B₀ : ℝ := 1 / (specB k l * specD k l)
  have hsum : c + A₀ + B₀ = leafBoundingEntry k l i₀ j₀ := by
    rw [hdyn.2.2.2.2.2.1]; dsimp [c, A₀, B₀]
    have ha_pos : 0 < specA k l := lt_trans zero_lt_one hglob.2.1
    have hb_pos : 0 < specB k l := by rw [hB_eq]; positivity
    have hsub : specB k l - specA k l = specD k l := by
      unfold specB specA; ring
    have hmul : (treeOrder k l : ℝ) = specA k l * specB k l := by
      rw [hglob.2.2.2.1, ← hsub]; ring
    have : specA k l ≠ 0 := ha_pos.ne'; have : specB k l ≠ 0 := hb_pos.ne'
    have : specB k l - specA k l ≠ 0 := by rw [hsub, hD_eq]; exact hd_pos.ne'
    rw [hmul, ← hsub]; field_simp; ring
  have hprob_eq : leafTransferProb k l i₀ j₀ Real.pi =
      ‖(c : ℂ) - (A₀ : ℂ) * Complex.exp (Complex.I * (specA k l : ℂ) * (Real.pi : ℂ)) +
        (B₀ : ℂ) * Complex.exp (Complex.I * (specB k l : ℂ) * (Real.pi : ℂ))‖ ^ 2 := by
    unfold leafTransferProb; rw [hdyn.2.2.2.2.1]; dsimp [c, A₀, B₀]; push_cast; ring_nf
  have hca : Real.cos (specA k l * Real.pi) = -1 := by
    refine Real.cos_eq_neg_one_iff.mpr ⟨(2 * (m + 1) ^ 2 : ℤ), ?_⟩
    rw [hA_eq]; dsimp [s]; push_cast; ring
  have hcb : Real.cos (specB k l * Real.pi) = 1 := by
    refine (Real.cos_eq_one_iff _).mpr ⟨(2 * (m : ℤ) ^ 2 + 6 * (m : ℤ) + 5 : ℤ), ?_⟩
    rw [hB_eq]; dsimp [s]; push_cast; ring
  have hcab : Real.cos ((specA k l - specB k l) * Real.pi) = -1 := by
    refine Real.cos_eq_neg_one_iff.mpr ⟨(-(s : ℤ) - 1 : ℤ), ?_⟩
    rw [hA_eq, hB_eq]; push_cast; ring
  have hgap := three_phase_gap c A₀ B₀ (specA k l) (specB k l) Real.pi
  rw [hsum, ← hprob_eq, hca, hcb, hcab] at hgap
  have hPB : leafTransferProb k l i₀ j₀ Real.pi = (leafBoundingEntry k l i₀ j₀) ^ 2 := by
    linarith
  have hBH : ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * (leafBoundingEntry k l i₀ j₀) ^ 2 =
      envelopeH d := by
    have hn_eq := hglob.2.2.2.1
    have hn_pos : 0 < (treeOrder k l : ℝ) := by unfold treeOrder; positivity
    have hLn : 0 ≤ ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * (leafBoundingEntry k l i₀ j₀) ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hn_pos.le ((3 : ℝ) / 2)) (sq_nonneg _)
    refine (sq_eq_sq₀ hLn (le_trans zero_le_one hH_gt.le)).mp ?_
    have hrpow_sq : (((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2))) ^ 2 = (treeOrder k l : ℝ) ^ 3 := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hn_pos.le,
        show ((3 : ℝ) / 2) * ((2 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hqm : 0 < d ^ 2 - 2 * d + 5 := by
      linarith [sq_nonneg (d - 1), show d ^ 2 - 2 * d + 5 = (d - 1) ^ 2 + 4 by ring]
    have hqp : 0 < d ^ 2 + 2 * d + 5 := by
      linarith [sq_nonneg (d + 1), show d ^ 2 + 2 * d + 5 = (d + 1) ^ 2 + 4 by ring]
    have hHpow_sq : ((d ^ 2 + 2 * d + 5) ^ ((3 : ℝ) / 2)) ^ 2 = (d ^ 2 + 2 * d + 5) ^ 3 := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hqp.le,
        show ((3 : ℝ) / 2) * ((2 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hH_sq : envelopeH d ^ 2 = (d ^ 2 + 2 * d + 5) ^ 3 / (d ^ 4 * (d ^ 2 - 2 * d + 5)) := by
      unfold envelopeH; rw [div_pow, mul_pow, hHpow_sq, Real.sq_sqrt hqm.le]; ring
    rw [mul_pow, hrpow_sq, hdyn.2.2.2.2.2.1, hn_eq, hA_eq, hD_eq, hH_sq]
    have ha_d : (s : ℝ) ^ 2 + 1 = (d ^ 2 - 2 * d + 5) / 4 := by dsimp [d]; ring
    rw [ha_d]; have : d ≠ 0 := hd_pos.ne'; have : d ^ 2 - 2 * d + 5 ≠ 0 := hqm.ne'
    field_simp; ring
  exact ⟨hk_ge, hl_ge, hm_le, i₀, j₀, by rw [hPB, hBH], hBH, hH_gt⟩

private lemma envelope_large_bound {d : ℝ} (hd : 128 ≤ d) :
    max (envelopeG d) (envelopeH d) = envelopeH d ∧ envelopeH d - 1 ≤ 175 / d := by
  have hd_pos : 0 < d := by linarith
  have henv := spectral_envelope_and_antitonicity d (d + 1) hd_pos (by linarith)
  have hd1 : 1 ≤ d := by linarith
  have hd2 : d ≤ d ^ 2 := by simpa only [pow_one] using pow_le_pow_right₀ hd1 (by decide : 1 ≤ 2)
  have hd3 : d ≤ d ^ 3 := by simpa only [pow_one] using pow_le_pow_right₀ hd1 (by decide : 1 ≤ 3)
  have hd4 : d ≤ d ^ 4 := by simpa only [pow_one] using pow_le_pow_right₀ hd1 (by decide : 1 ≤ 4)
  have hqm1 : 1 ≤ d ^ 2 - 2 * d + 5 := by
    linarith [sq_nonneg (d - 1), show d ^ 2 - 2 * d + 5 = (d - 1) ^ 2 + 4 by ring]
  have hdK : d ≤ d * (d ^ 2 - 2 * d + 5) :=
    by simpa only [mul_one] using mul_le_mul_of_nonneg_left hqm1 hd_pos.le
  have hG_le : envelopeG d ^ 2 ≤ 1 := by
    rw [henv.1]
    have h1 : 1 / d ^ 2 ≤ 1 / d := one_div_le_one_div_of_le hd_pos hd2
    have h2 : 3 / d ^ 2 ≤ 3 / d := div_le_div_of_nonneg_left (by norm_num) hd_pos hd2
    have h3 : 3 / d ^ 3 ≤ 3 / d := div_le_div_of_nonneg_left (by norm_num) hd_pos hd3
    have h4 : 1 / d ^ 4 ≤ 1 / d := one_div_le_one_div_of_le hd_pos hd4
    have hsum : 16 * (1 / d + 3 / d + 3 / d + 1 / d) = 128 / d := by ring
    have h128 : 128 / d ≤ 1 := (div_le_one hd_pos).mpr hd
    linarith
  have hG_nonneg : 0 ≤ envelopeG d := by
    unfold envelopeG
    have : 0 ≤ (d + 1) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (by linarith) ((3 : ℝ) / 2); positivity
  have hG_le1 : envelopeG d ≤ 1 :=
    (sq_le_sq₀ hG_nonneg zero_le_one).mp (by simpa only [one_pow] using hG_le)
  have hH_gt : 1 < envelopeH d := henv.2.2.1
  have hGH : envelopeG d ≤ envelopeH d := hG_le1.trans hH_gt.le
  have hH_sq_le : envelopeH d ^ 2 ≤ 1 + 175 / d := by
    rw [henv.2.1]
    have h38 : 38 / d ^ 2 ≤ 38 / d := div_le_div_of_nonneg_left (by norm_num) hd_pos hd2
    have h40 : 40 / d ^ 3 ≤ 40 / d := div_le_div_of_nonneg_left (by norm_num) hd_pos hd3
    have h25 : 25 / d ^ 4 ≤ 25 / d := div_le_div_of_nonneg_left (by norm_num) hd_pos hd4
    have h64 : 64 / (d * (d ^ 2 - 2 * d + 5)) ≤ 64 / d :=
      div_le_div_of_nonneg_left (by norm_num) hd_pos hdK
    linarith [show 8 / d + 38 / d + 40 / d + 25 / d + 64 / d = 175 / d by ring]
  refine ⟨max_eq_right hGH, ?_⟩
  have hmul_le : (envelopeH d - 1) * 1 ≤ (envelopeH d - 1) * (envelopeH d + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith [show (envelopeH d - 1) * (envelopeH d + 1) = envelopeH d ^ 2 - 1 by ring]

/-- Asymptotic tail constant `1`, uniform `(1 + ε) n^(-3/2)` decay, and `3/2` sharpness. -/
theorem sharp_asymptotic_tail_decay (N : ℝ) (hN : 4 ≤ N) :
    1 ≤ tailTransferSup N ∧ tailTransferSup N ≤ tailBoundingSup N ∧
      tailBoundingSup N ≤ max (envelopeG (tailThresholdD N)) (envelopeH (tailThresholdD N)) ∧
      (∀ M : ℝ,
        (tailBoundingSet M).Nonempty ∧ BddAbove (tailBoundingSet M) ∧
          IsLUB (tailBoundingSet M) (tailBoundingSup M) ∧
          (tailTransferSet M).Nonempty ∧ BddAbove (tailTransferSet M) ∧
          IsLUB (tailTransferSet M) (tailTransferSup M)) ∧
      Filter.Tendsto tailBoundingSup Filter.atTop (nhds (1 : ℝ)) ∧
      Filter.Tendsto tailTransferSup Filter.atTop (nhds (1 : ℝ)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℝ, ∀ (k l : ℕ), 2 ≤ k → 1 ≤ l → N₀ ≤ (treeOrder k l : ℝ) →
        ∀ (i : Fin k) (j : Fin l) (t : ℝ),
          leafTransferProb k l i j t ≤ (leafBoundingEntry k l i j) ^ 2 ∧
            (leafBoundingEntry k l i j) ^ 2 ≤
              (1 + ε) * ((treeOrder k l : ℝ) ^ (-(3 : ℝ) / 2))) ∧
      (∀ β : ℝ, (3 : ℝ) / 2 < β → ¬ ∃ C : ℝ, ∀ (k l : ℕ), 2 ≤ k → 1 ≤ l →
        ∀ (i : Fin k) (j : Fin l) (t : ℝ),
          leafTransferProb k l i j t ≤ C * ((treeOrder k l : ℝ) ^ (-β))) := by
  have hall : ∀ M : ℝ,
      1 ≤ tailTransferSup M ∧ tailTransferSup M ≤ tailBoundingSup M ∧
        (tailBoundingSet M).Nonempty ∧ BddAbove (tailBoundingSet M) ∧
        IsLUB (tailBoundingSet M) (tailBoundingSup M) ∧
        (tailTransferSet M).Nonempty ∧ BddAbove (tailTransferSet M) ∧
        IsLUB (tailTransferSet M) (tailTransferSup M) := fun M => by
    let m := Nat.ceil (max 0 M)
    obtain ⟨hk, hl, hm_le, i₀, j₀, hP, hB, hH_gt⟩ := even_witness_at_pi m
    have hM_le : M ≤ (treeOrder ((2 * (m + 1)) * (2 * (m + 1) + 1) + 1)
        ((2 * (m + 1)) * (2 * (m + 1) + 1)) : ℝ) :=
      (le_max_right 0 M).trans ((Nat.le_ceil _).trans hm_le)
    have hmemP : envelopeH (2 * ((2 * (m + 1) : ℕ) : ℝ) + 1) ∈ tailTransferSet M :=
      ⟨_, _, hk, hl, hM_le, i₀, j₀, Real.pi, hP.symm⟩
    have hmemB : envelopeH (2 * ((2 * (m + 1) : ℕ) : ℝ) + 1) ∈ tailBoundingSet M :=
      ⟨_, _, hk, hl, hM_le, i₀, j₀, hB.symm⟩
    have hubB : optimalTransferConst ∈ upperBounds (tailBoundingSet M) := by
      rintro y ⟨k, l, hk', hl', _, i, j, rfl⟩
      have hg := sharp_global_spectral_transfer_bound k l hk' hl' i j 0
      have hnp : 0 < (treeOrder k l : ℝ) := by unfold treeOrder; positivity
      have hm := mul_le_mul_of_nonneg_left hg.2.2.2.2.2.2.1
        (Real.rpow_nonneg hnp.le ((3 : ℝ) / 2))
      have hr : ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) *
          ((treeOrder k l : ℝ) ^ (-(3 : ℝ) / 2)) = 1 := by
        rw [← Real.rpow_add hnp]; norm_num
      calc ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * (leafBoundingEntry k l i j) ^ 2
          ≤ ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) *
              (optimalTransferConst * ((treeOrder k l : ℝ) ^ (-(3 : ℝ) / 2))) := hm
        _ = optimalTransferConst * (((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) *
              ((treeOrder k l : ℝ) ^ (-(3 : ℝ) / 2))) := by ring
        _ = optimalTransferConst := by rw [hr, mul_one]
    have hubP : optimalTransferConst ∈ upperBounds (tailTransferSet M) := by
      rintro y ⟨k, l, hk', hl', _, i, j, t, rfl⟩
      exact (strict_nonattainment k l hk' hl' i j t).le
    have hbddB : BddAbove (tailBoundingSet M) := ⟨optimalTransferConst, hubB⟩
    have hbddP : BddAbove (tailTransferSet M) := ⟨optimalTransferConst, hubP⟩
    have hneB : (tailBoundingSet M).Nonempty := ⟨_, hmemB⟩
    have hneP : (tailTransferSet M).Nonempty := ⟨_, hmemP⟩
    have h1_le : 1 ≤ tailTransferSup M := hH_gt.le.trans (le_csSup hbddP hmemP)
    have hPB_le : tailTransferSup M ≤ tailBoundingSup M := by
      refine csSup_le hneP fun y hy => ?_
      rcases hy with ⟨k, l, hk', hl', hMk, i, j, t, rfl⟩
      have hg := sharp_global_spectral_transfer_bound k l hk' hl' i j t
      have hnp : 0 < (treeOrder k l : ℝ) := by unfold treeOrder; positivity
      refine (mul_le_mul_of_nonneg_left hg.2.2.2.2.2.1
        (Real.rpow_nonneg hnp.le ((3 : ℝ) / 2))).trans ?_
      exact le_csSup hbddB ⟨k, l, hk', hl', hMk, i, j, rfl⟩
    exact ⟨h1_le, hPB_le, hneB, hbddB, isLUB_csSup hneB hbddB,
      hneP, hbddP, isLUB_csSup hneP hbddP⟩
  have hthresh : ∀ {M : ℝ}, 4 ≤ M →
      tailBoundingSup M ≤ max (envelopeG (tailThresholdD M)) (envelopeH (tailThresholdD M)) :=
    fun {M} hM => by
      refine csSup_le (hall M).2.2.1 fun y hy => ?_
      rcases hy with ⟨k, l, hk, hl, hMn, i, j, rfl⟩
      have hg := sharp_global_spectral_transfer_bound k l hk hl i j 0
      have hd_ge_D : tailThresholdD M ≤ specD k l := by
        unfold tailThresholdD; refine max_le hg.1 ?_
        unfold specD; refine Real.sqrt_le_sqrt ?_
        have hM1 : 0 ≤ M - 1 := by linarith
        have hkl_ge : M - 1 ≤ (k : ℝ) * ((l : ℝ) + 1) := by
          unfold treeOrder at hMn; push_cast at hMn; linarith
        have hsq_le : (2 * Real.sqrt (M - 1)) ^ 2 ≤ ((k : ℝ) + (l : ℝ) + 1) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hM1]
          linarith [sq_nonneg ((k : ℝ) - (l : ℝ) - 1),
            show ((k : ℝ) + (l : ℝ) + 1) ^ 2 - 4 * ((k : ℝ) * ((l : ℝ) + 1)) =
              ((k : ℝ) - (l : ℝ) - 1) ^ 2 by ring]
        have hsqrt_le : 2 * Real.sqrt (M - 1) ≤ (k : ℝ) + (l : ℝ) + 1 :=
          (sq_le_sq₀ (by positivity) (by positivity)).mp hsq_le
        linarith [sq_nonneg ((k : ℝ) - (l : ℝ) - 1),
          show ((k : ℝ) - (l : ℝ)) ^ 2 + 4 * (l : ℝ) - (2 * ((k : ℝ) + (l : ℝ) + 1) - 3) =
            ((k : ℝ) - (l : ℝ) - 1) ^ 2 by ring]
      have hD_pos : 0 < tailThresholdD M :=
        lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num)) (le_max_left _ _)
      refine hg.2.2.2.2.1.trans ?_
      rcases lt_or_eq_of_le hd_ge_D with hlt | heq
      · have hanti := spectral_envelope_and_antitonicity (tailThresholdD M) (specD k l) hD_pos hlt
        exact max_le (hanti.2.2.2.1.le.trans (le_max_left _ _))
          (hanti.2.2.2.2.1.le.trans (le_max_right _ _))
      · rw [heq]
  have heps : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℝ, 4 ≤ N₀ ∧ ∀ M : ℝ, N₀ ≤ M →
      tailBoundingSup M < 1 + ε := fun ε hε => by
    let D : ℝ := max 128 (175 / ε + 1)
    let N₀ : ℝ := max 4 (((D ^ 2 + 3) / 4) ^ 2 + 1)
    refine ⟨N₀, le_max_left _ _, fun M hM => ?_⟩
    have hM4 : 4 ≤ M := (le_max_left 4 _).trans hM
    have hM_sub : ((D ^ 2 + 3) / 4) ^ 2 ≤ M - 1 := by
      have : ((D ^ 2 + 3) / 4) ^ 2 + 1 ≤ M := (le_max_right 4 _).trans hM
      linarith
    have hD128 : 128 ≤ D := le_max_left _ _
    have hD_le_t : D ≤ tailThresholdD M := by
      unfold tailThresholdD; refine le_trans ?_ (le_max_right _ _)
      have hsq1 : (D ^ 2 + 3) / 4 ≤ Real.sqrt (M - 1) := by
        rw [← Real.sqrt_sq (show 0 ≤ (D ^ 2 + 3) / 4 by positivity)]
        exact Real.sqrt_le_sqrt hM_sub
      rw [← Real.sqrt_sq (show 0 ≤ D by linarith)]
      exact Real.sqrt_le_sqrt (by linarith)
    have ht128 : 128 ≤ tailThresholdD M := hD128.trans hD_le_t
    obtain ⟨hmax_eq, hH_sub⟩ := envelope_large_bound ht128
    have h175 : 175 / tailThresholdD M < ε := by
      have hD_gt : 175 / ε < D := by
        have : 175 / ε + 1 ≤ D := le_max_right 128 _
        linarith
      have hD_pos : 0 < D := by linarith
      have ht_pos : 0 < tailThresholdD M := by linarith
      have h1 : 175 < D * ε := (div_lt_iff₀ hε).mp hD_gt
      have h2 : D * ε ≤ ε * tailThresholdD M := by
        rw [mul_comm D ε]; exact mul_le_mul_of_nonneg_left hD_le_t hε.le
      exact (div_lt_iff₀ ht_pos).mpr (lt_of_lt_of_le h1 h2)
    calc tailBoundingSup M
        ≤ max (envelopeG (tailThresholdD M)) (envelopeH (tailThresholdD M)) := hthresh hM4
      _ = envelopeH (tailThresholdD M) := hmax_eq
      _ ≤ 1 + 175 / tailThresholdD M := by linarith
      _ < 1 + ε := by linarith
  have htendB : Filter.Tendsto tailBoundingSup Filter.atTop (nhds (1 : ℝ)) := by
    rw [Metric.tendsto_atTop]; intro ε hε
    obtain ⟨N₀, _, hN₀⟩ := heps ε hε
    refine ⟨N₀, fun M hM => ?_⟩
    rw [Real.dist_eq, abs_lt]
    have h1 : 1 ≤ tailBoundingSup M := (hall M).1.trans (hall M).2.1
    exact ⟨by linarith, by linarith [hN₀ M hM]⟩
  have htendP : Filter.Tendsto tailTransferSup Filter.atTop (nhds (1 : ℝ)) := by
    rw [Metric.tendsto_atTop]; intro ε hε
    obtain ⟨N₀, _, hN₀⟩ := heps ε hε
    refine ⟨N₀, fun M hM => ?_⟩
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [(hall M).1], by linarith [(hall M).2.1, hN₀ M hM]⟩
  have hunif : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℝ, ∀ (k l : ℕ), 2 ≤ k → 1 ≤ l →
      N₀ ≤ (treeOrder k l : ℝ) → ∀ (i : Fin k) (j : Fin l) (t : ℝ),
        leafTransferProb k l i j t ≤ (leafBoundingEntry k l i j) ^ 2 ∧
          (leafBoundingEntry k l i j) ^ 2 ≤
            (1 + ε) * ((treeOrder k l : ℝ) ^ (-(3 : ℝ) / 2)) := fun ε hε => by
    obtain ⟨N₀, _, hN₀⟩ := heps ε hε
    refine ⟨N₀, fun k l hk hl hkn i j t => ?_⟩
    have hg := sharp_global_spectral_transfer_bound k l hk hl i j t
    refine ⟨hg.2.2.2.2.2.1, ?_⟩
    have hmem : ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * (leafBoundingEntry k l i j) ^ 2 ∈
        tailBoundingSet N₀ := ⟨k, l, hk, hl, hkn, i, j, rfl⟩
    have hle : ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * (leafBoundingEntry k l i j) ^ 2 ≤
        1 + ε := (le_csSup (hall N₀).2.2.2.1 hmem).trans (hN₀ N₀ le_rfl).le
    have hnp : 0 < (treeOrder k l : ℝ) := by unfold treeOrder; positivity
    have hm := mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hnp.le (-(3 : ℝ) / 2))
    have hr : ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) *
        ((treeOrder k l : ℝ) ^ (-(3 : ℝ) / 2)) = 1 := by
      rw [← Real.rpow_add hnp]; norm_num
    rwa [mul_right_comm, hr, one_mul] at hm
  have hsharp : ∀ β : ℝ, (3 : ℝ) / 2 < β → ¬ ∃ C : ℝ, ∀ (k l : ℕ), 2 ≤ k → 1 ≤ l →
      ∀ (i : Fin k) (j : Fin l) (t : ℝ),
        leafTransferProb k l i j t ≤ C * ((treeOrder k l : ℝ) ^ (-β)) := by
    rintro β hβ ⟨C, hC⟩
    set δ : ℝ := β - (3 : ℝ) / 2
    have hδ : 0 < δ := sub_pos.mpr hβ
    let B : ℕ := Nat.ceil (max 1 C) + 1
    let K : ℕ := Nat.ceil (1 / δ)
    let m : ℕ := B ^ K
    obtain ⟨hk, hl, hm_le, i₀, j₀, hP, _, hH_gt⟩ := even_witness_at_pi m
    set nR : ℝ := (treeOrder ((2 * (m + 1)) * (2 * (m + 1) + 1) + 1)
      ((2 * (m + 1)) * (2 * (m + 1) + 1)) : ℝ)
    have hn_pos : 0 < nR := by dsimp [nR]; unfold treeOrder; positivity
    have hC_bound := hC _ _ hk hl i₀ j₀ Real.pi
    have hmul := mul_le_mul_of_nonneg_left hC_bound (Real.rpow_nonneg hn_pos.le β)
    have hr1 : (nR ^ β) * (nR ^ (-β)) = 1 := by rw [← Real.rpow_add hn_pos]; ring_nf; simp
    have hr2 : nR ^ β = (nR ^ δ) * (nR ^ ((3 : ℝ) / 2)) := by
      rw [← Real.rpow_add hn_pos]; congr 1; dsimp [δ]; ring
    have hnδ_lt_C : nR ^ δ < C := by
      have hrhs : (nR ^ β) * (C * (nR ^ (-β))) = C := by
        calc (nR ^ β) * (C * (nR ^ (-β))) = C * ((nR ^ β) * (nR ^ (-β))) := by ring
          _ = C := by rw [hr1, mul_one]
      have hlhs : (nR ^ β) * leafTransferProb _ _ i₀ j₀ Real.pi =
          (nR ^ δ) * envelopeH (2 * ((2 * (m + 1) : ℕ) : ℝ) + 1) := by
        rw [hr2, mul_assoc, hP]
      have hnd_pos : 0 < nR ^ δ := Real.rpow_pos_of_pos hn_pos δ
      have hlt_mul : nR ^ δ * 1 < (nR ^ δ) * envelopeH (2 * ((2 * (m + 1) : ℕ) : ℝ) + 1) :=
        mul_lt_mul_of_pos_left hH_gt hnd_pos
      rw [hrhs, hlhs] at hmul; linarith
    have hB1 : (1 : ℝ) ≤ (B : ℝ) := by
      have : (1 : ℝ) ≤ (Nat.ceil (max 1 C) : ℝ) :=
        (le_max_left 1 C).trans (Nat.le_ceil _)
      dsimp [B]; push_cast; linarith
    have hC_lt_B : C < (B : ℝ) := by
      have : C ≤ (Nat.ceil (max 1 C) : ℝ) := (le_max_right 1 C).trans (Nat.le_ceil _)
      dsimp [B]; push_cast; linarith
    have h1_le_Kδ : (1 : ℝ) ≤ (K : ℝ) * δ := by
      have : 1 / δ ≤ (K : ℝ) := Nat.le_ceil (1 / δ)
      rwa [div_le_iff₀ hδ] at this
    have hB_le_nδ : (B : ℝ) ≤ nR ^ δ := by
      calc (B : ℝ) = (B : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (B : ℝ) ^ ((K : ℝ) * δ) := Real.rpow_le_rpow_of_exponent_le hB1 h1_le_Kδ
        _ = ((B : ℝ) ^ (K : ℝ)) ^ δ := Real.rpow_mul (by linarith) (K : ℝ) δ
        _ = (m : ℝ) ^ δ := by rw [Real.rpow_natCast]; dsimp [m]; push_cast; rfl
        _ ≤ nR ^ δ := Real.rpow_le_rpow (by positivity) hm_le hδ.le
    linarith
  exact ⟨(hall N).1, (hall N).2.1, hthresh hN, fun M => (hall M).2.2,
    htendB, htendP, hunif, hsharp⟩

end D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSharpTransferDecay
