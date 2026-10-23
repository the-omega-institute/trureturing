/- GID: D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The fluctuation condition forces the optimal calibrated visibility bound. -/

/-
proof_shape: result: bind-only
proof_shape: source_effect_eq_phi: bind-only; consumers: phi_diagonal_coefficient, effA_diagonal, result; escape_witness: none
escape_witness: none
admission_basis: open-problem-resolution (#16507; Proved)
proof_shape: phi_diagonal_coefficient: bind-only; consumers: effA_diagonal, coeff_nonneg, coefficient_sum; escape_witness: none
proof_shape: effA_diagonal: bind-only; consumers: sqrt_effA; escape_witness: none
proof_shape: coeff_nonneg: bind-only; consumers: sqrt_effA, luders_single, result; escape_witness: none
proof_shape: sqrt_effA: bind-only; consumers: luders_single; escape_witness: none
proof_shape: luders_single: bind-only; consumers: diagonal_pin; escape_witness: none
proof_shape: marginalB: bind-only; consumers: result; escape_witness: none
proof_shape: diagonal_pin: bind-only; consumers: result; escape_witness: none
proof_shape: rotated_entry: bind-only; consumers: effBU_entry; escape_witness: none
proof_shape: had_pair_exists: bind-only; consumers: result; escape_witness: none
proof_shape: effBU_entry: bind-only; consumers: had_pair_exists; escape_witness: none
proof_shape: psd_sum_coherence: bind-only; consumers: result; escape_witness: none
proof_shape: coefficient_sum: bind-only; consumers: result; escape_witness: none
proof_shape: kappa_identity: bind-only; consumers: visibility_algebra; escape_witness: none
proof_shape: visibility_algebra: bind-only; consumers: result; escape_witness: none
Direct frozen dependencies (declaration identities at the merged dev base):
  D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity.cfc_diagonal
    declaration statement_id: sha256:873e4955783786d99a250879f3da4640dab6550433b567150988ca3aaede9fe0
  D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.hadamard_unitary
    declaration statement_id: sha256:4e37cb688ab72d0d3829cb3f171e52ef49c90b228dd41564bc35ec0b24c4553e
  D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.hadamard
    declaration statement_id: sha256:a7d8c3cc2756b00f52b2d9b38b6d5628d980af56019a448359228d12fe0f3cc0
  D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.half_sqrt_two_sq
    declaration statement_id: sha256:70c1b53dcec77377712b2ca72440af20e571c209cda05423cadd61c525b65dbb
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap
    declaration statement_id: sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
  D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.phi
    declaration statement_id: sha256:478d10f4d2630256660ee5625f24c556783d91db591c700b1e3b12dffa485453
  D5/S3/Quantum/Matrix/CartesianVariance.psd_entry_bound
    declaration statement_id: sha256:029989c48264702a7ddb2f7963b30fbc3260f0c293862ce2cf6561a7a358a67e
  D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM
    declaration statement_id: sha256:218e2b42c4dc29468db56af33ad277eb32b8ed575533012439ed233131c5efa1
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16609.
The rotated-effect proof uses HaarTwoCopyTwirl.Hadamard.hadamard_unitary.
Its scalar coefficient uses NandiMutualPredictabilityLOCCRefutation.half_sqrt_two_sq.
The source effects are effA and effB; proofs use the frozen Tomiyama noise map
through source_effect_eq_phi. Scalar coefficients are real diagonal entries of phi,
with no separate coefficient definition.
-/

import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
import D5.S3.Quantum.Entanglement.NandiMutualPredictabilityLOCCRefutation
import D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
open D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity (phi)
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)

namespace D5.S3.Quantum.Measurements.CalibratedJointMeasurabilityOptimality

def effA (d : ℕ) (lam : ℝ) (a : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  (lam : ℂ) • Matrix.single a a 1 + (((1-lam)/d : ℝ) : ℂ) • 1

def effB (d : ℕ) (gam : ℝ) (b : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  (gam : ℂ) • Matrix.single b b 1 + (((1-gam)/d : ℝ) : ℂ) • 1

def effBU {d : ℕ} {gam : ℝ} (U : Matrix (Fin d) (Fin d) ℂ) (b : Fin d) :=
  star U * effB d gam b * U

def luders {d : ℕ} (A rho : Matrix (Fin d) (Fin d) ℂ) :=
  CFC.sqrt A * rho * CFC.sqrt A

def AverageCondition {d : ℕ}
    (W : Fin d × Fin d → Matrix (Fin d) (Fin d) ℂ)
    (A B : Fin d → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ f g : Fin d → ℝ,
    ∑ a, ∑ b, ((g b - f a : ℝ) : ℂ) • W (a,b) =
      ∑ b, (g b : ℂ) • B b - ∑ a, (f a : ℂ) • A a

def FluctuationCondition {d : ℕ}
    (W : Fin d × Fin d → Matrix (Fin d) (Fin d) ℂ)
    (A B : Fin d → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ rho : Matrix (Fin d) (Fin d) ℂ, rho.PosSemidef → rho.trace = 1 →
    (∀ i j, i ≠ j → rho i j = 0) → ∀ a b,
      (W (a,b) * rho).trace = (B b * luders (A a) rho).trace

def kappa (d : ℕ) (lam : ℝ) : ℝ :=
  2 * Real.sqrt (lam + (1-lam)/d) * Real.sqrt ((1-lam)/d) +
    ((d : ℝ)-2) * ((1-lam)/d)

def visibilityBound (d : ℕ) (lam : ℝ) : ℝ :=
  2 * kappa d lam / (d + 2*kappa d lam - d*kappa d lam)

def claim : Prop := ∀ d : ℕ, 2 ≤ d → ∀ lam gam : ℝ,
  0 < lam → lam < 1 → 0 < gam → gam < 1 →
  (∀ U ∈ Matrix.unitaryGroup (Fin d) ℂ,
    ∃ W : Fin d × Fin d → Matrix (Fin d) (Fin d) ℂ,
      IsPOVM W ∧ AverageCondition W (effA d lam) (effBU (gam := gam) U) ∧
      FluctuationCondition W (effA d lam) (effBU (gam := gam) U)) →
    gam ≤ visibilityBound d lam


private theorem source_effect_eq_phi (d : ℕ) (lam : ℝ) (a : Fin d) :
    (lam : ℂ) • Matrix.single a a 1 + (((1-lam)/d : ℝ) : ℂ) • 1 =
      phi d (1-lam) 0 (single a a 1) := by
  simp [D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity.phi]

private theorem phi_diagonal_coefficient (d : ℕ) (lam : ℝ) (a k : Fin d) :
    (phi d (1-lam) 0 (single a a 1) k k).re =
      if k = a then lam + (1-lam)/d else (1-lam)/d := by
  rw [← source_effect_eq_phi]
  by_cases hk : k = a
  · subst k; simp
  · simp [Matrix.single, Matrix.of_apply, hk, Ne.symm hk]

private theorem effA_diagonal (d : ℕ) (lam : ℝ) (a : Fin d) :
    phi d (1-lam) 0 (single a a 1) = diagonal (fun k => ((phi d (1-lam) 0 (single a a 1) k k).re : ℂ)) := by
  simp_rw [phi_diagonal_coefficient]
  rw [← source_effect_eq_phi]
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = a
    · subst i; simp
    · simp [Matrix.single, Matrix.of_apply, hi, Ne.symm hi]
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single, Matrix.of_apply, Matrix.one_apply, diagonal_apply, if_neg hij]
    split_ifs with h
    · obtain ⟨ha, hb⟩ := h
      exact (hij (ha.symm.trans hb)).elim
    · simp

private theorem coeff_nonneg {d : ℕ} {lam : ℝ} (hl : 0 ≤ lam) (hu : lam ≤ 1)
    (a k : Fin d) : 0 ≤ (phi d (1-lam) 0 (single a a 1) k k).re := by
  rw [phi_diagonal_coefficient]
  split_ifs <;> positivity

private theorem sqrt_effA {d : ℕ} {lam : ℝ} (hl : 0 ≤ lam) (hu : lam ≤ 1) (a : Fin d) :
    CFC.sqrt (phi d (1-lam) 0 (single a a 1)) =
      diagonal (fun k => (Real.sqrt ((phi d (1-lam) 0 (single a a 1) k k).re) : ℂ)) := by
  have hA : (phi d (1-lam) 0 (single a a 1)).PosSemidef := by
    rw [effA_diagonal, posSemidef_diagonal_iff]
    intro k
    exact_mod_cast coeff_nonneg hl hu a k
  rw [CFC.sqrt_eq_real_sqrt _ hA.nonneg, cfcₙ_eq_cfc]
  conv_lhs => rw [effA_diagonal]
  exact D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal
    Real.sqrt (fun k => (phi d (1-lam) 0 (single a a 1) k k).re)

private theorem luders_single {d : ℕ} {lam : ℝ} (hl : 0 ≤ lam) (hu : lam ≤ 1)
    (a k : Fin d) :
    luders (phi d (1-lam) 0 (single a a 1)) (single k k 1) =
      ((phi d (1-lam) 0 (single a a 1) k k).re : ℂ) • single k k 1 := by
  rw [luders, sqrt_effA hl hu]
  ext i j
  rw [mul_diagonal, diagonal_mul]
  by_cases hi : i = k <;> by_cases hj : j = k
  · subst i; subst j
    simpa only [Matrix.single_apply_same, Matrix.smul_apply, smul_eq_mul, mul_one, Complex.ofReal_mul] using
      congrArg (fun x : ℝ => (x : ℂ)) (Real.mul_self_sqrt (coeff_nonneg hl hu a k))
  · subst i; simp [Matrix.single, hj, Ne.symm hj]
  · subst j; simp [Matrix.single, hi, Ne.symm hi]
  · simp [Matrix.single, hi, hj, Ne.symm hi, Ne.symm hj]

private theorem marginalB {d : ℕ} {W : Fin d × Fin d → Matrix (Fin d) (Fin d) ℂ}
    {A B : Fin d → Matrix (Fin d) (Fin d) ℂ}
    (h : AverageCondition W A B) (b : Fin d) : ∑ a, W (a,b) = B b := by
  have hh := h (fun _ => 0) (fun k => if k = b then 1 else 0)
  simpa using hh

private theorem diagonal_pin {d : ℕ} {lam : ℝ}
    {W : Fin d × Fin d → Matrix (Fin d) (Fin d) ℂ}
    {B : Fin d → Matrix (Fin d) (Fin d) ℂ}
    (hl : 0 ≤ lam) (hu : lam ≤ 1)
    (h : FluctuationCondition W ((fun a : Fin d => phi d (1-lam) 0 (single a a 1))) B) (a b k : Fin d) :
    W (a,b) k k = ((phi d (1-lam) 0 (single a a 1) k k).re : ℂ) * B b k k := by
  have hP : (single k k (1 : ℂ)).PosSemidef := by
    rw [← diagonal_single, posSemidef_diagonal_iff]
    intro i
    simp only [Pi.single_apply]
    split_ifs <;> positivity
  have hp := h (single k k 1) hP (by simp)
    (by intro i j hij; simp only [Matrix.single, Matrix.of_apply]; split_ifs with hh
        · exact (hij (hh.1.symm.trans hh.2)).elim
        · rfl) a b
  rw [luders_single hl hu, Matrix.mul_smul] at hp
  simpa [Matrix.trace_mul_single, mul_comm] using hp


private theorem rotated_entry {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (b i j : Fin d) :
    (star U * (single b b (1:ℂ) : Matrix (Fin d) (Fin d) ℂ) * U) i j = star (U b i) * U b j := by
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, ite_and]

private theorem effBU_entry {d : ℕ} {gam : ℝ} (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (b i j : Fin d) :
    effBU (gam := gam) U b i j =
      (gam : ℂ) * (star (U b i) * U b j) + (((1-gam)/d : ℝ) : ℂ) *
        (if i = j then 1 else 0) := by
  unfold effBU effB
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.add_mul,
    Matrix.smul_mul, Matrix.smul_mul, mul_one, hU.1]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, rotated_entry, Matrix.one_apply]

private theorem had_pair_exists {d : ℕ} {gam : ℝ} (i j : Fin d) (hij : i ≠ j) :
    ∃ U : Matrix (Fin d) (Fin d) ℂ,
      U ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
      effBU (gam := gam) U i i i = ((gam/2+(1-gam)/d : ℝ) : ℂ) ∧
      effBU (gam := gam) U i j j = ((gam/2+(1-gam)/d : ℝ) : ℂ) ∧
      effBU (gam := gam) U i i j = ((gam/2 : ℝ) : ℂ) := by
  let hcoef : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ)
  have hcoef_sq : hcoef * hcoef = (1/2 : ℂ) := by
    have h := D5.S3.Quantum.Entanglement.NandiMutualPredictabilityLOCCRefutation.half_sqrt_two_sq
    simpa only [hcoef, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using congrArg (fun x : ℝ => (x : ℂ)) h
  let had : Matrix (Fin d) (Fin d) ℂ :=
    1 + single i i (hcoef - 1) + single i j hcoef +
      single j i hcoef + single j j (-hcoef - 1)
  have hs : star hcoef = hcoef := by simp [hcoef]
  have ht : 2 * hcoef ^ 2 = 1 := by rw [pow_two, hcoef_sq]; norm_num
  have hu : had ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    have h := D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.Hadamard.hadamard_unitary
      i j hij hcoef hs ht
    have he : D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.Hadamard.hadamard
        i j hcoef = had := by
      dsimp [D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.Hadamard.hadamard, had]
      abel
    rwa [he] at h
  refine ⟨had, hu, ?_⟩
  have hii : had i i = hcoef := by simp [had, hij, hij.symm]
  have hij' : had i j = hcoef := by simp [had, hij, hij.symm]
  simp only [effBU_entry _ hu, hii, hij', hs, hcoef_sq,
    if_pos rfl, if_neg hij, mul_zero, add_zero, mul_one]
  constructor
  · push_cast; ring
  constructor <;> push_cast <;> ring

private theorem psd_sum_coherence {d : ℕ} (W : Fin d → Matrix (Fin d) (Fin d) ℂ)
    (hW : ∀ a, (W a).PosSemidef) (i j : Fin d) (p q : Fin d → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) (t : ℝ) (ht : 0 ≤ t)
    (hdi : ∀ a, (W a i i).re = p a * t)
    (hdj : ∀ a, (W a j j).re = q a * t) :
    ‖∑ a, W a i j‖ ≤ t * ∑ a, Real.sqrt (p a) * Real.sqrt (q a) := by
  have hn (a : Fin d) : ‖W a i j‖ ≤ t * (Real.sqrt (p a) * Real.sqrt (q a)) := by
    have h := D5.S3.Quantum.Matrix.CartesianVariance.psd_entry_bound (hW a) i j
    rw [Complex.normSq_eq_norm_sq, hdi a, hdj a] at h
    have he : (p a * t) * (q a * t) =
        (t * (Real.sqrt (p a) * Real.sqrt (q a)))^2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (hp a), Real.sq_sqrt (hq a)]
      ring
    rw [he] at h
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h
  calc
    ‖∑ a, W a i j‖ ≤ ∑ a, ‖W a i j‖ := norm_sum_le _ _
    _ ≤ ∑ a, t * (Real.sqrt (p a) * Real.sqrt (q a)) :=
      Finset.sum_le_sum fun a _ => hn a
    _ = _ := (Finset.mul_sum _ _ _).symm


private theorem coefficient_sum {d : ℕ} {lam : ℝ} (hu : lam ≤ 1)
    (i j : Fin d) (hij : i ≠ j) :
    (∑ a : Fin d, Real.sqrt ((phi d (1-lam) 0 (single a a 1) i i).re) * Real.sqrt ((phi d (1-lam) 0 (single a a 1) j j).re)) =
      kappa d lam := by
  let s : ℝ := (1-lam)/d
  let q : ℝ := Real.sqrt (lam+s) * Real.sqrt s
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hf (a : Fin d) : Real.sqrt ((phi d (1-lam) 0 (single a a 1) i i).re) * Real.sqrt ((phi d (1-lam) 0 (single a a 1) j j).re) =
      s + (if a = i then q-s else 0) + (if a = j then q-s else 0) := by
    by_cases hai : a = i
    · subst a
      simp [phi_diagonal_coefficient, hij, hij.symm, q, s]
    by_cases haj : a = j
    · subst a
      simp [phi_diagonal_coefficient, hij, hij.symm, q, s, mul_comm]
    · simpa only [phi_diagonal_coefficient, if_neg hai, if_neg haj, if_neg (Ne.symm hai),
        if_neg (Ne.symm haj), add_zero] using Real.mul_self_sqrt hs
  simp_rw [hf]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  dsimp [kappa, s, q]
  ring


private theorem kappa_identity {d : ℕ} {lam : ℝ} (hd : 2 ≤ d)
    (hl : 0 ≤ lam) (hu : lam ≤ 1) :
    kappa d lam = 1 - (Real.sqrt (lam+(1-lam)/d) - Real.sqrt ((1-lam)/d))^2 := by
  have hdR : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hs : 0 ≤ (1-lam)/(d:ℝ) := div_nonneg (sub_nonneg.mpr hu) hdR.le
  have hr : 0 ≤ lam+(1-lam)/(d:ℝ) := add_nonneg hl hs
  have hn : lam+(d:ℝ)*((1-lam)/d) = 1 := by field_simp; ring
  dsimp [kappa]
  nlinarith [Real.sq_sqrt hr, Real.sq_sqrt hs]

private theorem visibility_algebra {d : ℕ} {lam gam : ℝ} (hd : 2 ≤ d)
    (hl : 0 ≤ lam) (hu : lam ≤ 1)
    (h : gam/2 ≤ kappa d lam * (gam/2 + (1-gam)/d)) :
    gam ≤ visibilityBound d lam := by
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0:ℝ) < d := by linarith
  have hk : kappa d lam ≤ 1 := by rw [kappa_identity hd hl hu]; nlinarith [sq_nonneg (Real.sqrt (lam+(1-lam)/d)-Real.sqrt ((1-lam)/d))]
  have hden : 0 < (d:ℝ)+2*kappa d lam-d*kappa d lam := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdR) (sub_nonneg.mpr hk)]
  rw [visibilityBound, le_div_iff₀ hden]
  have hh := mul_le_mul_of_nonneg_right h hd0.le
  have hcancel : ((1-gam)/(d:ℝ))*(d:ℝ) = 1-gam := div_mul_cancel₀ _ (ne_of_gt hd0)
  nlinarith


theorem result : claim := by
  intro d hd lam gam hl hu hg hv hall
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hh := congrArg Fin.val h
    norm_num [i,j] at hh
  obtain ⟨U, hU, he⟩ := had_pair_exists (gam := gam) i j hij
  obtain ⟨W,hW,hA,hF⟩ := hall U hU
  have hE : effA d lam = (fun a : Fin d => phi d (1-lam) 0 (single a a 1)) := by
    funext a
    exact source_effect_eq_phi d lam a
  rw [hE] at hA hF
  let t : ℝ := gam/2 + (1-gam)/d
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hdi (a : Fin d) : (W (a,i) i i).re = (phi d (1-lam) 0 (single a a 1) i i).re * t := by
    rw [diagonal_pin hl.le hu.le hF a i i, he.1]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rfl
  have hdj (a : Fin d) : (W (a,i) j j).re = (phi d (1-lam) 0 (single a a 1) j j).re * t := by
    rw [diagonal_pin hl.le hu.le hF a i j, he.2.1]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rfl
  have hx := psd_sum_coherence (fun a => W (a,i)) (fun a => hW.1 (a,i)) i j
    (fun a => (phi d (1-lam) 0 (single a a 1) i i).re) (fun a => (phi d (1-lam) 0 (single a a 1) j j).re)
    (fun a => coeff_nonneg hl.le hu.le a i) (fun a => coeff_nonneg hl.le hu.le a j)
    t ht hdi hdj
  have hm : (∑ a, W (a,i) i j) = effBU (gam := gam) U i i j := by
    simpa only [Matrix.sum_apply] using
      congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j) (marginalB hA i)
  rw [hm, he.2.2, coefficient_sum hu.le i j hij] at hx
  have hgam : 0 ≤ gam/2 := by positivity
  have hnorm : ‖((gam/2 : ℝ) : ℂ)‖ = gam/2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_of_nonneg hgam
  rw [hnorm] at hx
  apply visibility_algebra hd hl.le hu.le
  simpa only [t, mul_comm] using hx

end D5.S3.Quantum.Measurements.CalibratedJointMeasurabilityOptimality
