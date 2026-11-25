/- GID: D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact canonical recovery for a commuting three-branch mixture in dimension four. -/

import D5.S3.Quantum.Recovery.BinaryRandomUnitaryRecovery

/-! The certificate in `certificate.txt` uses signed fourth roots of unity and
a dual slack with nonzero eigenvalue `4 * sqrt 3`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate Matrix
open Matrix Finset
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Divergence.CanonicalChannelDPI (actual_kraus_representation)
open D5.S3.Quantum.Recovery.BinaryRandomUnitaryChannel
open D5.S3.Quantum.Recovery.BinaryRandomUnitaryRecovery (binary_unitary_optimal)

noncomputable section

namespace D5.S3.Quantum.Recovery.TernaryRandomUnitaryRecovery

local notation "Iℂ" => Complex.I
local notation "r" => Real.sqrt (3 : ℝ)

private theorem sqrt_three_sq : r ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private theorem sqrt_three_pos : 0 < r := Real.sqrt_pos.2 (by norm_num)

/-- The three signed fourth-root phase columns, in the certificate order. -/
def phases : Matrix (Fin 4) (Fin 3) ℂ :=
  !![1, 1, 1; -Iℂ, Iℂ, 1; Iℂ, 1, -Iℂ; 1, -Iℂ, Iℂ]

private theorem phase_norm (j : Fin 4) (b : Fin 3) : ‖phases j b‖ = 1 := by
  fin_cases j <;> fin_cases b <;> simp [phases]

/-- The three physical unitary branches. -/
def branch (b : Fin 3) : unitaryGroup (Fin 4) ℂ :=
  diagonalUnitary (fun j => phases j b) (fun j => phase_norm j b)

theorem branches_commute (b c : Fin 3) : Commute (branch b) (branch c) := by
  change branch b * branch c = branch c * branch b
  apply Subtype.ext
  change diagonal _ * diagonal _ = diagonal _ * diagonal _
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext j
  exact mul_comm _ _

private def gram : CodeMatrix 4 :=
  !![3, 1, 1, 1;
     1, 3, -1 + 2 * Iℂ, -1 - 2 * Iℂ;
     1, -1 - 2 * Iℂ, 3, -1 + 2 * Iℂ;
     1, -1 + 2 * Iℂ, -1 - 2 * Iℂ, 3]

private def weight : Fin 4 → ℝ := ![2 * r, 4 + 2 * r, 4 + 2 * r, 4 + 2 * r]

private theorem weight_pos (j : Fin 4) : 0 < weight j := by
  have := sqrt_three_pos
  fin_cases j <;> simp [weight] <;> linarith

private theorem sum_weight : ∑ j, weight j = 12 + 8 * r := by
  simp [Fin.sum_univ_succ, weight]
  ring

private def slack : CodeMatrix 4 := diagonal (fun j => (weight j : ℂ)) - gram

private theorem gram_eq : phases * phasesᴴ = gram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [phases, gram, Matrix.mul_apply, Fin.sum_univ_succ, Complex.ext_iff,
      Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]

private theorem slack_hermitian : slackᴴ = slack := by
  rw [slack, conjTranspose_sub, ← gram_eq, conjTranspose_mul, conjTranspose_conjTranspose,
    diagonal_conjTranspose]
  simp

private theorem slack_sq : slack * slack = (↑(4 * r) : ℂ) • slack := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    norm_num [slack, gram, weight, Matrix.diagonal, Fin.sum_univ_succ, Complex.ext_iff,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im] <;>
    (try constructor) <;> nlinarith only [sqrt_three_sq]

private def a : ℝ := 2 * r / 3 - 1

private theorem a_pos : 0 < a := by
  have hr := sqrt_three_pos
  have hs := sqrt_three_sq
  unfold a
  nlinarith

private theorem a_lt_one : a < 1 := by
  have hr := sqrt_three_pos
  have hs := sqrt_three_sq
  unfold a
  nlinarith

private def v : Fin 4 → ℂ := ![1, (a : ℂ), (a : ℂ), (a : ℂ)]
private def w : Fin 4 → ℂ :=
  ![0, 1, ⟨-1 / 2, -r / 2⟩, ⟨-1 / 2, r / 2⟩]

private theorem slack_v : slack *ᵥ v = 0 := by
  funext j
  fin_cases j <;>
    norm_num [slack, gram, weight, v, a, Matrix.mulVec, dotProduct, Matrix.diagonal,
      Fin.sum_univ_succ, Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im] <;>
    nlinarith only [sqrt_three_sq]

private theorem slack_w : slack *ᵥ w = 0 := by
  funext j
  fin_cases j <;>
    norm_num [slack, gram, weight, w, Matrix.mulVec, dotProduct, Matrix.diagonal,
      Fin.sum_univ_succ, Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im] <;>
    (try constructor) <;> nlinarith only [sqrt_three_sq]

/-- The complementary projection, multiplied by the positive scalar `4 * sqrt 3`. -/
private theorem slack_projector :
    slack = (↑(4 * r) : ℂ) • (1 : CodeMatrix 4) -
      (↑(3 + 2 * r) : ℂ) • vecMulVec v (star v) -
      (↑(4 * r / 3) : ℂ) • vecMulVec w (star w) := by
  have hc : r * r ^ 2 = r * 3 := congrArg (fun x : ℝ => r * x) sqrt_three_sq
  have hv : star v = v := by
    funext j
    fin_cases j <;> simp [v]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, hv, vecMulVec_apply, smul_eq_mul,
    Pi.star_apply, Complex.star_def]
  fin_cases i <;> fin_cases j <;>
    norm_num [slack, gram, weight, v, w, a, Matrix.diagonal, Matrix.one_apply,
      Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im] <;>
    (try constructor) <;> nlinarith only [sqrt_three_sq, hc]

private theorem kernel_span (z : Fin 4 → ℂ) (hz : slack *ᵥ z = 0) :
    ∃ s t : ℂ, z = s • v + t • w := by
  have hr : (↑(4 * r) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) sqrt_three_pos.ne')
  have houter (x y : Fin 4 → ℂ) : vecMulVec x y *ᵥ z = (y ⬝ᵥ z) • x := by
    rw [vecMulVec_mulVec]
    funext j
    exact mul_comm _ _
  rw [slack_projector, sub_mulVec, sub_mulVec, smul_mulVec, smul_mulVec, smul_mulVec,
    one_mulVec, houter, houter] at hz
  have h := sub_eq_zero.mp hz
  have h' := sub_eq_iff_eq_add.mp h
  refine ⟨(↑(4 * r) : ℂ)⁻¹ * (↑(3 + 2 * r) : ℂ) * (star v ⬝ᵥ z),
    (↑(4 * r) : ℂ)⁻¹ * (↑(4 * r / 3) : ℂ) * (star w ⬝ᵥ z), ?_⟩
  have heq := congrArg (fun x : Fin 4 → ℂ => (↑(4 * r) : ℂ)⁻¹ • x) h'
  simpa only [smul_add, smul_smul, inv_mul_cancel₀ hr, one_smul, mul_assoc, add_comm] using heq

private theorem root_norm (sign : ℝ) (hsign : sign ^ 2 = 1) :
    Complex.normSq (⟨-1 / 2, sign * r / 2⟩ : ℂ) = 1 := by
  change (-1 / 2 : ℝ) * (-1 / 2) + (sign * r / 2) * (sign * r / 2) = 1
  calc
    _ = 1 / 4 + sign ^ 2 * r ^ 2 / 4 := by ring
    _ = 1 := by rw [hsign, sqrt_three_sq]; norm_num

private theorem kernel_excludes_phases (z : Fin 4 → ℂ) (hz : slack *ᵥ z = 0)
    (hunit : ∀ j, Complex.normSq (z j) = 1) : False := by
  obtain ⟨s, t, rfl⟩ := kernel_span z hz
  have h0 : Complex.normSq s = 1 := by simpa [v, w] using hunit 0
  let c : ℂ := s * (a : ℂ)
  have h1 : Complex.normSq (c + t) = 1 := by simpa [c, v, w] using hunit 1
  have h2 : Complex.normSq (c + t * (⟨-1 / 2, -r / 2⟩ : ℂ)) = 1 := by
    simpa [c, v, w] using hunit 2
  have h3 : Complex.normSq (c + t * (⟨-1 / 2, r / 2⟩ : ℂ)) = 1 := by
    simpa [c, v, w] using hunit 3
  have hω₂ : Complex.normSq (⟨-1 / 2, -r / 2⟩ : ℂ) = 1 := by
    simpa using root_norm (-1) (by norm_num)
  have hω₃ : Complex.normSq (⟨-1 / 2, r / 2⟩ : ℂ) = 1 := by
    simpa using root_norm 1 (by norm_num)
  -- Compare the three squared moduli of c + t times a cube root of unity.
  simp only [Complex.normSq_add, Complex.normSq_mul, hω₂, hω₃, mul_one] at h1 h2 h3
  rw [show (conj (t * (⟨-1 / 2, -r / 2⟩ : ℂ))) =
      conj t * conj (⟨-1 / 2, -r / 2⟩ : ℂ) from map_mul _ _ _, ← mul_assoc] at h2
  rw [show (conj (t * (⟨-1 / 2, r / 2⟩ : ℂ))) =
      conj t * conj (⟨-1 / 2, r / 2⟩ : ℂ) from map_mul _ _ _, ← mul_assoc] at h3
  have hre2 (q : ℂ) (x : ℝ) : (q * conj (⟨-1 / 2, x⟩ : ℂ)).re =
      q.re * (-1 / 2) + q.im * x := by
    change q.re * (-1 / 2) - q.im * -x = _
    ring
  rw [hre2] at h2 h3
  have hre : (c * conj t).re = 0 := by linarith
  have him : (c * conj t).im = 0 := by
    have h : (c * conj t).im * r = 0 := by linarith
    exact (mul_eq_zero.mp h).resolve_right sqrt_three_pos.ne'
  have hc : c ≠ 0 := by
    apply mul_ne_zero
    · intro hs
      simp [hs] at h0
    · exact_mod_cast a_pos.ne'
  have ht : t = 0 := by
    have h : c * conj t = 0 := Complex.ext hre him
    simpa using (mul_eq_zero.mp h).resolve_left hc
  have ha : a ^ 2 = 1 := by
    have : Complex.normSq c = 1 := by simpa [ht] using h1
    simpa only [c, Complex.normSq_mul, h0, Complex.normSq_ofReal, one_mul, pow_two]
      using this
  nlinarith [a_pos, a_lt_one, mul_pos a_pos (sub_pos.mpr a_lt_one)]

private theorem diagonal_complete {k : Type} [Fintype k] (z : k → Fin 4 → ℂ)
    (hz : ∀ j, ∑ b, Complex.normSq (z b j) = 1) :
    ∑ b, (diagonal (z b))ᴴ * diagonal (z b) = (1 : CodeMatrix 4) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.sum_apply, diagonal_conjTranspose, diagonal_mul_diagonal,
      diagonal_apply_eq, Pi.star_apply, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Matrix.one_apply_eq]
    exact_mod_cast hz i
  · simp [Matrix.sum_apply, diagonal_conjTranspose, diagonal_mul_diagonal, hij]

private theorem diagonal_mass_le {k : Type} [Fintype k] (L : k → CodeMatrix 4)
    (hL : ∑ b, (L b)ᴴ * L b = 1) (j : Fin 4) :
    ∑ b, Complex.normSq (L b j j) ≤ 1 := by
  have h := congrArg (fun X : CodeMatrix 4 => (X j j).re) hL
  simp only [Matrix.sum_apply, Complex.re_sum, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
    Matrix.one_apply_eq, Complex.one_re] at h
  rw [← h]
  exact sum_le_sum fun b _ =>
    single_le_sum (fun i _ => Complex.normSq_nonneg (L b i j)) (mem_univ j)

private def noiseKraus (b : Fin 3) : CodeMatrix 4 :=
  diagonal (fun j => (↑(Real.sqrt (1 / 3 : ℝ)) : ℂ) * phases j b)

private theorem noise_complete : ∑ b, (noiseKraus b)ᴴ * noiseKraus b = 1 := by
  apply diagonal_complete
  intro j
  simp [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq (phases j _),
    phase_norm]

/-- The actual CPTP noise with three equally weighted commuting branches. -/
def channel : CodeChannel 4 :=
  (finite_kraus_quantum_channel noiseKraus noise_complete).choose

private theorem noise_action (X : CodeMatrix 4) :
    channelAction channel X = ∑ b, noiseKraus b * X * (noiseKraus b)ᴴ :=
  (finite_kraus_quantum_channel noiseKraus noise_complete).choose_spec X

theorem channel_action (X : CodeMatrix 4) : channelAction channel X =
    ∑ b : Fin 3, (1 / 3 : ℂ) • channelAction (unitaryChannel (branch b)) X := by
  rw [noise_action]
  apply sum_congr rfl
  intro b _
  rw [unitaryChannel_action]
  have hb : noiseKraus b = (↑(Real.sqrt (1 / 3 : ℝ)) : ℂ) • (branch b : CodeMatrix 4) := by
    ext i j
    by_cases hij : i = j <;> simp [noiseKraus, branch, diagonalUnitary, Matrix.diagonal, hij]
  simp only [hb, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  rw [← pow_two, ← Complex.ofReal_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  norm_num

private def columnScore (z : Fin 4 → ℂ) : ℝ :=
  ∑ b, Complex.normSq ((phasesᴴ *ᵥ z) b)

private theorem score_kraus {k : Type} [Fintype k] (decoder : CodeChannel 4)
    (L : k → CodeMatrix 4)
    (hL : ∀ X, channelAction decoder X = ∑ b, L b * X * (L b)ᴴ) :
    recoveryScore channel decoder = (∑ b, columnScore (fun j => conj (L b j j))) / 48 := by
  have hcomp : channelAction (decoder.comp channel) =
      MatrixMap.of_kraus (fun t : k × Fin 3 => L t.1 * noiseKraus t.2)
        (fun t : k × Fin 3 => L t.1 * noiseKraus t.2) := by
    apply LinearMap.ext
    intro X
    change channelAction decoder (channelAction channel X) = _
    rw [hL, noise_action]
    simp only [Matrix.mul_sum, Matrix.sum_mul, MatrixMap.of_kraus, LinearMap.sum_apply,
      LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_prod_type, Matrix.conjTranspose_mul,
      Matrix.mul_assoc]
  unfold recoveryScore
  rw [hcomp, canonical_overlap_kraus _ (by decide), Fintype.sum_prod_type]
  have htrace (b : k) (i : Fin 3) :
      trace (L b * noiseKraus i) = (↑(Real.sqrt (1 / 3 : ℝ)) : ℂ) *
        conj ((phasesᴴ *ᵥ (fun j => conj (L b j j))) i) := by
    simp only [noiseKraus, Matrix.trace, Matrix.diag, Matrix.mul_diagonal, Matrix.mulVec,
      dotProduct, Matrix.conjTranspose_apply, Complex.star_def, map_sum, map_mul,
      Complex.conj_conj, Finset.mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  simp only [htrace, Complex.normSq_mul, Complex.normSq_conj, Complex.normSq_ofReal,
    ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 3), ← Finset.mul_sum, columnScore]
  ring

private theorem normSq_mulVec_sum {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℂ)
    (z : n → ℂ) :
    ∑ i, Complex.normSq ((A *ᵥ z) i) = (star z ⬝ᵥ ((Aᴴ * A) *ᵥ z)).re := by
  rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  simp only [dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

private theorem columnScore_identity (z : Fin 4 → ℂ) :
    columnScore z = ∑ j, weight j * Complex.normSq (z j) -
      (∑ j, Complex.normSq ((slack *ᵥ z) j)) / (4 * r) := by
  have hdiff : slack *ᵥ z =
      (diagonal (fun j => (weight j : ℂ))) *ᵥ z - gram *ᵥ z := by
    rw [slack, sub_mulVec]
  have hdiag : (star z ⬝ᵥ (diagonal (fun j => (weight j : ℂ)) *ᵥ z)).re =
      ∑ j, weight j * Complex.normSq (z j) := by
    simp only [dotProduct, Complex.re_sum, mulVec_diagonal, Pi.star_apply, Complex.star_def]
    apply sum_congr rfl
    intro j _
    rw [mul_left_comm, ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  have hcol : columnScore z = (star z ⬝ᵥ (gram *ᵥ z)).re := by
    unfold columnScore
    rw [normSq_mulVec_sum, conjTranspose_conjTranspose, gram_eq]
  rw [normSq_mulVec_sum, slack_hermitian, slack_sq, smul_mulVec, dotProduct_smul,
    smul_eq_mul, Complex.re_ofReal_mul, hdiff, dotProduct_sub, Complex.sub_re, hdiag, ← hcol]
  have hdenom : 4 * r ≠ 0 := mul_ne_zero (by norm_num) sqrt_three_pos.ne'
  rw [mul_div_cancel_left₀ _ hdenom]
  ring

private theorem exact_normalization : (12 + 8 * r) / 48 = 1 / 4 + r / 6 := by ring

/-- A dual upper bound for every actual CPTP decoder, with arbitrary Kraus matrices. -/
theorem score_le (decoder : CodeChannel 4) :
    recoveryScore channel decoder ≤ 1 / 4 + r / 6 := by
  let K := actual_kraus_representation decoder
  have hcol (b) : columnScore (fun j => conj (K.kraus b j j)) ≤
      ∑ j, weight j * Complex.normSq (K.kraus b j j) := by
    rw [columnScore_identity]
    simp only [Complex.normSq_conj]
    exact sub_le_self _ (div_nonneg (sum_nonneg fun _ _ => Complex.normSq_nonneg _)
      (by positivity))
  rw [score_kraus decoder K.kraus K.haction, ← exact_normalization, ← sum_weight]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ ∑ b, ∑ j, weight j * Complex.normSq (K.kraus b j j) :=
      sum_le_sum fun b _ => hcol b
    _ = ∑ j, weight j * ∑ b, Complex.normSq (K.kraus b j j) := by
      rw [sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ j, weight j := sum_le_sum fun j _ =>
      mul_le_of_le_one_right (weight_pos j).le (diagonal_mass_le K.kraus K.hkraus j)

private def witness (b : Bool) : Fin 4 → ℂ :=
  if b then (↑(Real.sqrt (1 - a ^ 2)) : ℂ) • w else v

/-- The explicit two diagonal Kraus operators attaining the endpoint. -/
def optimalKraus (b : Bool) : CodeMatrix 4 := diagonal (fun j => conj (witness b j))

private theorem witness_mass (j : Fin 4) : ∑ b, Complex.normSq (witness b j) = 1 := by
  have ha : 0 ≤ 1 - a ^ 2 := by
    nlinarith [a_pos, a_lt_one, mul_pos a_pos (sub_pos.mpr a_lt_one)]
  simp only [Fintype.sum_bool, witness, ite_true, ite_false, Bool.false_eq_true, Pi.smul_apply,
    smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt ha]
  fin_cases j <;> simp [v, w, ← pow_two] <;> ring_nf <;> rw [sqrt_three_sq] <;> ring

theorem optimalKraus_complete : ∑ b, (optimalKraus b)ᴴ * optimalKraus b = 1 := by
  apply diagonal_complete
  simpa only [Complex.normSq_conj] using witness_mass

/-- An actual trace-preserving decoder with the two diagonal Kraus operators. -/
def optimalDecoder : CodeChannel 4 :=
  (finite_kraus_quantum_channel optimalKraus optimalKraus_complete).choose

theorem optimalDecoder_action (X : CodeMatrix 4) :
    channelAction optimalDecoder X = ∑ b, optimalKraus b * X * (optimalKraus b)ᴴ :=
  (finite_kraus_quantum_channel optimalKraus optimalKraus_complete).choose_spec X

theorem score_attained : recoveryScore channel optimalDecoder = 1 / 4 + r / 6 := by
  have hz (b : Bool) : (fun j => conj (optimalKraus b j j)) = witness b := by
    funext j
    simp [optimalKraus]
  have hkernel (b : Bool) : slack *ᵥ witness b = 0 := by
    cases b <;> simp [witness, mulVec_smul, slack_v, slack_w]
  rw [score_kraus optimalDecoder optimalKraus optimalDecoder_action]
  simp_rw [hz, columnScore_identity, hkernel]
  simp only [Pi.zero_apply, Complex.normSq_zero, Finset.sum_const_zero, zero_div, sub_zero]
  rw [sum_comm]
  simp_rw [← Finset.mul_sum, witness_mass, mul_one]
  rw [sum_weight, exact_normalization]

/-- Strict separation for every unitary decoder, with no restriction on its entries. -/
theorem unitary_score_lt (U : unitaryGroup (Fin 4) ℂ) :
    recoveryScore channel (unitaryChannel U) < 1 / 4 + r / 6 := by
  let L : Unit → CodeMatrix 4 := fun _ => U
  let z : Fin 4 → ℂ := fun j => conj ((U : CodeMatrix 4) j j)
  have hscore : recoveryScore channel (unitaryChannel U) = columnScore z / 48 := by
    rw [score_kraus _ L (fun X => by simp [L, unitaryChannel_action]), Fintype.sum_unique]
  have hcomplete : ∑ b : Unit, (L b)ᴴ * L b = 1 := by
    simpa only [Fintype.sum_unique, L, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self U
  have hmass (j : Fin 4) : Complex.normSq (z j) ≤ 1 := by
    simpa only [Fintype.sum_unique, L, z, Complex.normSq_conj] using
      diagonal_mass_le L hcomplete j
  rw [hscore, ← exact_normalization, ← sum_weight]
  apply (div_lt_div_iff_of_pos_right (by norm_num)).2
  by_contra! hge
  rw [columnScore_identity] at hge
  have hterm (j : Fin 4) : 0 ≤ weight j * (1 - Complex.normSq (z j)) :=
    mul_nonneg (weight_pos j).le (sub_nonneg.mpr (hmass j))
  have hmissing : 0 ≤ ∑ j, weight j * (1 - Complex.normSq (z j)) :=
    sum_nonneg fun j _ => hterm j
  have hnorm : 0 ≤ ∑ j, Complex.normSq ((slack *ᵥ z) j) :=
    sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hslack : 0 ≤ (∑ j, Complex.normSq ((slack *ᵥ z) j)) / (4 * r) :=
    div_nonneg hnorm (by positivity)
  simp only [mul_sub, mul_one, sum_sub_distrib] at hmissing
  have hzero : ∑ j, weight j * (1 - Complex.normSq (z j)) = 0 := by
    simp only [mul_sub, mul_one, sum_sub_distrib]
    linarith
  have hkernel : slack *ᵥ z = 0 := by
    have hdiv : (∑ j, Complex.normSq ((slack *ᵥ z) j)) / (4 * r) = 0 := by linarith
    have hsum := (div_eq_zero_iff.mp hdiv).resolve_right
      (mul_ne_zero (by norm_num) sqrt_three_pos.ne')
    funext j
    exact Complex.normSq_eq_zero.mp
      ((sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _).1 hsum j (mem_univ j))
  apply kernel_excludes_phases z hkernel
  intro j
  have hj := (sum_eq_zero_iff_of_nonneg fun j _ => hterm j).1 hzero j (mem_univ j)
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hj).resolve_left (weight_pos j).ne')).symm

/-- One branch is included at a zero-weight endpoint of the checked binary theorem. -/
theorem binary_branch_bound {d : ℕ} (hd : 0 < d) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) (U V : unitaryGroup (Fin d) ℂ) :
    ∃ Z : unitaryGroup (Fin d) ℂ, ∀ D : CodeChannel d,
      recoveryScore (binaryChannel hp hq hpq U V) D ≤
      recoveryScore (binaryChannel hp hq hpq U V) (unitaryChannel Z) :=
  binary_unitary_optimal hd hp hq hpq U V

/-- The channel itself has no representation by just two unitary branches. -/
theorem no_binary_representation {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) (U V : unitaryGroup (Fin 4) ℂ) :
    channel ≠ binaryChannel hp hq hpq U V := by
  intro heq
  obtain ⟨Z, hZ⟩ := binary_branch_bound (by decide) hp hq hpq U V
  have h := hZ optimalDecoder
  rw [← heq, score_attained] at h
  exact (not_lt_of_ge h) (unitary_score_lt Z)

#print axioms branches_commute
#print axioms channel_action
#print axioms optimalKraus_complete
#print axioms optimalDecoder_action
#print axioms score_le
#print axioms score_attained
#print axioms unitary_score_lt
#print axioms binary_branch_bound
#print axioms no_binary_representation

end D5.S3.Quantum.Recovery.TernaryRandomUnitaryRecovery
