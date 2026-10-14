/- GID: D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/QutritComplementaryEntropyFrontier
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Qutrit complementary map entropies have a sharp lower frontier. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Entropy.Forgetting.CapacityMonotone

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier

open scoped BigOperators ComplexOrder Matrix Kronecker
open D5.S3.Quantum.Information.PartialTraceMutualInformation

-- Channel and state definitions.
def admissible
    (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) : Prop :=
  V.conjTranspose * V = 1

def swap
    (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3) ℂ :=
  fun p i => V (p.2, p.1) i

def channelB
    (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ)
    (R : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  partialTraceRight (V * R * V.conjTranspose)

def joint
    (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  V * ((1 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) *
    V.conjTranspose

def rhoB
    (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  partialTraceRight (joint V)

def rhoE
    (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  partialTraceLeft (joint V)

def choi
    (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  fun p q =>
    (1 / 3 : ℝ) •
      ((channelB V (Matrix.single p.1 q.1 (1 : ℂ))) p.2 q.2)

-- Gram identities, positivity, normalization, and exchange of the factors.
private theorem joint_eq_scaled_gram (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    joint V = (1 / 3 : ℝ) • (V * V.conjTranspose) := by
  rw [joint, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

private theorem joint_posSemidef (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    (joint V).PosSemidef := by
  rw [joint_eq_scaled_gram]
  exact (Matrix.posSemidef_self_mul_conjTranspose V).smul (by norm_num : (0 : ℝ) ≤ 1 / 3)

private theorem rhoB_posSemidef (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    (rhoB V).PosSemidef :=
  partialTraceRight_posSemidef (joint_posSemidef V)

private theorem rhoE_posSemidef (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    (rhoE V).PosSemidef :=
  partialTraceLeft_posSemidef (joint_posSemidef V)

private theorem joint_trace (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ)
    (hV : admissible V) : (joint V).trace = 1 := by
  rw [joint_eq_scaled_gram, Matrix.trace_smul, Matrix.trace_mul_comm, hV,
    Matrix.trace_one]
  norm_num [Complex.real_smul]

private theorem joint_upper (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ)
    (hV : admissible V) :
    ((1 / 3 : ℝ) • (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) -
      joint V).PosSemidef := by
  have hp : (1 - V * V.conjTranspose) * (1 - V * V.conjTranspose).conjTranspose =
      1 - V * V.conjTranspose := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_sub, sub_mul,
      mul_one, one_mul]
    rw [Matrix.mul_assoc V V.conjTranspose (V * V.conjTranspose),
      ← Matrix.mul_assoc V.conjTranspose V V.conjTranspose, hV]
    simp only [Matrix.one_mul]
    abel
  rw [joint_eq_scaled_gram, ← smul_sub, ← hp]
  exact (Matrix.posSemidef_self_mul_conjTranspose _).smul (by norm_num : (0 : ℝ) ≤ 1 / 3)

private theorem swap_swap (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    swap (swap V) = V := rfl

private theorem swap_admissible (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ)
    (hV : admissible V) : admissible (swap V) := by
  change (swap V).conjTranspose * swap V = 1
  rw [← hV]
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, swap, Fintype.sum_prod_type]
  exact Finset.sum_comm

private theorem channelB_swap (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ)
    (R : Matrix (Fin 3) (Fin 3) ℂ) :
    channelB (swap V) R = partialTraceLeft (V * R * V.conjTranspose) := by
  ext i j
  simp only [channelB, partialTraceLeft, partialTraceRight, Matrix.mul_apply,
    Matrix.conjTranspose_apply, swap]

private theorem rhoB_swap (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    rhoB (swap V) = rhoE V :=
  channelB_swap V ((1 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℂ))

-- The normalized block Choi matrix and the complementary Gram matrix.
private def reshuffle (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3) ℂ :=
  fun p e => V (p.2, e) p.1

private theorem choi_eq_scaled_gram (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    choi V = (1 / 3 : ℝ) • (reshuffle V * (reshuffle V).conjTranspose) := by
  ext p q
  simp [choi, channelB, partialTraceRight, Matrix.mul_apply, Matrix.single,
    Matrix.conjTranspose_apply, reshuffle, Matrix.smul_apply, Finset.mul_sum, ite_and, eq_comm]

private theorem choi_posSemidef (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    (choi V).PosSemidef := by
  rw [choi_eq_scaled_gram]
  exact (Matrix.posSemidef_self_mul_conjTranspose _).smul (by norm_num : (0 : ℝ) ≤ 1 / 3)

def outputEntropy
    (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) : ℝ :=
  spectralEntropy (rhoB_posSemidef V).isHermitian

def mapEntropy
    (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) : ℝ :=
  spectralEntropy (choi_posSemidef V).isHermitian

def entropy3 (x : Fin 3 → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (x i)

def h (a : ℝ) : ℝ :=
  Real.binEntropy a

def g (a : ℝ) : ℝ :=
  Real.negMulLog (1 / 3 + a) +
  Real.negMulLog (1 / 3) +
  Real.negMulLog (1 / 3 - a)

def attainer (a : ℝ) :
    Matrix (Fin 3 × Fin 3) (Fin 3) ℂ :=
  Matrix.single (0, 0) 0 1 +
  Matrix.single (1, 0) 1 (Real.sqrt (1 - 3 * a) : ℂ) +
  Matrix.single (0, 1) 1 (Real.sqrt (3 * a) : ℂ) +
  Matrix.single (2, 0) 2 1

def claim : Prop :=
  (∀ V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ,
    admissible V →
    ∀ a : ℝ, a ∈ Set.Icc 0 (1 / 3 : ℝ) →
      (mapEntropy V ≤ h a →
        g a ≤ mapEntropy (swap V)) ∧
      (mapEntropy (swap V) ≤ h a →
        g a ≤ mapEntropy V)) ∧
  (∀ a : ℝ, a ∈ Set.Icc 0 (1 / 3 : ℝ) →
    (admissible (attainer a) ∧
      mapEntropy (attainer a) = h a ∧
      mapEntropy (swap (attainer a)) = g a) ∧
    (admissible (swap (attainer a)) ∧
      mapEntropy (swap (attainer a)) = g a ∧
      mapEntropy (swap (swap (attainer a))) = h a))

-- Complementary Choi spectrum.
private theorem reshuffle_gram (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    (1 / 3 : ℝ) • ((reshuffle V).conjTranspose * reshuffle V) = (rhoE V).transpose := by
  rw [rhoE, joint_eq_scaled_gram]
  ext i j
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.transpose_apply, partialTraceLeft, reshuffle, Finset.smul_sum]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  congr 1
  funext b
  congr 1
  funext k
  rw [mul_comm]

private theorem choi_charpoly (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    (choi V).charpoly = Polynomial.X ^ 6 * (rhoE V).charpoly := by
  rw [choi_eq_scaled_gram, ← Matrix.mul_smul]
  rw [Matrix.charpoly_mul_comm_of_le (reshuffle V)
    ((1 / 3 : ℝ) • (reshuffle V).conjTranspose) (by simp)]
  rw [Matrix.smul_mul, reshuffle_gram, Matrix.charpoly_transpose]
  norm_num

private theorem spectralEntropy_of_charpoly_factor
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (k : ℕ)
    (hchar : A.charpoly = Polynomial.X ^ k * B.charpoly) :
    spectralEntropy hA = spectralEntropy hB := by
  have hr := congrArg (fun p : Polynomial ℂ => p.roots) hchar
  rw [Polynomial.roots_mul (by rw [← hchar]; exact A.charpoly_monic.ne_zero),
    Polynomial.roots_X_pow] at hr
  have he := congrArg (fun s : Multiset ℂ => (s.map (fun z => Real.negMulLog (RCLike.re z))).sum) hr
  rw [hA.roots_charpoly_eq_eigenvalues, hB.roots_charpoly_eq_eigenvalues] at he
  change (∑ i, Real.negMulLog (hA.eigenvalues i)) = ∑ i, Real.negMulLog (hB.eigenvalues i)
  rw [Finset.sum, Finset.sum]
  simpa only [Multiset.map_map, Function.comp_apply, RCLike.ofReal_re,
    Multiset.map_add, Multiset.sum_add, Multiset.nsmul_singleton, Multiset.map_replicate,
    Multiset.sum_replicate, map_zero, Real.negMulLog_zero, nsmul_zero, zero_add] using he

private theorem spectralEntropy_of_diagonal
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (d : n → ℝ)
    (hD : A = Matrix.diagonal (fun i => (d i : ℂ))) :
    spectralEntropy hA = ∑ i, Real.negMulLog (d i) := by
  apply spectral_sum_eq_of_charpoly_prod hA d Real.negMulLog
  rw [hD, Matrix.charpoly_diagonal]
  rfl

private theorem source_bridge (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ)
    (hV : admissible V) :
    (choi V).trace = 1 ∧ mapEntropy V = outputEntropy (swap V) := by
  constructor
  · rw [choi_eq_scaled_gram, Matrix.trace_smul, Matrix.trace_mul_comm,
      ← Matrix.trace_smul, reshuffle_gram, Matrix.trace_transpose,
      rhoE, trace_partialTraceLeft, joint_trace V hV]
  · change spectralEntropy (choi_posSemidef V).isHermitian = _
    have hs := spectralEntropy_of_charpoly_factor (choi_posSemidef V).isHermitian
      (rhoE_posSemidef V).isHermitian 6 (choi_charpoly V)
    rw [outputEntropy]
    simpa only [rhoB_swap] using hs

-- Merging a chosen eigenvalue against the remaining two outcomes.
open D5.S3.Entropy.Forgetting.CapacityMonotone in
private theorem entropy3_merge
    (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hs : (∑ i, x i) = 1) (i : Fin 3) :
    h (1 - x i) ≤ entropy3 x := by
  classical
  let f : Fin 3 → Bool := fun j => decide (j = i)
  have hf : Function.Surjective f := by
    intro b
    cases b with
    | false =>
      obtain ⟨j, hj⟩ := exists_ne i
      exact ⟨j, by simp [f, hj]⟩
    | true => exact ⟨i, by simp [f]⟩
  have hm := (deterministic_forgetting_entropy_capacity_monotone x f ⟨hx, hs⟩ hf).1
  have ht : pushforward f x true = x i := by
    simp [pushforward, f, eq_comm]
  have hb : pushforward f x false = 1 - x i := by
    fin_cases i <;>
      simp [pushforward, f,
        Fin.sum_univ_three] <;> simp only [Fin.sum_univ_three] at hs <;> linarith
  change Real.binEntropy (1 - x i) ≤ _
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simpa only [D5.S3.Entropy.MaxEntropy.shannonEntropy, Fintype.sum_bool,
    ht, hb, sub_sub_cancel, entropy3, add_comm] using hm

-- Scalar monotonicity and the two capacity cuts.
private theorem g_eq_binary (u : ℝ) :
    g u = h (1 / 3) + (2 / 3 : ℝ) * h ((1 + 3 * u) / 2) := by
  rw [g, h, h, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rw [show (1 / 3 : ℝ) + u = (2 / 3) * ((1 + 3 * u) / 2) by ring,
    show (1 / 3 : ℝ) - u = (2 / 3) * (1 - (1 + 3 * u) / 2) by ring,
    Real.negMulLog_mul, Real.negMulLog_mul]
  rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num]
  ring

private theorem g_antitone : AntitoneOn g (Set.Icc 0 (1 / 3 : ℝ)) := by
  intro u hu v hv huv
  rw [g_eq_binary, g_eq_binary]
  apply add_le_add (le_refl _)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.binEntropy_strictAntiOn.antitoneOn
    (by constructor <;> norm_num <;> linarith [hu.1, hu.2])
    (by constructor <;> norm_num <;> linarith [hv.1, hv.2]) (by linarith)

private theorem table_cuts (w : Matrix (Fin 3) (Fin 3) ℝ)
    (hw : ∀ i j, w i j ∈ Set.Icc 0 (1 / 3 : ℝ))
    (hs : (∑ i, ∑ j, w i j) = 1) (i j : Fin 3) :
    (∑ k, w i k) + (∑ k, w k j) ≤ 4 / 3 ∧
      (∑ k, w i k) - (∑ k, w k j) ≤ 2 / 3 := by
  have hrow := Finset.sum_erase_add Finset.univ (fun k => w i k) (Finset.mem_univ j)
  have hcol := Finset.sum_erase_add Finset.univ (fun k => w k j) (Finset.mem_univ i)
  have htotal : (∑ k ∈ Finset.univ.erase i, ∑ l, w k l) + (∑ l, w i l) = 1 :=
    (Finset.sum_erase_add Finset.univ (fun k => ∑ l, w k l) (Finset.mem_univ i)).trans hs
  have hcap : (∑ k ∈ Finset.univ.erase j, w i k) ≤ 2 / 3 := by
    calc
      _ ≤ ∑ k ∈ Finset.univ.erase j, (1 / 3 : ℝ) :=
        Finset.sum_le_sum fun k _ => (hw i k).2
      _ = 2 / 3 := by norm_num [Finset.card_erase_of_mem]
  have hcol0 : 0 ≤ ∑ k ∈ Finset.univ.erase i, w k j :=
    Finset.sum_nonneg fun k _ => (hw k j).1
  have hout : (∑ k ∈ Finset.univ.erase i, w k j) ≤
      ∑ k ∈ Finset.univ.erase i, ∑ l, w k l := by
    apply Finset.sum_le_sum
    intro k _
    exact Finset.single_le_sum (fun l _ => (hw k l).1) (Finset.mem_univ j)
  constructor <;> linarith [(hw i j).2]

-- The explicit isometry and its two diagonal marginals.
private theorem attainer_admissible (a : ℝ) (ha : a ∈ Set.Icc 0 (1 / 3 : ℝ)) :
    admissible (attainer a) := by
  have hs0 : (Real.sqrt (1 - 3 * a) : ℂ) ^ 2 = (1 - 3 * a : ℝ) := by
    exact_mod_cast Real.sq_sqrt (by linarith [ha.2] : 0 ≤ 1 - 3 * a)
  have hs1 : (Real.sqrt (3 * a) : ℂ) ^ 2 = (3 * a : ℝ) := by
    exact_mod_cast Real.sq_sqrt (by linarith [ha.1] : 0 ≤ 3 * a)
  change (attainer a).conjTranspose * attainer a = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [attainer, Matrix.single, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_three, ← pow_two, hs0, hs1, -Real.sqrt_mul]

private theorem attainer_marginals (a : ℝ) (ha : a ∈ Set.Icc 0 (1 / 3 : ℝ)) :
    rhoB (attainer a) = Matrix.diagonal
      (fun i => ((![1 / 3 + a, 1 / 3 - a, 1 / 3] i : ℝ) : ℂ)) ∧
    rhoE (attainer a) = Matrix.diagonal
      (fun i => ((![1 - a, a, 0] i : ℝ) : ℂ)) := by
  have hs0 : (Real.sqrt (1 - 3 * a) : ℂ) ^ 2 = (1 - 3 * a : ℝ) := by
    exact_mod_cast Real.sq_sqrt (by linarith [ha.2] : 0 ≤ 1 - 3 * a)
  have hs1 : (Real.sqrt (3 * a) : ℂ) ^ 2 = (3 * a : ℝ) := by
    exact_mod_cast Real.sq_sqrt (by linarith [ha.1] : 0 ≤ 3 * a)
  constructor <;> simp only [rhoB, rhoE] <;> rw [joint_eq_scaled_gram] <;> ext i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [partialTraceRight, partialTraceLeft, attainer, Matrix.single, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_three,
      ← pow_two, hs0, hs1, Matrix.smul_apply, Complex.real_smul, -Real.sqrt_mul,
      Matrix.cons_val, eq_comm, Finset.filter_eq'] <;> ring

private theorem attainer_entropies (a : ℝ) (ha : a ∈ Set.Icc 0 (1 / 3 : ℝ)) :
    mapEntropy (attainer a) = h a ∧ mapEntropy (swap (attainer a)) = g a := by
  obtain ⟨hB, hE⟩ := attainer_marginals a ha
  constructor
  · rw [(source_bridge _ (attainer_admissible a ha)).2]
    have he := spectralEntropy_of_diagonal (rhoB_posSemidef (swap (attainer a))).isHermitian
      ![1 - a, a, 0] (by rw [rhoB_swap]; exact hE)
    change spectralEntropy (rhoB_posSemidef (swap (attainer a))).isHermitian = _
    rw [he, h, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [Fin.sum_univ_three, Matrix.cons_val, Real.negMulLog_zero, add_zero]
    ring
  · rw [(source_bridge _ (swap_admissible _ (attainer_admissible a ha))).2, swap_swap]
    have he := spectralEntropy_of_diagonal (rhoB_posSemidef (attainer a)).isHermitian
      ![1 / 3 + a, 1 / 3 - a, 1 / 3] hB
    change spectralEntropy (rhoB_posSemidef (attainer a)).isHermitian = _
    rw [he, g]
    simp only [Fin.sum_univ_three, Matrix.cons_val]
    ring

end D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier
