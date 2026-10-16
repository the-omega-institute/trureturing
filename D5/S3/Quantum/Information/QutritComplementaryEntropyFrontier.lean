/- GID: D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/QutritComplementaryEntropyFrontier
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Qutrit complementary map entropies have a sharp lower frontier. -/

import D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
import D5.S3.Entropy.Forgetting.CapacityMonotone
import D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier

open scoped BigOperators ComplexOrder Matrix Kronecker
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

-- Channel and state definitions.
def admissible
    (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) : Prop :=
  D5.S3.Quantum.Foundation.FiniteTraceDistance.isometry V

def swap
    (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3) ℂ :=
  V.submatrix Prod.swap id

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
  let K : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ := fun e b i => V (b, e) i
  (1 / 3 : ℂ) • (MatrixMap.choi_matrix (MatrixMap.of_kraus K K)).submatrix Prod.swap Prod.swap

set_option backward.isDefEq.respectTransparency false in
private theorem choi_apply (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ)
    (p q : Fin 3 × Fin 3) :
    choi V p q = (1 / 3 : ℝ) •
      ((channelB V (Matrix.single p.1 q.1 (1 : ℂ))) p.2 q.2) := by
  simp [choi.eq_1, MatrixMap.choi_of_kraus, Matrix.sum_apply, Matrix.vecMulVec,
    channelB, partialTraceRight, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.single, Finset.mul_sum, Complex.real_smul, ite_and, eq_comm]

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
    swap (swap V) = V := by
  rw [swap.eq_1, swap.eq_1]
  rfl

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
  simp only [channelB.eq_1, partialTraceLeft, partialTraceRight, Matrix.mul_apply,
    Matrix.conjTranspose_apply, swap, Matrix.submatrix_apply, Prod.swap, id_eq]

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
  simp [choi_apply, channelB, partialTraceRight, Matrix.mul_apply, Matrix.single,
    Matrix.conjTranspose_apply, reshuffle.eq_1, Matrix.smul_apply, Finset.mul_sum, ite_and, eq_comm]

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
  D5.S3.Entropy.MaxEntropy.shannonEntropy x

def h (a : ℝ) : ℝ :=
  Real.binEntropy a

def g (a : ℝ) : ℝ :=
  entropy3 ![1 / 3 + a, 1 / 3, 1 / 3 - a]

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
  simpa only [entropy3, D5.S3.Entropy.MaxEntropy.shannonEntropy, Fintype.sum_bool,
    ht, hb, sub_sub_cancel, add_comm] using hm

-- Two-point spreading and scalar entropy bounds.
private theorem negMulLog_pair_spread {l r p q : ℝ}
    (hl : 0 ≤ l) (hp : p ∈ Set.Icc l r) (hq : q ∈ Set.Icc l r)
    (hs : p + q = l + r) :
    Real.negMulLog l + Real.negMulLog r ≤ Real.negMulLog p + Real.negMulLog q := by
  rcases lt_or_eq_of_le (hp.1.trans hp.2) with hlr | hlr
  · exact D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation.pair_entropy_le
      hl hlr hp.1 hp.2 hs
  · have hp' : p = l := le_antisymm (hp.2.trans hlr.ge) hp.1
    have hq' : q = r := le_antisymm hq.2 (hlr.ge.trans hq.1)
    simp only [hp', hq', le_refl]

private theorem entropy3_box
    (x : Fin 3 → ℝ) (l m r : ℝ) (hl : 0 ≤ l)
    (hlm : l ≤ m) (hx : ∀ i, x i ∈ Set.Icc l r)
    (hs : (∑ i, x i) = l + m + r) :
    Real.negMulLog l + Real.negMulLog m + Real.negMulLog r ≤ entropy3 x := by
  simp only [Fin.sum_univ_three] at hs
  rw [entropy3.eq_1]
  simp only [D5.S3.Entropy.MaxEntropy.shannonEntropy, Fin.sum_univ_three]
  by_cases h0 : x 0 ≤ m
  · let t := l + m - x 0
    have ht : t ∈ Set.Icc l m := by dsimp [t]; constructor <;> linarith [(hx 0).1]
    have hfirst := negMulLog_pair_spread hl ⟨(hx 0).1, h0⟩ ht (by dsimp [t]; ring)
    have hlast := negMulLog_pair_spread (l := t) (r := r) (le_trans hl ht.1)
      (p := x 1) (q := x 2)
      ⟨by dsimp [t]; linarith [(hx 2).2], (hx 1).2⟩
      ⟨by dsimp [t]; linarith [(hx 1).2], (hx 2).2⟩
      (by dsimp [t]; linarith)
    linarith
  · let t := m + r - x 0
    have ht : t ∈ Set.Icc m r := by dsimp [t]; constructor <;> linarith [(hx 0).2]
    have hfirst := negMulLog_pair_spread (le_trans hl hlm) ⟨le_of_not_ge h0, (hx 0).2⟩ ht
      (by dsimp [t]; ring)
    have hlast := negMulLog_pair_spread (l := l) (r := t) hl
      (p := x 1) (q := x 2)
      ⟨(hx 1).1, by dsimp [t]; linarith [(hx 2).1]⟩
      ⟨(hx 2).1, by dsimp [t]; linarith [(hx 1).1]⟩
      (by dsimp [t]; linarith)
    linarith

private theorem small_entropy_tail
    (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i) (hs : (∑ i, x i) = 1)
    (a : ℝ) (ha : a ∈ Set.Icc 0 (1 / 3 : ℝ)) (hH : entropy3 x ≤ h a) :
    ∃ i : Fin 3, (1 / 2 : ℝ) < x i ∧ 1 - x i ∈ Set.Icc 0 a := by
  have hhalf : h a < h (1 / 2) :=
    Real.binEntropy_strictMonoOn ⟨ha.1, by norm_num; linarith [ha.2]⟩
      (by constructor <;> norm_num) (by linarith [ha.2])
  have hi : ∃ i, (1 / 2 : ℝ) < x i := by
    by_contra hn
    push Not at hn
    have hb := entropy3_box x 0 (1 / 2) (1 / 2) (by norm_num)
      (by norm_num) (fun i => ⟨hx i, hn i⟩) (by norm_num; exact hs)
    have hh : Real.negMulLog 0 + Real.negMulLog (1 / 2) + Real.negMulLog (1 / 2) =
        h (1 / 2) := by
      rw [h, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
      norm_num
    rw [hh] at hb
    linarith
  obtain ⟨i, hi⟩ := hi
  have hxi : x i ≤ 1 := by
    rw [← hs]
    exact Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
  have hu : 1 - x i ∈ Set.Icc 0 (2 : ℝ)⁻¹ := by constructor <;> norm_num <;> linarith
  refine ⟨i, hi, sub_nonneg.mpr hxi, ?_⟩
  by_contra hna
  have hb := Real.binEntropy_strictMonoOn
    ⟨ha.1, by norm_num; linarith [ha.2]⟩ hu (lt_of_not_ge hna)
  have hm := entropy3_merge x hx hs i
  change Real.binEntropy (1 - x i) ≤ entropy3 x at hm
  change entropy3 x ≤ Real.binEntropy a at hH
  linarith

-- Scalar monotonicity and the two capacity cuts.
private theorem g_eq_binary (u : ℝ) :
    g u = h (1 / 3) + (2 / 3 : ℝ) * h ((1 + 3 * u) / 2) := by
  simp only [g, entropy3, D5.S3.Entropy.MaxEntropy.shannonEntropy,
    Fin.sum_univ_three, Matrix.cons_val]
  rw [h, h, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
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

private theorem table_tradeoff
    (w : Matrix (Fin 3) (Fin 3) ℝ)
    (hw : ∀ i j, w i j ∈ Set.Icc 0 (1 / 3 : ℝ))
    (hs : (∑ i, ∑ j, w i j) = 1) (a : ℝ)
    (ha : a ∈ Set.Icc 0 (1 / 3 : ℝ))
    (hH : entropy3 (fun i => ∑ j, w i j) ≤ h a) :
    g a ≤ entropy3 (fun j => ∑ i, w i j) := by
  obtain ⟨i, _, hu⟩ := small_entropy_tail (fun i => ∑ j, w i j)
    (fun i => Finset.sum_nonneg fun j _ => (hw i j).1) hs a ha hH
  let u := 1 - ∑ j, w i j
  have hui : u ∈ Set.Icc 0 (1 / 3 : ℝ) := ⟨hu.1, hu.2.trans ha.2⟩
  have hc : ∀ j, (∑ k, w k j) ∈ Set.Icc (1 / 3 - u) (1 / 3 + u) := by
    intro j
    obtain ⟨hp, hm⟩ := table_cuts w hw hs i j
    dsimp [u]
    constructor <;> linarith
  have hb := entropy3_box (fun j => ∑ i, w i j)
    (1 / 3 - u) (1 / 3) (1 / 3 + u)
    (by linarith [hui.2]) (by linarith [hui.1]) hc
    (by rw [Finset.sum_comm, hs]; ring)
  have hg := g_antitone hui ha hu.2
  simp only [g, entropy3, D5.S3.Entropy.MaxEntropy.shannonEntropy,
    Fin.sum_univ_three, Matrix.cons_val] at hb hg ⊢
  linarith

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
    simp [attainer.eq_1, Matrix.single, Matrix.mul_apply, Matrix.conjTranspose_apply,
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
  constructor <;> simp only [rhoB.eq_1, rhoE] <;> rw [joint_eq_scaled_gram] <;> ext i j <;>
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
    simp only [entropy3, D5.S3.Entropy.MaxEntropy.shannonEntropy,
      Fin.sum_univ_three, Matrix.cons_val]
    ring

-- Covariance under independent changes of the two marginal eigenbases.
private theorem partialTrace_local_unitary_covariance
    (P : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (U Z : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1)
    (hZ : Z * Z.conjTranspose = 1) :
    partialTraceRight ((U ⊗ₖ Z).conjTranspose * P * (U ⊗ₖ Z)) =
      U.conjTranspose * partialTraceRight P * U ∧
    partialTraceLeft ((U ⊗ₖ Z).conjTranspose * P * (U ⊗ₖ Z)) =
      Z.conjTranspose * partialTraceLeft P * Z := by
  constructor
  · simpa only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose] using
      D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation.trace_local_right
        P U.conjTranspose Z.conjTranspose
        (by simpa only [Matrix.conjTranspose_conjTranspose] using hZ)
  · simpa only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose] using
      D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation.trace_local_left
        P U.conjTranspose Z.conjTranspose
        (by simpa only [Matrix.conjTranspose_conjTranspose] using hU)

private theorem spectral_table
    (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) (hV : admissible V) :
    ∃ w : Matrix (Fin 3) (Fin 3) ℝ,
      (∀ i j, w i j ∈ Set.Icc 0 (1 / 3 : ℝ)) ∧
      (∑ i, ∑ j, w i j) = 1 ∧
      entropy3 (fun i => ∑ j, w i j) = outputEntropy V ∧
      entropy3 (fun j => ∑ i, w i j) = outputEntropy (swap V) := by
  let hB := (rhoB_posSemidef V).isHermitian
  let hE := (rhoE_posSemidef V).isHermitian
  let U : Matrix (Fin 3) (Fin 3) ℂ := hB.eigenvectorUnitary
  let Z : Matrix (Fin 3) (Fin 3) ℂ := hE.eigenvectorUnitary
  have hU : U * U.conjTranspose = 1 := Unitary.coe_mul_star_self hB.eigenvectorUnitary
  have hZ : Z * Z.conjTranspose = 1 := Unitary.coe_mul_star_self hE.eigenvectorUnitary
  let W := U ⊗ₖ Z
  have hW : W * W.conjTranspose = 1 :=
    (Matrix.kronecker_mem_unitary hB.eigenvectorUnitary.property
      hE.eigenvectorUnitary.property).2
  have hW' : W.conjTranspose * W = 1 :=
    (Matrix.kronecker_mem_unitary hB.eigenvectorUnitary.property
      hE.eigenvectorUnitary.property).1
  let P := W.conjTranspose * joint V * W
  let w : Matrix (Fin 3) (Fin 3) ℝ := fun i j => (P (i, j) (i, j)).re
  have hp : P.PosSemidef := (joint_posSemidef V).conjTranspose_mul_mul_same W
  have hc : ((1 / 3 : ℝ) • 1 - P).PosSemidef := by
    have hh := (joint_upper V hV).conjTranspose_mul_mul_same W
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hW'] using hh
  obtain ⟨hr, he⟩ := partialTrace_local_unitary_covariance (joint V) U Z hU hZ
  have hdiagB : U.conjTranspose * rhoB V * U =
      Matrix.diagonal (fun i => (hB.eigenvalues i : ℂ)) := by
    simpa only [U, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      hB.conjStarAlgAut_star_eigenvectorUnitary
  have hdiagE : Z.conjTranspose * rhoE V * Z =
      Matrix.diagonal (fun i => (hE.eigenvalues i : ℂ)) := by
    simpa only [Z, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      hE.conjStarAlgAut_star_eigenvectorUnitary
  have hrow (i : Fin 3) : (∑ j, w i j) = hB.eigenvalues i := by
    have hd := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => (M i i).re)
      (hr.trans hdiagB)
    simpa only [partialTraceRight, Matrix.diagonal_apply_eq, Complex.ofReal_re,
      Complex.re_sum] using hd
  have hcol (j : Fin 3) : (∑ i, w i j) = hE.eigenvalues j := by
    have hd := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => (M j j).re)
      (he.trans hdiagE)
    simpa only [partialTraceLeft, Matrix.diagonal_apply_eq, Complex.ofReal_re,
      Complex.re_sum] using hd
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · intro i j
    refine ⟨(Complex.nonneg_iff.mp (hp.diag_nonneg (i := (i, j)))).1, ?_⟩
    have hd := (Complex.nonneg_iff.mp (hc.diag_nonneg (i := (i, j)))).1
    apply sub_nonneg.mp
    simpa only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      Complex.sub_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.one_re, Complex.one_im, mul_one, mul_zero, sub_zero] using hd
  · have ht : P.trace = 1 := by
      dsimp [P]
      rw [Matrix.trace_mul_cycle, hW, Matrix.one_mul, joint_trace V hV]
    have ht' := congrArg Complex.re ht
    simpa only [Matrix.trace, Fintype.sum_prod_type, Complex.re_sum, Complex.one_re,
      Matrix.diag_apply] using ht'
  · simp only [hrow, entropy3, D5.S3.Entropy.MaxEntropy.shannonEntropy,
      outputEntropy, spectralEntropy]
  · change entropy3 (fun j => ∑ i, w i j) = spectralEntropy _
    simp only [hcol, entropy3, D5.S3.Entropy.MaxEntropy.shannonEntropy, spectralEntropy, rhoB_swap]

private theorem output_tradeoff
    (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) (hV : admissible V)
    (a : ℝ) (ha : a ∈ Set.Icc 0 (1 / 3 : ℝ)) (hS : outputEntropy V ≤ h a) :
    g a ≤ outputEntropy (swap V) := by
  obtain ⟨w, hw, hs, hB, hE⟩ := spectral_table V hV
  rw [← hE]
  apply table_tradeoff w hw hs a ha
  rw [hB]
  exact hS

theorem result : claim := by
  constructor
  · intro V hV a ha
    constructor
    · intro hS
      rw [(source_bridge V hV).2] at hS
      have hb := output_tradeoff (swap V) (swap_admissible V hV) a ha hS
      rw [swap_swap] at hb
      rw [(source_bridge (swap V) (swap_admissible V hV)).2, swap_swap]
      exact hb
    · intro hS
      rw [(source_bridge (swap V) (swap_admissible V hV)).2, swap_swap] at hS
      rw [(source_bridge V hV).2]
      exact output_tradeoff V hV a ha hS
  · intro a ha
    have hv := attainer_admissible a ha
    have he := attainer_entropies a ha
    exact ⟨⟨hv, he⟩, ⟨swap_admissible _ hv, he.2, by rw [swap_swap]; exact he.1⟩⟩

end D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier
