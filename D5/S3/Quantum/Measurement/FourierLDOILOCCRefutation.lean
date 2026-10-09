/- GID: D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/FourierLDOILOCCRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.claim; result=D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.result; claim=D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.claim
   digest: A finite-round LOCC protocol refutes Fourier LDOI lower-bound tightness. -/

/-
proof_shape: result: bind-only (the bypass assumes claim and lets S = Set.range (success 3):
  if S is unbounded above, Real.sSup_of_not_bddAbove gives sSup S = 0, contradicting lower 3 = 4/9;
  otherwise le_csSup with Set.mem_range_self T and success_T gives 1/2 ≤ 4/9, contradicting lower_lt_half).
escape_witness: none (admission basis open-problem-resolution)
admission_basis: open-problem-resolution (#14672; Refuted)
Direct frozen dependencies: none (pinned Mathlib only).
Registration is paused under CLAUDE.md §3.9.
proof_shape: instrument_mass: bind-only; consumers: alice_mass, bob_mass.
proof_shape: alice_mass: bind-only; consumers: score_le_mass.
proof_shape: bob_mass: bind-only; consumers: score_le_mass.
proof_shape: score_le_mass: content; consumers: success_le_one.
proof_shape: fourier_normSq: bind-only; consumers: phi_mass.
proof_shape: phi_mass: bind-only; consumers: success_le_one.
proof_shape: success_le_one: content; consumers: success_bddAbove.
proof_shape: success_bddAbove: bind-only; consumers: result.
proof_shape: c_sq: bind-only; consumers: cc_sq, cross_score.
proof_shape: cc_sq: bind-only; consumers: cc_pow, pair_complete, coin_complete, basis_complete.
proof_shape: cc_pow: bind-only; consumers: basis_complete.
proof_shape: pair_complete: bind-only; consumers: T.
proof_shape: split_complete: bind-only; consumers: T.
proof_shape: coin_complete: bind-only; consumers: inside, outside.
proof_shape: comp_complete: bind-only; consumers: outside.
proof_shape: basis_complete: bind-only; consumers: inside.
proof_shape: diagonal_score: bind-only; consumers: success_T.
proof_shape: inv_sqrt: bind-only; consumers: cross_score.
proof_shape: cross_score: bind-only; consumers: success_T.
proof_shape: success_T: bind-only; consumers: result.
proof_shape: lower_lt_half: bind-only; consumers: result.
The public definitions encode the Fourier LDOI basis and the uniform prior.
optLOCC is the supremum over finite-round LOCC trees with dimension-preserving
local Kraus instruments. Every finite-round LOCC measurement has this form,
since each Kraus operator's output space pulls back by polar decomposition;
this correspondence is an argument on paper. The concrete protocol measures a third
complementary outcome, resets measured factors to level zero, and assigns a
fixed guess on an impossible branch.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open scoped BigOperators
open Matrix
namespace D5.S3.Quantum.Measurement.FourierLDOILOCCRefutation

def fourier (n : ℕ) (i k : Fin n) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (i.val : ℂ) * (k.val : ℂ) / (n : ℂ)) /
    (Real.sqrt (n : ℝ) : ℂ)

def phi {n : ℕ} (l : (Fin n × Fin n)) : (Fin n × Fin n → ℂ) :=
  if l.1 = l.2 then fun p => if p.1 = p.2 then fourier n l.1 p.1 else 0
  else if l.1 < l.2 then fun p =>
    ((Pi.single (l.1,l.2) (1 : ℂ) : Fin n × Fin n → ℂ) p +
      (Pi.single (l.2,l.1) (1 : ℂ) : Fin n × Fin n → ℂ) p) / (Real.sqrt 2 : ℂ)
  else fun p =>
    ((Pi.single (l.2,l.1) (1 : ℂ) : Fin n × Fin n → ℂ) p -
      (Pi.single (l.1,l.2) (1 : ℂ) : Fin n × Fin n → ℂ) p) / (Real.sqrt 2 : ℂ)

/-- Finite-round LOCC (LOCC_ℕ) trees of complete local Kraus instruments.
Their success supremum equals the supremum over all LOCC measurements:
LOCC_ℕ ⊆ LOCC ⊆ cl(LOCC_ℕ) by Chitambar–Leung–Mančinska–Ozols–Winter,
Commun. Math. Phys. 328 (2014), 303–326, DOI 10.1007/s00220-014-1953-9,
and success is a continuous linear functional of the measurement.
This carrier correspondence is an argument on paper. -/
inductive Protocol (n : ℕ) : Type
  | leaf (guess : (Fin n × Fin n)) : Protocol n
  | alice {m : ℕ} (K : Fin m → Matrix (Fin n) (Fin n) ℂ)
      (complete : ∑ a, (K a).conjTranspose * K a = 1)
      (next : Fin m → Protocol n) : Protocol n
  | bob {m : ℕ} (K : Fin m → Matrix (Fin n) (Fin n) ℂ)
      (complete : ∑ a, (K a).conjTranspose * K a = 1)
      (next : Fin m → Protocol n) : Protocol n

def actA {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (v : (Fin n × Fin n → ℂ)) : (Fin n × Fin n → ℂ) :=
  fun p => ∑ a, K p.1 a * v (a,p.2)
def actB {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (v : (Fin n × Fin n → ℂ)) : (Fin n × Fin n → ℂ) :=
  fun p => ∑ b, K p.2 b * v (p.1,b)
def mass {n : ℕ} (v : (Fin n × Fin n → ℂ)) : ℝ := ∑ p, Complex.normSq (v p)

def score {n : ℕ} (l : (Fin n × Fin n)) : Protocol n → (Fin n × Fin n → ℂ) → ℝ
  | .leaf g, v => if g = l then mass v else 0
  | .alice K _ next, v => ∑ a, score l (next a) (actA (K a) v)
  | .bob K _ next, v => ∑ a, score l (next a) (actB (K a) v)

def success (n : ℕ) (T : Protocol n) : ℝ :=
  (1 / (n : ℝ)^2) * ∑ l, score l T (phi l)

/-- The success supremum over finite-round LOCC (LOCC_ℕ) trees.
It equals the supremum over all LOCC measurements, since
LOCC_ℕ ⊆ LOCC ⊆ cl(LOCC_ℕ) and success is a continuous linear functional;
see Chitambar–Leung–Mančinska–Ozols–Winter, Commun. Math. Phys. 328 (2014),
303–326, DOI 10.1007/s00220-014-1953-9. This equality is cited on paper,
not asserted as a Lean theorem. -/
def optLOCC (n : ℕ) : ℝ := sSup (Set.range (success n))
def lower (n : ℕ) : ℝ := 1/2 - ((n : ℝ)-2)/(2*(n : ℝ)^2)
def claim : Prop := ∀ n : ℕ, 3 ≤ n → optLOCC n = lower n

private lemma instrument_mass {n m : ℕ}
    (K : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (hK : ∑ a, (K a).conjTranspose * K a = 1) (v : Fin n → ℂ) :
    ∑ a, ∑ i, Complex.normSq ((K a *ᵥ v) i) = ∑ i, Complex.normSq (v i) := by
  have h : ∑ a, star (K a *ᵥ v) ⬝ᵥ (K a *ᵥ v) = star v ⬝ᵥ v := by
    simp_rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
    rw [← dotProduct_sum, ← Matrix.sum_mulVec, hK, Matrix.one_mulVec]
  have hr := congrArg Complex.re h
  simpa only [dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re] using hr

private lemma alice_mass {n m : ℕ}
    (K : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (hK : ∑ a, (K a).conjTranspose * K a = 1) (v : Fin n × Fin n → ℂ) :
    ∑ a, mass (actA (K a) v) = mass v := by
  simp only [mass, actA, Fintype.sum_prod_type]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  exact instrument_mass K hK (fun x => v (x,y))

private lemma bob_mass {n m : ℕ}
    (K : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (hK : ∑ a, (K a).conjTranspose * K a = 1) (v : Fin n × Fin n → ℂ) :
    ∑ a, mass (actB (K a) v) = mass v := by
  simp only [mass, actB, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  exact instrument_mass K hK (fun y => v (x,y))

private lemma score_le_mass {n : ℕ} (l : Fin n × Fin n) (T : Protocol n)
    (v : Fin n × Fin n → ℂ) : score l T v ≤ mass v := by
  induction T generalizing v with
  | leaf g =>
    simp only [score]
    split
    · exact le_rfl
    · exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
  | alice K hK next ih =>
    exact (Finset.sum_le_sum (fun a _ => ih a _)).trans_eq (alice_mass K hK v)
  | bob K hK next ih =>
    exact (Finset.sum_le_sum (fun a _ => ih a _)).trans_eq (bob_mass K hK v)

private lemma fourier_normSq {n : ℕ} (i k : Fin n) :
    Complex.normSq (fourier n i k) = 1 / (n : ℝ) := by
  rw [fourier, Complex.normSq_div, Complex.normSq_eq_norm_sq, Complex.norm_exp]
  simp [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.normSq_ofReal,
    Real.sq_sqrt (Nat.cast_nonneg n)]

private lemma phi_mass {n : ℕ} (l : Fin n × Fin n) : mass (phi l) = 1 := by
  rcases l with ⟨i,j⟩
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt))
  by_cases hij : i = j
  · subst j
    simp [mass, phi, Fintype.sum_prod_type, apply_ite, fourier_normSq, hn]
  · have hji : j ≠ i := Ne.symm hij
    have hs : Complex.normSq (Real.sqrt 2 : ℂ) = 2 := by
      simp [Complex.normSq_ofReal, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hpoint (p : Fin n × Fin n) :
        Complex.normSq (phi (i,j) p) =
          (if p = (i,j) then 1/2 else 0) + (if p = (j,i) then 1/2 else 0) := by
      by_cases hp : p = (i,j)
      · subst p
        by_cases hlt : i < j <;> simp [phi, hij, hji, hlt, Pi.single_apply, Complex.normSq_div, hs]
      · by_cases hp' : p = (j,i)
        · subst p
          by_cases hlt : i < j <;>
            simp [phi, hij, hji, hlt, Pi.single_apply, Complex.normSq_div, hs]
        · by_cases hlt : i < j <;>
            simp [phi, hij, hlt, Pi.single_apply, hp, hp', Complex.normSq_div, hs]
    simp only [mass, hpoint, Finset.sum_add_distrib]
    norm_num

private lemma success_le_one (n : ℕ) (T : Protocol n) : success n T ≤ 1 := by
  by_cases hn : n = 0
  · subst n; simp [success]
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    calc
      success n T ≤ (1 / (n : ℝ)^2) * ∑ l : Fin n × Fin n, (1 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum (fun l _ => (score_le_mass l T _).trans_eq (phi_mass l))
      _ = 1 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul, mul_one]
        field_simp
        simp [Nat.cast_mul, pow_two]

private lemma success_bddAbove (n : ℕ) : BddAbove (Set.range (success n)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨T, rfl⟩
  exact success_le_one n T

private def c : ℝ := (Real.sqrt 2)⁻¹
private lemma c_sq : c * c = 1/2 := by
  unfold c
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num
private lemma cc_sq : (c : ℂ) * c = 1/2 := by
  rw [← Complex.ofReal_mul, c_sq]
  norm_num
private lemma cc_pow : (c : ℂ)^2 = 1/2 := by simpa [pow_two] using cc_sq


private def pairK (t : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (fun r => if r ≠ (![2,1,0] t) then (c:ℂ) else 0)

private def splitK (t : Fin 3) (z : Fin 2) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (fun r => if (if z = 0 then r ≠ (![2,1,0] t) else r = (![2,1,0] t)) then 1 else 0)

private def coinK (_ : Fin 2) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (fun _ => (c:ℂ))

private def phase (q : Fin 2) : ℂ := if q = 0 then 1 else -Complex.I

private def bra (t : Fin 3) (q : Fin 2) (a : Fin 3) (s : Fin 3) : ℂ :=
  if a = 2 then (if s = (![2,1,0] t) then 1 else 0)
  else if s = (![0,0,1] t) then c
  else if s = (![1,2,2] t) then (if a = 0 then 1 else -1) * (c:ℂ) * phase q
  else 0

private def basisK (t : Fin 3) (q : Fin 2) (a : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.vecMulVec (Pi.single 0 1) (bra t q a)

private lemma pair_complete : ∑ t, (pairK t).conjTranspose * pairK t = 1 := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [pairK, Matrix.diagonal, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Fin.ext_iff, -Fin.val_eq_zero_iff, cc_sq, Matrix.one_apply] <;>
    ring_nf <;> simp [cc_sq]

private lemma split_complete (t : Fin 3) : ∑ z, (splitK t z).conjTranspose * splitK t z = 1 := by
  ext r s
  fin_cases t <;> fin_cases r <;> fin_cases s <;>
    norm_num [splitK, Matrix.diagonal, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Fin.ext_iff, -Fin.val_eq_zero_iff, Matrix.one_apply]

private lemma coin_complete : ∑ z, (coinK z).conjTranspose * coinK z = 1 := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [coinK, Matrix.diagonal, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Fin.ext_iff, -Fin.val_eq_zero_iff, cc_sq, Matrix.one_apply] <;>
    ring_nf <;> simp [cc_sq]

private lemma comp_complete : ∑ a : Fin 3,
    (Matrix.single a a (1 : ℂ)).conjTranspose * Matrix.single a a (1 : ℂ) = 1 := by
  simpa only [Matrix.conjTranspose_single, star_one,
    Matrix.single_mul_single_same, one_mul] using
    (Matrix.sum_single_one : (∑ a : Fin 3, Matrix.single a a (1 : ℂ)) = 1)

private lemma basis_complete (t : Fin 3) (q : Fin 2) :
    ∑ a, (basisK t q a).conjTranspose * basisK t q a = 1 := by
  ext r s
  fin_cases t <;> fin_cases q <;> fin_cases r <;> fin_cases s <;>
    simp [basisK, Matrix.vecMulVec, Pi.single_apply, bra, phase, Matrix.mul_apply,
      Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Fin.ext_iff, -Fin.val_eq_zero_iff, Matrix.one_apply, cc_sq] <;>
    ring_nf <;> simp [Complex.I_sq, cc_pow]

private def insideGuess (t : Fin 3) (a b : Fin 3) : (Fin 3 × Fin 3) :=
  if a = b then ((![0,0,1] t),(![1,2,2] t)) else ((![1,2,2] t),(![0,0,1] t))
private def outsideGuess (a b : Fin 3) (z : Fin 2) : (Fin 3 × Fin 3) :=
  if a = b then (0,1) else if z = 0 then (a,b) else (b,a)

private def inside (t : Fin 3) : Protocol 3 :=
  .alice coinK coin_complete fun q =>
    .alice (basisK t q) (basis_complete t q) fun a =>
      .bob (basisK t q) (basis_complete t q) fun b =>
        .leaf (insideGuess t a b)

private def outside : Protocol 3 :=
  .alice (fun a : Fin 3 => Matrix.single a a (1 : ℂ)) comp_complete fun a =>
    .bob (fun b : Fin 3 => Matrix.single b b (1 : ℂ)) comp_complete fun b =>
      .alice coinK coin_complete fun z => .leaf (outsideGuess a b z)

private def T : Protocol 3 :=
  .alice pairK pair_complete fun t =>
    .bob (splitK t) (split_complete t) fun z => if z = 0 then inside t else outside

private lemma diagonal_score (i : Fin 3) (v : (Fin 3 × Fin 3 → ℂ)) : score (i,i) T v = 0 := by
  fin_cases i <;>
    simp [T, inside, outside, score, insideGuess, outsideGuess,
      Fin.sum_univ_succ, Fin.ext_iff, -Fin.val_eq_zero_iff]

private lemma inv_sqrt : (Real.sqrt 2 : ℂ)⁻¹ = (c:ℂ) := by simp [c]

private lemma cross_score (i j : Fin 3) (hij : i ≠ j) : score (i,j) T (phi (i,j)) = 3/4 := by
  fin_cases i <;> fin_cases j
  all_goals simp [Fin.ext_iff, -Fin.val_eq_zero_iff] at hij
  all_goals
    simp [T, inside, outside, score, insideGuess, outsideGuess,
      Fin.sum_univ_succ, Fin.ext_iff, -Fin.val_eq_zero_iff]
  all_goals
  simp [insideGuess, outsideGuess,
    Fin.sum_univ_succ, Fin.ext_iff, -Fin.val_eq_zero_iff,
    actA, actB, mass, Fintype.sum_prod_type, phi, Pi.single_apply,
    pairK, splitK, coinK, Matrix.diagonal, Matrix.single, basisK, Matrix.vecMulVec, bra, phase,
    div_eq_mul_inv, inv_sqrt, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  all_goals ring_nf
  all_goals rw [show c^6 = (c*c)^3 by ring, show c^10 = (c*c)^5 by ring]
  all_goals norm_num [c_sq]

private lemma success_T : success 3 T = 1/2 := by
  unfold success
  rw [Fintype.sum_prod_type]
  simp [Fin.sum_univ_succ, cross_score, diagonal_score,
    Fin.ext_iff, -Fin.val_eq_zero_iff]
  norm_num

private lemma lower_lt_half (n : ℕ) (hn : 3 ≤ n) : lower n < 1/2 := by
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < (n:ℝ)-2 := by linarith
  have hd : 0 < 2*(n:ℝ)^2 := by positivity
  unfold lower
  exact sub_lt_self _ (div_pos hp hd)

theorem result : ¬ claim := by
  intro h
  have bad : success 3 T ≤ optLOCC 3 :=
    le_csSup (success_bddAbove 3) (Set.mem_range_self T)
  rw [success_T, h 3 (by decide)] at bad
  exact (not_le_of_gt (lower_lt_half 3 (by decide))) bad

end D5.S3.Quantum.Measurement.FourierLDOILOCCRefutation
