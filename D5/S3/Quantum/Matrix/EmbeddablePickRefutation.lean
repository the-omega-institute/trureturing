/- GID: D5/S3/Quantum/Matrix/EmbeddablePickRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/EmbeddablePickRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/EmbeddablePickRefutation.claim; result=D5/S3/Quantum/Matrix/EmbeddablePickRefutation.result; claim=D5/S3/Quantum/Matrix/EmbeddablePickRefutation.claim
   digest: A positive Pick function sends an embeddable stochastic matrix to a negative entry. -/


/- Source: Johnson–Mondal–Tsatsomeros, arXiv:2609.06298v1, Remark 3.28 and Table 2, row 13.
   escape_witness: the Markov generator P − I, its closed-form exponential A,
     and the negative (1,4) entry of the positive Pick function 2z/(1+z) applied to A.
   Direct frozen dependencies:
     D5/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation (pickFun, pickCalc),
     statement_id: sha256:2e8482331b343bf50cafbf64429cf0adabb6db985cdf355408b4f6f4c3e96532.
   admission_basis: open-problem-resolution (#15994; Refuted)
   Per-declaration proof_shape and live consumers:
     IsStochastic: definition; consumers=IsEmbeddable, embeddable_A
     IsEmbeddable: definition; consumers=claim, embeddable_A, result
     claim: definition; consumer=result
     P: definition; consumers=powers, power_tail, exp_P, exp_generator, A_entries, embeddable_A
     Q: definition; consumers=powers, power_tail, exp_P, A_entries
     A: definition; consumers=exp_generator, A_entries, A_triangular, A_diagonal,
       embeddable_A, shifted_inverse, calc_entry, calc_negative, result
     C: definition; consumers=shifted_inverse, calc_entry
     cons_last: bind-only; consumers=powers, A_entries, A_triangular, A_diagonal,
       embeddable_A, shifted_inverse
     powers: bind-only; consumer=power_tail
     power_tail: content; consumer=exp_P
     scalar_tail: bind-only; consumer=exp_P
     exp_P: content; consumer=exp_generator
     exp_generator: content; consumer=embeddable_A
     A_entries: bind-only; consumers=A_triangular, A_diagonal, embeddable_A, shifted_inverse
     A_triangular: bind-only; consumers=embeddable_A, result
     A_diagonal: bind-only; consumers=embeddable_A, result
     embeddable_A: content; consumer=result
     shifted_inverse: bind-only; consumer=calc_entry
     pick_positive: bind-only; consumer=result
     calc_entry: bind-only; consumer=calc_negative
     calc_negative: bind-only; consumer=result
     result: content; designated refutation by explicit construction. -/

import D5.S3.Quantum.Matrix.InfinitelyDivisiblePickRefutation
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix
open D5.S3.Quantum.Matrix.InfinitelyDivisiblePickRefutation
namespace D5.S3.Quantum.Matrix.EmbeddablePickRefutation

/-- A nonnegative matrix with unit row sums. -/
def IsStochastic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧ ∀ i, ∑ j, A i j = 1
/-- Remark 3.28: a nonsingular stochastic matrix `A = exp B` with `B` essentially nonnegative and `B e = 0`. -/
def IsEmbeddable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsStochastic A ∧ IsUnit A.det ∧ ∃ B : Matrix (Fin n) (Fin n) ℝ,
    (∀ i j, i ≠ j → 0 ≤ B i j) ∧ (∀ i, ∑ j, B i j = 0) ∧ NormedSpace.exp B = A
/-- Preservation of embeddable matrices by Pick functions (Table 2, row 13), restricted as in the
row-12 module to Pick functions with finitely supported measure positive on `(0, ∞)` and to
upper-triangular matrices with positive diagonal (spectrum inside `(0, ∞)`); refuting this
restriction refutes the general preservation statement. -/
def claim : Prop :=
  ∀ (k : ℕ) (a b : ℝ) (t w : Fin k → ℝ), 0 ≤ b → (∀ i, 0 < t i) → (∀ i, 0 ≤ w i) →
    (∀ x : ℝ, 0 < x → 0 < pickFun a b t w x) →
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), IsEmbeddable A →
      (∀ i j, j < i → A i j = 0) → (∀ i, 0 < A i i) →
      IsEmbeddable (pickCalc a b t w A)

private def P : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,1,0,0; 0,0,1,0; 0,0,0,1; 0,0,0,1]
private def Q : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,0,0,1; 0,0,0,1; 0,0,0,1; 0,0,0,1]
private def A : Matrix (Fin 4) (Fin 4) ℝ :=
  Real.exp (-1) • (1 + P + (1/2 : ℝ) • P^2 + (Real.exp 1 - 5/2) • Q)

private lemma cons_last (a : ℝ) (v : Fin 3 → ℝ) :
    Matrix.vecCons a v (3 : Fin 4) = v 2 := rfl

private lemma powers : P^3 = Q ∧ Q * P = Q := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [P, Q, pow_succ, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four,
      Matrix.cons_val_succ', Matrix.cons_val_zero', Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.ext_iff, Fin.reduceFinMk, cons_last]

private lemma power_tail (k : ℕ) : P^(k+3) = Q := by
  induction k with
  | zero => simpa using powers.1
  | succ k ih => rw [show k+1+3 = (k+3)+1 by omega, pow_succ, ih, powers.2]

private lemma scalar_tail : (∑' k : ℕ, ((k+3).factorial : ℝ)⁻¹) = Real.exp 1 - 5/2 := by
  have hs : Summable (fun k : ℕ => (k.factorial : ℝ)⁻¹) := by
    simpa using Real.summable_pow_div_factorial 1
  have h := hs.sum_add_tsum_nat_add 3
  have he : (∑' k : ℕ, (k.factorial : ℝ)⁻¹) = Real.exp 1 := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
    simp
  rw [he] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

private lemma exp_P : NormedSpace.exp P =
    1 + P + (1/2 : ℝ) • P^2 + (Real.exp 1 - 5/2) • Q := by
  open scoped Matrix.Norms.Operator in
    have hs := NormedSpace.expSeries_summable' (𝕂 := ℝ) P
    rw [NormedSpace.exp_eq_tsum ℝ]
    dsimp only
    rw [← hs.sum_add_tsum_nat_add 3]
    simp_rw [power_tail]
    have ht : Summable (fun k : ℕ => ((k+3).factorial : ℝ)⁻¹) := by
      have h : Summable (fun k : ℕ => (k.factorial : ℝ)⁻¹) := by
        simpa using Real.summable_pow_div_factorial 1
      exact (summable_nat_add_iff 3).mpr h
    rw [ht.tsum_smul_const Q, scalar_tail]
    norm_num [Finset.sum_range_succ]

private lemma exp_generator : NormedSpace.exp (P - 1) = A := by
  have he : NormedSpace.exp (- (1 : Matrix (Fin 4) (Fin 4) ℝ)) =
      Real.exp (-1) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    have hd : -(1 : Matrix (Fin 4) (Fin 4) ℝ) = diagonal (fun _ => (-1 : ℝ)) := by
      ext i j; simp [Matrix.diagonal, Matrix.one_apply]; split_ifs <;> simp_all
    rw [hd, Matrix.exp_diagonal]
    ext i j
    simp [Matrix.diagonal, ← Real.exp_eq_exp_ℝ, Matrix.one_apply]
  rw [sub_eq_add_neg, Matrix.exp_add_of_commute P (-1) (by simp [Commute]), he,
    Matrix.mul_smul, mul_one, exp_P]
  rfl


private lemma A_entries : A =
    !![1 / Real.exp 1, 1 / Real.exp 1, 1 / (2 * Real.exp 1), 1 - 5 / (2 * Real.exp 1);
       0, 1 / Real.exp 1, 1 / Real.exp 1, 1 - 2 / Real.exp 1;
       0, 0, 1 / Real.exp 1, 1 - 1 / Real.exp 1;
       0, 0, 0, 1] := by
  have he := Real.exp_ne_zero 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, P, Q, pow_two, Real.exp_neg, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_four, Matrix.cons_val_succ', Matrix.cons_val_zero', Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      Fin.reduceFinMk, cons_last, Fin.ext_iff] <;> field_simp <;> ring

private lemma A_triangular : A.IsUpperTriangular := by
  intro i j h
  rw [A_entries]
  fin_cases i <;> fin_cases j <;> simp_all [Fin.reduceFinMk, cons_last]

private lemma A_diagonal : ∀ i, 0 < A i i := by
  intro i
  rw [A_entries]
  fin_cases i <;> norm_num [Fin.reduceFinMk, cons_last] <;> positivity

private lemma embeddable_A : IsEmbeddable A := by
  have he : 5/2 < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := Real.exp_pos 1
  refine ⟨⟨?_, ?_⟩, ?_, P - 1, ?_, ?_, exp_generator⟩
  · intro i j
    rw [A_entries]
    fin_cases i <;> fin_cases j <;>
      norm_num [Fin.reduceFinMk, cons_last]
    all_goals first | positivity | (apply (div_le_one (by positivity)).mpr; linarith) |
      (apply inv_le_one_of_one_le₀; linarith)
  · intro i
    rw [A_entries]
    simp only [Fin.sum_univ_four]
    fin_cases i <;>
      norm_num [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, cons_last] <;>
      field_simp <;> ring
  · rw [Matrix.det_of_isUpperTriangular A_triangular]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => ne_of_gt (A_diagonal i)))
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [P, Fin.ext_iff, Fin.reduceFinMk, cons_last]
  · intro i
    simp only [Fin.sum_univ_four, Matrix.sub_apply]
    fin_cases i <;>
      norm_num [P, Matrix.one_apply, Fin.ext_iff, Matrix.cons_val_two,
        Matrix.vecHead, Matrix.vecTail, cons_last]

private def C : Matrix (Fin 4) (Fin 4) ℝ :=
  let e := Real.exp 1
  let d := 1 + e
  !![e/d, -e/d^2, e*(1-e)/(2*d^3), (-e^3+2*e^2+2*e+1)/(2*d^3);
     0, e/d, -e/d^2, (1+2*e-e^2)/(2*d^2);
     0, 0, e/d, (1-e)/(2*d);
     0, 0, 0, 1/2]

private lemma shifted_inverse :
    (A + (1 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ))⁻¹ = C := by
  have he := Real.exp_ne_zero 1
  have hd : 1 + Real.exp 1 ≠ 0 := by positivity
  apply Matrix.inv_eq_right_inv
  rw [A_entries]
  unfold C
  generalize Real.exp 1 = e at *
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [C, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four,
      Fin.reduceFinMk, Matrix.cons_val_succ', Matrix.cons_val_zero', Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      cons_last, Fin.ext_iff] <;> field_simp <;> ring

private lemma pick_positive : ∀ x : ℝ, 0 < x →
    0 < pickFun 1 0 (![1] : Fin 1 → ℝ) (![1] : Fin 1 → ℝ) x := by
  intro x hx
  have hd : 0 < 1 + x := by positivity
  simp only [pickFun, Fin.sum_univ_one, Matrix.cons_val_zero, zero_mul, add_zero, one_mul]
  have he : 1 + (x - 1) / (1 + x) = 2 * x / (1 + x) := by
    rw [one_add_div (ne_of_gt hd)]
    congr 1
    ring
  rw [he]
  positivity

private lemma calc_entry :
    pickCalc 1 0 (![1] : Fin 1 → ℝ) (![1] : Fin 1 → ℝ) A 0 3 =
      ((Real.exp 1)^3 - 2*(Real.exp 1)^2 - 2*Real.exp 1 - 1) / (1+Real.exp 1)^3 := by
  simp only [pickCalc, Fin.sum_univ_one, Matrix.cons_val_zero]
  rw [shifted_inverse]
  have hc : C 0 3 = (-(Real.exp 1)^3 + 2*(Real.exp 1)^2 + 2*Real.exp 1 + 1) /
      (2*(1+Real.exp 1)^3) := rfl
  simp only [one_smul, zero_smul, add_zero, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hc]
  have hd : 1 + Real.exp 1 ≠ 0 := by positivity
  generalize Real.exp 1 = e at *
  norm_num [Matrix.one_apply, Fin.ext_iff]
  field_simp
  ring

private lemma calc_negative :
    pickCalc 1 0 (![1] : Fin 1 → ℝ) (![1] : Fin 1 → ℝ) A 0 3 < 0 := by
  rw [calc_entry]
  apply div_neg_of_neg_of_pos _ (by positivity)
  have hlo : 2.718 < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hhi : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
  have hsq : (Real.exp 1)^2 < 2.72^2 := by nlinarith
  have hc : (Real.exp 1)^3 < 2.72^3 := by
    nlinarith [mul_pos (sub_pos.mpr hhi) (by positivity : 0 < (Real.exp 1)^2)]
  nlinarith [sq_nonneg (Real.exp 1 - 2.718)]

theorem result : ¬ claim := by
  intro h
  have hout := h 1 1 0 ![1] ![1] (by norm_num)
    (by intro i; fin_cases i; norm_num)
    (by intro i; fin_cases i; norm_num) pick_positive 4 A embeddable_A
    A_triangular A_diagonal
  exact (not_le_of_gt calc_negative) (hout.1.1 0 3)

end D5.S3.Quantum.Matrix.EmbeddablePickRefutation
