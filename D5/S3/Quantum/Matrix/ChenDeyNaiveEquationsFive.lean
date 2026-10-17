/- GID: D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.claim; result=D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.result; claim=D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.claim
   digest: The naive orthostochastic equations are insufficient at order five. -/

/- open-problem-resolution (#17606; Refuted)

result
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#17606; Refuted)
  Direct frozen dependencies:
    D5/S3/Weil/ZetaLinear/VonNeumann.normSqMatrix
    statement_id: sha256:e52dbe98c1d31846023642a54bf054704c393626b7a8169c76de496f1c932bea

All twelve private lemmas have proof_shape: bind-only and escape_witness: none.
Consumers:
  b_entry: b_doubly_stochastic, sqrt_product, b_naive, lift_entry_sq.
  b_doubly_stochastic: result.
  sqrt_four, sqrt_sixteen: sqrt_product.
  sqrt_product, extra_distinct: b_naive.
  b_naive: result.
  lift_entry_sq: lift_entry_integer.
  lift_entry_integer, scaled_mul_transpose, seventeen_pow_five_not_square:
    b_not_orthostochastic.
  b_not_orthostochastic: result.
After inlining same-module helpers, lift_entry_sq, lift_entry_integer,
b_not_orthostochastic and result use the frozen normSqMatrix definition above;
the other private lemmas have Direct frozen dependencies: none.
The public definitions IsOrthostochastic and claim also use that definition;
the other definitions have Direct frozen dependencies: none.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The five source predicates are those of issue #17606. The entrywise square
uses RHLinalg.normSqMatrix, and the Birkhoff polytope uses doublyStochastic.
For every distinct row or column pair of B, the radical terms are
2/17, 2/17, 4/17, 4/17, 4/17. Three positive signs and two negative signs
cancel them. A global real orthogonal lift, scaled by sqrt 17, would have
integer entries and determinant squared equal to 17^5, a nonsquare.
-/
import D5.S3.Weil.ZetaLinear.VonNeumann
import Mathlib.Tactic.NormNum.IsSquare

noncomputable section

open Matrix Finset

namespace D5.S3.Quantum.Matrix.ChenDeyNaiveEquationsFive

/-- `B` is orthostochastic: the entrywise square of a real orthogonal matrix (Chen–Dey, arXiv:2001.10691, Section 1). -/
def IsOrthostochastic {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ U ∈ Matrix.orthogonalGroup (Fin n) ℝ, B = RHLinalg.normSqMatrix U

/-- The column naive condition `C_{i,j} = 0`: some signs make the entrywise square roots of columns `i` and `j`
orthogonal (the equivalent form stated after Definition 4). -/
def ColumnNaive {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : Prop :=
  ∃ ε : Fin n → ℝ, (∀ k, ε k = 1 ∨ ε k = -1) ∧ ∑ k, ε k * Real.sqrt (B k i * B k j) = 0

/-- The row naive condition `R_{i,j} = 0`, by transposing indices. -/
def RowNaive {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : Prop :=
  ∃ ε : Fin n → ℝ, (∀ k, ε k = 1 ∨ ε k = -1) ∧ ∑ k, ε k * Real.sqrt (B i k * B j k) = 0

/-- `B` satisfies every naive equation `C_{i,j}, R_{i,j}` (`i < j`). -/
def SatisfiesNaive {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, i < j → ColumnNaive B i j ∧ RowNaive B i j

/-- Question 5 for `n = 5`: every doubly stochastic `5 × 5` matrix satisfying the naive equations is orthostochastic. -/
def claim : Prop :=
  ∀ B : Matrix (Fin 5) (Fin 5) ℝ, B ∈ doublyStochastic ℝ (Fin 5) → SatisfiesNaive B → IsOrthostochastic B


def B : Matrix (Fin 5) (Fin 5) ℝ :=
  (1 / 17 : ℝ) • ((4 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ)) -
    (3 : ℝ) • (1 : Matrix (Fin 5) (Fin 5) ℝ))

private lemma b_entry (i j : Fin 5) : B i j = if i = j then 1 / 17 else 4 / 17 := by
  simp only [B, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply,
    Matrix.one_apply, smul_eq_mul]
  split <;> norm_num

private lemma b_doubly_stochastic : B ∈ doublyStochastic ℝ (Fin 5) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [b_entry]
    split <;> norm_num
  · intro i
    have he (j : Fin 5) : B i j = 4 / 17 - if i = j then 3 / 17 else 0 := by
      rw [b_entry]
      split <;> norm_num
    simp_rw [he]
    norm_num [Finset.sum_sub_distrib]
  · intro j
    have he (i : Fin 5) : B i j = 4 / 17 - if i = j then 3 / 17 else 0 := by
      rw [b_entry]
      split <;> norm_num
    simp_rw [he]
    norm_num [Finset.sum_sub_distrib]

private lemma sqrt_four : Real.sqrt (4 / 289 : ℝ) = 2 / 17 := by
  apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
  norm_num

private lemma sqrt_sixteen : Real.sqrt (16 / 289 : ℝ) = 4 / 17 := by
  apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
  norm_num

private lemma sqrt_product (i j k : Fin 5) (hij : i ≠ j) :
    Real.sqrt (B k i * B k j) = if k = i ∨ k = j then 2 / 17 else 4 / 17 := by
  by_cases hki : k = i
  · have hkj : k ≠ j := fun h => hij (hki.symm.trans h)
    rw [if_pos (Or.inl hki), b_entry, b_entry, if_pos hki, if_neg hkj]
    convert sqrt_four using 1 <;> norm_num
  · by_cases hkj : k = j
    · rw [if_pos (Or.inr hkj), b_entry, b_entry, if_neg hki, if_pos hkj]
      convert sqrt_four using 1 <;> norm_num
    · rw [if_neg (not_or.mpr ⟨hki, hkj⟩), b_entry, b_entry, if_neg hki, if_neg hkj]
      convert sqrt_sixteen using 1 <;> norm_num

private def extra (i j : Fin 5) : Fin 5 :=
  if i ≠ 0 ∧ j ≠ 0 then 0 else if i ≠ 1 ∧ j ≠ 1 then 1 else 2

private lemma extra_distinct (i j : Fin 5) : extra i j ≠ i ∧ extra i j ≠ j := by
  revert i j
  decide +kernel

private def signs (i j : Fin 5) (k : Fin 5) : ℝ :=
  if k = i ∨ k = j ∨ k = extra i j then 1 else -1

private lemma b_naive : SatisfiesNaive B := by
  intro i j hij
  have hc : ColumnNaive B i j := by
    refine ⟨signs i j, ?_, ?_⟩
    · intro k
      unfold signs
      split <;> simp
    · simp_rw [sqrt_product i j _ (ne_of_lt hij)]
      have hij' : i ≠ j := ne_of_lt hij
      obtain ⟨hei, hej⟩ := extra_distinct i j
      have he (k : Fin 5) :
          signs i j k * (if k = i ∨ k = j then 2 / 17 else 4 / 17) =
            -(4 / 17 : ℝ) + (if k = i then 6 / 17 else 0) +
              (if k = j then 6 / 17 else 0) +
              (if k = extra i j then 8 / 17 else 0) := by
        by_cases hki : k = i <;> by_cases hkj : k = j <;>
          by_cases hke : k = extra i j <;> simp_all [signs] <;> norm_num
      simp_rw [he]
      norm_num [Finset.sum_add_distrib]
  refine ⟨hc, ?_⟩
  simpa only [ColumnNaive, RowNaive, b_entry, eq_comm] using hc

private lemma lift_entry_sq {U : Matrix (Fin 5) (Fin 5) ℝ}
    (hB : B = RHLinalg.normSqMatrix U) (i j : Fin 5) :
    (Real.sqrt 17 * U i j) ^ 2 = if i = j then 1 else 4 := by
  have he : (U i j) ^ 2 = B i j := by
    have h := congrArg (fun A : Matrix (Fin 5) (Fin 5) ℝ => A i j) hB
    simpa only [RHLinalg.normSqMatrix, Matrix.of_apply, Real.norm_eq_abs,
      sq_abs] using h.symm
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 17), he, b_entry]
  split <;> norm_num

private lemma lift_entry_integer {U : Matrix (Fin 5) (Fin 5) ℝ}
    (hB : B = RHLinalg.normSqMatrix U) (i j : Fin 5) :
    ∃ z : ℤ, (z : ℝ) = Real.sqrt 17 * U i j ∧
      (if i = j then z = 1 ∨ z = -1 else z = 2 ∨ z = -2) := by
  have h := lift_entry_sq hB i j
  by_cases hij : i = j
  · simp only [if_pos hij] at h ⊢
    have hs : Real.sqrt 17 * U i j = 1 ∨ Real.sqrt 17 * U i j = -1 := by
      exact sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num at h ⊢; exact h)
    rcases hs with hs | hs
    · exact ⟨1, by simpa using hs.symm, Or.inl rfl⟩
    · exact ⟨-1, by simpa using hs.symm, Or.inr rfl⟩
  · simp only [if_neg hij] at h ⊢
    have hs : Real.sqrt 17 * U i j = 2 ∨ Real.sqrt 17 * U i j = -2 := by
      exact sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num at h ⊢; exact h)
    rcases hs with hs | hs
    · exact ⟨2, by simpa using hs.symm, Or.inl rfl⟩
    · exact ⟨-2, by simpa using hs.symm, Or.inr rfl⟩

private lemma scaled_mul_transpose {U : Matrix (Fin 5) (Fin 5) ℝ}
    (hU : U ∈ Matrix.orthogonalGroup (Fin 5) ℝ) :
    (Real.sqrt 17 • U) * (Real.sqrt 17 • U)ᵀ =
      (17 : ℝ) • (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 17),
    (Matrix.mem_orthogonalGroup_iff (Fin 5) ℝ).mp hU]

private lemma seventeen_pow_five_not_square : ¬ IsSquare (17 ^ 5 : ℤ) := by
  norm_num

private lemma b_not_orthostochastic : ¬ IsOrthostochastic B := by
  rintro ⟨U, hU, hB⟩
  choose z hz hsign using lift_entry_integer hB
  let Z : Matrix (Fin 5) (Fin 5) ℤ := z
  have hm : Z.map (fun z : ℤ => (z : ℝ)) = Real.sqrt 17 • U := by
    ext i j
    exact hz i j
  have hd : ((Z.det : ℝ)) ^ 2 = (17 : ℝ) ^ 5 := by
    have hdet := congrArg Matrix.det (scaled_mul_transpose hU)
    rw [Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_smul (1 : Matrix (Fin 5) (Fin 5) ℝ) (17 : ℝ), Matrix.det_one] at hdet
    simpa only [Int.cast_det, hm, pow_two, Fintype.card_fin, mul_one] using hdet
  have hzdet : Z.det ^ 2 = (17 : ℤ) ^ 5 := by exact_mod_cast hd
  exact seventeen_pow_five_not_square ⟨Z.det, by nlinarith [hzdet]⟩

theorem result : ¬ claim := by
  intro hc
  exact b_not_orthostochastic (hc B b_doubly_stochastic b_naive)

end D5.S3.Quantum.Matrix.ChenDeyNaiveEquationsFive
