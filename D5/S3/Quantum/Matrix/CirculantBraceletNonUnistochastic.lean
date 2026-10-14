/- GID: D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic.claim; result=D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic.result; claim=D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic.claim
   digest: A circulant bracelet matrix of order twelve is not unistochastic. -/

/- open-problem-resolution (#16299; Refuted)

result
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#16299; Refuted)
  Direct frozen dependencies:
    D5/S3/Weil/ZetaLinear/VonNeumann.normSqMatrix
    statement_id: sha256:e52dbe98c1d31846023642a54bf054704c393626b7a8169c76de496f1c932bea

All private theorem and lemma declarations are bind-only, with consumers:
  b_entry: b_doubly_stochastic, sqrt_product, unitary_zero_iff, unitary_self_product.
  b_circulant: result.
  row_card, col_card: b_doubly_stochastic.
  b_doubly_stochastic: b_bracelet.
  column_overlap, row_overlap, sqrt_product, constant_bracelet: b_bracelet.
  b_bracelet: result.
  overlap_11, overlap_2, t_support: b_not_unistochastic.
  overlap_06: column_sum_reduce.
  unitary_zero_iff: row_sum_reduce, column_sum_reduce, b_not_unistochastic.
  unitary_self_product, row_orthogonal, column_orthogonal, row_sum_reduce,
    column_sum_reduce, two_term_ratio: b_not_unistochastic.
  b_not_unistochastic: result.
Only unitary_zero_iff, unitary_self_product, row_sum_reduce, column_sum_reduce,
b_not_unistochastic and result use the above frozen definition after inlining
same-module helpers; the other private proofs have no direct frozen dependency.
No escape witness is asserted for any declaration.

The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).

The source predicates use Matrix.circulant, doublyStochastic and the frozen
RHLinalg.normSqMatrix directly. The private matrix B is constructed by
Matrix.circulant; b_entry gives the offset description used in the inequalities.
There is no separate squared-norm matrix or support-decidability instance.
The entries are 1/6 at offsets 0, 1, 3, 4, 6 and 9. Row orthogonality forces
parallel restrictions of columns 0, 3 and 6 on rows 0, 3, 6 and 9, contradicting
column orthogonality.
-/
import D5.S3.Weil.ZetaLinear.VonNeumann
import Mathlib.LinearAlgebra.Matrix.Circulant



noncomputable section
open Matrix Finset
namespace D5.S3.Quantum.Matrix.CirculantBraceletNonUnistochastic

def IsCirculant {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∃ v : Fin d → ℝ, B = Matrix.circulant v

def IsUnistochastic {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∃ U ∈ Matrix.unitaryGroup (Fin d) ℂ, B = RHLinalg.normSqMatrix U

def IsBracelet {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  B ∈ doublyStochastic ℝ (Fin d) ∧
  (∀ k l : Fin d, k ≠ l →
    2 * (⨆ j, √(B j k * B j l)) ≤ ∑ j, √(B j k * B j l)) ∧
  (∀ j k : Fin d, j ≠ k →
    2 * (⨆ l, √(B j l * B k l)) ≤ ∑ l, √(B j l * B k l))

def claim : Prop := ∀ d : ℕ, 4 < d → ∀ B : Matrix (Fin d) (Fin d) ℝ,
  IsCirculant B → IsBracelet B → IsUnistochastic B

private def S : Finset (Fin 12) := {0, 1, 3, 4, 6, 9}
private def B : Matrix (Fin 12) (Fin 12) ℝ :=
  Matrix.circulant (fun k => if -k ∈ S then 1/6 else 0)

private lemma b_entry (i j : Fin 12) : B i j = if j - i ∈ S then 1/6 else 0 := by
  simp only [B, Matrix.circulant_apply, neg_sub]

private theorem b_circulant : IsCirculant B := by
  refine ⟨fun k => if -k ∈ S then 1/6 else 0, ?_⟩
  rfl

private lemma row_card (i : Fin 12) : (univ.filter (fun j => j - i ∈ S)).card = 6 := by
  revert i
  decide +kernel

private lemma col_card (j : Fin 12) : (univ.filter fun i => (j - i ∈ S)).card = 6 := by
  revert j
  decide +kernel

private theorem b_doubly_stochastic : B ∈ doublyStochastic ℝ (Fin 12) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simp only [b_entry]
    split <;> norm_num
  · intro i
    simp only [b_entry, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, row_card]
    norm_num
  · intro j
    simp only [b_entry, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, col_card]
    norm_num

private theorem column_overlap (k l : Fin 12) (h : k ≠ l) :
    2 ≤ (univ.filter fun j => (k - j ∈ S) ∧ (l - j ∈ S)).card := by
  revert k l
  decide +kernel

private theorem row_overlap (j k : Fin 12) (h : j ≠ k) :
    2 ≤ (univ.filter fun l => (l - j ∈ S) ∧ (l - k ∈ S)).card := by
  revert j k
  decide +kernel

private lemma sqrt_product (i j k l : Fin 12) :
    √(B i j * B k l) = if (j - i ∈ S) ∧ (l - k ∈ S) then 1/6 else 0 := by
  by_cases h : (j - i ∈ S) <;> by_cases h' : (l - k ∈ S) <;>
    simp [b_entry, h, h']

private lemma constant_bracelet {n : Type*} [Fintype n] [Nonempty n]
    (p : n → Prop) [DecidablePred p] (h : 2 ≤ (univ.filter p).card) :
    2 * (⨆ j, if p j then (1:ℝ)/6 else 0) ≤
      ∑ j, if p j then (1:ℝ)/6 else 0 := by
  have hmax : (⨆ j, if p j then (1:ℝ)/6 else 0) ≤ 1/6 := by
    apply ciSup_le
    intro j
    split <;> norm_num
  have hsum : (∑ j, if p j then (1:ℝ)/6 else 0) =
      ((univ.filter p).card : ℝ) * (1/6) := by
    simp [← Finset.sum_filter]
  rw [hsum]
  have hcard : (2:ℝ) ≤ ((univ.filter p).card : ℝ) := by exact_mod_cast h
  nlinarith

private theorem b_bracelet : IsBracelet B := by
  refine ⟨b_doubly_stochastic, ?_, ?_⟩
  · intro k l h
    simp_rw [sqrt_product]
    exact constant_bracelet _ (column_overlap k l h)
  · intro j k h
    simp_rw [sqrt_product]
    exact constant_bracelet _ (row_overlap j k h)

private def T : Finset (Fin 12) := {0, 3, 6, 9}

private lemma overlap_11 : ∀ r : Fin 12, r ∈ T → ∀ c : Fin 12,
    ((c - r ∈ S) ∧ (c - 11 ∈ S)) ↔ c ∈ ({0,3} : Finset (Fin 12)) := by
  decide +kernel

private lemma overlap_2 : ∀ r : Fin 12, r ∈ T → ∀ c : Fin 12,
    ((c - r ∈ S) ∧ (c - 2 ∈ S)) ↔ c ∈ ({3,6} : Finset (Fin 12)) := by
  decide +kernel

private lemma overlap_06 : ∀ r : Fin 12, ((0 - r ∈ S) ∧ (6 - r ∈ S)) ↔ r ∈ T := by
  decide +kernel

private lemma t_support : ∀ r : Fin 12, r ∈ T → (0 - r ∈ S) := by
  decide +kernel

private lemma unitary_zero_iff {U : Matrix (Fin 12) (Fin 12) ℂ}
    (hB : B = RHLinalg.normSqMatrix U) (i j : Fin 12) :
    U i j = 0 ↔ ¬ (j - i ∈ S) := by
  have he : ‖U i j‖ ^ 2 = B i j := by
    rw [hB]
    rfl
  by_cases hs : (j - i ∈ S)
  · simp only [hs, not_true_eq_false, iff_false]
    intro hz
    rw [hz, norm_zero, zero_pow (by decide), b_entry, if_pos hs] at he
    norm_num at he
  · simp only [hs, not_false_eq_true, iff_true]
    rw [b_entry, if_neg hs] at he
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (U i j)])

private lemma unitary_self_product {U : Matrix (Fin 12) (Fin 12) ℂ}
    (hB : B = RHLinalg.normSqMatrix U) (i j : Fin 12) (hs : (j - i ∈ S)) :
    star (U i j) * U i j = (1:ℂ)/6 := by
  have he : ‖U i j‖ ^ 2 = (1:ℝ)/6 := by
    change RHLinalg.normSqMatrix U i j = _
    rw [← hB, b_entry, if_pos hs]
  calc
    star (U i j) * U i j = ((‖U i j‖^2 : ℝ) : ℂ) := by
      simpa only [Complex.star_def, Complex.ofReal_pow] using Complex.conj_mul' (U i j)
    _ = (1:ℂ)/6 := by simpa using congrArg Complex.ofReal he

private lemma row_orthogonal {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (i j : n) (hij : i ≠ j) : ∑ c, U i c * star (U j c) = 0 := by
  have h := congrArg (fun A : Matrix n n ℂ => A i j) (Unitary.mul_star_self_of_mem hU)
  simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, hij] using h

private lemma column_orthogonal {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (i j : n) (hij : i ≠ j) : ∑ r, star (U r i) * U r j = 0 := by
  have h := congrArg (fun A : Matrix n n ℂ => A i j) (Unitary.star_mul_self_of_mem hU)
  simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, hij] using h

private lemma row_sum_reduce {U : Matrix (Fin 12) (Fin 12) ℂ}
    (hB : B = RHLinalg.normSqMatrix U) (i j : Fin 12)
    (s : Finset (Fin 12)) (hs : ∀ c, ((c - i ∈ S) ∧ (c - j ∈ S)) ↔ c ∈ s) :
    (∑ c, U i c * star (U j c)) = ∑ c ∈ s, U i c * star (U j c) := by
  symm
  apply Finset.sum_subset (Finset.subset_univ s)
  intro c _ hc
  have h := mt (hs c).mp hc
  rcases not_and_or.mp h with h | h
  · rw [(unitary_zero_iff hB i c).mpr h, zero_mul]
  · rw [(unitary_zero_iff hB j c).mpr h, star_zero, mul_zero]

private lemma column_sum_reduce {U : Matrix (Fin 12) (Fin 12) ℂ}
    (hB : B = RHLinalg.normSqMatrix U) :
    (∑ r, star (U r 0) * U r 6) = ∑ r ∈ T, star (U r 0) * U r 6 := by
  symm
  apply Finset.sum_subset (Finset.subset_univ T)
  intro r _ hr
  have h := mt (overlap_06 r).mp hr
  rcases not_and_or.mp h with h | h
  · rw [(unitary_zero_iff hB r 0).mpr h, star_zero, zero_mul]
  · rw [(unitary_zero_iff hB r 6).mpr h, mul_zero]

private lemma two_term_ratio (x y a b : ℂ) (hb : b ≠ 0)
    (h : x * a + y * b = 0) : y = -(a / b) * x := by
  have hy : y = -(x * a) / b := (eq_div_iff hb).2 (by linear_combination h)
  rw [hy]
  ring

private theorem b_not_unistochastic : ¬ IsUnistochastic B := by
  rintro ⟨U, hU, hB⟩
  have hnz (i j : Fin 12) (hs : (j - i ∈ S)) : U i j ≠ 0 := by
    intro hz
    exact (unitary_zero_iff hB i j).mp hz hs
  have h110 : U 11 0 ≠ 0 := hnz 11 0 (by decide)
  have h113 : U 11 3 ≠ 0 := hnz 11 3 (by decide)
  have h23 : U 2 3 ≠ 0 := hnz 2 3 (by decide)
  have h26 : U 2 6 ≠ 0 := hnz 2 6 (by decide)
  let lam : ℂ := -(star (U 11 0) / star (U 11 3))
  let mu : ℂ := -(star (U 2 3) / star (U 2 6))
  have hlam : lam ≠ 0 := by
    exact neg_ne_zero.mpr (div_ne_zero (by simpa using h110) (by simpa using h113))
  have hmu : mu ≠ 0 := by
    exact neg_ne_zero.mpr (div_ne_zero (by simpa using h23) (by simpa using h26))
  have h13 (r : Fin 12) (hr : r ∈ T) : U r 3 = lam * U r 0 := by
    have hne : r ≠ 11 := by
      have h : ∀ r : Fin 12, r ∈ T → r ≠ 11 := by decide +kernel
      exact h r hr
    have h := row_orthogonal hU r 11 hne
    rw [row_sum_reduce hB r 11 {0,3} (overlap_11 r hr)] at h
    simp only [Finset.sum_insert (by decide : (0:Fin 12) ∉ ({3}:Finset (Fin 12))),
      Finset.sum_singleton] at h
    exact two_term_ratio _ _ _ _ (by simpa using h113) h
  have h36 (r : Fin 12) (hr : r ∈ T) : U r 6 = mu * U r 3 := by
    have hne : r ≠ 2 := by
      have h : ∀ r : Fin 12, r ∈ T → r ≠ 2 := by decide +kernel
      exact h r hr
    have h := row_orthogonal hU r 2 hne
    rw [row_sum_reduce hB r 2 {3,6} (overlap_2 r hr)] at h
    simp only [Finset.sum_insert (by decide : (3:Fin 12) ∉ ({6}:Finset (Fin 12))),
      Finset.sum_singleton] at h
    exact two_term_ratio _ _ _ _ (by simpa using h26) h
  have hcol := column_orthogonal hU (0:Fin 12) 6 (by decide)
  rw [column_sum_reduce hB] at hcol
  have hsum : (∑ r ∈ T, star (U r 0) * U r 6) =
      mu * lam * ((4:ℂ)/6) := by
    calc
      (∑ r ∈ T, star (U r 0) * U r 6) =
          ∑ r ∈ T, mu * lam * ((1:ℂ)/6) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [h36 r hr, h13 r hr]
        calc
          star (U r 0) * (mu * (lam * U r 0)) =
              mu * lam * (star (U r 0) * U r 0) := by ring
          _ = mu * lam * ((1:ℂ)/6) := by
            rw [unitary_self_product hB r 0 (t_support r hr)]
      _ = mu * lam * ((4:ℂ)/6) := by
        have hcard : T.card = 4 := by decide +kernel
        simp only [Finset.sum_const, nsmul_eq_mul, hcard]
        ring
  rw [hsum] at hcol
  exact (mul_ne_zero (mul_ne_zero hmu hlam) (by norm_num)) hcol

theorem result : ¬ claim := by
  intro h
  exact b_not_unistochastic (h 12 (by norm_num) B b_circulant b_bracelet)

end D5.S3.Quantum.Matrix.CirculantBraceletNonUnistochastic
