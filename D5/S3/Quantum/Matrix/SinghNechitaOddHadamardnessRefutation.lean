/- GID: D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation.claim; result=D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation.result; claim=D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation.claim
   digest: Order nine obstructs the conjectured odd-order minimum of Hadamardness. -/

import D5.S3.Factorization.CubeGapFiveNoSquare
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Vec

/-! The sign-matrix Hadamardness conjecture of Singh and Nechita,
arXiv:2112.11123v1, equation `eq:Hada_measure` and the conjecture following its table.
The integer trace equals the source's real trace for real sign matrices.
admission_basis: open-problem-resolution
-/

open Matrix
open scoped BigOperators

set_option linter.style.longLine false

namespace D5.S3.Quantum.Matrix.SinghNechitaOddHadamardnessRefutation

/-- Every entry is one of the two real signs, represented exactly as integers. -/
def IsSignMatrix {d : ℕ} (c : Matrix (Fin d) (Fin d) ℤ) : Prop :=
  ∀ i j, c i j = 1 ∨ c i j = -1

/-- The trace of the square of the row Gram matrix. -/
def hadamardness {d : ℕ} (c : Matrix (Fin d) (Fin d) ℤ) : ℤ :=
  Matrix.trace ((c * cᵀ) * (c * cᵀ))

/-- In every odd order the stated value is attained and is a lower bound. -/
def claim : Prop :=
  ∀ d : ℕ, Odd d →
    ∃ c : Matrix (Fin d) (Fin d) ℤ,
      IsSignMatrix c ∧ hadamardness c = ((d ^ 3 + d * (d - 1) : ℕ) : ℤ) ∧
      ∀ b : Matrix (Fin d) (Fin d) ℤ, IsSignMatrix b →
        ((d ^ 3 + d * (d - 1) : ℕ) : ℤ) ≤ hadamardness b

private lemma hadamardness_sum {d : ℕ} (c : Matrix (Fin d) (Fin d) ℤ) :
    hadamardness c = ∑ i, ∑ j, (c * cᵀ) i j ^ 2 := by
  calc
    hadamardness c = (c * cᵀ).vec ⬝ᵥ (c * cᵀ).vec := by
      change Matrix.trace ((c * cᵀ) * (c * cᵀ)) = _
      simpa only [(Matrix.isSymm_mul_transpose_self c).eq]
        using (Matrix.vec_dotProduct_vec (c * cᵀ) (c * cᵀ)).symm
    _ = _ := by
      simp only [dotProduct, Matrix.vec, Fintype.sum_prod_type, pow_two]
      exact Finset.sum_comm

private lemma gram_diag (c : Matrix (Fin 9) (Fin 9) ℤ) (hc : IsSignMatrix c)
    (i : Fin 9) : (c * cᵀ) i i = 9 := by
  simp only [mul_apply, transpose_apply]
  calc
    _ = ∑ _ : Fin 9, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro k _
      simpa only [pow_two] using (sq_eq_one_iff.mpr (hc i k))
    _ = 9 := by norm_num

private lemma gram_odd (c : Matrix (Fin 9) (Fin 9) ℤ) (hc : IsSignMatrix c)
    (i j : Fin 9) : ((c * cᵀ) i j : ZMod 2) = 1 := by
  simp only [mul_apply, transpose_apply, Int.cast_sum, Int.cast_mul]
  calc
    _ = ∑ _ : Fin 9, (1 : ZMod 2) := by
      apply Finset.sum_congr rfl
      intro k _
      rcases hc i k with h | h <;> rcases hc j k with h2 | h2 <;>
        rw [h, h2] <;> norm_num <;> decide
    _ = 1 := by norm_num; decide

private lemma equality_forces_unit (c : Matrix (Fin 9) (Fin 9) ℤ)
    (hc : IsSignMatrix c) (he : hadamardness c = 801) :
    ∀ i j, i ≠ j → (c * cᵀ) i j = 1 ∨ (c * cᵀ) i j = -1 := by
  have hle (i j : Fin 9) : (if i = j then 81 else 1 : ℤ) ≤ (c * cᵀ) i j ^ 2 := by
    by_cases hij : i = j
    · subst j
      rw [gram_diag c hc]
      norm_num
    · simp only [ite_eq_right hij]
      have hn : (c * cᵀ) i j ≠ 0 := by
        intro hz
        have hm := gram_odd c hc i j
        rw [hz] at hm
        norm_num at hm
      exact Int.add_one_le_iff.mpr (sq_pos_of_ne_zero hn)
  have hsum : (∑ i : Fin 9, ∑ j : Fin 9, (if i = j then 81 else 1 : ℤ)) = 801 := by
    norm_num [Fin.sum_univ_succ]
  have ht : (∑ i : Fin 9, ∑ j : Fin 9, (if i = j then 81 else 1 : ℤ)) =
      ∑ i, ∑ j, (c * cᵀ) i j ^ 2 := by
    rw [← hadamardness_sum, he, hsum]
  intro i j hij
  have hi := (Finset.sum_eq_sum_iff_of_le
    (fun i _ => Finset.sum_le_sum (fun j _ => hle i j))).mp ht i (Finset.mem_univ i)
  have hj := (Finset.sum_eq_sum_iff_of_le (fun j _ => hle i j)).mp hi j
    (Finset.mem_univ j)
  simp only [ite_eq_right hij] at hj
  exact (sq_eq_one_iff).mp hj.symm

private lemma gram_triangle (c : Matrix (Fin 9) (Fin 9) ℤ) (hc : IsSignMatrix c)
    (i j r : Fin 9) :
    ((c * cᵀ) i j : ZMod 4) =
      ((c * cᵀ) i r : ZMod 4) + ((c * cᵀ) r j : ZMod 4) - 1 := by
  simp only [mul_apply, transpose_apply, Int.cast_sum, Int.cast_mul]
  calc
    _ = ∑ k : Fin 9, ((c i k : ZMod 4) * (c r k : ZMod 4) +
        (c r k : ZMod 4) * (c j k : ZMod 4) - 1) := by
      apply Finset.sum_congr rfl
      intro k _
      rcases hc i k with hi | hi <;> rcases hc j k with hj | hj <;>
        rcases hc r k with hr | hr <;> rw [hi, hj, hr] <;> norm_num <;> decide
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      congr 1

private lemma normalize_gram (c : Matrix (Fin 9) (Fin 9) ℤ)
    (hc : IsSignMatrix c)
    (hu : ∀ i j, i ≠ j → (c * cᵀ) i j = 1 ∨ (c * cᵀ) i j = -1) :
    ∃ b : Matrix (Fin 9) (Fin 9) ℤ,
      b * bᵀ = (8 : ℤ) • 1 + Matrix.of (fun _ _ => 1) := by
  let s : Fin 9 → ℤ := fun i => if i = 0 then 1 else (c * cᵀ) i 0
  let b : Matrix (Fin 9) (Fin 9) ℤ := diagonal s * c
  have hs (i : Fin 9) : s i = 1 ∨ s i = -1 := by
    dsimp [s]
    split_ifs with hi
    · exact Or.inl rfl
    · exact hu i 0 hi
  have hb : IsSignMatrix b := by
    intro i k
    simp only [b, diagonal_mul]
    exact Int.isUnit_iff.mp ((Int.isUnit_iff.mpr (hs i)).mul (Int.isUnit_iff.mpr (hc i k)))
  have hg (i j : Fin 9) : (b * bᵀ) i j = s i * s j * (c * cᵀ) i j := by
    dsimp only [b]
    rw [transpose_mul, diagonal_transpose, mul_assoc, ← mul_assoc c]
    simp only [diagonal_mul, mul_diagonal]
    ring
  have hunit (i j : Fin 9) (hij : i ≠ j) :
      (b * bᵀ) i j = 1 ∨ (b * bᵀ) i j = -1 := by
    rw [hg]
    exact Int.isUnit_iff.mp (((Int.isUnit_iff.mpr (hs i)).mul
      (Int.isUnit_iff.mpr (hs j))).mul (Int.isUnit_iff.mpr (hu i j hij)))
  have hfirst (i : Fin 9) (hi : i ≠ 0) : (b * bᵀ) i 0 = 1 := by
    rw [hg]
    simp only [s, ite_eq_left rfl, ite_eq_right hi, mul_one]
    simpa only [pow_two] using (sq_eq_one_iff.mpr (hu i 0 hi))
  refine ⟨b, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    rw [gram_diag b hb]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, ite_true]
    norm_num
  · have he : (b * bᵀ) i j = 1 := by
      by_cases hi : i = 0
      · subst i
        rw [(Matrix.isSymm_mul_transpose_self b).apply j 0]
        exact hfirst j (Ne.symm hij)
      by_cases hj : j = 0
      · subst j
        exact hfirst i hi
      have hm := gram_triangle b hb i j 0
      rw [hfirst i hi, (Matrix.isSymm_mul_transpose_self b).apply j 0, hfirst j hj] at hm
      rcases hunit i j hij with he | he
      · exact he
      · rw [he] at hm
        norm_num at hm
        exact False.elim ((by decide : (-1 : ZMod 4) ≠ 1) hm)
    rw [he]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      ite_eq_right hij]
    norm_num

private lemma gram_impossible (b : Matrix (Fin 9) (Fin 9) ℤ)
    (hb : b * bᵀ = (8 : ℤ) • 1 + Matrix.of (fun _ _ => 1)) : False := by
  let a : Matrix (Fin 9) (Fin 9) (ZMod 3) := b.map (Int.castRingHom (ZMod 3))
  have ha : a * aᵀ = (2 : ZMod 3) •
      (1 + replicateCol Unit (fun _ : Fin 9 => (2 : ZMod 3)) *
        replicateRow Unit (fun _ : Fin 9 => (1 : ZMod 3))) := by
    have hm := congrArg (fun m : Matrix (Fin 9) (Fin 9) ℤ =>
      m.map (Int.castRingHom (ZMod 3))) hb
    rw [Matrix.map_mul] at hm
    change a * aᵀ = _ at hm
    rw [hm]
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.of_apply, Int.coe_castRingHom, Matrix.mul_apply, Matrix.replicateCol,
      Matrix.replicateRow, smul_eq_mul]
    by_cases hij : i = j <;>
      simp only [hij, ite_true, ite_false] <;> norm_num <;> decide
  have hd : (a.det) ^ 2 = 2 := by
    have hh := congrArg Matrix.det ha
    rw [det_mul, det_transpose, det_smul,
      det_one_add_replicateCol_mul_replicateRow] at hh
    rw [pow_two]
    exact hh.trans (by decide)
  have hn (z : ZMod 3) : z ^ 2 ≠ 2 := by
    intro hz
    apply D5.S3.Factorization.CubeGapFiveNoSquare.sq_mod_three_ne_two z.val
    simpa only [pow_two, ZMod.val_mul, ZMod.val_two_eq_two_mod] using congrArg ZMod.val hz
  exact hn a.det hd

theorem result : ¬ claim := by
  intro h
  obtain ⟨c, hc, he, _⟩ := h 9 (by decide)
  norm_num at he
  obtain ⟨b, hb⟩ := normalize_gram c hc (equality_forces_unit c hc he)
  exact gram_impossible b hb

end D5.S3.Quantum.Matrix.SinghNechitaOddHadamardnessRefutation
