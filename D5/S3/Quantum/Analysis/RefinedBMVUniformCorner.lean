/- GID: D5/S3/Quantum/Analysis/RefinedBMVUniformCorner
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMVUniformCorner
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The ordered scalar corner inequality for the refined BMV defect at every positive exponent. -/

import D5.S3.Quantum.Analysis.RefinedBMVDimThreeInteger
import D5.S3.Quantum.Schatten.CompoundMatrices
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The refined BMV scalar corner inequality for every positive exponent

The proof uses the triangular coefficient matrix from
a reverse Cauchy–Schwarz argument via the rectangular Cauchy–Binet theorem.
-/

open scoped BigOperators Matrix

noncomputable section

namespace RefinedBMV.DimThree

private def triangle (p : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (p + 1) ×ˢ Finset.range (p + 1)).filter fun ij => ij.1 + ij.2 ≤ p

private theorem mem_triangle {p : ℕ} {ij : ℕ × ℕ} :
    ij ∈ triangle p ↔ ij.1 + ij.2 ≤ p := by
  simp only [triangle, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

private theorem sum_triangle {R : Type*} [AddCommMonoid R] (p : ℕ) (f : ℕ × ℕ → R) :
    (∑ ij ∈ triangle p, f ij) =
      ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (p + 1 - i), f (i, j) := by
  rw [triangle, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.sum_filter]
  have h : (Finset.range (p + 1)).filter (fun j => i + j ≤ p) =
      Finset.range (p + 1 - i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    omega
  rw [h]

private theorem list_sum_range {R : Type*} [AddCommMonoid R] (n : ℕ) (f : ℕ → R) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  simp only [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range,
    Multiset.map_coe, Multiset.sum_coe]

private theorem sum_gaps {R : Type*} [AddCommMonoid R] (p : ℕ) (f : ℕ × ℕ × ℕ → R) :
    ((gaps p).map f).sum = ∑ ij ∈ triangle p, f (ij.1, ij.2, p - ij.1 - ij.2) := by
  have sum_flatMap (l : List ℕ) (g : ℕ → List R) :
      (l.flatMap g).sum = (l.map fun i => (g i).sum).sum := by
    induction l with
    | nil => rfl
    | cons i l ih => simp [List.flatMap_cons, List.sum_append, ih]
  rw [gaps, List.map_flatMap, sum_flatMap, list_sum_range, sum_triangle]
  simp_rw [List.map_map, Function.comp_apply, list_sum_range]

private theorem triangle_card (p : ℕ) : (triangle p).card = (p + 2).choose 2 := by
  calc
    _ = ∑ i ∈ Finset.range (p + 1), (p + 1 - i) := by
      simpa using sum_triangle p (fun _ => (1 : ℕ))
    _ = ∑ i ∈ Finset.range (p + 1), (i + 1) := by
      rw [← Finset.sum_range_reflect (fun i : ℕ => i + 1) (p + 1)]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      omega
    _ = _ := by simpa only [Nat.choose_one_right] using Nat.sum_range_add_choose p 1

/-- The number of ordered triples of gaps of total size `p`. -/
theorem gaps_length_eq_choose (p : ℕ) : (gaps p).length = (p + 2).choose 2 := by
  have h : (gaps p).length = (triangle p).card := by
    simpa [List.map_const', List.sum_replicate, nsmul_eq_mul] using
      sum_gaps p (fun _ => (1 : ℕ))
  exact h.trans (triangle_card p)

private def monomial (p : ℕ) (a x y : ℝ) (ij : ℕ × ℕ) : ℝ :=
  (a ^ 3) ^ ij.1 * (x ^ 3) ^ ij.2 * (y ^ 3) ^ (p - ij.1 - ij.2)

private def homogeneous (p : ℕ) (a x y : ℝ) : ℝ :=
  ∑ ij ∈ triangle p, monomial p a x y ij

private def correction (p : ℕ) (a x y : ℝ) : ℝ :=
  ((p + 2).choose 2 : ℝ) * (a * x * y) ^ p

private theorem defect_eq_sub (p : ℕ) (a x y : ℝ) :
    defect p a x y = homogeneous p a x y - correction p a x y := by
  simp only [defect, homogeneous, correction, gaps_length_eq_choose, sum_gaps, monomial]

private theorem homogeneous_swap (p : ℕ) (a x y : ℝ) :
    homogeneous p x a y = homogeneous p a x y := by
  unfold homogeneous
  refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro ij hij
    simpa [mem_triangle, add_comm] using hij
  · intro ij hij
    simpa [mem_triangle, add_comm] using hij
  · intro ij _
    exact Prod.swap_swap ij
  · intro ij _
    exact Prod.swap_swap ij
  · intro ij _
    simp only [monomial, Prod.fst_swap, Prod.snd_swap]
    rw [show p - ij.1 - ij.2 = p - ij.2 - ij.1 by omega, mul_comm ((x ^ 3) ^ ij.1)]

private theorem defect_swap_first (p : ℕ) (a x y : ℝ) : defect p x a y = defect p a x y := by
  simp only [defect_eq_sub, homogeneous_swap p a x y, correction, mul_comm x a]

private def rotate (p : ℕ) (ij : ℕ × ℕ) : ℕ × ℕ :=
  (ij.2, p - ij.1 - ij.2)

private theorem sum_rotate (p : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ ij ∈ triangle p, f (rotate p ij)) = ∑ ij ∈ triangle p, f ij := by
  refine Finset.sum_nbij' (rotate p) (fun ij => (p - ij.1 - ij.2, ij.1)) ?_ ?_ ?_ ?_ ?_
  · intro ij hij
    simp only [mem_triangle, rotate] at hij ⊢
    omega
  · intro ij hij
    simp only [mem_triangle] at hij ⊢
    omega
  · intro ij hij
    have h := mem_triangle.mp hij
    apply Prod.ext <;> simp only [rotate] <;> omega
  · intro ij hij
    have h := mem_triangle.mp hij
    apply Prod.ext <;> simp only [rotate] <;> omega
  · intro ij _
    rfl

private theorem correction_nonneg (p : ℕ) {a x y : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x)
    (hy : 0 ≤ y) : 0 ≤ correction p a x y := by
  unfold correction
  positivity

private theorem correction_le_homogeneous (p : ℕ) {a x y : ℝ}
    (ha : 0 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y) : correction p a x y ≤ homogeneous p a x y := by
  let base (ij : ℕ × ℕ) := a ^ ij.1 * x ^ ij.2 * y ^ (p - ij.1 - ij.2)
  have base_nonneg (ij : ℕ × ℕ) : 0 ≤ base ij := by dsimp [base]; positivity
  have cube (ij : ℕ × ℕ) : monomial p a x y ij = base ij ^ 3 := by
    simp only [monomial, base, mul_pow, ← pow_mul, Nat.mul_comm 3]
  have pointwise (ij : ℕ × ℕ) (hij : ij ∈ triangle p) :
      3 * (a * x * y) ^ p ≤ monomial p a x y ij + monomial p a x y (rotate p ij) +
        monomial p a x y (rotate p (rotate p ij)) := by
    have hprod : base ij * base (rotate p ij) * base (rotate p (rotate p ij)) =
        (a * x * y) ^ p := by
      obtain ⟨i, j⟩ := ij
      have h := mem_triangle.mp hij
      change i + j ≤ p at h
      let k := p - i - j
      have hk : i + j + k = p := by dsimp [k]; omega
      have hi : p - j - k = i := by omega
      have hj : p - k - i = j := by omega
      have hr : rotate p (j, k) = (k, i) := Prod.ext rfl hi
      rw [show rotate p (i, j) = (j, k) from rfl, hr]
      change (a ^ i * x ^ j * y ^ k) * (a ^ j * x ^ k * y ^ (p - j - k)) *
          (a ^ k * x ^ i * y ^ (p - k - i)) = _
      rw [hi, hj, mul_pow, mul_pow, ← hk]
      simp only [pow_add]
      ring
    let u := base ij
    let v := base (rotate p ij)
    let w := base (rotate p (rotate p ij))
    have hu : 0 ≤ u := base_nonneg _
    have hv : 0 ≤ v := base_nonneg _
    have hw : 0 ≤ w := base_nonneg _
    simp only [cube, ← hprod]
    change 3 * (u * v * w) ≤ u ^ 3 + v ^ 3 + w ^ 3
    apply sub_nonneg.mp
    calc
      0 ≤ (u + v + w) * ((u - v) ^ 2 + (v - w) ^ 2 + (w - u) ^ 2) / 2 := by positivity
      _ = _ := by ring
  have h := Finset.sum_le_sum pointwise
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_add_distrib] at h
  rw [sum_rotate p (fun ij => monomial p a x y (rotate p ij)),
    sum_rotate p (monomial p a x y), triangle_card] at h
  unfold correction homogeneous
  nlinarith only [h]

private def coefficients (p : ℕ) (y : ℝ) : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ :=
  Matrix.of fun i j => if i.val + j.val ≤ p then (y ^ 3) ^ (p - i.val - j.val) else 0

private def powers (p : ℕ) (u : Fin 2 → ℝ) : Matrix (Fin 2) (Fin (p + 1)) ℝ :=
  Matrix.of fun i j => (u i ^ 3) ^ j.val

private theorem compression_apply (p : ℕ) (u : Fin 2 → ℝ) (y : ℝ) (r s : Fin 2) :
    (powers p u * coefficients p y * (powers p u)ᵀ) r s = homogeneous p (u r) (u s) y := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, powers, coefficients, Matrix.of_apply,
    Finset.mul_sum]
  let entry (i j : ℕ) : ℝ :=
    (u r ^ 3) ^ i * ((if i + j ≤ p then (y ^ 3) ^ (p - i - j) else 0) * (u s ^ 3) ^ j)
  have hinner (i : Fin (p + 1)) :
      (∑ j : Fin (p + 1), entry i j) = ∑ j ∈ Finset.range (p + 1), entry i j :=
    Fin.sum_univ_eq_sum_range (entry i) (p + 1)
  change (∑ i : Fin (p + 1), ∑ j : Fin (p + 1), entry i j) = _
  simp_rw [hinner]
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range (p + 1), entry i j) (p + 1),
    homogeneous, triangle, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : i + j ≤ p
  · simp only [entry, monomial, Prod.fst, Prod.snd, if_pos hij]
    ring
  · simp [entry, hij]

private abbrev MinorIndices (p : ℕ) := {s : Finset (Fin (p + 1)) // s.card = 2}

private abbrev indices {p : ℕ} (s : MinorIndices p) : Fin 2 ↪o Fin (p + 1) :=
  s.1.orderEmbOfFin s.2

private def compressionTerm {p : ℕ} (F : Matrix (Fin 2) (Fin (p + 1)) ℝ)
    (M : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ) (t s : MinorIndices p) : ℝ :=
  (F.submatrix id (indices s)).det * (M.submatrix (indices s) (indices t)).det *
    (F.submatrix id (indices t)).det

private theorem compression_det {p : ℕ} (F : Matrix (Fin 2) (Fin (p + 1)) ℝ)
    (M : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ) :
    (F * M * Fᵀ).det = ∑ t : MinorIndices p, ∑ s : MinorIndices p, compressionTerm F M t s := by
  classical
  rw [cauchyBinet (F * M) Fᵀ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Matrix.submatrix_mul F M id id (indices t) Function.bijective_id,
    Matrix.submatrix_id_id, cauchyBinet, Finset.sum_mul]
  simp only [compressionTerm, Matrix.submatrix_submatrix, Function.id_comp, Function.comp_id,
    ← Matrix.transpose_submatrix, Matrix.det_transpose]

private theorem coefficients_minor_nonpos {p : ℕ} {y : ℝ} (hy : 0 ≤ y)
    (r c : Fin 2 ↪o Fin (p + 1)) :
    ((coefficients p y).submatrix r c).det ≤ 0 := by
  have hr : (r 0).val ≤ (r 1).val :=
    (r.strictMono (by decide : (0 : Fin 2) < 1)).le
  have hc : (c 0).val ≤ (c 1).val :=
    (c.strictMono (by decide : (0 : Fin 2) < 1)).le
  simp only [Matrix.det_fin_two, Matrix.submatrix_apply, coefficients, Matrix.of_apply]
  by_cases h : (r 1).val + (c 1).val ≤ p
  · have h00 : (r 0).val + (c 0).val ≤ p := by omega
    have h01 : (r 0).val + (c 1).val ≤ p := by omega
    have h10 : (r 1).val + (c 0).val ≤ p := by omega
    simp only [if_pos h, if_pos h00, if_pos h01, if_pos h10, sub_nonpos, ← pow_add]
    have he : (p - (r 0).val - (c 0).val) + (p - (r 1).val - (c 1).val) =
        (p - (r 0).val - (c 1).val) + (p - (r 1).val - (c 0).val) := by omega
    exact le_of_eq (congrArg (fun n : ℕ => (y ^ 3) ^ n) he)
  · simp only [if_neg h, mul_zero, zero_sub, neg_nonpos]
    split_ifs <;> positivity

private theorem powers_minor_nonneg {p : ℕ} {a x : ℝ} (ha : 0 ≤ a) (hax : a ≤ x)
    (c : Fin 2 ↪o Fin (p + 1)) :
    ((powers p ![a, x]).submatrix id c).det ≥ 0 := by
  have hc : (c 0).val ≤ (c 1).val :=
    (c.strictMono (by decide : (0 : Fin 2) < 1)).le
  have he : (c 1).val = (c 0).val + ((c 1).val - (c 0).val) := by omega
  have hx := ha.trans hax
  have hpow : (a ^ 3) ^ ((c 1).val - (c 0).val) ≤ (x ^ 3) ^ ((c 1).val - (c 0).val) :=
    pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ ha hax 3) _
  simp only [Matrix.det_fin_two, Matrix.submatrix_apply, powers, Matrix.of_apply, id_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [he]
  simp only [pow_add]
  calc
    0 ≤ (a ^ 3) ^ (c 0).val * (x ^ 3) ^ (c 0).val *
        ((x ^ 3) ^ ((c 1).val - (c 0).val) - (a ^ 3) ^ ((c 1).val - (c 0).val)) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hpow)
    _ = _ := by ring

private theorem homogeneous_det_bound {p : ℕ} (hp : 0 < p) {a x y : ℝ} (ha : 0 ≤ a)
    (hax : a ≤ x) (hy : 0 ≤ y) :
    homogeneous p a a y * homogeneous p x x y - homogeneous p a x y ^ 2 ≤
      -((x ^ 3) ^ p - (a ^ 3) ^ p) ^ 2 := by
  classical
  let F := powers p ![a, x]
  let M := coefficients p y
  let last := Fin.last p
  have h0last : (0 : Fin (p + 1)) < last := by simpa [last, Fin.lt_def] using hp
  let ends : MinorIndices p := ⟨{0, last}, Finset.card_pair h0last.ne⟩
  have hindices : (![0, last] : Fin 2 → Fin (p + 1)) = indices ends := by
    apply Finset.orderEmbOfFin_unique ends.2
    · intro i
      fin_cases i <;> simp [ends]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  have he0 : indices ends 0 = 0 := by
    simpa only [Matrix.cons_val_zero] using (congrFun hindices 0).symm
  have he1 : indices ends 1 = last := by
    simpa only [Matrix.cons_val_one, Matrix.head_cons] using (congrFun hindices 1).symm
  have hF : (F.submatrix id (indices ends)).det = (x ^ 3) ^ p - (a ^ 3) ^ p := by
    simp [F, powers, Matrix.det_fin_two, he0, he1, last]
  have hM : (M.submatrix (indices ends) (indices ends)).det = -1 := by
    have hn : ¬ p + p ≤ p := by omega
    simp [M, coefficients, Matrix.det_fin_two, he0, he1, last, hn]
  have hterm (t s : MinorIndices p) : compressionTerm F M t s ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (powers_minor_nonneg ha hax (indices s))
        (coefficients_minor_nonpos hy (indices s) (indices t)))
      (powers_minor_nonneg ha hax (indices t))
  have hdet : (F * M * Fᵀ).det ≤ -((x ^ 3) ^ p - (a ^ 3) ^ p) ^ 2 := by
    rw [compression_det]
    calc
      _ ≤ ∑ s : MinorIndices p, compressionTerm F M ends s := by
        simpa only [Finset.sum_singleton] using
          (Finset.sum_le_sum_of_subset_of_nonpos (Finset.subset_univ {ends})
            (f := fun t => ∑ s : MinorIndices p, compressionTerm F M t s)
            (fun t _ _ => Finset.sum_nonpos fun s _ => hterm t s))
      _ ≤ compressionTerm F M ends ends := by
        simpa only [Finset.sum_singleton] using
          (Finset.sum_le_sum_of_subset_of_nonpos (Finset.subset_univ {ends})
            (f := compressionTerm F M ends) (fun s _ _ => hterm ends s))
      _ = _ := by rw [compressionTerm, hF, hM]; ring
  simpa only [Matrix.det_fin_two, F, M, compression_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, ← sq, homogeneous_swap p a x y] using hdet

private theorem sqrt_sub_add_le {h₀ h₁ g₀ g₁ : ℝ} (hg₀ : 0 ≤ g₀) (hg₁ : 0 ≤ g₁)
    (hh₀ : g₀ ≤ h₀) (hh₁ : g₁ ≤ h₁) :
    √((h₀ - g₀) * (h₁ - g₁)) + √(g₀ * g₁) ≤ √(h₀ * h₁) := by
  have hf (i : Fin 2) : 0 ≤ (![h₀ - g₀, g₀] : Fin 2 → ℝ) i := by
    fin_cases i <;> simp [sub_nonneg.mpr hh₀, hg₀]
  have hg (i : Fin 2) : 0 ≤ (![h₁ - g₁, g₁] : Fin 2 → ℝ) i := by
    fin_cases i <;> simp [sub_nonneg.mpr hh₁, hg₁]
  have h := Real.sum_sqrt_mul_sqrt_le Finset.univ hf hg
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    sub_add_cancel, Real.sqrt_mul (sub_nonneg.mpr hh₀), Real.sqrt_mul hg₀,
    Real.sqrt_mul (hg₀.trans hh₀)] using h

private theorem sqrt_correction (p : ℕ) {a x y : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    √(correction p a a y * correction p x x y) = correction p a x y := by
  apply (Real.sqrt_eq_iff_eq_sq
    (mul_nonneg (correction_nonneg p ha ha hy) (correction_nonneg p hx hx hy))
    (correction_nonneg p ha hx hy)).mpr
  simp only [correction, mul_pow]
  ring

private theorem corner_ordered {p : ℕ} (hp : 0 < p) {a x y : ℝ} (ha : 0 ≤ a) (hax : a ≤ x)
    (hy : 0 ≤ y) :
    √(defect p a a y * defect p x x y) ≤ defect p a x y ∧
      (a < x → √(defect p a a y * defect p x x y) < defect p a x y) := by
  have hx := ha.trans hax
  have hn := (correction_nonneg p ha hx hy).trans (correction_le_homogeneous p ha hx hy)
  have h₀ := correction_le_homogeneous p ha ha hy
  have h₁ := correction_le_homogeneous p hx hx hy
  have hrad : 0 ≤ homogeneous p a a y * homogeneous p x x y :=
    mul_nonneg ((correction_nonneg p ha ha hy).trans h₀)
      ((correction_nonneg p hx hx hy).trans h₁)
  have hcs := sqrt_sub_add_le (correction_nonneg p ha ha hy) (correction_nonneg p hx hx hy) h₀ h₁
  rw [sqrt_correction p ha hx hy] at hcs
  have hdet := homogeneous_det_bound hp ha hax hy
  have hw : √(homogeneous p a a y * homogeneous p x x y) ≤ homogeneous p a x y :=
    (Real.sqrt_le_left hn).mpr (sub_nonpos.mp (hdet.trans (neg_nonpos.mpr (sq_nonneg _))))
  simp only [defect_eq_sub]
  refine ⟨(le_sub_iff_add_le).mpr (hcs.trans hw), fun hlt => ?_⟩
  have hpow : (a ^ 3) ^ p < (x ^ 3) ^ p :=
    pow_lt_pow_left₀ (pow_lt_pow_left₀ hlt ha (by decide)) (by positivity) hp.ne'
  have hs : √(homogeneous p a a y * homogeneous p x x y) < homogeneous p a x y :=
    (Real.sqrt_lt hrad hn).mpr
      (sub_neg.mp (hdet.trans_lt (neg_lt_zero.mpr (sq_pos_of_pos (sub_pos.mpr hpow)))))
  exact (lt_sub_iff_add_lt).mpr (hcs.trans_lt hs)

/-- The scalar corner inequality for every positive exponent and nonnegative roots. -/
theorem defect_corner {p : ℕ} (hp : 0 < p) {a x y : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x)
    (hy : 0 ≤ y) : √(defect p a a y * defect p x x y) ≤ defect p a x y := by
  rcases le_total a x with h | h
  · exact (corner_ordered hp ha h hy).1
  · simpa only [defect_swap_first p a x y, mul_comm (defect p x x y)] using
      (corner_ordered hp hx h hy).1

/-- The corner inequality is strict when the two roots differ. -/
theorem defect_corner_strict {p : ℕ} (hp : 0 < p) {a x y : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hax : a ≠ x) : √(defect p a a y * defect p x x y) < defect p a x y := by
  rcases lt_or_gt_of_ne hax with h | h
  · exact (corner_ordered hp ha h.le hy).2 h
  · simpa only [defect_swap_first p a x y, mul_comm (defect p x x y)] using
      (corner_ordered hp hx h.le hy).2 h

/-- The polynomial form of the scalar corner inequality. -/
theorem defect_corner_sq {p : ℕ} (hp : 0 < p) {a x y : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x)
    (hy : 0 ≤ y) : defect p a a y * defect p x x y ≤ defect p a x y ^ 2 := by
  have h := defect_corner hp ha hx hy
  exact (Real.sqrt_le_left ((Real.sqrt_nonneg _).trans h)).mp h

end RefinedBMV.DimThree

end
