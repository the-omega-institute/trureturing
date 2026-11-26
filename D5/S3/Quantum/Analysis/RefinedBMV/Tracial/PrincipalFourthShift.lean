/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/PrincipalFourthShift
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scalar shifts preserve the four-copy refined BMV bound under signed principal minors. -/

import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ThreeBlockGram
import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.ConstantDiagonal
import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.PrincipalFourthBound
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! A positive scalar shift adds only nonnegative contributions from
shorter closed cycles to the four-copy spectral gap. -/

namespace RefinedBMV.Tracial

open Matrix FourCopyGap
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open private contract diagonal_gap_scaled eigenDiagonal rootDiagonal trace_mask_product
  gaps_card_pos wordMean_conjugation
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

private def fourEntry (C : Matrix n n ℂ) (i j k l : n) : ℂ :=
  C i j * C j k * C k l * C l i

private theorem cycleTrace_entries (C : Matrix n n ℂ) (i j k l : n) :
    cycleTrace (spectralBlock id C) i j k l = fourEntry C i j k l := by
  rw [← trace_mask_product]
  let T (q : n) : Matrix n n ℂ := Matrix.of fun a b ↦ if a = q then C a b else 0
  have hT (q : n) : spectralMask id q * C = T q := by
    ext a b
    by_cases h : a = q <;> simp [spectralMask, T, diagonal_mul, h]
  simp [hT, T, trace, mul_apply, fourEntry, mul_assoc, mul_ite, ite_mul]

private def entriesGap (p : ℕ) (x : n → ℝ) (C : Matrix n n ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, (gapDefect p (x i) (x j) (x k) (x l) : ℂ) *
    fourEntry C i j k l

private theorem entriesGap_eq_scaled (p : ℕ) (x : n → ℝ) (C : Matrix n n ℂ) :
    entriesGap p x C = ((gaps p).card : ℂ) *
      (FourCopyGap.wordMean p (eigenDiagonal id x) C - trace ((rootDiagonal id x p * C) ^ 4)) := by
  rw [diagonal_gap_scaled]
  simp [entriesGap, contract, cycleTrace_entries]

omit [DecidableEq n] in
private theorem sum_reverse {R : Type*} [AddCommMonoid R] (f : n → n → n → R) :
    (∑ j, ∑ k, ∑ l, f l k j) = ∑ j, ∑ k, ∑ l, f j k l := by
  calc
    _ = ∑ k, ∑ j, ∑ l, f l k j := Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ j, f l k j := Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ l, ∑ k, ∑ j, f l k j := Finset.sum_comm
    _ = _ := rfl

omit [DecidableEq n] in
private theorem entriesGap_im_zero (p : ℕ) (x : n → ℝ) {C : Matrix n n ℂ}
    (hC : C.IsHermitian) : (entriesGap p x C).im = 0 := by
  have hstar : star (entriesGap p x C) = entriesGap p x C := by
    simp only [entriesGap, map_sum, Complex.star_def]
    apply Finset.sum_congr rfl
    intro i _
    rw [← sum_reverse (fun j k l ↦ (gapDefect p (x i) (x j) (x k) (x l) : ℂ) *
      fourEntry C i j k l)]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    have hgap : gapDefect p (x i) (x j) (x k) (x l) =
        gapDefect p (x i) (x l) (x k) (x j) := by
      rw [ThreeBlockGram.gapDefect_swap12 p (x i) (x j) (x k) (x l),
        ThreeBlockGram.gapDefect_swap23 p (x i) (x k) (x j) (x l),
        ThreeBlockGram.gapDefect_swap12 p (x i) (x k) (x l) (x j)]
    rw [hgap]
    have hreal (a : ℝ) : star (a : ℂ) = (a : ℂ) := by simp
    simp only [fourEntry, map_mul, ← Complex.star_def, hC.apply, hreal]
    ring
  have hi := congrArg Complex.im hstar
  rw [Complex.star_def, Complex.conj_im] at hi
  linarith

private def shifted (C : Matrix n n ℂ) (r : ℝ) : Matrix n n ℂ :=
  C + (r : ℂ) • (1 : Matrix n n ℂ)

omit [Fintype n] in
private theorem shifted_apply (C : Matrix n n ℂ) (r : ℝ) (i j : n) :
    shifted C r i j = C i j + if i = j then (r : ℂ) else 0 := by
  by_cases h : i = j <;> simp [shifted, h]

omit [Fintype n] in
private theorem shifted_hermitian {C : Matrix n n ℂ} (hC : C.IsHermitian) (r : ℝ) :
    (shifted C r).IsHermitian := by
  apply IsHermitian.ext
  intro i j
  simp only [shifted_apply, star_add, hC.apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

omit [Fintype n] [DecidableEq n] in
private theorem diag_eq_re {C : Matrix n n ℂ} (hdiag : ∀ i, 0 ≤ C i i) (i : n) :
    C i i = ((C i i).re : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using (Complex.nonneg_iff.mp (hdiag i)).2.symm

omit [Fintype n] [DecidableEq n] in
private theorem pair_eq_normSq {C : Matrix n n ℂ} (hC : C.IsHermitian) (i j : n) :
    C i j * C j i = (Complex.normSq (C i j) : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def, hC.apply, mul_comm]

omit [Fintype n] in
private theorem shifted_diag_real (C : Matrix n n ℂ) (hdiag : ∀ i, 0 ≤ C i i)
    (r : ℝ) (i : n) :
    shifted C r i i = ((C i i).re + r : ℝ) := by
  rw [shifted_apply]
  simp only [ite_true, Complex.ofReal_add]
  rw [← diag_eq_re hdiag]

omit [Fintype n] in
private theorem shifted_off (C : Matrix n n ℂ) (r : ℝ) {i j : n} (h : i ≠ j) :
    shifted C r i j = C i j := by
  simp [shifted_apply, h]

omit [Fintype n] in
private theorem mixed_triangle_nonneg {C : Matrix n n ℂ} (hC : C.IsHermitian)
    (hdiag : ∀ i, 0 ≤ C i i)
    (htri : ∀ i j k, i ≠ j → j ≠ k → k ≠ i → 0 ≤ (C i j * C j k * C k i).re)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (i j k : n) :
    0 ≤ (shifted C a i j * shifted C b j k * shifted C c k i).re := by
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      have h := (Complex.nonneg_iff.mp (hdiag i)).1
      simp only [shifted_diag_real C hdiag, ← Complex.ofReal_mul, Complex.ofReal_re]
      exact mul_nonneg (mul_nonneg (add_nonneg h ha) (add_nonneg h hb)) (add_nonneg h hc)
    · have h := (Complex.nonneg_iff.mp (hdiag i)).1
      simp only [shifted_diag_real C hdiag, shifted_off C _ hik,
        shifted_off C _ (Ne.symm hik), mul_assoc, pair_eq_normSq hC,
        Complex.re_ofReal_mul, Complex.ofReal_re]
      exact mul_nonneg (add_nonneg h ha) (Complex.normSq_nonneg _)
  · by_cases hjk : j = k
    · subst k
      have h := (Complex.nonneg_iff.mp (hdiag j)).1
      rw [shifted_off C _ hij, shifted_off C _ (Ne.symm hij),
        show C i j * shifted C b j j * C j i =
          shifted C b j j * (C i j * C j i) by ring,
        pair_eq_normSq hC, shifted_diag_real C hdiag, Complex.re_ofReal_mul, Complex.ofReal_re]
      exact mul_nonneg (add_nonneg h hb) (Complex.normSq_nonneg _)
    · by_cases hki : k = i
      · subst k
        have h := (Complex.nonneg_iff.mp (hdiag i)).1
        simp only [shifted_off C _ hij, shifted_off C _ hjk, shifted_diag_real C hdiag,
          pair_eq_normSq hC,
          Complex.re_ofReal_mul, Complex.ofReal_re]
        exact mul_nonneg (Complex.normSq_nonneg _) (add_nonneg h hc)
      · simpa only [shifted_off C _ hij, shifted_off C _ hjk, shifted_off C _ hki] using
          htri i j k hij hjk hki

omit [Fintype n] in
private theorem fourEntry_shift_re_le {C : Matrix n n ℂ} (hC : C.IsHermitian)
    (hdiag : ∀ i, 0 ≤ C i i)
    (htri : ∀ i j k, i ≠ j → j ≠ k → k ≠ i → 0 ≤ (C i j * C j k * C k i).re)
    {r : ℝ} (hr : 0 ≤ r) (i j k l : n) :
    (fourEntry C i j k l).re ≤ (fourEntry (shifted C r) i j k l).re := by
  let B := shifted C r
  have hm (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :=
    mixed_triangle_nonneg hC hdiag htri ha hb hc
  have hzero (u v : n) : shifted C 0 u v = C u v := by simp [shifted]
  have h1 : 0 ≤ (((if i = j then (r : ℂ) else 0) : ℂ) *
      (B j k * B k l * B l i)).re := by
    by_cases h : i = j
    · subst j
      simpa [B, Complex.re_ofReal_mul] using mul_nonneg hr (hm r r r hr hr hr i k l)
    · simp [h]
  have h2 : 0 ≤ (((if j = k then (r : ℂ) else 0) : ℂ) *
      (C i j * B k l * B l i)).re := by
    by_cases h : j = k
    · subst k
      simpa [B, hzero, Complex.re_ofReal_mul] using
        mul_nonneg hr (hm 0 r r le_rfl hr hr i j l)
    · simp [h]
  have h3 : 0 ≤ (((if k = l then (r : ℂ) else 0) : ℂ) *
      (C i j * C j k * B l i)).re := by
    by_cases h : k = l
    · subst l
      simpa [B, hzero, Complex.re_ofReal_mul] using
        mul_nonneg hr (hm 0 0 r le_rfl le_rfl hr i j k)
    · simp [h]
  have h4 : 0 ≤ (((if l = i then (r : ℂ) else 0) : ℂ) *
      (C i j * C j k * C k l)).re := by
    by_cases h : l = i
    · subst l
      simpa [hzero, Complex.re_ofReal_mul] using mul_nonneg hr (hm 0 0 0 le_rfl le_rfl le_rfl i j k)
    · simp [h]
  have hstep (u v : n) : B u v - C u v = if u = v then (r : ℂ) else 0 := by
    dsimp [B]
    rw [shifted_apply]
    ring
  have hchange : fourEntry B i j k l - fourEntry C i j k l =
      (B i j - C i j) * (B j k * B k l * B l i) +
      (B j k - C j k) * (C i j * B k l * B l i) +
      (B k l - C k l) * (C i j * C j k * B l i) +
      (B l i - C l i) * (C i j * C j k * C k l) := by
    unfold fourEntry
    ring
  rw [hstep, hstep, hstep, hstep] at hchange
  have h := congrArg Complex.re hchange
  simp only [Complex.sub_re, Complex.add_re] at h
  linarith

/-- Nonnegative diagonal and real triangle weights make the normalized
four-copy gap nondecreasing under a nonnegative scalar shift. -/
theorem diagonal_fourth_gap_shift_mono {s : Type*} (p : ℕ) (label : n → s)
    (x : s → ℝ) (hx : ∀ a, 0 ≤ x a) {C : Matrix n n ℂ} (hC : C.IsHermitian)
    (hdiag : ∀ i, 0 ≤ C i i)
    (htri : ∀ i j k, i ≠ j → j ≠ k → k ≠ i → 0 ≤ (C i j * C j k * C k i).re)
    {r : ℝ} (hr : 0 ≤ r) :
    FourCopyGap.wordMean p (eigenDiagonal label x) C - trace ((rootDiagonal label x p * C) ^ 4) ≤
      FourCopyGap.wordMean p (eigenDiagonal label x) (C + (r : ℂ) • 1) -
        trace ((rootDiagonal label x p * (C + (r : ℂ) • 1)) ^ 4) := by
  let B := shifted C r
  let y := x ∘ label
  have hscaled : entriesGap p y C ≤ entriesGap p y B := by
    apply Complex.le_def.mpr
    refine ⟨?_, (entriesGap_im_zero p y hC).trans
      (entriesGap_im_zero p y (shifted_hermitian hC r)).symm⟩
    simp only [entriesGap, Complex.re_sum, Complex.re_ofReal_mul]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro k _
    apply Finset.sum_le_sum
    intro l _
    exact mul_le_mul_of_nonneg_left (fourEntry_shift_re_le hC hdiag htri hr i j k l)
      (gapDefect_nonneg p (hx _) (hx _) (hx _) (hx _))
  rw [entriesGap_eq_scaled, entriesGap_eq_scaled] at hscaled
  have hcard : (0 : ℝ) < (gaps p).card := by exact_mod_cast gaps_card_pos p
  obtain ⟨hre, him⟩ := Complex.le_def.mp hscaled
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, add_zero] at hre him
  exact Complex.le_def.mpr ⟨(mul_le_mul_iff_of_pos_left hcard).mp hre,
    mul_left_cancel₀ hcard.ne' him⟩

omit [Fintype n] in
private theorem signed_minor_embedding {C : Matrix n n ℂ} {m : ℕ}
    (hm : 0 < m) (hm' : m ≤ 4) (e : Fin m ↪ n)
    (hC : ∀ I : Finset n, 0 < I.card → I.card ≤ 4 →
      0 ≤ (-1 : ℂ) ^ (I.card + 1) *
        (C.submatrix (Subtype.val : I → n) (Subtype.val : I → n)).det) :
    0 ≤ (-1 : ℂ) ^ (m + 1) * (C.submatrix e e).det := by
  let I : Finset n := Finset.univ.map e
  have hI : I.card = m := by simp [I]
  let f : Fin m → I := fun i ↦ ⟨e i, Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  let F : Fin m ≃ I := Equiv.ofBijective f ⟨
    fun i j h ↦ e.injective (congrArg Subtype.val h),
    fun ⟨i, hi⟩ ↦ by
      obtain ⟨j, _, h⟩ := Finset.mem_map.mp hi
      exact ⟨j, Subtype.ext h⟩⟩
  have heq : (C.submatrix e e).det =
      (C.submatrix (Subtype.val : I → n) (Subtype.val : I → n)).det := by
    rw [← det_submatrix_equiv_self F
      (C.submatrix (Subtype.val : I → n) (Subtype.val : I → n))]
    congr 1
  have h := hC I (by rwa [hI]) (by rwa [hI])
  rwa [heq, ← hI]

omit [Fintype n] in
private theorem diagonal_nonneg_of_signed_minors {C : Matrix n n ℂ}
    (hC : ∀ I : Finset n, 0 < I.card → I.card ≤ 4 →
      0 ≤ (-1 : ℂ) ^ (I.card + 1) *
        (C.submatrix (Subtype.val : I → n) (Subtype.val : I → n)).det) (i : n) :
    0 ≤ C i i := by
  let e : Fin 1 ↪ n := ⟨fun _ ↦ i, fun a b _ ↦ Subsingleton.elim a b⟩
  have he : e 0 = i := rfl
  simpa [det_unique, he] using
    (signed_minor_embedding (C := C) (m := 1) (by decide) (by decide) e hC)

omit [Fintype n] in
private theorem diagonal_product_le_of_signed_minors {C : Matrix n n ℂ} (hC : C.IsHermitian)
    (hdiag : ∀ i, 0 ≤ C i i)
    (hM : ∀ I : Finset n, 0 < I.card → I.card ≤ 4 →
      0 ≤ (-1 : ℂ) ^ (I.card + 1) *
        (C.submatrix (Subtype.val : I → n) (Subtype.val : I → n)).det)
    {i j : n} (hij : i ≠ j) :
    (C i i).re * (C j j).re ≤ Complex.normSq (C i j) := by
  let e : Fin 2 ↪ n := ⟨![i, j], Matrix.injective_pair_iff_ne.mpr hij⟩
  have h := signed_minor_embedding (C := C) (m := 2) (by decide) (by decide) e hM
  have he0 : e 0 = i := rfl
  have he1 : e 1 = j := rfl
  rw [det_fin_two] at h
  simp only [submatrix_apply, he0, he1] at h
  rw [pair_eq_normSq hC, diag_eq_re hdiag i, diag_eq_re hdiag j] at h
  have h' := (Complex.nonneg_iff.mp h).1
  norm_num [Complex.neg_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re] at h'
  linarith

omit [Fintype n] in
private theorem triangle_nonneg_of_signed_minors {C : Matrix n n ℂ} (hC : C.IsHermitian)
    (hdiag : ∀ i, 0 ≤ C i i)
    (hM : ∀ I : Finset n, 0 < I.card → I.card ≤ 4 →
      0 ≤ (-1 : ℂ) ^ (I.card + 1) *
        (C.submatrix (Subtype.val : I → n) (Subtype.val : I → n)).det)
    (i j k : n) (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
    0 ≤ (C i j * C j k * C k i).re := by
  let e : Fin 3 ↪ n := ⟨![i, j, k], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [Ne.symm hij, Ne.symm hjk, Ne.symm hki]⟩
  have h := signed_minor_embedding (C := C) (m := 3) (by decide) (by decide) e hM
  have he0 : e 0 = i := rfl
  have he1 : e 1 = j := rfl
  have he2 : e 2 = k := rfl
  let T := C i j * C j k * C k i
  have hclosed : C i k * C j i * C k j = star T := by
    simp only [T, star_mul, hC.apply]
    ring
  have hdet : (C.submatrix e e).det =
      C i i * C j j * C k k - C i i * (C j k * C k j) -
        C j j * (C i k * C k i) - C k k * (C i j * C j i) + T + star T := by
    rw [← hclosed, det_fin_three]
    simp only [submatrix_apply, he0, he1, he2, T]
    ring
  rw [hdet, pair_eq_normSq hC, pair_eq_normSq hC, pair_eq_normSq hC,
    diag_eq_re hdiag i, diag_eq_re hdiag j, diag_eq_re hdiag k] at h
  have h' := (Complex.nonneg_iff.mp h).1
  norm_num [Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re,
    Complex.star_def, Complex.conj_re, ← Complex.ofReal_mul] at h'
  have hi := mul_le_mul_of_nonneg_left
    (diagonal_product_le_of_signed_minors hC hdiag hM hjk) (Complex.nonneg_iff.mp (hdiag i)).1
  have hj := mul_le_mul_of_nonneg_left
    (diagonal_product_le_of_signed_minors hC hdiag hM (Ne.symm hki))
    (Complex.nonneg_iff.mp (hdiag j)).1
  have hk := mul_le_mul_of_nonneg_left
    (diagonal_product_le_of_signed_minors hC hdiag hM hij) (Complex.nonneg_iff.mp (hdiag k)).1
  have hpos := mul_nonneg (mul_nonneg (Complex.nonneg_iff.mp (hdiag i)).1
    (Complex.nonneg_iff.mp (hdiag j)).1) (Complex.nonneg_iff.mp (hdiag k)).1
  change 0 ≤ T.re
  nlinarith only [h', hi, hj, hk, hpos]

/-- A nonnegative scalar shift increases the normalized four-copy gap
when the Hermitian matrix has the prescribed signs of its principal minors. -/
theorem diagonal_fourth_gap_shift_mono_of_signed_minors {s : Type*} (p : ℕ) (label : n → s)
    (x : s → ℝ) (hx : ∀ a, 0 ≤ x a) {C : Matrix n n ℂ} (hC : C.IsHermitian)
    (hM : ∀ I : Finset n, 0 < I.card → I.card ≤ 4 →
      0 ≤ (-1 : ℂ) ^ (I.card + 1) *
        (C.submatrix (Subtype.val : I → n) (Subtype.val : I → n)).det)
    {r : ℝ} (hr : 0 ≤ r) :
    FourCopyGap.wordMean p (eigenDiagonal label x) C - trace ((rootDiagonal label x p * C) ^ 4) ≤
      FourCopyGap.wordMean p (eigenDiagonal label x) (C + (r : ℂ) • 1) -
        trace ((rootDiagonal label x p * (C + (r : ℂ) • 1)) ^ 4) := by
  have hd := diagonal_nonneg_of_signed_minors hM
  exact diagonal_fourth_gap_shift_mono p label x hx hC hd
    (triangle_nonneg_of_signed_minors hC hd hM) hr

/-- The four-copy product lower bound for a nonnegative scalar shift
of a Hermitian matrix satisfying the signed principal minor criterion. -/
theorem diagonal_word_bound_shift_of_signed_minors {d : ℕ} {s : Type*}
    [Finite s] (p : ℕ) (label : Fin d → s) (x : s → ℝ) (hx : ∀ a, 0 ≤ x a)
    {C : Matrix (Fin d) (Fin d) ℂ} (hC : C.IsHermitian)
    (hM : ∀ I : Finset (Fin d), 0 < I.card → I.card ≤ 4 →
      0 ≤ (-1 : ℂ) ^ (I.card + 1) *
        (C.submatrix (Subtype.val : I → Fin d) (Subtype.val : I → Fin d)).det)
    {r : ℝ} (hr : 0 ≤ r) :
    trace ((rootDiagonal label x p * (C + (r : ℂ) • 1)) ^ 4) ≤
      FourCopyGap.wordMean p (eigenDiagonal label x) (C + (r : ℂ) • 1) := by
  have hbase := diagonal_word_bound_of_signed_minors p label x hx C hM
  have hmono := diagonal_fourth_gap_shift_mono_of_signed_minors p label x hx hC hM hr
  obtain ⟨hbaseRe, hbaseIm⟩ := Complex.le_def.mp hbase
  obtain ⟨hmonoRe, hmonoIm⟩ := Complex.le_def.mp hmono
  rw [Complex.sub_re, Complex.sub_re] at hmonoRe
  rw [Complex.sub_im, Complex.sub_im] at hmonoIm
  exact Complex.le_def.mpr ⟨by linarith only [hbaseRe, hmonoRe],
    by linarith only [hbaseIm, hmonoIm]⟩

set_option maxHeartbeats 350000 in
-- The conjugation proof transports the dependent inertia index through block matrices.
/-- A nonnegative scalar shift of a Hermitian matrix with at most one
positive eigenvalue satisfies the four-copy bound when its spectral block
traces are nonnegative. The spectral blocks are those of the first factor. -/
theorem diagonal_word_bound_shift_of_posIndex_fiber_trace_nonneg {d : ℕ} {s : Type*}
    [Finite s] [DecidableEq s] (p : ℕ) (label : Fin d → s)
    (x : s → ℝ) (hx : ∀ a, 0 ≤ x a) {C : Matrix (Fin d) (Fin d) ℂ}
    (hC : C.IsHermitian) (hIndex : RHLinalg.posIndex hC ≤ 1)
    (hFiber : ∀ a : s, 0 ≤ trace (C.submatrix
      (Subtype.val : {i // label i = a} → Fin d) Subtype.val)) {r : ℝ} (hr : 0 ≤ r) :
    trace ((rootDiagonal label x p * (C + (r : ℂ) • 1)) ^ 4) ≤
      FourCopyGap.wordMean p (eigenDiagonal label x) (C + (r : ℂ) • 1) := by
  obtain ⟨U, hfix, hflat⟩ := exists_unitary_const_diagonal_fibers label hC
  let φ := Unitary.conjStarAlgAut ℂ _ U
  have hC' : (φ C).IsHermitian := by
    simpa only [φ, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      conjTranspose_conjTranspose] using
      isHermitian_conjTranspose_mul_mul (U.valᴴ) hC
  have hIndex' : RHLinalg.posIndex hC' ≤ 1 := by
    simpa only [φ, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      conjTranspose_conjTranspose] using
      (RHLinalg.posIndex_conj_le hC (U.valᴴ)).trans hIndex
  have hdiag : ∀ i, 0 ≤ φ C i i := by
    intro i
    change 0 ≤ Unitary.conjStarAlgAut ℂ _ U C i i
    rw [hflat, div_eq_mul_inv]
    have hden : (0 : ℂ) ≤ (Fintype.card {j // label j = label i} : ℂ)⁻¹ := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.zero_le_real]
      positivity
    exact mul_nonneg (hFiber (label i)) hden
  have hbound := diagonal_word_bound_shift_of_signed_minors p label x hx hC'
    (fun I hi _ ↦ signed_principal_minors_nonneg_of_posIndex hC' hIndex' hdiag I hi) hr
  have hfixA : φ (eigenDiagonal label x) = eigenDiagonal label x := hfix (fun a ↦ (x a : ℂ))
  have hfixR : φ (rootDiagonal label x p) = rootDiagonal label x p :=
    hfix (fun a ↦ ((x a ^ ((p : ℝ) / 4) : ℝ) : ℂ))
  have hshift : φ (C + (r : ℂ) • 1) = φ C + (r : ℂ) • 1 := by
    rw [map_add, map_smul, map_one]
  have hm := wordMean_conjugation p U (eigenDiagonal label x) (C + (r : ℂ) • 1)
  change FourCopyGap.wordMean p (φ (eigenDiagonal label x))
    (φ (C + (r : ℂ) • 1)) = _ at hm
  rw [hfixA, hshift] at hm
  have ht := trace_conjugation U ((rootDiagonal label x p * (C + (r : ℂ) • 1)) ^ 4)
  change trace (φ ((rootDiagonal label x p * (C + (r : ℂ) • 1)) ^ 4)) = _ at ht
  rw [map_pow, map_mul, hfixR, hshift] at ht
  rw [ht, hm] at hbound
  exact hbound


/-- The four-copy product bound when a nonnegative scalar lies between the
second eigenvalue of the second factor and every spectral block mean. -/
theorem diagonal_word_bound_of_second_eigenvalue_le_fiber_trace
    {d : ℕ} {s : Type*} [Finite s] [DecidableEq s]
    (p : ℕ) (label : Fin d → s) (x : s → ℝ) (hx : ∀ a, 0 ≤ x a)
    {B : Matrix (Fin d) (Fin d) ℂ} (hB : B.IsHermitian)
    (j : Fin (Fintype.card (Fin d))) (hj : j.val = 1) {c : ℝ} (hc : 0 ≤ c)
    (hEigen : hB.eigenvalues₀ j ≤ c)
    (hMean : ∀ a : s, (c : ℂ) * (Fintype.card {i // label i = a} : ℂ) ≤
      trace (B.submatrix (Subtype.val : {i // label i = a} → Fin d) Subtype.val)) :
    trace ((rootDiagonal label x p * B) ^ 4) ≤
      FourCopyGap.wordMean p (eigenDiagonal label x) B := by
  let C := B - (c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)
  have hOne : ((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)).IsHermitian :=
    Matrix.isHermitian_one.smul (show IsSelfAdjoint (c : ℂ) by
      change star (c : ℂ) = (c : ℂ)
      exact Complex.conj_ofReal _)
  have hC : C.IsHermitian := hB.sub hOne
  have hIndex := posIndex_sub_scalar_le_of_ordered_eigenvalue_le hB j c hEigen hC
  rw [hj] at hIndex
  have hFiber (a : s) :
      0 ≤ trace (C.submatrix (Subtype.val : {i // label i = a} → Fin d) Subtype.val) := by
    let e : {i // label i = a} → Fin d := Subtype.val
    change 0 ≤ trace (C.submatrix e e)
    have hsub : C.submatrix e e = B.submatrix e e - (c : ℂ) •
        (1 : Matrix (Fin d) (Fin d) ℂ).submatrix e e := rfl
    rw [hsub, Matrix.submatrix_one e Subtype.val_injective, Matrix.trace_sub,
      Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
    obtain ⟨hre, him⟩ := Complex.le_def.mp (hMean a)
    exact Complex.nonneg_iff.mpr ⟨by rwa [Complex.sub_re, sub_nonneg],
      by rw [Complex.sub_im, ← him, sub_self]⟩
  have h := diagonal_word_bound_shift_of_posIndex_fiber_trace_nonneg p label x hx
    hC hIndex hFiber hc
  simpa only [C, sub_add_cancel] using h

#print axioms diagonal_word_bound_of_second_eigenvalue_le_fiber_trace


/-- The four-copy product lower bound for a positive semidefinite first
factor, under the second-eigenvalue criterion on the spectral blocks of
the first factor. The exponents and words are evaluated before changing basis. -/
theorem product_bound_of_second_eigenvalue_le_fiber_trace
    {d : ℕ} {s : Type*} [Finite s] [DecidableEq s]
    (p : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef) (hB : B.IsHermitian)
    (label : Fin d → s) (x : s → ℝ) (hx : ∀ a, 0 ≤ x a)
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (hdiag : Unitary.conjStarAlgAut ℂ _ U A = eigenDiagonal label x)
    (j : Fin (Fintype.card (Fin d))) (hj : j.val = 1) {c : ℝ} (hc : 0 ≤ c)
    (hEigen : hB.eigenvalues₀ j ≤ c)
    (hMean : ∀ a : s, (c : ℂ) * (Fintype.card {i // label i = a} : ℂ) ≤
      trace ((Unitary.conjStarAlgAut ℂ _ U B).submatrix
        (Subtype.val : {i // label i = a} → Fin d) Subtype.val)) :
    trace (((A ^ ((p : ℝ) / 4)) * B) ^ 4) ≤ FourCopyGap.wordMean p A B := by
  let φ := Unitary.conjStarAlgAut ℂ _ U
  have hB' : (φ B).IsHermitian := by
    change star (φ B) = φ B
    rw [← map_star, Matrix.star_eq_conjTranspose, hB.eq]
  have hpoly : (φ B).charpoly = B.charpoly := by
    rw [show φ B = (U.val * B) * star U.val by rfl, Matrix.charpoly_mul_comm,
      ← mul_assoc, Unitary.coe_star_mul_self, one_mul]
  have hOrdered : hB'.eigenvalues₀ = hB.eigenvalues₀ := by
    rw [← List.ofFn_inj, ← hB'.sort_roots_charpoly_eq_eigenvalues₀,
      ← hB.sort_roots_charpoly_eq_eigenvalues₀, hpoly]
  have hr : φ (A ^ ((p : ℝ) / 4)) = rootDiagonal label x p := by
    let f : ℝ → ℝ := fun y ↦ y ^ ((p : ℝ) / 4)
    have hf : φ (cfc f A) = cfc f (φ A) :=
      StarAlgHomClass.map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint) φ f A
        (hf := (Set.toFinite (spectrum ℝ A)).continuousOn f)
        (hφ := φ.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional)
        (ha := hA.isHermitian) (hφa := by
          have hSelf : IsSelfAdjoint A := hA.isHermitian
          exact hSelf.map φ)
    rw [CFC.rpow_eq_cfc_real hA.nonneg, hf, show φ A = _ from hdiag]
    exact D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal
      f (fun a ↦ x (label a))
  have hm : FourCopyGap.wordMean p (eigenDiagonal label x) (φ B) =
      FourCopyGap.wordMean p A B := by
    rw [← hdiag]
    exact wordMean_conjugation p U A B
  have ht : trace ((rootDiagonal label x p * φ B) ^ 4) =
      trace (((A ^ ((p : ℝ) / 4)) * B) ^ 4) := by
    rw [← hr, ← map_mul φ, ← map_pow φ]
    exact trace_conjugation U _
  have hEigen' : hB'.eigenvalues₀ j ≤ c := by simpa only [hOrdered] using hEigen
  simpa only [ht, hm] using
    diagonal_word_bound_of_second_eigenvalue_le_fiber_trace p label x hx hB'
      j hj hc hEigen' hMean

#print axioms product_bound_of_second_eigenvalue_le_fiber_trace

end
end RefinedBMV.Tracial
