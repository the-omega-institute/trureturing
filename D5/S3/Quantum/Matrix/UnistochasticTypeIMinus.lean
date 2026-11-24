/- GID: D5/S3/Quantum/Matrix/UnistochasticTypeIMinus
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/UnistochasticTypeIMinus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The strict Type I− hyperoctant excludes order-four unistochastic matrices. -/
import D5.S3.Weil.ZetaLinear.VonNeumann
import Mathlib.Algebra.Order.Star.Real

/-! The strict Type I− exclusion follows from two planar overlap Gram matrices. -/

noncomputable section

open Matrix Finset
open scoped ComplexConjugate

namespace D5.S3.Quantum.Matrix.UnistochasticTypeIMinus

private def signs : Matrix (Fin 4) (Fin 3) ℝ :=
  !![1, 1, 1; 1, -1, -1; -1, 1, -1; -1, -1, 1]

/-- The three nonconstant Hadamard characters, normalized to length one. -/
def H : Matrix (Fin 4) (Fin 3) ℝ := Matrix.of fun a l => signs a l / 2

private def transform (x : Fin 4 → ℝ) (l : Fin 3) : ℝ :=
  ∑ a, signs a l * x a

private theorem recover (x : Fin 4 → ℝ) (a : Fin 4) :
    4 * x a = (∑ b, x b) + ∑ l, signs a l * transform x l := by
  fin_cases a <;> norm_num [transform, signs, Fin.sum_univ_succ] <;> ring

private theorem sum_signs (l : Fin 3) : ∑ a, signs a l = 0 := by
  fin_cases l <;> norm_num [signs, Fin.sum_univ_succ]

private theorem coordinate (B : Matrix (Fin 4) (Fin 4) ℝ) (r l : Fin 3) :
    (Hᵀ * B * H) r l = transform (fun a => transform (B a) l) r / 4 := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, H, Matrix.of_apply]
  rw [transform, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : (∑ b, B a b * (signs b l / 2)) = transform (B a) l / 2 := by
    rw [transform, Finset.sum_div]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [h]
  ring

private theorem row_transform_sum (B : Matrix (Fin 4) (Fin 4) ℝ)
    (hcol : ∀ b, ∑ a, B a b = 1) (l : Fin 3) :
    ∑ a, transform (B a) l = 0 := by
  simp only [transform]
  rw [Finset.sum_comm]
  simp [← Finset.mul_sum, hcol, sum_signs]

private def probability (U : Matrix (Fin 4) (Fin 4) ℂ) :=
  RHLinalg.normSqMatrix U

private def overlaps (U : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4) (j : Fin 4) : ℂ :=
  U a j * conj (U b j)

private def signed (U : Matrix (Fin 4) (Fin 4) ℂ) (l : Fin 3) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  U * Matrix.diagonal (fun j => (signs j l : ℂ)) * star U

private theorem signed_entry (U : Matrix (Fin 4) (Fin 4) ℂ)
    (l : Fin 3) (a b : Fin 4) :
    signed U l a b = ∑ j, (signs j l : ℂ) * overlaps U a b j := by
  unfold signed
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,
    Matrix.star_apply, Complex.star_def, overlaps, mul_left_comm, mul_assoc]

private theorem signed_star (U : Matrix (Fin 4) (Fin 4) ℂ) (l : Fin 3) :
    star (signed U l) = signed U l := by
  unfold signed
  rw [star_mul, star_mul, star_star, mul_assoc]
  congr 2
  ext i j
  by_cases h : i = j
  · subst j
    simp [Matrix.star_apply]
  · simp [Matrix.star_apply, Matrix.diagonal_apply_ne _ h,
      Matrix.diagonal_apply_ne _ (Ne.symm h)]

private theorem signed_unitary {U : Matrix (Fin 4) (Fin 4) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) (l : Fin 3) :
    signed U l ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  have hd : Matrix.diagonal (fun j => (signs j l : ℂ)) ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have hstar : star (Matrix.diagonal (fun j => (signs j l : ℂ))) =
        Matrix.diagonal (fun j => (signs j l : ℂ)) := by
      ext i j
      by_cases h : i = j
      · subst j
        simp [Matrix.star_apply]
      · simp [Matrix.star_apply, Matrix.diagonal_apply_ne _ h,
          Matrix.diagonal_apply_ne _ (Ne.symm h)]
    rw [hstar, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    fin_cases j <;> fin_cases l <;> norm_num [signs]
  exact (Matrix.unitaryGroup (Fin 4) ℂ).mul_mem
    ((Matrix.unitaryGroup (Fin 4) ℂ).mul_mem hU hd) (Unitary.star_mem hU)

private theorem signed_diag (U : Matrix (Fin 4) (Fin 4) ℂ) (l : Fin 3) (a : Fin 4) :
    signed U l a a = (transform (probability U a) l : ℂ) := by
  simp only [signed_entry, overlaps, Complex.mul_conj', transform,
    probability, RHLinalg.normSqMatrix, Matrix.of_apply, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_pow]

private theorem overlaps_sum {U : Matrix (Fin 4) (Fin 4) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) {a b : Fin 4} (hab : a ≠ b) :
    ∑ j, overlaps U a b j = 0 := by
  have h := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℂ => A a b)
    (Unitary.mul_star_self_of_mem hU)
  simpa [Matrix.mul_apply, Matrix.star_apply, Complex.star_def, Matrix.one_apply, hab, overlaps]
    using h

private def gram (z w : ℂ) : ℝ := z.re * w.re + z.im * w.im

private theorem gram_diag (z : ℂ) : gram z z = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, gram]

private theorem pair_transform (z : Fin 4 → ℂ) (hz : ∑ j, z j = 0) (n : Fin 3) :
    gram (∑ j, (signs j (n + 1) : ℂ) * z j)
         (∑ j, (signs j (n + 2) : ℂ) * z j) =
      2 * transform (fun j => ‖z j‖ ^ 2) n := by
  have hz3 : z 3 = -(z 0 + z 1 + z 2) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, add_zero] at hz
    change z 0 + (z 1 + (z 2 + z 3)) = 0 at hz
    linear_combination hz
  fin_cases n <;>
    norm_num [Fin.sum_univ_succ, signs, gram, transform, Complex.sq_norm, Complex.normSq_apply,
      hz3, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
      Complex.sub_re, Complex.sub_im, Fin.reduceAdd] <;> ring

private theorem probability_cross (B : Matrix (Fin 4) (Fin 4) ℝ)
    (hrow : ∀ a, ∑ b, B a b = 1) (a b : Fin 4) (n : Fin 3) :
    2 * transform (fun j => B a j * B b j) n =
      (transform (B a) n + transform (B b) n +
        transform (B a) (n + 1) * transform (B b) (n + 2) +
        transform (B a) (n + 2) * transform (B b) (n + 1)) / 2 := by
  have h (a j : Fin 4) : B a j = (1 + ∑ l, signs j l * transform (B a) l) / 4 := by
    linarith [recover (B a) j, hrow a]
  conv_lhs => unfold transform
  simp_rw [h a, h b]
  fin_cases n <;> norm_num [Fin.sum_univ_succ, signs, Fin.reduceAdd] <;> ring

private theorem signed_cross {U : Matrix (Fin 4) (Fin 4) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) {a b : Fin 4} (hab : a ≠ b) (n : Fin 3) :
    gram (signed U (n + 1) a b) (signed U (n + 2) a b) =
      (transform (probability U a) n + transform (probability U b) n +
        transform (probability U a) (n + 1) * transform (probability U b) (n + 2) +
        transform (probability U a) (n + 2) * transform (probability U b) (n + 1)) / 2 := by
  rw [signed_entry, signed_entry, pair_transform _ (overlaps_sum hU hab)]
  have h (j : Fin 4) : ‖overlaps U a b j‖ ^ 2 = probability U a j * probability U b j := by
    simp [overlaps, probability, RHLinalg.normSqMatrix, mul_pow]
  simp_rw [h]
  exact probability_cross _ (mem_doublyStochastic_iff_sum.mp
    (RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary hU)).2.1 a b n


-- Row zero is fixed. A cyclic choice of r chooses the other member of its pair.
private theorem row_coordinates (B : Matrix (Fin 4) (Fin 4) ℝ)
    (hcol : ∀ b, ∑ a, B a b = 1) {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : ∀ r l, R r l = -(Hᵀ * B * H) r l) (r l : Fin 3) :
    transform (B 0) l = -(R r l + R (r + 1) l + R (r + 2) l) ∧
    transform (B r.succ) l = -R r l + R (r + 1) l + R (r + 2) l ∧
    transform (B (r + 1).succ) l = R r l - R (r + 1) l + R (r + 2) l ∧
    transform (B (r + 2).succ) l = R r l + R (r + 1) l - R (r + 2) l := by
  have h (a : Fin 4) : transform (B a) l = -∑ j, signs a j * R j l := by
    have ha := recover (fun i => transform (B i) l) a
    rw [row_transform_sum B hcol l, zero_add] at ha
    have hsum : -(∑ j, signs a j * R j l) =
        (∑ j, signs a j * transform (fun i => transform (B i) l) j) / 4 := by
      rw [← Finset.sum_neg_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by rw [hR, coordinate]; ring
    rw [hsum]
    linarith only [ha]
  rw [h 0, h r.succ, h (r + 1).succ, h (r + 2).succ]
  fin_cases r <;> norm_num [Fin.sum_univ_succ, signs, Fin.reduceAdd] <;>
    ring_nf <;> simp

private theorem signed_symmetric (U : Matrix (Fin 4) (Fin 4) ℂ) (l : Fin 3) (a b : Fin 4) :
    probability (signed U l) a b = probability (signed U l) b a := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M a b) (signed_star U l)
  change star (signed U l b a) = signed U l a b at h
  simp [probability, RHLinalg.normSqMatrix, ← h]

private theorem opposing_entries (B : Matrix (Fin 4) (Fin 4) ℝ)
    (hrow : ∀ a, ∑ b, B a b = 1) (hsymm : ∀ a b, B a b = B b a) (r : Fin 3) :
    2 * (B (r + 1).succ (r + 2).succ - B 0 r.succ) =
      B 0 0 + B r.succ r.succ - B (r + 1).succ (r + 1).succ - B (r + 2).succ (r + 2).succ := by
  have h0 := hrow 0
  have h1 := hrow 1
  have h2 := hrow 2
  have h3 := hrow 3
  have expand (a : Fin 4) : (∑ b, B a b) = B a 0 + (B a 1 + (B a 2 + B a 3)) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rfl
  rw [expand] at h0 h1 h2 h3
  rw [hsymm 1 0] at h1
  rw [hsymm 2 0, hsymm 2 1] at h2
  rw [hsymm 3 0, hsymm 3 1, hsymm 3 2] at h3
  fin_cases r <;> norm_num [Fin.reduceAdd]
  · linear_combination h2 + h3 - h0 - h1
  · rw [hsymm (3 : Fin 4) 1]
    linear_combination h1 + h3 - h0 - h2
  · linear_combination h1 + h2 - h0 - h3

private theorem diagonal_difference {U : Matrix (Fin 4) (Fin 4) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : ∀ r l, R r l = -(Hᵀ * probability U * H) r l) (r l : Fin 3) :
    gram (signed U l (r + 1).succ (r + 2).succ) (signed U l (r + 1).succ (r + 2).succ) =
    gram (signed U l 0 r.succ) (signed U l 0 r.succ) + 4 * R (r + 1) l * R (r + 2) l := by
  have hcol := (mem_doublyStochastic_iff_sum.mp
    (RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary hU)).2.2
  obtain ⟨h0, hr, hs, hv⟩ := row_coordinates (probability U) hcol hR r l
  have hsigned := (mem_doublyStochastic_iff_sum.mp
    (RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary (signed_unitary hU l))).2.1
  have h := opposing_entries (probability (signed U l)) hsigned (signed_symmetric U l) r
  change 2 * (‖signed U l (r + 1).succ (r + 2).succ‖ ^ 2 - ‖signed U l 0 r.succ‖ ^ 2) =
    ‖signed U l 0 0‖ ^ 2 + ‖signed U l r.succ r.succ‖ ^ 2 -
      ‖signed U l (r + 1).succ (r + 1).succ‖ ^ 2 -
      ‖signed U l (r + 2).succ (r + 2).succ‖ ^ 2 at h
  simp only [signed_diag, Complex.norm_real, Real.norm_eq_abs, sq_abs, h0, hr, hs, hv] at h
  simp only [gram_diag]
  nlinarith only [h]

private def good (R : Matrix (Fin 3) (Fin 3) ℝ) (r n : Fin 3) : Prop :=
  R r (n + 1) * R r (n + 2) ≤
    R (r + 1) (n + 1) * R (r + 1) (n + 2) + R (r + 2) (n + 1) * R (r + 2) (n + 2)

private theorem combinatorial_pairs (G : Fin 3 → Fin 3 → Prop)
    (hgood : ∀ n, G 0 n ∨ G 1 n) :
    ∃ r k : Fin 3, G r (k + 1) ∧ G r (k + 2) := by
  rcases hgood 0 with h0 | h0 <;> rcases hgood 1 with h1 | h1
  · exact ⟨0, 2, h0, h1⟩
  · rcases hgood 2 with h2 | h2
    · exact ⟨0, 1, h2, h0⟩
    · exact ⟨1, 0, h1, h2⟩
  · rcases hgood 2 with h2 | h2
    · exact ⟨0, 0, h1, h2⟩
    · exact ⟨1, 1, h2, h0⟩
  · exact ⟨1, 2, h0, h1⟩

private theorem two_good_pairs (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : ∀ i j, 0 < R i j) :
    ∃ r k : Fin 3, good R r (k + 1) ∧ good R r (k + 2) := by
  have h01 (n : Fin 3) : good R 0 n ∨ good R 1 n := by
    by_contra! ⟨h0, h1⟩
    simp only [good, Fin.reduceAdd] at h0 h1
    linarith [mul_pos (hR 2 (n + 1)) (hR 2 (n + 2))]
  exact combinatorial_pairs (good R) h01

private theorem gram_comm (z w : ℂ) : gram z w = gram w z := by
  unfold gram
  ring

private theorem gram_psd {n : ℕ} (z : Fin n → ℂ) :
    (Matrix.of fun i j => gram (z i) (z j)).PosSemidef := by
  let C : Matrix (Fin 2) (Fin n) ℝ := Matrix.of fun i j => ![(z j).re, (z j).im] i
  have h : Cᴴ * C = Matrix.of fun i j => gram (z i) (z j) := by
    ext i j
    simp [C, Matrix.mul_apply, Fin.sum_univ_two, gram]
  rw [← h]
  exact Matrix.posSemidef_conjTranspose_mul_self C

private def schur (z w t : ℂ) : ℝ := gram z w - gram z t * gram w t / gram t t

private theorem schur_facts (z w t : ℂ) (ht : 0 < gram t t) :
    0 ≤ schur z z t ∧ 0 ≤ schur w w t ∧ schur z z t * schur w w t = schur z w t ^ 2 := by
  let perp (x : ℂ) := x.re * t.im - x.im * t.re
  have h (x y : ℂ) : schur x y t = perp x * perp y / gram t t := by
    unfold schur perp
    field_simp [ne_of_gt ht]
    unfold gram
    ring
  rw [h z z, h w w, h z w]
  refine ⟨div_nonneg (mul_self_nonneg _) ht.le, div_nonneg (mul_self_nonneg _) ht.le, ?_⟩
  field_simp [ne_of_gt ht]

private theorem correction_le {a b x y : ℝ} (ha : 0 ≤ a) (hab : b ≤ a)
    (hx : 0 < x) (hxy : x ≤ y) : b / y ≤ a / x := by
  have hy := hx.trans_le hxy
  calc
    b / y ≤ a / y := div_le_div_of_nonneg_right hab hy.le
    _ ≤ a / x := div_le_div_of_nonneg_left ha hx hxy

private theorem schur_contradiction (p₁ p₂ p₃ q₁ q₂ q₃ : ℂ)
    (h₁ : gram p₁ p₁ < gram q₁ q₁) (h₂ : gram p₂ p₂ < gram q₂ q₂)
    (hpq : gram p₃ p₃ < gram q₃ q₃) (hq : gram q₃ q₃ ≤ 1)
    (a a' b b' : ℝ) (ha : -gram p₁ p₃ = a) (ha' : -gram p₂ p₃ = a')
    (hb : gram q₁ q₃ = b) (hb' : gram q₂ q₃ = b')
    (hab : |b| ≤ a) (hab' : |b'| ≤ a') (ha0 : 0 < a)
    {c : ℝ} (hc : 0 < c) (habSum : c ≤ a * a' + b * b')
    (hsum : gram p₁ p₂ + gram q₁ q₂ < c)
    (hdiff : gram p₁ p₂ < gram q₁ q₂) : False := by
  set x := gram p₃ p₃
  set y := gram q₃ q₃
  have hx : 0 < x := by
    have hnonneg : 0 ≤ x := (gram_psd ![p₁, p₂, p₃]).diag_nonneg (i := 2)
    refine lt_of_le_of_ne hnonneg ?_
    intro hzero
    have hz : p₃ = 0 := by
      have hnorm : ‖p₃‖ ^ 2 = 0 := (gram_diag p₃).symm.trans hzero.symm
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
    simp [hz, gram] at ha
    linarith
  have hxy : x < y := hpq
  have hy := hx.trans hxy
  have hyl : y ≤ 1 := hq
  have hxl := hxy.le.trans hyl
  have ha'0 := (abs_nonneg b').trans hab'
  have habProd : b * b' ≤ a * a' := by
    calc
      b * b' ≤ |b * b'| := le_abs_self _
      _ = |b| * |b'| := abs_mul _ _
      _ ≤ a * a' := mul_le_mul hab hab' (abs_nonneg _) ha0.le
  have hdiv₁ : b ^ 2 / y ≤ a ^ 2 / x := by
    apply correction_le (sq_nonneg _) _ hx hxy.le
    rw [← sq_abs b]
    exact pow_le_pow_left₀ (abs_nonneg _) hab 2
  have hdiv₂ : b' ^ 2 / y ≤ a' ^ 2 / x := by
    apply correction_le (sq_nonneg _) _ hx hxy.le
    rw [← sq_abs b']
    exact pow_le_pow_left₀ (abs_nonneg _) hab' 2
  have hdivDiff := correction_le (mul_nonneg ha0.le ha'0) habProd hx hxy.le
  have hdivSum : c ≤ a * a' / x + b * b' / y := by
    by_cases hbb : 0 ≤ b * b'
    · have hleft : a * a' ≤ a * a' / x := (le_div_iff₀ hx).mpr
        (mul_le_of_le_one_right (mul_nonneg ha0.le ha'0) hxl)
      have hright : b * b' ≤ b * b' / y :=
        (le_div_iff₀ hy).mpr (mul_le_of_le_one_right hbb hyl)
      linarith
    · have hneg : b * b' / x ≤ b * b' / y := by
        have hh := div_le_div_of_nonneg_left (neg_nonneg.mpr (le_of_not_ge hbb)) hx hxy.le
        simpa only [neg_div, neg_le_neg_iff] using hh
      calc
        c ≤ a * a' + b * b' := habSum
        _ ≤ (a * a' + b * b') / x :=
          (le_div_iff₀ hx).mpr (mul_le_of_le_one_right (hc.le.trans habSum) hxl)
        _ ≤ a * a' / x + b * b' / y := by rw [add_div]; exact add_le_add_right hneg _
  have hpa : gram p₁ p₃ = -a := by linarith
  have hpa' : gram p₂ p₃ = -a' := by linarith
  have hd₁ : schur p₁ p₁ p₃ < schur q₁ q₁ q₃ := by
    unfold schur
    rw [hpa, hb, neg_mul_neg, ← pow_two, ← pow_two]
    linarith only [h₁, hdiv₁]
  have hd₂ : schur p₂ p₂ p₃ < schur q₂ q₂ q₃ := by
    unfold schur
    rw [hpa', hb', neg_mul_neg, ← pow_two, ← pow_two]
    linarith only [h₂, hdiv₂]
  have hs : schur p₁ p₂ p₃ + schur q₁ q₂ q₃ < 0 := by
    unfold schur
    rw [hpa, hpa', hb, hb', neg_mul_neg]
    linarith
  have hd : schur p₁ p₂ p₃ < schur q₁ q₂ q₃ := by
    unfold schur
    rw [hpa, hpa', hb, hb', neg_mul_neg]
    linarith
  obtain ⟨hp₁, hp₂, hpdet⟩ := schur_facts p₁ p₂ p₃ hx
  obtain ⟨_, _, hqdet⟩ := schur_facts q₁ q₂ q₃ hy
  have habs : |schur q₁ q₂ q₃| < -schur p₁ p₂ p₃ :=
    abs_lt.mpr ⟨by simpa using hd, by linarith⟩
  have hoff := pow_lt_pow_left₀ habs (abs_nonneg _) (by decide : 2 ≠ 0)
  rw [sq_abs, neg_sq, ← hpdet, ← hqdet] at hoff
  have hdiag := mul_lt_mul_of_lt_of_le_of_nonneg_of_pos hd₁ hd₂.le hp₁ (hp₂.trans_lt hd₂)
  exact (not_lt_of_ge hdiag.le) hoff

private theorem off_diagonal {U : Matrix (Fin 4) (Fin 4) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) {T : Matrix (Fin 3) (Fin 3) ℝ}
    (hT : ∀ r l, T r l = -(Hᵀ * probability U * H) r l) (r n : Fin 3) :
    let R := T r
    let S := T (r + 1)
    let V := T (r + 2)
    let i := n + 1
    let j := n + 2
    gram (signed U i 0 r.succ) (signed U j 0 r.succ) =
      -R n + R i * R j - (S i + V i) * (S j + V j) ∧
    gram (signed U i (r + 1).succ (r + 2).succ) (signed U j (r + 1).succ (r + 2).succ) =
      R n + R i * R j - (S i - V i) * (S j - V j) := by
  have hcol := (mem_doublyStochastic_iff_sum.mp
    (RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary hU)).2.2
  have hrow := row_coordinates (probability U) hcol hT r
  have hp := signed_cross hU (a := 0) (b := r.succ) (by fin_cases r <;> decide) n
  have hq := signed_cross hU (a := (r + 1).succ) (b := (r + 2).succ)
    (by fin_cases r <;> decide) n
  dsimp only
  constructor
  · rw [hp, (hrow n).1, (hrow n).2.1, (hrow (n + 1)).1, (hrow (n + 1)).2.1,
      (hrow (n + 2)).1, (hrow (n + 2)).2.1]
    ring
  · rw [hq, (hrow n).2.2.1, (hrow n).2.2.2, (hrow (n + 1)).2.2.1,
      (hrow (n + 1)).2.2.2, (hrow (n + 2)).2.2.1, (hrow (n + 2)).2.2.2]
    ring

private theorem pair_bounds {r s v i j k p q : ℝ}
    (hr : 0 < r) (hsi : 0 < s) (hvi : 0 < v) (hsj : 0 < j) (hvj : 0 < k)
    (hgood : i ≤ s * j + v * k)
    (hp : p = -r + i - (s + v) * (j + k))
    (hq : q = r + i - (s - v) * (j - k)) :
    0 < -p ∧ |q| ≤ -p ∧ 2 * r ≤ -p + q ∧ 0 ≤ -p - q := by
  have hdiff : 0 ≤ -p - q := by nlinarith only [hgood, hp, hq]
  have hsum : 2 * r ≤ -p + q := by
    nlinarith only [hp, hq, mul_pos hsi hvj, mul_pos hvi hsj]
  refine ⟨by linarith, abs_le.mpr ⟨?_, ?_⟩, hsum, hdiff⟩ <;> linarith

private theorem cyclic (k : Fin 3) :
    (k + 1) + 1 = k + 2 ∧ (k + 1) + 2 = k ∧
    (k + 2) + 1 = k ∧ (k + 2) + 2 = k + 1 := by
  fin_cases k <;> decide

/-- No complex order-four unitary has strictly negative entries in all nine Type I− coordinates. -/
theorem exists_nonneg_typeIMinus (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    ∃ i j : Fin 3, 0 ≤ (Hᵀ * RHLinalg.normSqMatrix U * H) i j := by
  by_contra! h
  let T : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun r l => -(Hᵀ * probability U * H) r l
  have hT (r l) : T r l = -(Hᵀ * probability U * H) r l := rfl
  have hpos (r l) : 0 < T r l := neg_pos.mpr (h r l)
  obtain ⟨r, k, hg₂, hg₁⟩ := two_good_pairs T hpos
  let i := k + 1
  let j := k + 2
  let p (l : Fin 3) := signed U l 0 r.succ
  let q (l : Fin 3) := signed U l (r + 1).succ (r + 2).succ
  let R := T r
  let S := T (r + 1)
  let V := T (r + 2)
  have hdiag (l : Fin 3) : gram (p l) (p l) < gram (q l) (q l) := by
    change gram (signed U l 0 r.succ) (signed U l 0 r.succ) < _
    rw [diagonal_difference hU hT]
    have hδ := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) (hpos (r + 1) l))
      (hpos (r + 2) l)
    linarith
  have hupper : gram (q k) (q k) ≤ 1 := by
    rw [gram_diag]
    have hb := (mem_doublyStochastic_iff_sum.mp
      (RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary (signed_unitary hU k)))
    have hs := Finset.single_le_sum (fun b _ => hb.1 (r + 1).succ b)
      (Finset.mem_univ ((r + 2).succ))
    rw [hb.2.1] at hs
    exact hs
  obtain ⟨hc₁, hc₂, hc₃, hc₄⟩ := cyclic k
  have hoff (n : Fin 3) :
      gram (p (n + 1)) (p (n + 2)) = -R n + R (n + 1) * R (n + 2) -
        (S (n + 1) + V (n + 1)) * (S (n + 2) + V (n + 2)) ∧
      gram (q (n + 1)) (q (n + 2)) = R n + R (n + 1) * R (n + 2) -
        (S (n + 1) - V (n + 1)) * (S (n + 2) - V (n + 2)) := off_diagonal hU hT r n
  obtain ⟨hp₁, hq₁⟩ := hoff (k + 2)
  rw [hc₃, hc₄, gram_comm (p k)] at hp₁
  rw [hc₃, hc₄, gram_comm (q k)] at hq₁
  obtain ⟨hp₂, hq₂⟩ := hoff (k + 1)
  rw [hc₁, hc₂] at hp₂ hq₂
  have hgood₁ : R k * R i ≤ S k * S i + V k * V i := by
    unfold good at hg₁
    rwa [hc₃, hc₄] at hg₁
  have hgood₂ : R j * R k ≤ S j * S k + V j * V k := by
    unfold good at hg₂
    rwa [hc₁, hc₂] at hg₂
  set a := -gram (p i) (p k)
  set a' := -gram (p j) (p k)
  set b := gram (q i) (q k)
  set b' := gram (q j) (q k)
  obtain ⟨ha, hab, hsum₁, hdiff₁⟩ :=
    pair_bounds (hpos r j) (hpos (r + 1) k) (hpos (r + 2) k) (hpos (r + 1) i)
      (hpos (r + 2) i) hgood₁ hp₁ hq₁
  obtain ⟨_, hab', hsum₂, hdiff₂⟩ :=
    pair_bounds (hpos r i) (hpos (r + 1) j) (hpos (r + 2) j) (hpos (r + 1) k)
      (hpos (r + 2) k) hgood₂ hp₂ hq₂
  change |b| ≤ a at hab
  change |b'| ≤ a' at hab'
  change 2 * R j ≤ a + b at hsum₁
  change 2 * R i ≤ a' + b' at hsum₂
  change 0 ≤ a - b at hdiff₁
  change 0 ≤ a' - b' at hdiff₂
  have hc : 0 < 2 * R i * R j := mul_pos (mul_pos (by norm_num) (hpos r i)) (hpos r j)
  have hprod : 2 * R i * R j ≤ a * a' + b * b' := by
    have hmul := mul_le_mul hsum₁ hsum₂
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hpos r i).le)
      ((mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hpos r j).le).trans hsum₁)
    nlinarith only [hmul, mul_nonneg hdiff₁ hdiff₂]
  obtain ⟨hp, hq⟩ := hoff k
  have hsum : gram (p i) (p j) + gram (q i) (q j) < 2 * R i * R j := by
    nlinarith only [hp, hq, mul_pos (hpos (r + 1) i) (hpos (r + 1) j),
      mul_pos (hpos (r + 2) i) (hpos (r + 2) j)]
  have hdiff : gram (p i) (p j) < gram (q i) (q j) := by
    nlinarith only [hp, hq, hpos r k, mul_pos (hpos (r + 1) i) (hpos (r + 2) j),
      mul_pos (hpos (r + 2) i) (hpos (r + 1) j)]
  exact schur_contradiction (p i) (p j) (p k) (q i) (q j) (q k)
    (hdiag i) (hdiag j) (hdiag k) hupper a a' b b' rfl rfl rfl rfl hab hab' ha hc hprod hsum hdiff

end D5.S3.Quantum.Matrix.UnistochasticTypeIMinus
