/- GID: D5/S3/Quantum/Recovery/PetzRetainedQubitPairing
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzRetainedQubitPairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Opposite retained-qubit blocks share the norms of their noncentral coefficients. -/

import D5.S3.Quantum.Recovery.PetzSupportedLinearRank

/-! Centered logistic estimates for the opposite blocks of the ordinary Petz boundary. -/

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.Frobenius Kronecker
open D5.S3.Quantum.Recovery.PetzMixedBoundaryEvaluation (mixedBoundary)
open PetzLogisticEvaluation (correlation)
open PetzExponentialBoundaryEvaluation (petzWeight)
open scoped ComplexOrder MatrixOrder

open ExponentialGramWeightedEvaluation (exponentialSum frequency)

open private frobenius_sq from
  D5.S3.Quantum.Recovery.PetzExponentialBoundaryEvaluation
open private mixedBoundary_entry mixedFrequency from
  D5.S3.Quantum.Recovery.PetzMixedBoundaryEvaluation
open private gamma_norm_sq integral_logExponentialMode weighted_energy_eq_gram from
  D5.S3.Analytic.PetzLogisticEvaluation

namespace D5.S3.Quantum.Recovery.PetzRetainedQubitPairing

local notation "d" => (Real.sqrt 2 / 2)
local notation "λ₀" => (1 + Real.sqrt 2 / 2)

private theorem root_bounds : (7 / 10 : ℝ) < d ∧ d < 1 := by
  have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith

private def diagonal (x : ℝ) : ℝ := d + 2 * x - (λ₀ + 1) * x ^ 2

private def cross (x y z : ℝ) : ℝ := λ₀ * z - 1 + x + y - (λ₀ + 1) * x * y

private theorem centered_determinant {x y z η : ℝ}
    (hx : 0 ≤ x) (hx' : x ≤ 1 / 5) (hy : 0 ≤ y) (hy' : y ≤ 1 / 5)
    (hz : 0 ≤ z) (hz' : z ≤ 1) (hη : 0 ≤ η) (hη' : η ≤ 1)
    (hshape : η * (1 - z / 2) ≤ d)
    (hgap : (x - y) ^ 2 ≤ (7 / 25) * (1 - z)) :
    0 ≤ diagonal x ∧ 0 ≤ diagonal y ∧ η ^ 2 * cross x y z ^ 2 ≤ diagonal x * diagonal y := by
  have hLambda : λ₀ < 2 := by linarith [root_bounds.2]
  have hLambda_nonneg : 0 ≤ λ₀ := by linarith [root_bounds.1]
  have hfirst {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 5) : d ≤ diagonal t := by
    unfold diagonal
    have hm : (λ₀ + 1) * t ≤ 3 * (1 / 5 : ℝ) :=
      mul_le_mul (by linarith) ht' ht (by norm_num)
    nlinarith [mul_nonneg ht (show 0 ≤ 2 - (λ₀ + 1) * t by linarith)]
  have ha := hfirst hx hx'
  have hb := hfirst hy hy'
  have hd : 0 ≤ d := by linarith [root_bounds.1]
  refine ⟨hd.trans ha, hd.trans hb, ?_⟩
  have hxy : 0 ≤ x + y - (λ₀ + 1) * x * y := by
    have hm : (λ₀ + 1) * x ≤ 3 * (1 / 5 : ℝ) :=
      mul_le_mul (by linarith) hx' hx (by norm_num)
    nlinarith [mul_nonneg hy (show 0 ≤ 1 - (λ₀ + 1) * x by linarith)]
  rcases le_total (cross x y z) 0 with hc | hc
  · have hB : -(cross x y z) ≤ 1 - z / 2 := by
      unfold cross
      nlinarith [mul_nonneg hz (show 0 ≤ λ₀ - 1 / 2 by linarith [root_bounds.1])]
    have ηB : η * -(cross x y z) ≤ d :=
      (mul_le_mul_of_nonneg_left hB hη).trans hshape
    calc
      _ = (η * -(cross x y z)) ^ 2 := by ring
      _ ≤ d ^ 2 := pow_le_pow_left₀ (mul_nonneg hη (neg_nonneg.mpr hc)) ηB 2
      _ ≤ _ := by
        rw [sq]
        exact mul_le_mul ha hb hd (hd.trans ha)
  · let B₁ := cross x y 1
    have hB₁ : d ≤ B₁ := by
      dsimp [B₁, cross]
      linarith
    have hdiff : B₁ - cross x y z = λ₀ * (1 - z) := by dsimp [B₁, cross]; ring
    have hidentity : diagonal x * diagonal y - B₁ ^ 2 = -λ₀ ^ 2 * (x - y) ^ 2 := by
      dsimp [B₁, diagonal, cross]
      generalize Real.sqrt (2 : ℝ) = t
      ring
    have hthreshold : λ₀ * (7 / 25 : ℝ) ≤ d := by linarith [root_bounds.1]
    have hmul : λ₀ ^ 2 * (x - y) ^ 2 ≤
        (λ₀ * (1 - z)) * (B₁ + cross x y z) := calc
      _ ≤ λ₀ ^ 2 * ((7 / 25) * (1 - z)) :=
        mul_le_mul_of_nonneg_left hgap (sq_nonneg _)
      _ = (λ₀ * (1 - z)) * (λ₀ * (7 / 25)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg hLambda_nonneg (sub_nonneg.mpr hz'))
    have hsq : cross x y z ^ 2 ≤ diagonal x * diagonal y := by
      rw [← hdiff] at hmul
      nlinarith only [hmul, hidentity]
    calc
      _ ≤ 1 ^ 2 * cross x y z ^ 2 := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hη hη' 2) (sq_nonneg _)
      _ = cross x y z ^ 2 := by ring
      _ ≤ _ := hsq

private theorem centered_quadratic {x y z η u v r : ℝ}
    (hx : 0 ≤ x) (hx' : x ≤ 1 / 5) (hy : 0 ≤ y) (hy' : y ≤ 1 / 5)
    (hz : 0 ≤ z) (hz' : z ≤ 1) (hη : 0 ≤ η) (hη' : η ≤ 1)
    (hshape : η * (1 - z / 2) ≤ d)
    (hgap : (x - y) ^ 2 ≤ (7 / 25) * (1 - z))
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hr : |r| ≤ η * (u * v)) :
    (1 - x) ^ 2 * u ^ 2 + (1 - y) ^ 2 * v ^ 2 + 2 * (1 - x) * (1 - y) * r ≤
      λ₀ * ((1 - x ^ 2) * u ^ 2 + (1 - y ^ 2) * v ^ 2 + 2 * (z - x * y) * r) := by
  obtain ⟨ha, hb, hab⟩ := centered_determinant hx hx' hy hy' hz hz' hη hη' hshape hgap
  let A := diagonal x
  let B := diagonal y
  let C := cross x y z
  have hroots : (Real.sqrt A * Real.sqrt B) ^ 2 = A * B := by
    rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]
  have hcoef : η * |C| ≤ Real.sqrt A * Real.sqrt B := by
    have hs : (η * |C|) ^ 2 ≤ (Real.sqrt A * Real.sqrt B) ^ 2 := by
      rw [hroots, mul_pow, sq_abs]
      exact hab
    exact (sq_le_sq₀ (mul_nonneg hη (abs_nonneg _)) (by positivity)).mp hs
  have hpair : -(C * r) ≤ (Real.sqrt A * Real.sqrt B) * (u * v) := calc
    _ ≤ |C * r| := neg_le_abs _
    _ = |C| * |r| := abs_mul _ _
    _ ≤ |C| * (η * (u * v)) := mul_le_mul_of_nonneg_left hr (abs_nonneg _)
    _ = (η * |C|) * (u * v) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hu hv)
  have hq : 0 ≤ A * u ^ 2 + B * v ^ 2 + 2 * C * r := by
    have hsq : (Real.sqrt A * u - Real.sqrt B * v) ^ 2 =
        A * u ^ 2 + B * v ^ 2 - 2 * (Real.sqrt A * Real.sqrt B) * (u * v) := by
      rw [sub_sq, mul_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]
      ring
    nlinarith only [hpair, hsq, sq_nonneg (Real.sqrt A * u - Real.sqrt B * v)]
  dsimp [A, B, C, diagonal, cross] at hq
  linarith only [hq]

private def logistic (t : ℝ) : ℝ :=
  if t = 0 then 1 else (t / 2) / Real.sinh (t / 2)

private theorem logistic_neg (t : ℝ) : logistic (-t) = logistic t := by
  simp only [logistic, neg_eq_zero, neg_div, Real.sinh_neg, div_neg, neg_neg]

private theorem logistic_bounds (t : ℝ) : 0 ≤ logistic t ∧ logistic t ≤ 1 := by
  suffices h : ∀ s ≥ (0 : ℝ), 0 ≤ logistic s ∧ logistic s ≤ 1 by
    rcases le_total 0 t with ht | ht
    · exact h t ht
    · rw [← logistic_neg]
      exact h (-t) (neg_nonneg.mpr ht)
  intro s hs
  rcases eq_or_lt_of_le hs with rfl | hs
  · norm_num [logistic]
  have hhalf : 0 < s / 2 := by positivity
  have hden := Real.sinh_pos_iff.mpr hhalf
  rw [logistic, ite_eq_right hs.ne']
  exact ⟨div_nonneg hhalf.le hden.le, (div_le_one₀ hden).2
    (Real.self_le_sinh_iff.mpr hhalf.le)⟩

private theorem logistic_ge_sech_sq (t : ℝ) : 1 / Real.cosh (t / 4) ^ 2 ≤ logistic t := by
  have hmon : MonotoneOn (fun u : ℝ => u * Real.cosh u - Real.sinh u) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) (by fun_prop)
    · intro x _
      exact (((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
        (Real.hasDerivAt_sinh x)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : 0 ≤ x := interior_subset hx
      change 0 ≤ deriv (id * Real.cosh - Real.sinh) x
      rw [(((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
        (Real.hasDerivAt_sinh x)).deriv]
      simp only [id_eq, one_mul, add_sub_cancel_left]
      exact mul_nonneg hx' (Real.sinh_nonneg_iff.mpr hx')
  suffices h : ∀ s ≥ (0 : ℝ), 1 / Real.cosh (s / 4) ^ 2 ≤ logistic s by
    rcases le_total 0 t with ht | ht
    · exact h t ht
    · simpa only [neg_div, Real.cosh_neg, logistic_neg] using h (-t) (neg_nonneg.mpr ht)
  intro s hs
  rcases eq_or_lt_of_le hs with rfl | hs
  · norm_num [logistic]
  let u := s / 4
  have hu : 0 < u := by positivity
  have hc := Real.cosh_pos u
  have hval : Real.sinh u ≤ u * Real.cosh u := by
    have h := hmon (show (0 : ℝ) ∈ Set.Ici (0 : ℝ) by simp) hu.le hu.le
    simpa only [zero_mul, Real.sinh_zero, sub_zero, sub_nonneg] using h
  rw [logistic, ite_eq_right hs.ne', show s / 2 = 2 * u by dsimp [u]; ring, Real.sinh_two_mul]
  change 1 / Real.cosh u ^ 2 ≤ 2 * u / (2 * Real.sinh u * Real.cosh u)
  apply (div_le_div_iff₀ (sq_pos_of_pos hc) (by positivity : 0 < 2 * Real.sinh u * Real.cosh u)).2
  nlinarith only [mul_le_mul_of_nonneg_right hval (show 0 ≤ 2 * Real.cosh u by positivity)]

private theorem logistic_correlation {ι : Type*} (ω : ι → ℝ) (i j : ι) :
    (‖correlation ω i j‖ ^ 2 : ℂ) = (logistic (ω j - ω i) : ℂ) := by
  rw [correlation, Matrix.of_apply, integral_logExponentialMode]
  exact gamma_norm_sq _

section Blocks

variable {e : Type*} [Fintype e]

private abbrev Qubit := Fin 2

private def block (X : Matrix (Qubit × e) (Qubit × e) ℂ) (i j : Qubit) :
    Matrix e e ℂ := fun u v => X (i, u) (j, v)

omit [Fintype e] in
private theorem block_adjoint {X : Matrix (Qubit × e) (Qubit × e) ℂ}
    (hX : X.IsHermitian) (i j : Qubit) : (block X i j)ᴴ = block X j i := by
  ext u v
  exact congrFun (congrFun hX.eq (j, u)) (i, v)

private theorem opposite_norm {U : Matrix Qubit Qubit ℂ}
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) (i j : Qubit) :
    ‖U i j‖ = ‖U i.rev j.rev‖ := by
  have hrow (i : Qubit) : ‖U i 0‖ ^ 2 + ‖U i 1‖ ^ 2 = 1 := by
    have h := congrArg Complex.re (congrFun (congrFun hU' i) i)
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Matrix.one_apply_eq, Complex.add_re, RCLike.star_def, Complex.mul_conj,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq, Complex.one_re] using h
  have hcol (j : Qubit) : ‖U 0 j‖ ^ 2 + ‖U 1 j‖ ^ 2 = 1 := by
    have h := congrArg Complex.re (congrFun (congrFun hU j) j)
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Matrix.one_apply_eq, Complex.add_re, RCLike.star_def, Complex.conj_mul',
      ← Complex.ofReal_pow, Complex.ofReal_re, Complex.one_re] using h
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  fin_cases i <;> fin_cases j
  · change ‖U 0 0‖ ^ 2 = ‖U 1 1‖ ^ 2
    linarith only [hrow 0, hcol 1]
  · change ‖U 0 1‖ ^ 2 = ‖U 1 0‖ ^ 2
    linarith only [hrow 0, hcol 0]
  · change ‖U 1 0‖ ^ 2 = ‖U 0 1‖ ^ 2
    linarith only [hrow 0, hcol 0]
  · change ‖U 1 1‖ ^ 2 = ‖U 0 0‖ ^ 2
    linarith only [hrow 0, hcol 1]

private def innerRe (A B : Matrix e e ℂ) : ℝ :=
  ∑ u, ∑ v, (star (A u v) * B u v).re

private theorem abs_innerRe_le (A B : Matrix e e ℂ) : |innerRe A B| ≤ ‖A‖ * ‖B‖ := by
  let a (uv : e × e) := ‖A uv.1 uv.2‖
  let b (uv : e × e) := ‖B uv.1 uv.2‖
  have ha : (∑ uv, a uv ^ 2) = ‖A‖ ^ 2 := by
    rw [frobenius_sq, Fintype.sum_prod_type]
  have hb : (∑ uv, b uv ^ 2) = ‖B‖ ^ 2 := by
    rw [frobenius_sq, Fintype.sum_prod_type]
  have hn : (∑ uv, a uv * b uv) ≤ ‖A‖ * ‖B‖ := by
    apply (sq_le_sq₀ (Finset.sum_nonneg fun uv _ =>
      mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, ← ha, ← hb]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ a b
  have hentry (uv : e × e) :
      |(star (A uv.1 uv.2) * B uv.1 uv.2).re| ≤ a uv * b uv := by
    refine (Complex.abs_re_le_norm _).trans_eq ?_
    simp [a, b]
  unfold innerRe
  rw [← Fintype.sum_prod_type (f := fun uv : e × e => (star (A uv.1 uv.2) * B uv.1 uv.2).re)]
  exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun uv _ => hentry uv).trans hn)

private def halfRatio (p q : ℝ) : ℝ := Real.exp ((Real.log p - Real.log q) / 2)

private def pairedAngle (h k : ℝ) : ℝ := (h + k) / Real.sqrt (2 * (h ^ 2 + k ^ 2))

private theorem pairedAngle_bounds {h k : ℝ} (hh : 0 < h) (hk : 0 < k) :
    0 ≤ pairedAngle h k ∧ pairedAngle h k ≤ 1 ∧
      pairedAngle h k * (1 - (4 * h * k / (h + k) ^ 2) / 2) ≤ d := by
  have hd₀ : 0 ≤ d := by linarith [root_bounds.1]
  have hd₂ : d ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsum : 0 < h + k := add_pos hh hk
  have hss : 0 < h ^ 2 + k ^ 2 := by positivity
  have hden : 0 < Real.sqrt (2 * (h ^ 2 + k ^ 2)) := Real.sqrt_pos.2 (by positivity)
  have hden₂ := Real.sq_sqrt (show 0 ≤ 2 * (h ^ 2 + k ^ 2) by positivity)
  have hprod : 0 ≤ h * k := mul_nonneg hh.le hk.le
  refine ⟨div_nonneg hsum.le hden.le, ?_, ?_⟩
  · apply (div_le_iff₀ hden).2
    rw [one_mul]
    apply (sq_le_sq₀ hsum.le hden.le).mp
    rw [hden₂]
    nlinarith only [sq_nonneg (h-k)]
  · have hid : 1 - (4 * h * k / (h + k) ^ 2) / 2 =
        (h ^ 2 + k ^ 2) / (h + k) ^ 2 := by
      field_simp [hsum.ne']
      ring
    have hcancel : pairedAngle h k * ((h ^ 2 + k ^ 2) / (h + k) ^ 2) =
        (h ^ 2 + k ^ 2) / (Real.sqrt (2 * (h ^ 2 + k ^ 2)) * (h + k)) := by
      unfold pairedAngle
      field_simp [hsum.ne', hden.ne']
    rw [hid, hcancel]
    apply (div_le_iff₀ (mul_pos hden hsum)).2
    apply (sq_le_sq₀ hss.le (mul_nonneg hd₀ (mul_nonneg hden.le hsum.le))).mp
    rw [mul_pow, mul_pow, hd₂, hden₂]
    nlinarith only [mul_nonneg hss.le (show 0 ≤ (h + k) ^ 2 - (h ^ 2 + k ^ 2) by
      nlinarith only [hprod])]

private theorem halfRatio_shape (a b c f : ℝ) :
    4 * halfRatio a b * halfRatio c f / (halfRatio a b + halfRatio c f) ^ 2 =
      1 / Real.cosh (((Real.log c - Real.log a) - (Real.log f - Real.log b)) / 4) ^ 2 := by
  let x := Real.log a - Real.log b
  let y := Real.log c - Real.log f
  have hxy : (Real.log c - Real.log a) - (Real.log f - Real.log b) = y - x := by
    dsimp [x, y]
    ring
  rw [hxy]
  change 4 * Real.exp (x / 2) * Real.exp (y / 2) /
    (Real.exp (x / 2) + Real.exp (y / 2)) ^ 2 = _
  let m := Real.exp ((x + y) / 4)
  have hm : 0 < m := Real.exp_pos _
  have hpos : Real.exp (x / 2) + Real.exp (y / 2) = 2 * m * Real.cosh ((y-x)/4) := by
    rw [Real.cosh_eq]
    calc
      _ = m * Real.exp ((y - x) / 4) + m * Real.exp (-((y - x) / 4)) := by
        dsimp [m]
        rw [← Real.exp_add, ← Real.exp_add, show (x+y)/4 + (y-x)/4 = y/2 by ring,
          show (x+y)/4 + -((y-x)/4) = x/2 by ring]
        ring
      _ = _ := by ring
  have hprod : Real.exp (x / 2) * Real.exp (y / 2) = m ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    dsimp [m]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hpos, mul_assoc 4, hprod]
  have hc := (Real.cosh_pos ((y-x)/4)).ne'
  field_simp [hm.ne', hc]
  ring

private def sourceOff (U : Matrix Qubit Qubit ℂ) (X : Matrix (Qubit × e) (Qubit × e) ℂ)
    (i j : Qubit) : Matrix e e ℂ := U i j.rev • block X j.rev j

private def referenceOff (p q : Qubit → ℝ) (U : Matrix Qubit Qubit ℂ)
    (Y : Matrix (Qubit × e) (Qubit × e) ℂ) (i j : Qubit) : Matrix e e ℂ :=
  (-(halfRatio (p j) (q i.rev) : ℂ) * U i.rev j) • block Y i i.rev

private theorem paired_inner_bound (p q : Qubit → ℝ) (U : Matrix Qubit Qubit ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (X Y : Matrix (Qubit × e) (Qubit × e) ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (i j : Qubit) :
    let A := sourceOff U X i j
    let A' := sourceOff U X i.rev j.rev
    let B := referenceOff p q U Y i j
    let B' := referenceOff p q U Y i.rev j.rev
    let h := halfRatio (p j) (q i.rev)
    let k := halfRatio (p j.rev) (q i)
    |innerRe A B + innerRe A' B'| ≤ pairedAngle h k *
      (Real.sqrt (‖A‖ ^ 2 + ‖A'‖ ^ 2) * Real.sqrt (‖B‖ ^ 2 + ‖B'‖ ^ 2)) := by
  dsimp only
  let m := ‖U i j.rev‖
  let h := halfRatio (p j) (q i.rev)
  let k := halfRatio (p j.rev) (q i)
  let a := m * ‖block X j.rev j‖
  let b := m * ‖block Y i i.rev‖
  have hh : 0 < h := Real.exp_pos _
  have hk : 0 < k := Real.exp_pos _
  have ha : 0 ≤ a := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hb : 0 ≤ b := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hOpp := opposite_norm hU hU' i j.rev
  rw [Fin.rev_rev] at hOpp
  have hA : ‖sourceOff U X i j‖ = a := by simp [sourceOff, a, m, norm_smul]
  have hA' : ‖sourceOff U X i.rev j.rev‖ = a := by
    rw [sourceOff, norm_smul, Fin.rev_rev, ← hOpp, ← block_adjoint hX j.rev j,
      Matrix.frobenius_norm_conjTranspose]
  have hB : ‖referenceOff p q U Y i j‖ = h * b := by
    rw [referenceOff, norm_smul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hh, ← hOpp]
    ring
  have hB' : ‖referenceOff p q U Y i.rev j.rev‖ = k * b := by
    rw [referenceOff, Fin.rev_rev, norm_smul, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hk, ← block_adjoint hY i i.rev,
      Matrix.frobenius_norm_conjTranspose]
    ring
  have hscale : (h + k) * a * b = pairedAngle h k *
      (Real.sqrt (a ^ 2 + a ^ 2) * Real.sqrt ((h * b) ^ 2 + (k * b) ^ 2)) := by
    have h₂ : 0 ≤ (2 : ℝ) := by norm_num
    have hs : 0 ≤ h ^ 2 + k ^ 2 := by positivity
    rw [show a ^ 2 + a ^ 2 = 2 * a ^ 2 by ring,
      show (h * b) ^ 2 + (k * b) ^ 2 = (h ^ 2 + k ^ 2) * b ^ 2 by ring,
      Real.sqrt_mul h₂, Real.sqrt_mul hs, Real.sqrt_sq ha, Real.sqrt_sq hb,
      pairedAngle, Real.sqrt_mul h₂]
    have hp : Real.sqrt 2 * Real.sqrt (h ^ 2 + k ^ 2) ≠ 0 := by positivity
    field_simp [hp]
  calc
    _ ≤ |innerRe (sourceOff U X i j) (referenceOff p q U Y i j)| +
        |innerRe (sourceOff U X i.rev j.rev) (referenceOff p q U Y i.rev j.rev)| := abs_add_le _ _
    _ ≤ ‖sourceOff U X i j‖ * ‖referenceOff p q U Y i j‖ +
        ‖sourceOff U X i.rev j.rev‖ * ‖referenceOff p q U Y i.rev j.rev‖ :=
      add_le_add (abs_innerRe_le _ _) (abs_innerRe_le _ _)
    _ = _ := by
      rw [hA, hA', hB, hB', ← hscale]
      ring

private def sourceGap (p : Qubit → ℝ) (j : Qubit) : ℝ :=
  Real.log (p j.rev) - Real.log (p j)

private def referenceGap (q : Qubit → ℝ) (i : Qubit) : ℝ :=
  Real.log (q i) - Real.log (q i.rev)

private theorem pair_shape (p q : Qubit → ℝ) (i j : Qubit) :
    let h := halfRatio (p j) (q i.rev)
    let k := halfRatio (p j.rev) (q i)
    let z := logistic (sourceGap p j - referenceGap q i)
    pairedAngle h k * (1 - z / 2) ≤ d := by
  dsimp only
  let h := halfRatio (p j) (q i.rev)
  let k := halfRatio (p j.rev) (q i)
  have hh : 0 < h := Real.exp_pos _
  have hk : 0 < k := Real.exp_pos _
  have hsech := halfRatio_shape (p j) (q i.rev) (p j.rev) (q i)
  have hz := logistic_ge_sech_sq (sourceGap p j - referenceGap q i)
  have hz' : 4 * h * k / (h + k) ^ 2 ≤ logistic (sourceGap p j - referenceGap q i) := by
    exact hsech.le.trans hz
  obtain ⟨h₀, _, hb⟩ := pairedAngle_bounds hh hk
  exact (mul_le_mul_of_nonneg_left (by linarith only [hz']) h₀).trans hb

private def centeredEndpoint (x y : ℝ) (A B : Matrix e e ℂ) : Matrix e e ℂ :=
  (1 - (x : ℂ)) • A + (1 - (y : ℂ)) • B

private theorem norm_centeredEndpoint (x y : ℝ) (A B : Matrix e e ℂ) :
    ‖centeredEndpoint x y A B‖ ^ 2 =
      (1-x)^2 * ‖A‖^2 + (1-y)^2 * ‖B‖^2 + 2*(1-x)*(1-y)*innerRe A B := by
  simp only [centeredEndpoint, innerRe, frobenius_sq]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.sq_norm,
    Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

private def centeredEnergy (x y z : ℝ) (A B : Matrix e e ℂ) : ℝ :=
  (1 - x ^ 2) * ‖A‖ ^ 2 + (1 - y ^ 2) * ‖B‖ ^ 2 + 2 * (z - x * y) * innerRe A B

private theorem physical_centered_pair (p q : Qubit → ℝ) (U : Matrix Qubit Qubit ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (X Y : Matrix (Qubit × e) (Qubit × e) ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (i j : Qubit)
    (hx : logistic (sourceGap p j) ≤ 1 / 5) (hy : logistic (referenceGap q i) ≤ 1 / 5)
    (hgap : (logistic (sourceGap p j) - logistic (referenceGap q i)) ^ 2 ≤
      (7 / 25) * (1 - logistic (sourceGap p j - referenceGap q i))) :
    let x := logistic (sourceGap p j)
    let y := logistic (referenceGap q i)
    let z := logistic (sourceGap p j - referenceGap q i)
    let A := sourceOff U X i j
    let A' := sourceOff U X i.rev j.rev
    let B := referenceOff p q U Y i j
    let B' := referenceOff p q U Y i.rev j.rev
    ‖centeredEndpoint x y A B‖ ^ 2 + ‖centeredEndpoint x y A' B'‖ ^ 2 ≤
      λ₀ * (centeredEnergy x y z A B + centeredEnergy x y z A' B') := by
  dsimp only
  let x := logistic (sourceGap p j)
  let y := logistic (referenceGap q i)
  let z := logistic (sourceGap p j - referenceGap q i)
  let A := sourceOff U X i j
  let A' := sourceOff U X i.rev j.rev
  let B := referenceOff p q U Y i j
  let B' := referenceOff p q U Y i.rev j.rev
  let h := halfRatio (p j) (q i.rev)
  let k := halfRatio (p j.rev) (q i)
  change ‖centeredEndpoint x y A B‖ ^ 2 + ‖centeredEndpoint x y A' B'‖ ^ 2 ≤
    λ₀ * (centeredEnergy x y z A B + centeredEnergy x y z A' B')
  have hpair : |innerRe A B + innerRe A' B'| ≤ pairedAngle h k *
      (Real.sqrt (‖A‖ ^ 2 + ‖A'‖ ^ 2) * Real.sqrt (‖B‖ ^ 2 + ‖B'‖ ^ 2)) :=
    paired_inner_bound p q U hU hU' X Y hX hY i j
  have hang := pairedAngle_bounds (show 0 < h from Real.exp_pos _) (show 0 < k from Real.exp_pos _)
  have hz := logistic_bounds (sourceGap p j - referenceGap q i)
  have hresult := centered_quadratic (logistic_bounds (sourceGap p j)).1 hx
    (logistic_bounds (referenceGap q i)).1 hy hz.1 hz.2 hang.1 hang.2.1
    (pair_shape p q i j) hgap (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hpair
  change _ ≤ λ₀ * ((1-x^2) * _ + (1-y^2) * _ + 2*(z-x*y)*_) at hresult
  rw [Real.sq_sqrt (by positivity : 0 ≤ ‖A‖ ^ 2 + ‖A'‖ ^ 2),
    Real.sq_sqrt (by positivity : 0 ≤ ‖B‖ ^ 2 + ‖B'‖ ^ 2)] at hresult
  rw [norm_centeredEndpoint, norm_centeredEndpoint]
  unfold centeredEnergy
  linarith only [hresult]

private def central (p q : Qubit → ℝ) (U : Matrix Qubit Qubit ℂ)
    (X Y : Matrix (Qubit × e) (Qubit × e) ℂ) (i j : Qubit) : Matrix e e ℂ :=
  U i j • block X j j - ((halfRatio (p j) (q i) : ℂ) * U i j) • block Y i i

private theorem sum_qubit {R : Type*} [AddCommMonoid R] (a : Qubit → R) (i : Qubit) :
    (∑ k, a k) = a i + a i.rev := by
  rw [Fin.sum_univ_two]
  fin_cases i
  · rfl
  · exact add_comm _ _

omit [Fintype e] in
private theorem ofReal_halfRatio (p q : ℝ) :
    (halfRatio p q : ℂ) =
      Complex.exp ((Real.log p : ℂ) * ((1 / 2 : ℝ) : ℂ) -
        (Real.log q : ℂ) * ((1 / 2 : ℝ) : ℂ)) := by
  rw [halfRatio, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

private theorem mixedBoundary_qubit_entry [DecidableEq e]
    (p q : Qubit → ℝ) (U : Matrix Qubit Qubit ℂ)
    (X Y : Matrix (Qubit × e) (Qubit × e) ℂ) (i j : Qubit) (u v : e) (t : ℝ) :
    mixedBoundary p q X Y (U ⊗ₖ (1 : Matrix e e ℂ)) t (i,u) (j,v) =
      Complex.exp (frequency (fun _ : Unit => Real.log (p j) - Real.log (q i)) () * (t : ℂ)) *
        exponentialSum ![0, sourceGap p j, referenceGap q i]
          ![central p q U X Y i j u v, sourceOff U X i j u v, referenceOff p q U Y i j u v]
          (t : ℂ) := by
  rw [mixedBoundary_entry]
  have hX (k : Qubit) : (∑ w : e, (U ⊗ₖ (1 : Matrix e e ℂ)) (i,u) (k,w) *
      X (k,w) (j,v)) = U i k * X (k,u) (j,v) := by
    simp only [Matrix.kronecker_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single u]
    · simp
    · intro w _ hw
      simp [Ne.symm hw]
    · simp
  have hY (k : Qubit) : (∑ w : e, Y (i,u) (k,w) *
      (U ⊗ₖ (1 : Matrix e e ℂ)) (k,w) (j,v)) = Y (i,u) (k,v) * U k j := by
    simp only [Matrix.kronecker_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single v]
    · simp
    · intro w _ hw
      simp [hw]
    · simp
  have hPhase (a b : ℝ) :
      Complex.exp (Complex.I * (a : ℂ) * (t : ℂ)) *
        Complex.exp (Complex.I * (b : ℂ) * (t : ℂ)) =
      Complex.exp (Complex.I * ((a + b : ℝ) : ℂ) * (t : ℂ)) := by
    rw [← Complex.exp_add]
    push_cast
    congr 1
    ring
  simp only [exponentialSum, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    mixedFrequency, frequency, hX, hY, ← ofReal_halfRatio, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply,
    show (0 : Fin 1).succ = (1 : Fin 2) from rfl, Complex.ofReal_zero, mul_zero, zero_mul,
    Complex.exp_zero, mul_one]
  rw [sum_qubit _ j, sum_qubit _ i]
  simp only [central, sourceOff, referenceOff, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    block, mul_add, mul_sub]
  have hA : Real.log (p j) - Real.log (q i) + sourceGap p j =
      Real.log (p j.rev) - Real.log (q i) := by unfold sourceGap; ring
  have hB : Real.log (p j) - Real.log (q i) + referenceGap q i =
      Real.log (p j) - Real.log (q i.rev) := by unfold referenceGap; ring
  rw [← hA, ← hB, ← hPhase, ← hPhase]
  ring

private theorem scalar_energy (α β : ℝ) (C A B : ℂ) :
    let F (t : ℝ) := exponentialSum ![0, α, β] ![C, A, B] (t : ℂ)
    let x := logistic α
    let y := logistic β
    let z := logistic (α - β)
    Integrable (fun t => petzWeight t * ‖F t‖ ^ 2) ∧
    (∫ t, petzWeight t * ‖F t‖ ^ 2) =
      ‖C + (x : ℂ) * A + (y : ℂ) * B‖ ^ 2 +
        ((1-x^2)*‖A‖^2 + (1-y^2)*‖B‖^2 + 2*(z-x*y)*(star A*B).re) := by
  dsimp only
  obtain ⟨hInt, he⟩ := weighted_energy_eq_gram (![0, α, β] : Fin 3 → ℝ) (![C,A,B] : Fin 3 → ℂ)
  refine ⟨hInt, ?_⟩
  simp only [logistic_correlation] at he
  have h := congrArg Complex.re he
  simp only [Complex.ofReal_re, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    show (0 : Fin 1).succ = (1 : Fin 2) from rfl, sub_zero, zero_sub, sub_self, logistic_neg,
    show β - α = -(α - β) by ring,
    show logistic 0 = 1 by simp [logistic]] at h
  rw [h]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem endpoint_young (c : ℝ) (a b : ℂ) :
    c * ‖a + b‖ ^ 2 ≤ (1 + c) * (c * ‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hs : 0 ≤ ‖(c : ℂ) * a - b‖ ^ 2 := sq_nonneg _
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im] at hs ⊢
  linarith only [hs]

private theorem entry_centering [DecidableEq e] (p q : Qubit → ℝ) (U : Matrix Qubit Qubit ℂ)
    (X Y : Matrix (Qubit × e) (Qubit × e) ℂ) (i j : Qubit) (u v : e) :
    let x := logistic (sourceGap p j)
    let y := logistic (referenceGap q i)
    let z := logistic (sourceGap p j - referenceGap q i)
    let A := sourceOff U X i j u v
    let B := referenceOff p q U Y i j u v
    let C := central p q U X Y i j u v
    let m := C + (x : ℂ) * A + (y : ℂ) * B
    let n := centeredEndpoint x y (sourceOff U X i j) (referenceOff p q U Y i j) u v
    let F (t : ℝ) := mixedBoundary p q X Y (U ⊗ₖ (1 : Matrix e e ℂ)) t (i,u) (j,v)
    Integrable (fun t => petzWeight t * ‖F t‖ ^ 2) ∧
    λ₀ * ‖F 0‖ ^ 2 ≤ (1 + λ₀) * (λ₀ * ‖m‖ ^ 2 + ‖n‖ ^ 2) ∧
    (∫ t, petzWeight t * ‖F t‖ ^ 2) = ‖m‖ ^ 2 +
      ((1-x^2)*‖A‖^2 + (1-y^2)*‖B‖^2 + 2*(z-x*y)*(star A*B).re) := by
  dsimp only
  let C := central p q U X Y i j u v
  let A := sourceOff U X i j u v
  let B := referenceOff p q U Y i j u v
  let α := sourceGap p j
  let β := referenceGap q i
  let x := logistic α
  let y := logistic β
  let f := exponentialSum ![0, α, β] ![C, A, B]
  have hnorm (t : ℝ) :
      ‖mixedBoundary p q X Y (U ⊗ₖ (1 : Matrix e e ℂ)) t (i,u) (j,v)‖ = ‖f (t : ℂ)‖ := by
    rw [mixedBoundary_qubit_entry, norm_mul, Complex.norm_exp]
    simp [f, α, β, A, B, C, frequency, Complex.mul_re, Complex.mul_im]
  simp only [hnorm]
  refine ⟨(scalar_energy α β C A B).1, ?_, (scalar_energy α β C A B).2⟩
  have hf : f 0 = C + A + B := by
    simp [f, exponentialSum, Fin.sum_univ_three]
  rw [Complex.ofReal_zero, hf]
  have hsum : C + A + B = C + (x : ℂ) * A + (y : ℂ) * B +
      centeredEndpoint x y (sourceOff U X i j) (referenceOff p q U Y i j) u v := by
    simp only [centeredEndpoint, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    change C + A + B = _ + ((1 - (x : ℂ)) * A + (1 - (y : ℂ)) * B)
    ring
  rw [hsum]
  exact endpoint_young _ _ _

private theorem block_centering [DecidableEq e] (p q : Qubit → ℝ) (U : Matrix Qubit Qubit ℂ)
    (X Y : Matrix (Qubit × e) (Qubit × e) ℂ) (i j : Qubit) :
    let x := logistic (sourceGap p j)
    let y := logistic (referenceGap q i)
    let z := logistic (sourceGap p j - referenceGap q i)
    let A := sourceOff U X i j
    let B := referenceOff p q U Y i j
    let C := central p q U X Y i j
    let M := C + (x : ℂ) • A + (y : ℂ) • B
    let G (t : ℝ) := ∑ u : e, ∑ v : e,
      ‖mixedBoundary p q X Y (U ⊗ₖ (1 : Matrix e e ℂ)) t (i,u) (j,v)‖ ^ 2
    Integrable (fun t => petzWeight t * G t) ∧
    λ₀ * G 0 ≤ (1 + λ₀) * (λ₀ * ‖M‖ ^ 2 + ‖centeredEndpoint x y A B‖ ^ 2) ∧
    (∫ t, petzWeight t * G t) = ‖M‖ ^ 2 + centeredEnergy x y z A B := by
  dsimp only
  have hb (u v : e) := entry_centering p q U X Y i j u v
  simp only [Finset.mul_sum]
  refine ⟨integrable_finsetSum _ (fun u _ => integrable_finsetSum _ (fun v _ => (hb u v).1)),
    ?_, ?_⟩
  · simp only [frobenius_sq, Finset.mul_sum, ← Finset.sum_add_distrib,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => (hb u v).2.1
  · rw [integral_finsetSum _ (fun u _ => integrable_finsetSum _ (fun v _ => (hb u v).1))]
    simp_rw [integral_finsetSum _ (fun v _ => (hb _ v).1)]
    simp only [centeredEnergy, innerRe, frobenius_sq, Finset.mul_sum, ← Finset.sum_add_distrib,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => (hb u v).2.2

private theorem opposite_gaps (p q : Qubit → ℝ) (i j : Qubit) :
    sourceGap p j.rev = -sourceGap p j ∧ referenceGap q i.rev = -referenceGap q i := by
  simp only [sourceGap, referenceGap, Fin.rev_rev, neg_sub, and_self]

/-- Opposite mixed spectral blocks, in any finite environment, have the
centered logistic endpoint bound when the two marginal correlations and the
difference of those correlations satisfy the scalar inequalities displayed here. -/
theorem mixedBoundary_opposite_blocks_evaluation [DecidableEq e]
    (p q : Fin 2 → ℝ) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (X Y : Matrix (Fin 2 × e) (Fin 2 × e) ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (i j : Fin 2)
    (hx : logistic (sourceGap p j) ≤ 1 / 5) (hy : logistic (referenceGap q i) ≤ 1 / 5)
    (hgap : (logistic (sourceGap p j) - logistic (referenceGap q i)) ^ 2 ≤
      (7 / 25) * (1 - logistic (sourceGap p j - referenceGap q i))) :
    let F (t : ℝ) := mixedBoundary p q X Y (U ⊗ₖ (1 : Matrix e e ℂ)) t
    let G (t : ℝ) := ∑ u : e, ∑ v : e,
      (‖F t (i,u) (j,v)‖ ^ 2 + ‖F t (i.rev,u) (j.rev,v)‖ ^ 2)
    G 0 ≤ (2 + Real.sqrt 2 / 2) * (∫ t, petzWeight t * G t) := by
  dsimp only
  let F (t : ℝ) := mixedBoundary p q X Y (U ⊗ₖ (1 : Matrix e e ℂ)) t
  let G (i j : Fin 2) (t : ℝ) := ∑ u : e, ∑ v : e, ‖F t (i,u) (j,v)‖ ^ 2
  have hG (t : ℝ) : (∑ u : e, ∑ v : e, (‖F t (i,u) (j,v)‖ ^ 2 +
      ‖F t (i.rev,u) (j.rev,v)‖ ^ 2)) = G i j t + G i.rev j.rev t := by
    simp only [G, Finset.sum_add_distrib]
  change (∑ u : e, ∑ v : e, (‖F 0 (i,u) (j,v)‖ ^ 2 + ‖F 0 (i.rev,u) (j.rev,v)‖ ^ 2)) ≤
    (2 + Real.sqrt 2 / 2) * ∫ t, petzWeight t *
      (∑ u : e, ∑ v : e, (‖F t (i,u) (j,v)‖ ^ 2 + ‖F t (i.rev,u) (j.rev,v)‖ ^ 2))
  simp only [hG, mul_add]
  obtain ⟨hi, hEval, hInt⟩ := block_centering p q U X Y i j
  obtain ⟨hi', hEval', hInt'⟩ := block_centering p q U X Y i.rev j.rev
  dsimp only at hi hEval hInt hi' hEval' hInt'
  obtain ⟨hα, hβ⟩ := opposite_gaps p q i j
  rw [hα, hβ, logistic_neg, logistic_neg, show -sourceGap p j - -referenceGap q i =
    -(sourceGap p j - referenceGap q i) by ring, logistic_neg] at hInt'
  rw [hα, hβ, logistic_neg, logistic_neg] at hEval'
  rw [integral_add hi hi', hInt, hInt']
  have hp := physical_centered_pair p q U hU hU' X Y hX hY i j hx hy hgap
  dsimp only at hp
  have hpos : 0 < λ₀ := by linarith only [root_bounds.1]
  apply (mul_le_mul_iff_right₀ hpos).mp
  change λ₀ * (G i j 0 + G i.rev j.rev 0) ≤ _
  have hc : 0 ≤ 1 + λ₀ := by linarith
  nlinarith only [hEval, hEval', mul_le_mul_of_nonneg_left hp hc]

#print axioms mixedBoundary_opposite_blocks_evaluation

end Blocks

end D5.S3.Quantum.Recovery.PetzRetainedQubitPairing
