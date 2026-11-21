/- GID: D5/S3/Quantum/Recovery/PetzQubitBoundaryEstimates
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzQubitBoundaryEstimates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A close pair of logistic frequencies reduces the squared endpoint evaluation norm. -/

import D5.S3.Quantum.Recovery.PetzMixedBoundaryEvaluation

/-! Finite coefficient bounds for mixed qubit spectral blocks. -/

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory Set
open scoped BigOperators Matrix Matrix.Norms.Frobenius Kronecker ComplexOrder MatrixOrder
open D5.S3.Quantum.Recovery.PetzMixedBoundaryEvaluation (mixedBoundary)
open PetzExponentialBoundaryEvaluation (petzWeight)
open PetzLogisticEvaluation (correlation)
open ExponentialGramWeightedEvaluation (exponentialSum frequency)

open private frobenius_sq from D5.S3.Quantum.Recovery.PetzExponentialBoundaryEvaluation
open private mixedBoundary_entry mixedFrequency from
  D5.S3.Quantum.Recovery.PetzMixedBoundaryEvaluation
open private weighted_energy_eq_gram from D5.S3.Analytic.PetzLogisticEvaluation

namespace D5.S3.Quantum.Recovery.PetzQubitBoundaryEstimates

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

end Blocks

section ClosePair

open scoped InnerProductSpace
open Submodule
open D5.S3.Quantum.GNSMatrix (frobenius_norm_sq_eq_trace)

local notation "E₃" => EuclideanSpace ℂ (Fin 3)
local notation "M₃" => Matrix (Fin 3) (Fin 3) ℂ

private theorem exists_unit_orthogonal_pair (x y : E₃) :
    ∃ u : E₃, ‖u‖ = 1 ∧ ⟪x, u⟫_ℂ = 0 ∧ ⟪y, u⟫_ℂ = 0 := by
  classical
  let pair : Finset E₃ := {x, y}
  let K : Submodule ℂ E₃ := Submodule.span ℂ (pair : Set E₃)
  have hK : Module.finrank ℂ K ≤ 2 :=
    (finrank_span_finset_le_card (R := ℂ) pair).trans
      ((Finset.card_insert_le x {y}).trans (by simp))
  have hdim := K.finrank_add_finrank_orthogonal
  rw [finrank_euclideanSpace_fin] at hdim
  have : Nontrivial Kᗮ :=
    Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℂ Kᗮ)
  obtain ⟨v, hv⟩ := exists_ne (0 : Kᗮ)
  have hv' : (v : E₃) ≠ 0 := by
    intro h
    exact hv (Subtype.ext h)
  let u : E₃ := ((‖(v : E₃)‖⁻¹ : ℝ) : ℂ) • (v : E₃)
  have hu : u ∈ Kᗮ := Kᗮ.smul_mem _ v.property
  refine ⟨u, ?_, K.inner_right_of_mem_orthogonal (subset_span (by simp [pair])) hu,
    K.inner_right_of_mem_orthogonal (subset_span (by simp [pair])) hu⟩
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv')

private def outer (x y : E₃) : M₃ := vecMulVec x.ofLp (star y.ofLp)

private theorem trace_outer (x y : E₃) : (outer x y).trace = ⟪y, x⟫_ℂ :=
  Matrix.trace_vecMulVec _ _

private theorem trace_outer_mul (x y z w : E₃) :
    (outer x y * outer z w).trace = ⟪y, z⟫_ℂ * ⟪w, x⟫_ℂ := by
  simp only [outer, Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_smul,
    EuclideanSpace.inner_eq_star_dotProduct, smul_eq_mul]
  rw [dotProduct_comm (star y.ofLp)]

private theorem adjoint_outer (x y : E₃) : (outer x y)ᴴ = outer y x := by
  simp [outer, Matrix.conjTranspose_vecMulVec]

private theorem norm_trace_mul_le {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    ‖(Aᴴ * B).trace‖ ≤ ‖A‖ * ‖B‖ := by
  let flatten (X : Matrix n n ℂ) : EuclideanSpace ℂ (n × n) :=
    WithLp.toLp 2 fun uv => X uv.1 uv.2
  have hnorm (X : Matrix n n ℂ) : ‖flatten X‖ = ‖X‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [EuclideanSpace.norm_sq_eq, frobenius_sq, Fintype.sum_prod_type]
  have hinner : ⟪flatten A, flatten B⟫_ℂ = (Aᴴ * B).trace := by
    simp only [PiLp.inner_apply, flatten, RCLike.inner_apply',
      Fintype.sum_prod_type, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, RCLike.star_def]
    exact Finset.sum_comm
  simpa only [hinner, hnorm] using norm_inner_le_norm (𝕜 := ℂ) (flatten A) (flatten B)

/-- Project the identity away from a Hermitian matrix annihilating the three
rank-one projectors. The construction uses only a single correlated pair. -/
private theorem close_pair_trace_representer (z : Fin 3 → E₃)
    (hz : ∀ i, ⟪z i, z i⟫_ℂ = 1) (j : Fin 3) (hj : j ≠ 0)
    (hclose : (1 / 5 : ℝ) ≤ ‖⟪z 0, z j⟫_ℂ‖ ^ 2) :
    ∃ R : M₃, Rᴴ = R ∧ ‖R‖ ^ 2 ≤ 8 / 3 ∧
      ∀ i, (R * outer (z i) (z i)).trace = 1 := by
  obtain ⟨u, hu, hu₁, hu₂⟩ := exists_unit_orthogonal_pair (z 1) (z 2)
  let v := u - ⟪z 0, u⟫_ℂ • z 0
  let t := ‖v‖ ^ 2
  have huv₀ : ⟪z 0, v⟫_ℂ = 0 := by
    dsimp only [v]
    rw [inner_sub_right, inner_smul_right, hz, mul_one, sub_self]
  have hvv₀ : ⟪v, z 0⟫_ℂ = 0 := inner_eq_zero_symm.mp huv₀
  have huv : ⟪u, v⟫_ℂ = (t : ℂ) := by
    calc
      _ = ⟪v + ⟪z 0, u⟫_ℂ • z 0, v⟫_ℂ := by rw [show v + _ = u from sub_add_cancel _ _]
      _ = _ := by simp [huv₀, t, inner_self_eq_norm_sq_to_K]
  have hvu : ⟪v, u⟫_ℂ = (t : ℂ) := by
    rw [← inner_conj_symm, huv]
    simp
  have hvv : ⟪v, v⟫_ℂ = (t : ℂ) := by
    simp [t, inner_self_eq_norm_sq_to_K]
  have huu : ⟪u, u⟫_ℂ = 1 := inner_self_eq_one_of_norm_eq_one hu
  have ht : (1 / 5 : ℝ) ≤ t := by
    let x := z 0 - ⟪u, z 0⟫_ℂ • u
    have hx : ⟪x, x⟫_ℂ = (t : ℂ) := by
      rw [← hvv]
      simp only [x, v, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hz, huu]
      rw [inner_conj_symm u (z 0)]
      ring
    have hxn : ‖x‖ ^ 2 = t := by
      have h : RCLike.re ⟪x, x⟫_ℂ = t := congrArg Complex.re hx
      rwa [inner_self_eq_norm_sq] at h
    have huzj : ⟪z j, u⟫_ℂ = 0 := by
      fin_cases j
      · exact (hj rfl).elim
      · exact hu₁
      · exact hu₂
    have hpair : ⟪x, z j⟫_ℂ = ⟪z 0, z j⟫_ℂ := by
      simp [x, inner_eq_zero_symm.mp huzj]
    have hzn : ‖z j‖ = 1 := by
      apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp
      have h : RCLike.re ⟪z j, z j⟫_ℂ = 1 := congrArg Complex.re (hz j)
      rw [one_pow]
      rwa [inner_self_eq_norm_sq] at h
    have hc := norm_inner_le_norm (𝕜 := ℂ) x (z j)
    rw [hpair, hzn, mul_one] at hc
    exact hclose.trans ((pow_le_pow_left₀ (norm_nonneg _) hc 2).trans_eq hxn)
  let W : M₃ := (1 / 2 : ℂ) • (outer u v + outer v u)
  have hW : Wᴴ = W := by
    simp only [W, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, adjoint_outer,
      star_div₀, star_one, star_ofNat]
    rw [add_comm]
  have hTr : W.trace = (t : ℂ) := by
    simp only [W, Matrix.trace_smul, Matrix.trace_add, trace_outer, huv, hvu, smul_eq_mul]
    ring
  have hTrSq : (W * W).trace = (((t + t ^ 2) / 2 : ℝ) : ℂ) := by
    simp only [W, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, Matrix.trace_smul,
      Matrix.trace_add, trace_outer_mul, hvu, huv, hvv, huu, smul_eq_mul]
    push_cast
    ring
  have hWP (i : Fin 3) : (W * outer (z i) (z i)).trace = 0 := by
    simp only [W, Matrix.smul_mul, add_mul, Matrix.trace_smul, Matrix.trace_add,
      trace_outer_mul, smul_eq_mul]
    fin_cases i
    · simp [huv₀, hvv₀]
    · simp [hu₁, inner_eq_zero_symm.mp hu₁]
    · simp [hu₂, inner_eq_zero_symm.mp hu₂]
  let c := 2 / (1 + t)
  let R : M₃ := 1 - (c : ℂ) • W
  have hR : Rᴴ = R := by simp [R, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hW]
  refine ⟨R, hR, ?_, fun i => ?_⟩
  · have hnorm : ‖R‖ ^ 2 = 3 - 2 * c * t + c ^ 2 * ((t + t ^ 2) / 2) := by
      have h : ((‖R‖ ^ 2 : ℝ) : ℂ) =
          ((3 - 2 * c * t + c ^ 2 * ((t + t ^ 2) / 2) : ℝ) : ℂ) := by
        rw [frobenius_norm_sq_eq_trace, hR]
        simp only [R, sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
          Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_one, Matrix.trace_smul,
          hTr, hTrSq, smul_eq_mul, Fintype.card_fin, Nat.cast_ofNat]
        push_cast
        ring
      exact_mod_cast h
    have hden : 0 < 1 + t := by linarith
    have hratio : (1 / 3 : ℝ) ≤ 2 * t / (1 + t) :=
      (le_div_iff₀ hden).mpr (by linarith)
    rw [hnorm, show 3 - 2 * c * t + c ^ 2 * ((t + t ^ 2) / 2) = 3 - 2 * t / (1 + t) by
      dsimp [c]
      field_simp
      ring]
    linarith
  · simp only [R, sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.trace_sub,
      Matrix.trace_smul, trace_outer, hz, hWP, smul_zero, sub_zero]

/-- A correlation of at least one fifth between the central mode and another slot
bounds logistic evaluation by eight thirds, including coincident frequencies. -/
theorem close_pair_weighted_evaluation (ω : Fin 3 → ℝ) (a : Fin 3 → ℂ)
    (j : Fin 3) (hj : j ≠ 0) (hclose : (1 / 5 : ℝ) ≤ ‖correlation ω 0 j‖ ^ 2) :
    Integrable (fun t : ℝ => petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2) ∧
    ‖exponentialSum ω a 0‖ ^ 2 ≤ (8 / 3) *
      (∫ t : ℝ, petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2) := by
  obtain ⟨hInt, henergy⟩ := weighted_energy_eq_gram ω a
  obtain ⟨hPSD, hdiag, _⟩ := PetzLogisticEvaluation.exact_gram_factorization ω
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hPSD.nonneg
  let z (i : Fin 3) : E₃ := WithLp.toLp 2 fun k => B k i
  let P (i : Fin 3) := outer (z i) (z i)
  let S : M₃ := ∑ i, a i • P i
  have hdot (i j : Fin 3) : ⟪z i, z j⟫_ℂ = correlation ω i j := by
    rw [hB]
    exact (dotProduct_comm _ _)
  obtain ⟨R, hR, hRnorm, hRP⟩ := close_pair_trace_representer z
    (fun i => (hdot i i).trans (hdiag i)) j hj (by rwa [hdot])
  have hP (i : Fin 3) : (P i)ᴴ = P i := adjoint_outer _ _
  have hPair (i j : Fin 3) : (P i * P j).trace = (‖correlation ω i j‖ ^ 2 : ℂ) := by
    rw [show P i = outer (z i) (z i) from rfl, show P j = outer (z j) (z j) from rfl,
      trace_outer_mul, ← inner_conj_symm (z j) (z i), hdot]
    exact Complex.mul_conj' _
  have htrace : (Rᴴ * S).trace = ∑ i, a i := by
    simp only [hR, S, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
      P, hRP, smul_eq_mul, mul_one]
  have hnorm : ‖S‖ ^ 2 = ∫ t : ℝ, petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2 := by
    have h := congrArg Complex.re (frobenius_norm_sq_eq_trace S)
    rw [Complex.ofReal_re] at h
    rw [h, ← Complex.ofReal_re (∫ t : ℝ, petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2),
      henergy]
    congr 1
    simp only [S, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, hP,
      Finset.sum_mul_sum, Matrix.trace_sum, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_smul, hPair, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hEval := pow_le_pow_left₀ (norm_nonneg _) (norm_trace_mul_le R S) 2
  rw [htrace, mul_pow] at hEval
  have h := hEval.trans (mul_le_mul_of_nonneg_right hRnorm (sq_nonneg ‖S‖))
  exact ⟨hInt, by simpa [exponentialSum, hnorm] using h⟩

end ClosePair

end D5.S3.Quantum.Recovery.PetzQubitBoundaryEstimates
