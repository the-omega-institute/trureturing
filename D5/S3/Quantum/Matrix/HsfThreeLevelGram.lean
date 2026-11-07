/- GID: D5/S3/Quantum/Matrix/HsfThreeLevelGram
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfThreeLevelGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Normed]
   utility: none
   digest: Three-level positive Gram realization and all coefficient moment laws. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Matrix.HsfThreeLevelPolynomial

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Matrix.HsfThreeLevelSupplier

universe u

open private q aux g psi lam mu
  pairF delta q_pos aux_pos g_symm g_self
  hPoly hPoly_pos hPoly_identity vPoly_identity gapDen coreGap
  gapDen_pos coreGap_pos residualC residualC_pos left right
  third column_indices baseG detG dualG projectionCross
  residualE columnA residualT canonicalK residualY kNumeratorTerms
  kNumerator kDenominator columnNumerator tNumerator denominator_square polynomial_gap
  from D5.S3.Quantum.Matrix.HsfThreeLevelPolynomial

private theorem q_symm (a b : ℝ) : q a b = q b a := by unfold q; ring
private theorem aux_symm (a b : ℝ) : aux a b = aux b a := by unfold aux; ring

private theorem detG_formula (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) :
    detG p = (p 0-p 1)^2*(p 0-p 2)^2*(p 1-p 2)^2*hPoly (p 0) (p 1) (p 2)/
      (4*p 0*p 1*p 2*(q (p 0) (p 1))^2*(q (p 0) (p 2))^2*(q (p 1) (p 2))^2) := by
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have h0 := (hp 0).ne'
  have h1 := (hp 1).ne'
  have h2 := (hp 2).ne'
  have h01 := (q_pos (hp 0) (hp 1)).ne'
  have h02 := (q_pos (hp 0) (hp 2)).ne'
  have h12 := (q_pos (hp 1) (hp 2)).ne'
  rw [hPoly_identity]
  unfold detG g q at *
  field_simp [h0, h1, h2, h01, h02, h12] <;> ring

set_option maxHeartbeats 16000000 in
/-- Rational denominator clearing against the signed degree-30 numerator.
All facts used here are scalar facts or numerical coefficient data;
there is no spectral, jet, or supplier hypothesis. -/
private theorem canonicalK_clear (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) :
    canonicalK p*kDenominator (p 0) (p 1) (p 2) = kNumerator (p 0) (p 1) (p 2) := by
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have h0 := (hp 0).ne'
  have h1 := (hp 1).ne'
  have h2 := (hp 2).ne'
  have h01 : p 0-p 1 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h))
  have h02 : p 0-p 2 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (0 : Fin 3) ≠ 2) (hinj h))
  have h12 : p 1-p 2 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (1 : Fin 3) ≠ 2) (hinj h))
  have hq01 := (q_pos (hp 0) (hp 1)).ne'
  have hq02 := (q_pos (hp 0) (hp 2)).ne'
  have hq12 := (q_pos (hp 1) (hp 2)).ne'
  have hu01 := (aux_pos (hp 0) (hp 1)).ne'
  have hu02 := (aux_pos (hp 0) (hp 2)).ne'
  have hu12 := (aux_pos (hp 1) (hp 2)).ne'
  have hH := (hPoly_pos (hp 0) (hp 1) (hp 2)).ne'
  simp only [canonicalK, Fin.sum_univ_three, projectionCross]
  norm_num [left, right, third, dualG]
  rw [detG_formula p hp]
  simp only [kDenominator, kNumerator, kNumeratorTerms,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  field_simp [h0, h1, h2, h01, h02, h12, hq01, hq02, hq12,
    hu01, hu02, hu12, hH]
  simp only [hPoly_identity]
  unfold lam mu delta g q aux at *
  field_simp [h0, h1, h2, h01, h02, h12, hq01, hq02, hq12,
    hu01, hu02, hu12] <;> ring

private theorem residualT_clear (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) :
    residualT p*gapDen (p 0) (p 1) (p 2) = tNumerator (p 0) (p 1) (p 2) := by
  have hH := (hPoly_pos (hp 0) (hp 1) (hp 2)).ne'
  have hq01 := (q_pos (hp 0) (hp 1)).ne'
  have hq02 := (q_pos (hp 0) (hp 2)).ne'
  have hq12 := (q_pos (hp 1) (hp 2)).ne'
  have hu01 := (aux_pos (hp 0) (hp 1)).ne'
  have hu02 := (aux_pos (hp 0) (hp 2)).ne'
  have hu12 := (aux_pos (hp 1) (hp 2)).ne'
  have hh10 : hPoly (p 1) (p 0) (p 2) = hPoly (p 0) (p 1) (p 2) := by
    simp only [hPoly_identity]; ring
  have hh20 : hPoly (p 2) (p 0) (p 1) = hPoly (p 0) (p 1) (p 2) := by
    simp only [hPoly_identity]; ring
  have hh21 : hPoly (p 2) (p 1) (p 0) = hPoly (p 0) (p 1) (p 2) := by
    simp only [hPoly_identity]; ring
  have hh02 : hPoly (p 0) (p 2) (p 1) = hPoly (p 0) (p 1) (p 2) := by
    simp only [hPoly_identity]; ring
  have hh12 : hPoly (p 1) (p 2) (p 0) = hPoly (p 0) (p 1) (p 2) := by
    simp only [hPoly_identity]; ring
  simp only [residualT, columnA, residualE, Fin.sum_univ_three]
  norm_num [left, right, third]
  simp only [residualC, gapDen, tNumerator, columnNumerator,
    hh10, hh20, hh21, hh02, hh12]
  simp only [q_symm, aux_symm] at hq01 hq02 hq12 hu01 hu02 hu12 ⊢
  field_simp [hH, hq01, hq02, hq12, hu01, hu02, hu12] <;> ring

/-- Exact identity linking the positive core to the original rational budgets. -/
private theorem canonical_gap_identity (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) :
    residualT p-(canonicalK p)^2 = coreGap (p 0) (p 1) (p 2) := by
  have hD := (gapDen_pos (hp 0) (hp 1) (hp 2)).ne'
  have hB : kDenominator (p 0) (p 1) (p 2) ≠ 0 := by
    intro hzero
    have he := denominator_square (p 0) (p 1) (p 2)
    rw [hzero, zero_pow (by decide : 2 ≠ 0)] at he
    exact hD he.symm
  have hK : canonicalK p =
      kNumerator (p 0) (p 1) (p 2)/kDenominator (p 0) (p 1) (p 2) :=
    (eq_div_iff hB).mpr (canonicalK_clear p hp hinj)
  have hT : residualT p =
      tNumerator (p 0) (p 1) (p 2)/gapDen (p 0) (p 1) (p 2) :=
    (eq_div_iff hD).mpr (residualT_clear p hp)
  unfold coreGap
  rw [hT, hK, ← denominator_square, div_pow, ← sub_div, polynomial_gap]

private theorem residualE_pos (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j : Fin 3) (hij : i ≠ j) :
    0 < residualE p i j := by
  exact mul_pos (hp j) (residualC_pos (hp i) (hp j) (hp _) (fun h => hij (hinj h)))
private theorem columnA_pos (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (j : Fin 3) : 0 < columnA p j := by
  exact mul_pos (residualE_pos p hp hinj _ _ (column_indices j).1)
    (residualE_pos p hp hinj _ _ (column_indices j).2.1)

private theorem canonical_gap_pos (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) : (canonicalK p)^2 < residualT p := by
  have h01 : p 0 ≠ p 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h)
  have h02 : p 0 ≠ p 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hinj h)
  have h12 : p 1 ≠ p 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hinj h)
  have hpos := coreGap_pos (hp 0) (hp 1) (hp 2) h01 h02 h12
  rw [← canonical_gap_identity p hp hinj] at hpos
  exact sub_pos.mp hpos

private theorem detG_pos (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) : 0 < detG p := by
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have h01 : p 0-p 1 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h))
  have h02 : p 0-p 2 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (0 : Fin 3) ≠ 2) (hinj h))
  have h12 : p 1-p 2 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (1 : Fin 3) ≠ 2) (hinj h))
  have hs01 := sq_pos_of_ne_zero h01
  have hs02 := sq_pos_of_ne_zero h02
  have hs12 := sq_pos_of_ne_zero h12
  have hH := hPoly_pos (hp 0) (hp 1) (hp 2)
  have hq01 := q_pos (hp 0) (hp 1)
  have hq02 := q_pos (hp 0) (hp 2)
  have hq12 := q_pos (hp 1) (hp 2)
  rw [detG_formula p hp]
  positivity

private theorem pair_schur_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    0 < 1/b-a*(g a b)^2 := by
  have hq := (q_pos ha hb).ne'
  have he : 1/b-a*(g a b)^2 = (a-b)^2*aux a b/(4*b*(q a b)^2) := by
    unfold g q aux at *
    field_simp [hb.ne', hq] <;> ring
  have hs := sq_pos_of_ne_zero (sub_ne_zero.mpr hab)
  have hu := aux_pos ha hb
  have hqp := q_pos ha hb
  rw [he]
  positivity

/-- Explicit rational LDL completion of the three-by-three base quadratic
form. Square roots have not entered the scalar algebra. The ambient matrix
carrier in the ultimate supplier is unrestricted. -/
private theorem baseG_posDef (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) : (baseG p).PosDef := by
  let d0 : ℝ := 1/p 0
  let d1 : ℝ := 1/p 1-p 0*(g (p 0) (p 1))^2
  let d2 : ℝ := detG p/(d0*d1)
  have hd0 : 0 < d0 := one_div_pos.mpr (hp 0)
  have hd1 : 0 < d1 := pair_schur_pos (hp 0) (hp 1)
    (fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h))
  have hd2 : 0 < d2 := div_pos (detG_pos p hp hinj) (mul_pos hd0 hd1)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp only [baseG, Matrix.conjTranspose_apply, star_trivial]
    exact g_symm _ _
  · intro x hx
    let y0 := x 0+p 0*g (p 0) (p 1)*x 1+p 0*g (p 0) (p 2)*x 2
    let y1 := x 1+(g (p 1) (p 2)-p 0*g (p 0) (p 1)*g (p 0) (p 2))/d1*x 2
    have hid : star x ⬝ᵥ (baseG p*ᵥ x) = d0*y0^2+d1*y1^2+d2*(x 2)^2 := by
      simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Pi.star_apply,
        star_trivial, baseG]
      simp only [g_self (hp 0), g_self (hp 1), g_self (hp 2), g_symm]
      dsimp only [y0, y1, d2]
      field_simp [hd0.ne', hd1.ne']
      dsimp only [d0, d1]
      unfold detG
      try simp only [g_symm]
      have hn0 := (hp 0).ne'
      have hn1 := (hp 1).ne'
      have hn2 := (hp 2).ne'
      field_simp [hn0, hn1, hn2] <;> ring
    rw [hid]
    have hn0 : 0 ≤ d0*y0^2 := mul_nonneg hd0.le (sq_nonneg _)
    have hn1 : 0 ≤ d1*y1^2 := mul_nonneg hd1.le (sq_nonneg _)
    have hn2 : 0 ≤ d2*(x 2)^2 := mul_nonneg hd2.le (sq_nonneg _)
    by_contra hnot
    have hle := le_of_not_gt hnot
    have hz0 : d0*y0^2 = 0 := by linarith
    have hz1 : d1*y1^2 = 0 := by linarith
    have hz2 : d2*(x 2)^2 = 0 := by linarith
    have hy0 : y0 = 0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp hz0).resolve_left hd0.ne')
    have hy1 : y1 = 0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp hz1).resolve_left hd1.ne')
    have hx2 : x 2 = 0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp hz2).resolve_left hd2.ne')
    have hx1 : x 1 = 0 := by simpa only [y1, hx2, mul_zero, add_zero] using hy1
    have hx0 : x 0 = 0 := by simpa only [y0, hx1, hx2, mul_zero, add_zero] using hy0
    apply hx
    funext i
    fin_cases i <;> assumption

private theorem baseG_dual (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) : baseG p*dualG p = 1 := by
  have hd := (detG_pos p hp hinj).ne'
  have hn0 := (hp 0).ne'
  have hn1 := (hp 1).ne'
  have hn2 := (hp 2).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.mk_zero, Fin.mk_one, show (⟨2, by decide⟩ : Fin 3) = 2 from rfl,
      baseG, dualG, Matrix.mul_apply, Fin.sum_univ_three,
      g_self (hp 0), g_self (hp 1), g_self (hp 2), g_symm]
  all_goals
    field_simp [hd, hn0, hn1, hn2]
    unfold detG
    try simp only [g_symm (p 1) (p 0), g_symm (p 2) (p 0), g_symm (p 2) (p 1)]
    field_simp [hn0, hn1, hn2] <;> ring

/-- The residual allocation works for every three positive budgets, for either
sign of K. Its proof is elementary ordered-field arithmetic. -/
private theorem residual_allocation (A : Fin 3 → ℝ) (hA : ∀ j, 0 < A j)
    (K : ℝ) (hgap : K^2 < ∑ j, A j) :
    (∑ j, K*A j/(∑ k, A k)) = K ∧
      ∀ j, 0 < A j-(K*A j/(∑ k, A k))^2 := by
  let T := ∑ j, A j
  have hT : 0 < T := Finset.sum_pos (fun j _ => hA j) Finset.univ_nonempty
  have hj (j : Fin 3) : A j < T := by
    rw [show T = A 0+A 1+A 2 from Fin.sum_univ_three A]
    fin_cases j
    · change A 0 < A 0+A 1+A 2
      linarith [hA 1, hA 2]
    · change A 1 < A 0+A 1+A 2
      linarith [hA 0, hA 2]
    · change A 2 < A 0+A 1+A 2
      linarith [hA 0, hA 1]
  constructor
  · rw [← Finset.sum_div, ← Finset.mul_sum]
    exact mul_div_cancel_right₀ K hT.ne'
  · intro j
    change 0 < A j-(K*A j/T)^2
    have hnum : 0 < T*(T-A j)+A j*(T-K^2) :=
      add_pos (mul_pos hT (sub_pos.mpr (hj j)))
        (mul_pos (hA j) (sub_pos.mpr hgap))
    have he : A j-(K*A j/T)^2 =
        A j*(T*(T-A j)+A j*(T-K^2))/T^2 := by
      field_simp
      ring
    rw [he]
    exact div_pos (mul_pos (hA j) hnum) (sq_pos_of_pos hT)

private theorem canonical_residual_blocks (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) :
    (∑ j, residualY p j) = canonicalK p ∧
      ∀ j, 0 < residualE p (left j) j*residualE p (right j) j-(residualY p j)^2 := by
  simpa only [residualY, columnA, residualT] using
    residual_allocation (columnA p) (columnA_pos p hp hinj)
      (canonicalK p) (canonical_gap_pos p hp hinj)

/-- Explicit residual pair, including negative y. No absolute value or complex
phase is silently discarded. This is used in each of three orthogonal columns. -/
private def residualFirst (r : ℝ) : Fin 2 → ℝ := ![Real.sqrt r, 0]
private def residualSecond (r s y : ℝ) : Fin 2 → ℝ :=
  ![y/Real.sqrt r, Real.sqrt (s-y^2/r)]
private theorem residual_pair (r s y : ℝ) (hr : 0 < r) (hdet : 0 < r*s-y^2) :
    (∑ a, residualFirst r a*residualFirst r a) = r ∧
    (∑ a, residualFirst r a*residualSecond r s y a) = y ∧
    (∑ a, residualSecond r s y a*residualSecond r s y a) = s := by
  have hsqrt := Real.sqrt_pos.mpr hr
  have hsquare := Real.sq_sqrt hr.le
  have hrad : 0 < s-y^2/r := by
    apply (div_pos hdet hr).trans_eq
    field_simp [hr.ne'] <;> ring
  have hradSquare := Real.sq_sqrt hrad.le
  simp only [residualFirst, residualSecond, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_mul, add_zero]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith only [hsquare]
  · field_simp [hsqrt.ne']
  · rw [← pow_two, ← pow_two, div_pow, hsquare, hradSquare]
    field_simp [hr.ne'] <;> ring

/-- Standard finite PSD Gram realization, reusing CFC.sqrt rather than
reimplementing spectral theory or introducing an assumed Gram formula. -/
private theorem gram_realization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosSemidef) :
    ∀ i j, (∑ a, CFC.sqrt G a i*CFC.sqrt G a j) = G i j := by
  let R := CFC.sqrt G
  have hR : R.IsHermitian := (CFC.sqrt_nonneg G).posSemidef.isHermitian
  have hsq : R*R = G := by simpa only [pow_two] using CFC.sq_sqrt G hG.nonneg
  intro i j
  have he := congrArg (fun M : Matrix ι ι ℝ => M i j) (show Rᴴ*R = G by rw [hR.eq, hsq])
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial] using he

/-- Nine coefficient coordinates: three base coordinates and six independent
residual coordinates. This bound is unrelated to the carrier dimension. -/
private abbrev Coeff := Fin 3 ⊕ (Fin 3 × Fin 2)
private def baseCoordinates (p : Fin 3 → ℝ) (i a : Fin 3) : ℝ :=
  CFC.sqrt (baseG p) a i
private def dualCoordinates (p : Fin 3 → ℝ) (i a : Fin 3) : ℝ :=
  ∑ k, dualG p k i*baseCoordinates p k a
private def correctedCoordinates (p : Fin 3 → ℝ) (i j a : Fin 3) : ℝ :=
  lam (p i) (p j)*baseCoordinates p i a+
    mu (p i) (p j)*baseCoordinates p j a+
    (delta (p i) (p j) (p (third i j))/2)*dualCoordinates p (third i j) a
private def v (p : Fin 3 → ℝ) (i : Fin 3) : Coeff → ℝ
  | .inl a => Real.sqrt (p i)*baseCoordinates p i a
  | .inr _ => 0
private def m (p : Fin 3 → ℝ) (i j : Fin 3) : Coeff → ℝ
  | .inl a => if i = j then v p i (.inl a)
      else Real.sqrt (p j)*correctedCoordinates p i j a
  | .inr (col,a) => if i = j then 0 else if col = j then
      if i = left j then residualFirst (residualE p (left j) j) a
      else residualSecond (residualE p (left j) j) (residualE p (right j) j)
        (residualY p j) a
      else 0
private def dot (x y : Coeff → ℝ) : ℝ := ∑ a, x a*y a
private def tau (a b : ℝ) : ℝ := Real.sqrt (a*b)*g a b
private def beta (a b c : ℝ) : ℝ := Real.sqrt (a*b)*psi a b c

private theorem baseCoordinates_gram (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j : Fin 3) :
    (∑ a, baseCoordinates p i a*baseCoordinates p j a) = g (p i) (p j) := by
  simpa only [baseCoordinates, baseG] using
    gram_realization (baseG p) (baseG_posDef p hp hinj).posSemidef i j

private theorem base_dual_coordinates (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j : Fin 3) :
    (∑ a, baseCoordinates p i a*dualCoordinates p j a) = if i = j then 1 else 0 := by
  calc
    _ = ∑ k, dualG p k j*(∑ a, baseCoordinates p i a*baseCoordinates p k a) := by
      simp only [dualCoordinates, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ k, baseG p i k*dualG p k j := by
      apply Finset.sum_congr rfl
      intro k _
      rw [baseCoordinates_gram p hp hinj]
      dsimp only [baseG]
      ring
    _ = if i = j then 1 else 0 := by
      change (baseG p*dualG p) i j = _
      rw [baseG_dual p hp hinj]
      rfl

private theorem m_diagonal (p : Fin 3 → ℝ) (i : Fin 3) : m p i i = v p i := by
  funext a
  cases a with
  | inl a => simp only [m, ite_true]
  | inr a =>
    rcases a with ⟨col, a⟩
    simp only [m, v, ite_true]

private theorem v_gram (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j : Fin 3) :
    dot (v p i) (v p j) = tau (p i) (p j) := by
  simp only [dot, Fintype.sum_sum_type, v, mul_zero, Finset.sum_const_zero, add_zero, tau]
  calc
    _ = Real.sqrt (p i)*Real.sqrt (p j)*
        (∑ a, baseCoordinates p i a*baseCoordinates p j a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      rw [baseCoordinates_gram p hp hinj, Real.sqrt_mul (hp i).le]

/- The coefficient proofs below use only finite bilinear algebra after the
single CFC Gram realization above. In particular no square-root entry is
expanded, and the dual-dual contribution is retained. -/
private def dot3 (x y : Fin 3 → ℝ) : ℝ := ∑ a, x a*y a

private theorem dot3_comm (x y : Fin 3 → ℝ) : dot3 x y = dot3 y x := by
  unfold dot3
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem dot3_add_left (x y z : Fin 3 → ℝ) :
    dot3 (fun a => x a+y a) z = dot3 x z+dot3 y z := by
  simp only [dot3, add_mul, Finset.sum_add_distrib]

private theorem dot3_add_right (x y z : Fin 3 → ℝ) :
    dot3 x (fun a => y a+z a) = dot3 x y+dot3 x z := by
  simp only [dot3, mul_add, Finset.sum_add_distrib]

private theorem dot3_scale_left (r : ℝ) (x y : Fin 3 → ℝ) :
    dot3 (fun a => r*x a) y = r*dot3 x y := by
  simp only [dot3, mul_assoc, Finset.mul_sum]

private theorem dot3_scale_right (r : ℝ) (x y : Fin 3 → ℝ) :
    dot3 x (fun a => r*y a) = r*dot3 x y := by
  rw [dot3_comm, dot3_scale_left, dot3_comm y x]

private theorem dualG_symm (p : Fin 3 → ℝ) (i j : Fin 3) :
    dualG p i j = dualG p j i := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem dual_base_coordinates (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j : Fin 3) :
    dot3 (dualCoordinates p i) (baseCoordinates p j) = if i = j then 1 else 0 := by
  rw [dot3_comm]
  simpa only [dot3, eq_comm] using base_dual_coordinates p hp hinj j i

private theorem dual_dual_coordinates (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j : Fin 3) :
    dot3 (dualCoordinates p i) (dualCoordinates p j) = dualG p i j := by
  calc
    _ = ∑ k, dualG p k i*(∑ a,
        baseCoordinates p k a*dualCoordinates p j a) := by
      change (∑ a, (∑ k, dualG p k i*baseCoordinates p k a)*
        dualCoordinates p j a) = _
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = dualG p j i := by
      simp only [base_dual_coordinates p hp hinj]
      simp
    _ = dualG p i j := dualG_symm p j i

private theorem corrected_base (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (h i j : Fin 3) :
    dot3 (baseCoordinates p h) (correctedCoordinates p i j) =
      lam (p i) (p j)*g (p h) (p i)+
      mu (p i) (p j)*g (p h) (p j)+
      delta (p i) (p j) (p (third i j))/2*(if h = third i j then 1 else 0) := by
  change dot3 (baseCoordinates p h) (fun a =>
    lam (p i) (p j)*baseCoordinates p i a+
    mu (p i) (p j)*baseCoordinates p j a+
    (delta (p i) (p j) (p (third i j))/2)*dualCoordinates p (third i j) a) = _
  simp only [dot3_add_right, dot3_scale_right]
  simp only [dot3, baseCoordinates_gram p hp hinj,
    base_dual_coordinates p hp hinj]

/-- The full nine-term product includes the dual-dual term even when one
of the two defects vanishes. No division by a defect is used. -/
private theorem corrected_pair (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j k l : Fin 3) :
    dot3 (correctedCoordinates p i j) (correctedCoordinates p k l) =
      lam (p i) (p j)*lam (p k) (p l)*g (p i) (p k)+
      lam (p i) (p j)*mu (p k) (p l)*g (p i) (p l)+
      lam (p i) (p j)*(delta (p k) (p l) (p (third k l))/2)*
        (if i = third k l then 1 else 0)+
      mu (p i) (p j)*lam (p k) (p l)*g (p j) (p k)+
      mu (p i) (p j)*mu (p k) (p l)*g (p j) (p l)+
      mu (p i) (p j)*(delta (p k) (p l) (p (third k l))/2)*
        (if j = third k l then 1 else 0)+
      (delta (p i) (p j) (p (third i j))/2)*lam (p k) (p l)*
        (if third i j = k then 1 else 0)+
      (delta (p i) (p j) (p (third i j))/2)*mu (p k) (p l)*
        (if third i j = l then 1 else 0)+
      (delta (p i) (p j) (p (third i j))/2)*
        (delta (p k) (p l) (p (third k l))/2)*
        dualG p (third i j) (third k l) := by
  change dot3 (fun a =>
    lam (p i) (p j)*baseCoordinates p i a+
    mu (p i) (p j)*baseCoordinates p j a+
    (delta (p i) (p j) (p (third i j))/2)*dualCoordinates p (third i j) a)
    (fun a => lam (p k) (p l)*baseCoordinates p k a+
    mu (p k) (p l)*baseCoordinates p l a+
    (delta (p k) (p l) (p (third k l))/2)*dualCoordinates p (third k l) a) = _
  simp only [dot3_add_left, dot3_add_right, dot3_scale_left, dot3_scale_right,
    dual_base_coordinates p hp hinj, dual_dual_coordinates p hp hinj]
  simp only [dot3, baseCoordinates_gram p hp hinj,
    base_dual_coordinates p hp hinj]
  ring

private theorem third_properties (i j : Fin 3) (hij : i ≠ j) :
    third i j ≠ i ∧ third i j ≠ j ∧ third j i = third i j := by
  fin_cases i <;> fin_cases j <;> simp_all [third]

private theorem third_eq (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : third i j = k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [third]

private theorem off_column_cases (i j : Fin 3) (hij : i ≠ j) :
    i = left j ∨ i = right j := by
  fin_cases i <;> fin_cases j <;> simp_all [left, right]

private theorem dot_comm (x y : Coeff → ℝ) : dot x y = dot y x := by
  unfold dot
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem tau_symm (a b : ℝ) : tau a b = tau b a := by
  unfold tau
  rw [mul_comm b a, g_symm b a]

private theorem tau_self {a : ℝ} (ha : 0 < a) : tau a a = 1 := by
  rw [tau, Real.sqrt_mul_self ha.le, g_self ha]
  field_simp [ha.ne']

private theorem tau_triangle {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    tau a b*tau b c*tau c a = a*b*c*g a b*g b c*g c a := by
  calc
    _ = (Real.sqrt a*Real.sqrt a)*(Real.sqrt b*Real.sqrt b)*
        (Real.sqrt c*Real.sqrt c)*g a b*g b c*g c a := by
      simp only [tau, Real.sqrt_mul ha.le, Real.sqrt_mul hb.le,
        Real.sqrt_mul hc.le]
      ring
    _ = _ := by rw [Real.mul_self_sqrt ha.le, Real.mul_self_sqrt hb.le,
      Real.mul_self_sqrt hc.le]

/-- Normalized endpoint projection, including the actual diagonal row. -/
private def rowProjection (p : Fin 3 → ℝ) (i k j : Fin 3) : ℝ :=
  if k = j then g (p i) (p j) else
    lam (p k) (p j)*g (p i) (p k)+mu (p k) (p j)*g (p i) (p j)+
      delta (p k) (p j) (p (third k j))/2*(if i = third k j then 1 else 0)

private theorem v_m_projection (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i k j : Fin 3) :
    dot (v p i) (m p k j) =
      Real.sqrt (p i)*Real.sqrt (p j)*rowProjection p i k j := by
  by_cases hkj : k = j
  · subst k
    rw [m_diagonal, v_gram p hp hinj]
    simp only [ite_true, ite_false, rowProjection, if_pos rfl, tau, Real.sqrt_mul (hp i).le]
  · have he : dot (v p i) (m p k j) =
        Real.sqrt (p i)*Real.sqrt (p j)*
          dot3 (baseCoordinates p i) (correctedCoordinates p k j) := by
      simp only [ite_true, ite_false, dot, Fintype.sum_sum_type, v, m, if_neg hkj, zero_mul,
        Finset.sum_const_zero, add_zero, dot3]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [he, corrected_base p hp hinj]
    simp only [ite_true, ite_false, rowProjection, if_neg hkj]

set_option maxHeartbeats 16000000 in
/-- Twenty-seven compact rational identities, with arbitrary positive p.
The case split is on the three finite indices, never on sampled labels. -/
private theorem rowProjection_balance (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (i j k : Fin 3) :
    rowProjection p i k j+rowProjection p j k i = 2*psi (p i) (p j) (p k) := by
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have h0 := (hp 0).ne'
  have h1 := (hp 1).ne'
  have h2 := (hp 2).ne'
  have hq (r s : Fin 3) : (p r)^2+p r*p s+(p s)^2 ≠ 0 :=
    (q_pos (hp r) (hp s)).ne'
  have hu (r s : Fin 3) : 4*(p r)^2+7*p r*p s+4*(p s)^2 ≠ 0 :=
    (aux_pos (hp r) (hp s)).ne'
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [rowProjection, third]
  all_goals
    simp only [lam, mu, delta, psi, g, q, aux]
    field_simp [h0, h1, h2, hq 0 0, hq 0 1, hq 0 2,
      hq 1 0, hq 1 1, hq 1 2, hq 2 0, hq 2 1, hq 2 2,
      hu 0 1, hu 0 2, hu 1 0, hu 1 2, hu 2 0, hu 2 1] <;> ring

private theorem mixed_moment (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j k : Fin 3) :
    (dot (v p i) (m p k j)+dot (m p k i) (v p j))/2 =
      beta (p i) (p j) (p k) := by
  rw [dot_comm (m p k i) (v p j), v_m_projection p hp hinj,
    v_m_projection p hp hinj]
  have hb := rowProjection_balance p hp i j k
  unfold beta
  rw [Real.sqrt_mul (hp i).le]
  calc
    _ = (Real.sqrt (p i)*Real.sqrt (p j))*
        (rowProjection p i k j+rowProjection p j k i)/2 := by ring
    _ = _ := by rw [hb]; ring

private def pairR (a b : ℝ) : ℝ :=
  a*(a-b)^2*pairF a b/(4*(q a b)^3*aux a b)

private theorem pairR_budget {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    b*((lam a b)^2/a+2*lam a b*mu a b*g a b+(mu a b)^2/b+pairR a b) =
      4-a*b*(g a b)^2-2*a*psi a a b := by
  have hq := (q_pos ha hb).ne'
  have hqa := (q_pos ha ha).ne'
  have hqb := (q_pos hb hb).ne'
  have hqr := (q_pos hb ha).ne'
  have hu := (aux_pos ha hb).ne'
  unfold pairR pairF lam mu psi g q aux at *
  field_simp [ha.ne', hb.ne', hq, hqa, hqb, hqr, hu] <;> ring

set_option maxHeartbeats 16000000 in
/-- The diagonal cofactor for the missing third level. Its proof uses the
already supplied determinant formula, not another CFC computation. -/
private theorem dual_diagonal (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j : Fin 3) (hij : i ≠ j) :
    dualG p (third i j) (third i j) =
      p (third i j)*(q (p i) (p (third i j)))^2*
        (q (p j) (p (third i j)))^2*aux (p i) (p j)/
      ((p i-p (third i j))^2*(p j-p (third i j))^2*
        hPoly (p i) (p j) (p (third i j))) := by
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have h0 := (hp 0).ne'
  have h1 := (hp 1).ne'
  have h2 := (hp 2).ne'
  have hd (r s : Fin 3) (hrs : r ≠ s) : p r-p s ≠ 0 :=
    sub_ne_zero.mpr (fun h => hrs (hinj h))
  have hq (r s : Fin 3) : (p r)^2+p r*p s+(p s)^2 ≠ 0 :=
    (q_pos (hp r) (hp s)).ne'
  have hH (r s t : Fin 3) :
      4*(p r+p s+p t)^2*(p r*p s+p r*p t+p s*p t)^2-
        (p r*p s+p r*p t+p s*p t)^3-(p r+p s+p t)^3*p r*p s*p t ≠ 0 := by
    rw [← hPoly_identity]
    exact (hPoly_pos (hp r) (hp s) (hp t)).ne'
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  all_goals
    norm_num [third, dualG]
    rw [detG_formula p hp]
    simp only [hPoly_identity]
    unfold g q aux
    field_simp [h0, h1, h2, hq 0 1, hq 0 2, hq 1 0,
      hq 1 2, hq 2 0, hq 2 1,
      hd 0 1 (by decide), hd 0 2 (by decide), hd 1 0 (by decide),
      hd 1 2 (by decide), hd 2 0 (by decide), hd 2 1 (by decide),
      hH 0 1 2, hH 0 2 1, hH 1 0 2, hH 1 2 0, hH 2 0 1, hH 2 1 0] <;> ring

private theorem residualC_budget {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hac : a ≠ c) (hbc : b ≠ c) :
    residualC a b c+(delta a b c)^2/4*
      (c*(q a c)^2*(q b c)^2*aux a b/
        ((a-c)^2*(b-c)^2*hPoly a b c)) = pairR a b := by
  have hq := (q_pos ha hb).ne'
  have hqc := (q_pos ha hc).ne'
  have hqbc := (q_pos hb hc).ne'
  have hu := (aux_pos ha hb).ne'
  have huc := (aux_pos ha hc).ne'
  have hH := (hPoly_pos ha hb hc).ne'
  have hdac := sub_ne_zero.mpr hac
  have hdbc := sub_ne_zero.mpr hbc
  unfold residualC pairR delta
  rw [vPoly_identity]
  field_simp [hq, hqc, hqbc, hu, huc, hH, hdac, hdbc] <;> ring

private def edgeResidual (p : Fin 3 → ℝ) (i j : Fin 3) : Fin 2 → ℝ :=
  if i = left j then residualFirst (residualE p (left j) j)
  else residualSecond (residualE p (left j) j) (residualE p (right j) j)
    (residualY p j)

private theorem edgeResidual_gram (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i k j : Fin 3) (hij : i ≠ j) (hkj : k ≠ j) :
    (∑ a, edgeResidual p i j a*edgeResidual p k j a) =
      if i = k then residualE p i j else residualY p j := by
  have hidx := column_indices j
  have hpair := residual_pair (residualE p (left j) j)
    (residualE p (right j) j) (residualY p j)
    (residualE_pos p hp hinj _ _ hidx.1)
    ((canonical_residual_blocks p hp hinj).2 j)
  rcases off_column_cases i j hij with rfl | rfl <;>
    rcases off_column_cases k j hkj with rfl | rfl
  · simpa only [ite_true, ite_false, edgeResidual, if_pos rfl] using hpair.1
  · simpa only [ite_true, ite_false, edgeResidual, if_pos rfl, if_neg hidx.2.2.1,
      if_neg (Ne.symm hidx.2.2.1)] using hpair.2.1
  · simp only [ite_true, ite_false, edgeResidual, if_pos rfl, if_neg hidx.2.2.1,
      if_neg (Ne.symm hidx.2.2.1)]
    calc
      _ = ∑ a, residualFirst (residualE p (left j) j) a*
          residualSecond (residualE p (left j) j) (residualE p (right j) j)
            (residualY p j) a := by
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = _ := hpair.2.1
  · simpa only [ite_true, ite_false, edgeResidual, if_neg (Ne.symm hidx.2.2.1), if_pos rfl]
      using hpair.2.2

private theorem same_column_gram (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i k j : Fin 3) (hij : i ≠ j) (hkj : k ≠ j) :
    dot (m p i j) (m p k j) =
      p j*dot3 (correctedCoordinates p i j) (correctedCoordinates p k j)+
        (if i = k then residualE p i j else residualY p j) := by
  have hbase : (∑ a : Fin 3, m p i j (.inl a)*m p k j (.inl a)) =
      p j*dot3 (correctedCoordinates p i j) (correctedCoordinates p k j) := by
    simp only [ite_true, ite_false, m, if_neg hij, if_neg hkj, dot3]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    calc
      _ = (Real.sqrt (p j)*Real.sqrt (p j))*
          (correctedCoordinates p i j a*correctedCoordinates p k j a) := by ring
      _ = _ := by rw [Real.mul_self_sqrt (hp j).le]
  have hres : (∑ a : Fin 3 × Fin 2, m p i j (.inr a)*m p k j (.inr a)) =
      ∑ a, edgeResidual p i j a*edgeResidual p k j a := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ col : Fin 3, ∑ a : Fin 2,
          if col = j then edgeResidual p i j a*edgeResidual p k j a else 0 := by
        apply Finset.sum_congr rfl
        intro col _
        apply Finset.sum_congr rfl
        intro a _
        by_cases hcol : col = j <;>
          by_cases hi : i = left j <;> by_cases hk : k = left j <;>
          simp [m, hij, hkj, hcol, hi, hk, edgeResidual, (column_indices j).1]
      _ = _ := by rw [Finset.sum_comm]; simp
  rw [dot, Fintype.sum_sum_type, hbase, hres, edgeResidual_gram p hp hinj i k j hij hkj]

private theorem tau_square {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (tau a b)^2 = a*b*(g a b)^2 := by
  rw [tau, mul_pow, Real.sq_sqrt (mul_pos ha hb).le]

private theorem beta_diagonal {a b : ℝ} (ha : 0 < a) : beta a a b = a*psi a a b := by
  rw [beta, Real.sqrt_mul_self ha.le]

private theorem m_norm (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j : Fin 3) (hij : i ≠ j) :
    dot (m p i j) (m p i j) =
      4-(tau (p i) (p j))^2-2*beta (p i) (p i) (p j) := by
  have ht := third_properties i j hij
  have hcorr : dot3 (correctedCoordinates p i j) (correctedCoordinates p i j) =
      (lam (p i) (p j))^2/p i+
      2*lam (p i) (p j)*mu (p i) (p j)*g (p i) (p j)+
      (mu (p i) (p j))^2/p j+
      (delta (p i) (p j) (p (third i j)))^2/4*
        dualG p (third i j) (third i j) := by
    rw [corrected_pair p hp hinj]
    simp only [ite_true, ite_false, if_neg ht.1, if_neg ht.2.1, if_neg (Ne.symm ht.1),
      if_neg (Ne.symm ht.2.1), g_self (hp i), g_self (hp j),
      mul_zero, zero_mul, add_zero, zero_add]
    rw [g_symm (p j) (p i)]
    ring
  have hC : residualC (p i) (p j) (p (third i j))+
      (delta (p i) (p j) (p (third i j)))^2/4*
        dualG p (third i j) (third i j) = pairR (p i) (p j) := by
    rw [dual_diagonal p hp hinj i j hij]
    exact residualC_budget (hp i) (hp j) (hp (third i j))
      (fun h => ht.1 (hinj h).symm) (fun h => ht.2.1 (hinj h).symm)
  have hb := pairR_budget (hp i) (hp j)
  rw [same_column_gram p hp hinj i i j hij hij, if_pos rfl, hcorr,
    tau_square (hp i) (hp j), beta_diagonal (hp i)]
  dsimp only [residualE]
  linear_combination hb + (p j)*hC

private theorem corrected_cross (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    dot3 (correctedCoordinates p i j) (correctedCoordinates p k j) =
      projectionCross p i j k := by
  have ht := third_eq i j k hij hik hjk
  have ht' := third_eq k j i (Ne.symm hjk) (Ne.symm hik) (Ne.symm hij)
  rw [corrected_pair p hp hinj, ht, ht']
  simp only [ite_true, ite_false, if_pos rfl, if_neg hij, if_neg (Ne.symm hij),
    if_neg hjk, if_neg (Ne.symm hjk), g_self (hp j),
    mul_zero, zero_mul, mul_one, add_zero, zero_add]
  rw [dualG_symm p k i]
  unfold projectionCross
  ring

private theorem m_column_cross (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    dot (m p i j) (m p k j) = p j*projectionCross p i j k+residualY p j := by
  rw [same_column_gram p hp hinj i k j hij (Ne.symm hjk), if_neg hik,
    corrected_cross p hp hinj i j k hij hik hjk]

private theorem canonical_cycle (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) :
    dot (m p 1 0) (m p 2 0)+dot (m p 2 1) (m p 0 1)+
      dot (m p 0 2) (m p 1 2) =
        4-tau (p 0) (p 1)*tau (p 1) (p 2)*tau (p 2) (p 0) := by
  rw [dot_comm (m p 2 1) (m p 0 1)]
  rw [m_column_cross p hp hinj 1 0 2 (by decide) (by decide) (by decide),
    m_column_cross p hp hinj 0 1 2 (by decide) (by decide) (by decide),
    m_column_cross p hp hinj 0 2 1 (by decide) (by decide) (by decide),
    tau_triangle (hp 0) (hp 1) (hp 2)]
  have hY := (canonical_residual_blocks p hp hinj).1
  simp only [canonicalK, Fin.sum_univ_three] at hY
  norm_num [left, right] at hY
  linarith only [hY]

private theorem repeated_cycle (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i k : Fin 3) (hik : i ≠ k) :
    2*dot (v p i) (m p k i)+dot (m p i k) (m p i k) =
      4-(tau (p i) (p k))^2 := by
  have hm := mixed_moment p hp hinj i i k
  rw [dot_comm (m p k i) (v p i)] at hm
  rw [m_norm p hp hinj i k hik]
  linarith only [hm]

/-- All 27 cyclic coefficient laws. Repeated levels use the exact row norm;
the six distinct triples consume canonicalK without expanding its numerator. -/
private theorem cyclic_moment (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j k : Fin 3) :
    dot (m p j i) (m p k i)+dot (m p k j) (m p i j)+
      dot (m p i k) (m p j k) =
        4-tau (p i) (p j)*tau (p j) (p k)*tau (p k) (p i) := by
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      simp only [m_diagonal, v_gram p hp hinj, tau_self (hp i)]
      norm_num
    · have hr := repeated_cycle p hp hinj i k hik
      simp only [m_diagonal, tau_self (hp i), one_mul]
      rw [dot_comm (m p k i) (v p i), tau_symm (p k) (p i)]
      nlinarith only [hr]
  · by_cases hik : i = k
    · subst k
      have hr := repeated_cycle p hp hinj i j hij
      simp only [m_diagonal, tau_self (hp i), mul_one]
      rw [dot_comm (m p j i) (v p i), tau_symm (p j) (p i)]
      nlinarith only [hr]
    · by_cases hjk : j = k
      · subst k
        have hr := repeated_cycle p hp hinj j i (Ne.symm hij)
        simp only [m_diagonal, tau_self (hp j), mul_one]
        rw [dot_comm (m p i j) (v p j), tau_symm (p i) (p j)]
        nlinarith only [hr]
      · have hc := canonical_cycle p hp hinj
        fin_cases i <;> fin_cases j <;> fin_cases k <;>
          first
          | exact (hij rfl).elim
          | exact (hik rfl).elim
          | exact (hjk rfl).elim
          | (simp only [Fin.mk_zero, Fin.mk_one,
              show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] at hc ⊢ <;>
              simp only [dot_comm (m p 2 0) (m p 1 0),
              dot_comm (m p 2 1) (m p 0 1), dot_comm (m p 1 2) (m p 0 2),
              tau_symm (p 1) (p 0), tau_symm (p 2) (p 0),
              tau_symm (p 2) (p 1)] at hc ⊢ <;> linear_combination hc)

end D5.S3.Quantum.Matrix.HsfThreeLevelSupplier
