/- GID: D5/S3/Observer/CubicGain/CommonWordSensitivity
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/CommonWordSensitivity
   mirror-E: none(waiver:uniform-original-source-response-estimate)
   anchors: [mathlib/module/Mathlib.NumberTheory.Real.GoldenRatio]
   utility: none
   digest: Native word responses have golden exponential cubic source sensitivity. -/

import D5.S3.Observer.CubicGain.OriginalWorld
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

/-! Native chronological words amplify original-source perturbations by a golden
exponential and a cubic clock factor. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.CubicGain.CommonWordSensitivity

open D5.S3.Observer.CubicGain
open scoped Matrix

/-- True selects J and false selects M. The head acts first. -/
def futureProduct : List Bool → Mat
  | [] => 1
  | e :: u => futureProduct u * (if e then actionJ else actionM)

/-- The actual chronological product after the eighth action M. -/
def clockEight : Mat := actionM * actionJ * chronological 6

/-- The same whole polynomial is evaluated at the absolute future clock. -/
def futureRead (W : OriginalWorld) (u : List Bool) : ℝ :=
  W.2.2.1 + (originalPolynomial W).eval (8 + (u.length : ℝ)) *
    Matrix.trace (futureProduct u * clockEight * sourceMatrix W.1 W.2.1)

/-- Original source entries, drift and ordinary polynomial coefficients. -/
def sourceCoordinates (W : OriginalWorld) : Fin 8 → ℝ :=
  ![W.1, W.2.1, W.1 * (1-W.1) / W.2.1, W.2.2.1,
    W.2.2.2 0, W.2.2.2 1, W.2.2.2 2, W.2.2.2 3]

private theorem product_cone (u : List Bool) :
    (∀ i j, 0 ≤ futureProduct u i j) ∧
    ∀ i, futureProduct u i 0 + Real.goldenRatio * futureProduct u i 1 ≤
      Real.goldenRatio ^ u.length * (![1,Real.goldenRatio] : Fin 2 → ℝ) i := by
  induction u with
  | nil =>
    constructor
    · intro i j; fin_cases i <;> fin_cases j <;> norm_num [futureProduct]
    · intro i; fin_cases i <;> norm_num [futureProduct,Matrix.one_apply]
  | cons e u ih =>
    have hp := Real.goldenRatio_pos
    have hp1 := Real.one_lt_goldenRatio
    have hsq := Real.goldenRatio_sq
    constructor
    · intro i j
      cases e <;> fin_cases j <;>
        simp [futureProduct, actionJ, actionM, Matrix.mul_apply, Fin.sum_univ_two]
      all_goals first | exact ih.1 i 0 | exact ih.1 i 1 |
        exact add_nonneg (ih.1 i 0) (ih.1 i 1)
    · intro i
      have h0 := ih.1 i 0
      have h1 := ih.1 i 1
      have hi := mul_le_mul_of_nonneg_left (ih.2 i) hp.le
      have hs := congrArg (fun x : ℝ => x * futureProduct u i 1) hsq
      cases e <;>
        norm_num [futureProduct, actionJ, actionM, Matrix.mul_apply,
          Fin.sum_univ_two, List.length_cons, pow_succ]
      · nlinarith [hs]
      · nlinarith [mul_nonneg (by nlinarith [hsq] : 0 ≤ Real.goldenRatio^2-1) h1,hs]


private theorem product_entry (u : List Bool) (i j : Fin 2) :
    |futureProduct u i j| ≤ 2 * Real.goldenRatio ^ u.length := by
  obtain ⟨hn,hc⟩ := product_cone u
  rw [abs_of_nonneg (hn i j)]
  have hp := Real.one_lt_goldenRatio
  have hpow := pow_nonneg Real.goldenRatio_pos.le u.length
  have he : futureProduct u i j ≤
      futureProduct u i 0+Real.goldenRatio*futureProduct u i 1 := by
    fin_cases j
    · change futureProduct u i 0 ≤ _
      nlinarith [mul_nonneg Real.goldenRatio_pos.le (hn i 1)]
    · change futureProduct u i 1 ≤ _
      nlinarith [mul_nonneg (sub_nonneg.mpr hp.le) (hn i 1),hn i 0]
  have hv : (![1,Real.goldenRatio] : Fin 2 → ℝ) i ≤ 2 := by
    fin_cases i
    · norm_num
    · exact Real.goldenRatio_lt_two.le
  exact he.trans ((hc i).trans (by nlinarith [mul_le_mul_of_nonneg_left hv hpow]))


private theorem clock_eight_shape : clockEight = !![3,1;8,3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [clockEight,chronological,actionJ,actionM,Matrix.mul_apply,Fin.sum_univ_two]

private theorem advanced_entry (u : List Bool) (i j : Fin 2) :
    |(futureProduct u * clockEight) i j| ≤ 32 * Real.goldenRatio ^ u.length := by
  have h0 := product_entry u i 0
  have h1 := product_entry u i 1
  have hpow := pow_nonneg Real.goldenRatio_pos.le u.length
  have hc0 : |clockEight 0 j| ≤ 8 := by rw [clock_eight_shape]; fin_cases j <;> norm_num
  have hc1 : |clockEight 1 j| ≤ 8 := by rw [clock_eight_shape]; fin_cases j <;> norm_num
  rw [Matrix.mul_apply,Fin.sum_univ_two]
  calc
    _ ≤ |futureProduct u i 0| * |clockEight 0 j|+
        |futureProduct u i 1| * |clockEight 1 j| := by
      simpa only [abs_mul] using abs_add_le
        (futureProduct u i 0*clockEight 0 j) (futureProduct u i 1*clockEight 1 j)
    _ ≤ (2*Real.goldenRatio^u.length)*8+(2*Real.goldenRatio^u.length)*8 :=
      add_le_add (mul_le_mul h0 hc0 (abs_nonneg _) (by positivity))
        (mul_le_mul h1 hc1 (abs_nonneg _) (by positivity))
    _ = _ := by ring


private theorem trace_bound (u : List Bool) (P : Mat) (H : ℝ)
    (hP : ∀ i j, |P i j| ≤ H) :
    |Matrix.trace (futureProduct u * clockEight * P)| ≤
      128 * Real.goldenRatio ^ u.length * H := by
  let A := futureProduct u * clockEight
  have hb (i j : Fin 2) : |A i j * P j i| ≤
      32 * Real.goldenRatio ^ u.length * H := by
    rw [abs_mul]
    exact mul_le_mul (advanced_entry u i j) (hP j i) (abs_nonneg _) (by positivity)
  change |Matrix.trace (A * P)| ≤ _
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_two]
  calc
    _ ≤ (|A 0 0 * P 0 0| + |A 0 1 * P 1 0|) +
        (|A 1 0 * P 0 1| + |A 1 1 * P 1 1|) :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
    _ ≤ _ := by linarith [hb 0 0,hb 0 1,hb 1 0,hb 1 1]

private theorem polynomial_bound (a : Gain) (H : ℝ) (hH : 0 ≤ H)
    (ha : ∀ i, |a i| ≤ H) (n : ℕ) :
    |(Polynomial.ofFn 4 a).eval (8+(n : ℝ))| ≤ 2048 * H * (1+(n:ℝ))^3 := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  have he : (Polynomial.ofFn 4 a).eval (8+(n : ℝ)) =
      a 0 + a 1 * (8+(n:ℝ)) + a 2 * (8+(n:ℝ))^2 + a 3 * (8+(n:ℝ))^3 := by
    simp [Polynomial.ofFn_eq_sum_monomial,Fin.sum_univ_four]
  rw [he]
  calc
    _ ≤ |a 0| + |a 1 * (8+(n:ℝ))| + |a 2 * (8+(n:ℝ))^2| +
        |a 3 * (8+(n:ℝ))^3| := by
      exact (abs_add_le _ _).trans
        (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ H + H*(8+(n:ℝ)) + H*(8+(n:ℝ))^2 + H*(8+(n:ℝ))^3 := by
      simp only [abs_mul,abs_of_nonneg (by positivity : (0:ℝ) ≤ 8+n),abs_pow]
      gcongr
    _ ≤ _ := by
      have hs : 0 ≤ (n:ℝ)^2 := sq_nonneg _
      have hc : 0 ≤ (n:ℝ)^3 := pow_nonneg hn _
      nlinarith [mul_nonneg hH hn,mul_nonneg hH hs,mul_nonneg hH hc]

private theorem coordinate_difference (W W' : OriginalWorld) (i : Fin 8) :
    |sourceCoordinates W i-sourceCoordinates W' i| ≤
      ‖sourceCoordinates W-sourceCoordinates W'‖ := by
  simpa only [Real.norm_eq_abs,Pi.sub_apply] using
    norm_le_pi_norm (sourceCoordinates W-sourceCoordinates W') i

private theorem source_bound (W : OriginalWorld) (H : ℝ) (hH : 1 ≤ H)
    (h : ∀ i, |sourceCoordinates W i| ≤ H) :
    ∀ i j, |sourceMatrix W.1 W.2.1 i j| ≤ 2*H := by
  intro i j
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp [sourceCoordinates] at h0 h1 h2
  fin_cases i <;> fin_cases j
  · change |W.1| ≤ 2*H
    linarith
  · change |W.2.1| ≤ 2*H
    linarith
  · change |W.1*(1-W.1)/W.2.1| ≤ 2*H
    linarith
  · change |1-W.1| ≤ 2*H
    exact (abs_sub _ _).trans (by norm_num; linarith)

private theorem source_difference (W W' : OriginalWorld) :
    ∀ i j, |(sourceMatrix W.1 W.2.1-sourceMatrix W'.1 W'.2.1) i j| ≤
      ‖sourceCoordinates W-sourceCoordinates W'‖ := by
  intro i j
  have h0 := coordinate_difference W W' 0
  have h1 := coordinate_difference W W' 1
  have h2 := coordinate_difference W W' 2
  change |W.1-W'.1| ≤ _ at h0
  change |W.2.1-W'.2.1| ≤ _ at h1
  change |W.1*(1-W.1)/W.2.1-W'.1*(1-W'.1)/W'.2.1| ≤ _ at h2
  fin_cases i <;> fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · change |(1-W.1)-(1-W'.1)| ≤ _
    rw [show (1-W.1)-(1-W'.1) = -(W.1-W'.1) by ring,abs_neg]
    exact h0


/-- Uniform amplification of original-source errors for every common native word.
The estimate uses the same whole polynomial and the actual absolute clock. -/
theorem common_word_source_sensitivity (W W' : OriginalWorld) (H : ℝ) (hH : 1 ≤ H)
    (hW : ∀ i, |sourceCoordinates W i| ≤ H)
    (hW' : ∀ i, |sourceCoordinates W' i| ≤ H) (u : List Bool) :
    |futureRead W u-futureRead W' u| ≤
      (1+1048576*H) * Real.goldenRatio^u.length * (1+(u.length:ℝ))^3 *
        ‖sourceCoordinates W-sourceCoordinates W'‖ := by
  let δ := ‖sourceCoordinates W-sourceCoordinates W'‖
  let p := Real.goldenRatio^u.length
  let q := (1+(u.length:ℝ))^3
  let g := (originalPolynomial W).eval (8+(u.length : ℝ))
  let g' := (originalPolynomial W').eval (8+(u.length : ℝ))
  let A := futureProduct u * clockEight
  let P := sourceMatrix W.1 W.2.1
  let P' := sourceMatrix W'.1 W'.2.1
  have hδ : 0 ≤ δ := norm_nonneg _
  have hp : 1 ≤ p := one_le_pow₀ Real.one_lt_goldenRatio.le
  have hq : 1 ≤ q := one_le_pow₀ (by have := Nat.cast_nonneg u.length (α := ℝ); linarith)
  have hg' : |g'| ≤ 2048*H*q := by
    apply polynomial_bound _ H (by linarith) _ u.length
    intro i
    have hi : |W'.2.2.2 i| ≤ H := by
      fin_cases i <;> first | exact hW' 4 | exact hW' 5 | exact hW' 6 | exact hW' 7
    exact hi
  have hgd : |g-g'| ≤ 2048*δ*q := by
    have he : g-g' = (Polynomial.ofFn 4 (W.2.2.2-W'.2.2.2)).eval (8+(u.length : ℝ)) := by
      simp [g,g',originalPolynomial,Polynomial.ofFn_eq_sum_monomial,Fin.sum_univ_four]
    rw [he]
    apply polynomial_bound _ δ hδ _ u.length
    intro i
    fin_cases i <;> first | exact coordinate_difference W W' 4 |
      exact coordinate_difference W W' 5 | exact coordinate_difference W W' 6 |
      exact coordinate_difference W W' 7
  have ht : |Matrix.trace (A*P)| ≤ 256*p*H := by
    calc
      _ ≤ 128*p*(2*H) := trace_bound u P (2*H) (source_bound W H hH hW)
      _ = _ := by ring
  have htd : |Matrix.trace (A*P)-Matrix.trace (A*P')| ≤ 128*p*δ := by
    rw [← Matrix.trace_sub,← Matrix.mul_sub]
    exact trace_bound u (P-P') δ (source_difference W W')
  have hd : |W.2.2.1-W'.2.2.1| ≤ δ := coordinate_difference W W' 3
  have he : futureRead W u-futureRead W' u =
      (W.2.2.1-W'.2.2.1) + (g-g')*Matrix.trace (A*P) +
        g'*(Matrix.trace (A*P)-Matrix.trace (A*P')) := by
    dsimp [futureRead,g,g',A,P,P']
    ring
  rw [he]
  calc
    _ ≤ |W.2.2.1-W'.2.2.1| + |(g-g')*Matrix.trace (A*P)| +
        |g'*(Matrix.trace (A*P)-Matrix.trace (A*P'))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ δ+(2048*δ*q)*(256*p*H)+(2048*H*q)*(128*p*δ) := by
      simp only [abs_mul]
      gcongr
    _ ≤ _ := by
      have hpq : 1 ≤ p*q := one_le_mul_of_one_le_of_one_le hp hq
      have hδpq : δ ≤ p*q*δ := by nlinarith
      have hprod : 0 ≤ H*p*q*δ := by positivity
      change _ ≤ (1+1048576*H)*p*q*δ
      nlinarith

#print axioms common_word_source_sensitivity

end D5.S3.Observer.CubicGain.CommonWordSensitivity
