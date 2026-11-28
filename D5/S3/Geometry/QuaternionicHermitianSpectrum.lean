/- GID: D5/S3/Geometry/QuaternionicHermitianSpectrum
   generality: G
   mirror-B: none(waiver:covered-by-chordal-su2-sharp-bounds-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The first three moments of a real spectrum with unit trace and unit second moment bound the sum of its two largest entries. -/

import OmegaBuild.Commands
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

compile_only_with_mathlib

/-!
Omega original.

The first three moments of a real spectrum with unit trace and unit second
moment bound the sum of its two largest entries. The estimate retains the
full range of simplex weights.
-/

open scoped BigOperators

noncomputable section

namespace Omega.Geometry.HolonomySpectrum

/-- The cubic moment bound associated to a top-two sum and a tail of size `n`. -/
def topTwoCubic (n : ℕ) (x : ℝ) : ℝ :=
  3 * x / 2 - x ^ 3 / 2 - 3 * x * (1 - x) ^ 2 / (2 * n) + (1 - x) ^ 3 / (n : ℝ) ^ 2

/-- Simultaneous lower bounds on the repeated-index masses for a simplex with
at least four coordinates, including zero coordinates. -/
theorem simplex_moments {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (hm : 4 ≤ Fintype.card ι) :
    let m : ℝ := Fintype.card ι
    1 / m ≤ (∑ i, w i ^ 2) ∧
      (3 * m - 2) / m ^ 2 ≤ ∑ i, (3 * w i ^ 2 - 2 * w i ^ 3) := by
  classical
  let m : ℝ := Fintype.card ι
  have hm' : 4 ≤ m := by dsimp [m]; exact_mod_cast hm
  have hmp : 0 < m := by linarith
  have ha : 0 < 1 / m := one_div_pos.mpr hmp
  have ha' : 4 * (1 / m) ≤ 1 := by
    rw [mul_one_div, div_le_iff₀ hmp, one_mul]
    exact hm'
  have hw' (i : ι) : w i ≤ 1 := by
    rw [← hs]
    exact Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := w)
  rw [hs, one_pow, Finset.card_univ] at hcs
  refine ⟨(div_le_iff₀ hmp).mpr (by simpa [m, mul_comm] using hcs), ?_⟩
  let a : ℝ := 1 / m
  have ham : m * a = 1 := by dsimp [a]; field_simp
  have hterm (i : ι) : (3 * a ^ 2 - 2 * a ^ 3) +
        (6 * a - 6 * a ^ 2) * (w i - a) ≤ 3 * w i ^ 2 - 2 * w i ^ 3 := by
    have hcoef : 0 ≤ 3 - 4 * a - 2 * w i := by
      dsimp [a]
      linarith [hw' i]
    nlinarith only [mul_nonneg (sq_nonneg (w i - a)) hcoef]
  have hlo := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum, Finset.sum_sub_distrib, hs] at hlo
  change m * (3 * a ^ 2 - 2 * a ^ 3) +
    (6 * a - 6 * a ^ 2) * (1 - m * a) ≤ _ at hlo
  rw [ham, sub_self, mul_zero, add_zero] at hlo
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  convert hlo using 1
  dsimp [a]
  field_simp
  ring

/-- The difference between the top-two upper bound and the cubic moment is a sum
of squares times nonnegative factors. The tail may have repeated eigenvalues. -/
theorem topTwo_cubic_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ℝ) (u : ι → ℝ)
    (hab : b ≤ a) (hu : ∀ i, u i ≤ b)
    (h₁ : a + b + ∑ i, u i = 1) (h₂ : a ^ 2 + b ^ 2 + ∑ i, u i ^ 2 = 1) :
    a ^ 3 + b ^ 3 + ∑ i, u i ^ 3 ≤ topTwoCubic (Fintype.card ι) (a + b) := by
  classical
  let n : ℝ := Fintype.card ι
  let x := a + b
  let t := (1 - x) / n
  have hn : 0 < n := by dsimp [n]; exact_mod_cast Fintype.card_pos (α := ι)
  have hnt : n * t = 1 - x := by dsimp [t]; field_simp
  have hs : ∑ i, u i = n * t := by linarith only [h₁, hnt]
  have ht : t ≤ b := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hu i)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
    rw [hs] at h
    exact (mul_le_mul_iff_right₀ hn).mp h
  have hsum : 0 ≤ ∑ i, (u i - t) ^ 2 * (3 * x / 2 - 2 * t - u i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (by dsimp [x]; linarith [hu i])
  have hexpand (y : ℝ) :
      (y - t) ^ 2 * (3 * x / 2 - 2 * t - y) =
        (3 * x / 2) * y ^ 2 - y ^ 3 +
          (3 * t ^ 2 - 3 * x * t) * y + (3 * x / 2 - 2 * t) * t ^ 2 := by ring
  simp only [hexpand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hs] at hsum
  have htail : ∑ i, u i ^ 2 = 1 - a ^ 2 - b ^ 2 := by linarith only [h₂]
  rw [htail] at hsum
  have hdiff :
      topTwoCubic (Fintype.card ι) x - (a ^ 3 + b ^ 3 + ∑ i, u i ^ 3) =
        (3 * x / 2) * (1 - a ^ 2 - b ^ 2) - (∑ i, u i ^ 3) +
          (3 * t ^ 2 - 3 * x * t) * (n * t) + n * ((3 * x / 2 - 2 * t) * t ^ 2) := by
    have hn' : (Fintype.card ι : ℝ) ≠ 0 := hn.ne'
    unfold topTwoCubic
    dsimp [t, n, x]
    field_simp
    ring
  apply sub_nonneg.mp
  rw [hdiff]
  nlinarith only [hsum]

/-- Five eigenvalues with the trace, norm and holonomy lower bounds cannot
have a top-two sum at least twice the orthogonal Rayleigh lower bound. -/
theorem five_point_moment_obstruction (a b : ℝ) (u : Fin 3 → ℝ) {c : ℝ}
    (hc : 9 / 16 < c) (hab : b ≤ a) (hu : ∀ i, u i ≤ b)
    (h₁ : a + b + ∑ i, u i = 1) (h₂ : a ^ 2 + b ^ 2 + ∑ i, u i ^ 2 = 1)
    (h₃ : (13 + 12 * c) / 25 ≤ a ^ 3 + b ^ 3 + ∑ i, u i ^ 3) :
    a + b < (2 + 8 * c) / 5 := by
  by_contra! h
  have hm := topTwo_cubic_bound a b u hab hu h₁ h₂
  rw [Fintype.card_fin] at hm
  let y := (2 + 8 * c) / 5
  let x := a + b
  have hy : 0 ≤ y - 1 := by dsimp [y]; linarith
  have hx : y - 1 ≤ x - 1 := by dsimp [x, y]; linarith
  have hf (z : ℝ) : topTwoCubic 3 z = 1 - 2 * (z - 1) ^ 2 - 10 / 9 * (z - 1) ^ 3 := by
    unfold topTwoCubic
    norm_num
    ring
  have hmon : topTwoCubic 3 x ≤ topTwoCubic 3 y := by
    rw [hf, hf]
    linarith [pow_le_pow_left₀ hy hx 2, pow_le_pow_left₀ hy hx 3]
  have hgap : 0 < (13 + 12 * c) / 25 - topTwoCubic 3 y := by
    rw [show (13 + 12 * c) / 25 - topTwoCubic 3 y =
      4 * c * (16 * c - 9) * (16 * c + 9) / 225 by rw [hf]; dsimp [y]; ring]
    have hc₀ : 0 < c := by linarith
    have hc₁ : 0 < 16 * c - 9 := by linarith
    have hc₂ : 0 < 16 * c + 9 := by linarith
    positivity
  change _ ≤ topTwoCubic 3 x at hm
  linarith only [h₃, hm, hmon, hgap]


open Real

/-- The limiting three-parent spectrum stays strictly below the simultaneous
Rayleigh lower bound when the candidate overlap is below the target cosine. -/
theorem three_point_moment_obstruction {x y z c a : ℝ}
    (hxy : y ≤ x) (hyz : z ≤ y) (h₁ : x + y + z = 1)
    (h₂ : x ^ 2 + y ^ 2 + z ^ 2 = 1)
    (h₃ : 1 - 2 * (1 - c) / 9 ≤ x ^ 3 + y ^ 3 + z ^ 3)
    (hc₀ : √(2 : ℝ) / 2 ≤ c) (hc₁ : c ≤ 5 / 6)
    (ha₀ : 0 ≤ a) (ha₁ : a < 2 * c ^ 2 - 1) :
    (1 + a) * x + (1 - a) * y < 2 / 3 * (1 + c + (2 * c ^ 2 - 1)) := by
  let h := -z
  let H := (√(2 : ℝ) - 1) / 3
  let k := x - y
  let t := 2 * c ^ 2 - 1
  have hxy₀ : 0 ≤ k := sub_nonneg.mpr hxy
  have hv : x * y + x * z + y * z = 0 := by
    nlinarith only [h₁, h₂, congrArg (fun r : ℝ => r ^ 2) h₁]
  have hz : z ≤ 0 := by
    by_contra! hz
    have hy := hz.trans_le hyz
    have hx := hy.trans_le hxy
    have h₁ := mul_pos hx hy
    have h₂ := mul_pos hx hz
    have h₃ := mul_pos hy hz
    linarith
  have hh : 0 ≤ h := neg_nonneg.mpr hz
  have hs : x + y = 1 + h := by dsimp [h]; linarith
  have hprod : x * y = h * (1 + h) := by
    dsimp [h]
    nlinarith only [hv, congrArg (fun r : ℝ => z * r) h₁]
  have hd : k ^ 2 = 1 - 2 * h - 3 * h ^ 2 := by
    dsimp [k]
    nlinarith only [hprod, congrArg (fun r : ℝ => r ^ 2) hs]
  have hm : h ^ 2 * (1 + h) ≤ 2 * (1 - c) / 27 := by
    have hcube : x ^ 3 + y ^ 3 + z ^ 3 = 1 + 3 * x * y * z := by
      have h := congrArg (fun r : ℝ => r ^ 3) h₁
      have h' := congrArg (fun r : ℝ => (x + y + z) * r) hv
      nlinarith only [h, h']
    rw [hcube, mul_assoc 3 x y, hprod] at h₃
    dsimp [h]
    nlinarith only [h₃]
  have hsqrt := sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hroot₀ : (1 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hroot₁ : √(2 : ℝ) ≤ 3 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hH₂ : H ^ 2 * (1 + H) = (2 - √2) / 27 := by
    dsimp [H]
    nlinarith only [hsqrt, congrArg (fun r : ℝ => √2 * r) hsqrt]
  have hbound : h ≤ H := by
    by_contra! hgt
    have hHs := (pow_lt_pow_left₀ hgt hH two_ne_zero)
    have hpos : 0 < 1 + H := by positivity
    have hlt := mul_lt_mul_of_pos_right hHs hpos
    have hle := mul_le_mul_of_nonneg_left (show 1 + H ≤ 1 + h by linarith) (sq_nonneg h)
    linarith only [hlt, hle, hm, hH₂, hc₀]
  let K := √(2 / 3 : ℝ)
  have hK₂ : K ^ 2 = 2 / 3 := sq_sqrt (by norm_num)
  have hK₀ : 4 / 5 ≤ K := le_sqrt_of_sq_le (by norm_num)
  have hK₁ : K ≤ 5 / 6 := sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hKform : K ^ 2 = 1 - 2 * H - 3 * H ^ 2 := by
    dsimp [H]
    nlinarith only [hsqrt, hK₂]
  have hkdiff : k ^ 2 - K ^ 2 = (H - h) * (2 + 3 * (H + h)) := by
    rw [hd, hKform]
    ring
  have hks : K ≤ k := by
    apply le_of_pow_le_pow_left₀ two_ne_zero hxy₀
    nlinarith only [hkdiff, mul_nonneg (sub_nonneg.mpr hbound) (by positivity : 0 ≤ 2 + 3 * (H + h))]
  have hdiff : k - K ≤ 2 * (H - h) := by
    have hsum : 8 / 5 ≤ k + K := by linarith
    have hcub : 2 + 3 * (H + h) ≤ 3 := by
      dsimp [H] at hbound ⊢
      linarith
    have hleft := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hks)
    have hright := mul_le_mul_of_nonneg_left hcub (sub_nonneg.mpr hbound)
    nlinarith only [hkdiff, hleft, hright, hbound]
  have ht : 0 < t := ha₀.trans_lt ha₁
  have ht₁ : t ≤ 7 / 18 := by
    have hpos : 0 ≤ c := (div_nonneg (sqrt_nonneg _) (by norm_num)).trans hc₀
    dsimp [t]
    nlinarith only [pow_le_pow_left₀ hpos hc₁ 2]
  have hxk : 0 < k := by linarith
  have hmax : 1 + h + t * k ≤ 1 + H + t * K := by
    have hd := mul_le_mul_of_nonneg_left hdiff ht.le
    nlinarith only [hd, mul_nonneg (sub_nonneg.mpr hbound)
      (show 0 ≤ 1 - 2 * t by linarith)]
  have hcompare : 1 + H + t * K ≤ 2 / 3 * (1 + c + t) := by
    have hbase : 1 + H = 2 / 3 * (1 + √2 / 2) := by dsimp [H]; ring
    have ht' : t ≤ (10 / 3) * (c - √2 / 2) := by
      have htend : c + √2 / 2 ≤ 5 / 3 := by linarith
      dsimp [t]
      nlinarith only [hsqrt, mul_nonneg (sub_nonneg.mpr hc₀) (sub_nonneg.mpr htend)]
    have hKt := mul_le_mul_of_nonneg_right (show K - 2 / 3 ≤ 1 / 6 by linarith) ht.le
    linarith only [hbase, hKt, ht', hc₀]
  have hstrict := mul_lt_mul_of_pos_right ha₁ hxk
  dsimp [k] at hstrict hmax
  change 2 / 3 * (1 + c + t) > _
  nlinarith only [hs, hstrict, hmax, hcompare]


/-- The four-point cubic moment bounds the largest eigenvalue pair by
`1 + t`, where the cosine parameter is `1 - 6t² - 4t³`. -/
theorem four_point_top_pair {a b u v t : ℝ} (ht : 0 ≤ t)
    (hab : b ≤ a) (hu : u ≤ b) (hv : v ≤ b)
    (h₁ : a + b + u + v = 1) (h₂ : a ^ 2 + b ^ 2 + u ^ 2 + v ^ 2 = 1)
    (h₃ : (5 + 3 * (1 - 6 * t ^ 2 - 4 * t ^ 3)) / 8 ≤
      a ^ 3 + b ^ 3 + u ^ 3 + v ^ 3) : a + b ≤ 1 + t := by
  let tail : Fin 2 → ℝ := ![u, v]
  have ht₀ (i : Fin 2) : tail i ≤ b := by fin_cases i <;> assumption
  have hupper := topTwo_cubic_bound a b tail hab ht₀
    (by simpa [Fin.sum_univ_two, tail, add_assoc] using h₁)
    (by simpa [Fin.sum_univ_two, tail, add_assoc] using h₂)
  simp [Fin.sum_univ_two, tail, ← add_assoc] at hupper
  let x := a + b - 1
  by_contra! h
  have hx : t < x := by dsimp [x]; linarith
  have he : topTwoCubic 2 (a + b) = 1 - (9 / 4) * x ^ 2 - (3 / 2) * x ^ 3 := by
    unfold topTwoCubic
    dsimp [x]
    norm_num
    ring
  rw [he] at hupper
  have ht₂ := pow_lt_pow_left₀ hx ht two_ne_zero
  have ht₃ := pow_le_pow_left₀ ht hx.le 3
  linarith only [hupper, h₃, ht₂, ht₃]

/-- The spectral support estimate follows from the cubic bound and the
quadratic relation between the top two eigenvalues. -/
theorem four_point_support {a b u v t ω : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) (hθ : 0 ≤ 4 * t ^ 2 + 4 * t - 1)
    (hab : b ≤ a) (hu : u ≤ b) (hv : v ≤ b)
    (h₁ : a + b + u + v = 1) (h₂ : a ^ 2 + b ^ 2 + u ^ 2 + v ^ 2 = 1)
    (h₃ : (5 + 3 * (1 - 6 * t ^ 2 - 4 * t ^ 3)) / 8 ≤ a ^ 3 + b ^ 3 + u ^ 3 + v ^ 3)
    (hR : (1 + 3 * (1 - 6 * t ^ 2 - 4 * t ^ 3)) / 2 ≤ a + b + ω * (a - b)) :
    (1 + 2 * t) * (1 - 3 * t - 3 * t ^ 2) / √(1 - 2 * t - 2 * t ^ 2) ≤ ω := by
  let x := a + b
  let y := a - b
  let X := 1 + t
  let Y := √(1 - 2 * t - 2 * t ^ 2)
  let N := (1 + 2 * t) * (1 - 3 * t - 3 * t ^ 2)
  have ht₂ : t ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := pow_le_pow_left₀ ht ht' 2
  have hY₀ : 0 < 1 - 2 * t - 2 * t ^ 2 := by linarith
  have hY : 0 < Y := sqrt_pos.2 hY₀
  have hY₂ : Y ^ 2 = 1 + 2 * X - 2 * X ^ 2 := by
    dsimp [Y, X]
    rw [sq_sqrt hY₀.le]
    ring
  have hN : 0 < N :=
    mul_pos (by positivity) (by linarith)
  have hx : x ≤ X := four_point_top_pair ht hab hu hv h₁ h₂ h₃
  have hy : 0 ≤ y := sub_nonneg.mpr hab
  have hellipse : y ^ 2 ≤ 1 + 2 * x - 2 * x ^ 2 := by
    dsimp [x, y]
    nlinarith only [sq_nonneg (u - v), h₂, congrArg (fun z : ℝ => z ^ 2)
      (show u + v = 1 - (a + b) by linarith only [h₁])]
  have hlinear : Y * (y - Y) ≤ (X - x) * (2 * X - 1) := by
    nlinarith only [hellipse, hY₂, sq_nonneg (y - Y), sq_nonneg (X - x)]
  have hprod : N * (2 * X - 1) ≤ Y ^ 2 := by
    dsimp [N, X] at hY₂ ⊢
    nlinarith only [hY₂, mul_nonneg (mul_nonneg ht (by positivity : 0 ≤ t + 1)) hθ]
  have hcap : x + (N / Y) * y ≤ X + N := by
    have h := mul_le_mul_of_nonneg_left hlinear hN.le
    have h' := mul_le_mul_of_nonneg_left hprod (sub_nonneg.mpr hx)
    have he : (N / Y) * Y = N := div_mul_cancel₀ _ hY.ne'
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hY)).mp
    have h'' := congrArg (fun z : ℝ => z * Y * y) he
    nlinarith only [h, h', h'', he]
  have hR' : X + N ≤ x + ω * y := by
    linarith only [hR, show X + N = (1 + 3 * (1 - 6 * t ^ 2 - 4 * t ^ 3)) / 2 by
      dsimp [X, N]; ring]
  by_contra! hbad
  have hy' : 0 < y := by
    by_contra! hzero
    have he : y = 0 := le_antisymm hzero hy
    rw [he, mul_zero, add_zero] at hR'
    linarith
  have hstrict := mul_lt_mul_of_pos_right hbad hy'
  change ω * y < (N / Y) * y at hstrict
  linarith only [hcap, hR', hstrict]

end Omega.Geometry.HolonomySpectrum
