import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-
  Static attempt 2: compilation and independent shape review are pending.
  The concrete theorem below retains the exact attempt-1 statement.
  Its scalar premise `hq` must be supplied by a later genuine-angle consumer.
-/

private lemma flat_mate_q_identity
    (s d k X Z : ℝ)
    (hs : 0 < s) (hk0 : 0 < k) (hk1 : k < 1)
    (hX : 0 < X) (hZ : 0 < Z)
    (hXZ : X * Z = s ^ 2)
    (hd : d ^ 2 = k * s ^ 2 - 4 * k / (1 - k)) :
    X * (2 * (X + 2) - d ^ 2) / ((X + 2) * s ^ 2) =
      (k - k * Z / (Z + 2) -
          k * (1 - k * Z / (Z + 2)) * (k * X / (X + 2))) /
        ((k * Z / (Z + 2)) * (1 - k)) := by
  have hX2 : 0 < X + 2 := by linarith only [hX]
  have hZ2 : 0 < Z + 2 := by linarith only [hZ]
  have h1mk : 0 < 1 - k := sub_pos.mpr hk1
  have hv : 0 < k * Z / (Z + 2) := div_pos (mul_pos hk0 hZ) hZ2
  -- Clear the delta denominator before using its polynomial consequence.
  have hd_div : 4 * k / (1 - k) = k * s ^ 2 - d ^ 2 := by
    linarith only [hd]
  have hd_clear : 4 * k = (k * s ^ 2 - d ^ 2) * (1 - k) :=
    (div_eq_iff h1mk.ne').mp hd_div
  have hd_zero : k * s ^ 2 * (1 - k) - 4 * k - d ^ 2 * (1 - k) = 0 := by
    nlinarith only [hd_clear]
  -- Clear both outer denominators before unfolding the rational numerator.
  apply (div_eq_div_iff
    (mul_pos hX2 (sq_pos_of_pos hs)).ne' (mul_pos hv h1mk).ne').2
  have hcross :
      (X * (2 * (X + 2) - d ^ 2) * ((k * Z / (Z + 2)) * (1 - k)) -
          (k - k * Z / (Z + 2) -
            k * (1 - k * Z / (Z + 2)) * (k * X / (X + 2))) *
              ((X + 2) * s ^ 2)) * (Z + 2) =
        k * ((X * Z - s ^ 2) * (2 * (X + 2) - d ^ 2) * (1 - k) +
          s ^ 2 * (k * (X * Z) * (1 - k) - 4 * k - d ^ 2 * (1 - k))) := by
    field_simp [hX2.ne', hZ2.ne', hZ.ne', hk0.ne'] <;> ring
  have hzero :
      (X * (2 * (X + 2) - d ^ 2) * ((k * Z / (Z + 2)) * (1 - k)) -
          (k - k * Z / (Z + 2) -
            k * (1 - k * Z / (Z + 2)) * (k * X / (X + 2))) *
              ((X + 2) * s ^ 2)) * (Z + 2) = 0 := by
    simpa only [hXZ, sub_self, zero_mul, hd_zero, mul_zero, zero_add] using hcross
  have hdiff := (mul_eq_zero.mp hzero).resolve_right hZ2.ne'
  linarith only [hdiff]

private lemma flat_mate_scalar_core
    (s d k X Y : ℝ)
    (hs : 0 < s) (hd : d ^ 2 = k * s ^ 2 - 4 * k / (1 - k))
    (hk0 : 0 < k) (hk1 : k < 1)
    (hflat : s * (1 - k) < 2)
    (hX : 0 < X) (hY : 0 < Y) (hXY : s ^ 2 ≤ X * Y)
    (hYX : Y ≤ X)
    (hq : X * (2 * (X + 2) - d ^ 2) / ((X + 2) * s ^ 2) < (1 / 3 : ℝ)) :
    (1 / 3 : ℝ) < k * Y / (Y + 2) := by
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  have hX2 : 0 < X + 2 := by linarith only [hX]
  have hY2 : 0 < Y + 2 := by linarith only [hY]
  let Y0 : ℝ := s ^ 2 / X
  let u : ℝ := k * X / (X + 2)
  let v : ℝ := k * Y0 / (Y0 + 2)
  have hY0 : 0 < Y0 := div_pos hs2 hX
  have hXY0 : X * Y0 = s ^ 2 := by
    dsimp only [Y0]
    field_simp [hX.ne']
  have hY0leY : Y0 ≤ Y := by
    change s ^ 2 / X ≤ Y
    apply (div_le_iff₀ hX).2
    calc
      s ^ 2 ≤ X * Y := hXY
      _ = Y * X := mul_comm X Y
  have hs2leX2 : s ^ 2 ≤ X ^ 2 := by
    calc
      s ^ 2 ≤ X * Y := hXY
      _ ≤ X * X := mul_le_mul_of_nonneg_left hYX hX.le
      _ = X ^ 2 := by ring
  have hY0leX : Y0 ≤ X := by
    change s ^ 2 / X ≤ X
    apply (div_le_iff₀ hX).2
    simpa only [pow_two] using hs2leX2
  have hY02 : 0 < Y0 + 2 := by linarith only [hY0]
  have hv0 : 0 < v := div_pos (mul_pos hk0 hY0) hY02
  have huv : v ≤ u := by
    dsimp only [u, v]
    apply (div_le_div_iff₀ hY02 hX2).2
    have hnon : 0 ≤ k * (X - Y0) :=
      mul_nonneg hk0.le (sub_nonneg.mpr hY0leX)
    nlinarith only [hnon]
  by_cases hvgt : (1 / 3 : ℝ) < v
  · have hmon : k * Y0 / (Y0 + 2) ≤ k * Y / (Y + 2) := by
      apply (div_le_div_iff₀ hY02 hY2).2
      have hnon : 0 ≤ k * (Y - Y0) :=
        mul_nonneg hk0.le (sub_nonneg.mpr hY0leY)
      nlinarith only [hnon]
    exact lt_of_lt_of_le hvgt hmon
  exfalso
  have hvle : v ≤ (1 / 3 : ℝ) := le_of_not_gt hvgt
  have hFid : k - u - v + (2 - k) * u * v =
      k * (2 - s * (1 - k)) * (2 + s * (1 - k)) /
        ((X + 2) * (Y0 + 2)) := by
    calc
      k - u - v + (2 - k) * u * v =
          k * (4 - (X * Y0) * (1 - k) ^ 2) / ((X + 2) * (Y0 + 2)) := by
        dsimp only [u, v]
        field_simp [hX2.ne', hY02.ne', hY0.ne', hk0.ne'] <;> ring
      _ = k * (2 - s * (1 - k)) * (2 + s * (1 - k)) /
          ((X + 2) * (Y0 + 2)) := by
        rw [hXY0]
        ring
  have hF : 0 < k - u - v + (2 - k) * u * v := by
    have hleft : 0 < 2 - s * (1 - k) := sub_pos.mpr hflat
    have hright : 0 < 2 + s * (1 - k) := by
      have hp : 0 < s * (1 - k) := mul_pos hs (sub_pos.mpr hk1)
      linarith only [hp]
    rw [hFid]
    exact div_pos (mul_pos (mul_pos hk0 hleft) hright) (mul_pos hX2 hY02)
  have hhv : 0 < 1 - (2 - k) * v := by
    have hkvpos : 0 < k * v := mul_pos hk0 hv0
    nlinarith only [hvle, hkvpos]
  have hku : 0 < k - v - u * (1 - (2 - k) * v) := by
    nlinarith only [hF]
  have h1mv : 0 < 1 - v := by linarith only [hvle]
  -- Keep the lower bound on k polynomial: k * (1 + v) - 2 * v > 0.
  have hkvlin : 0 < k * (1 + v) - 2 * v := by
    have hgap : 0 ≤ (u - v) * (1 - (2 - k) * v) :=
      mul_nonneg (sub_nonneg.mpr huv) hhv.le
    have hid : (1 - v) * (k * (1 + v) - 2 * v) =
        (k - v - u * (1 - (2 - k) * v)) +
          (u - v) * (1 - (2 - k) * v) := by ring
    have hprod : 0 < (1 - v) * (k * (1 + v) - 2 * v) := by
      linarith only [hid, hku, hgap]
    exact pos_of_mul_pos_right hprod h1mv.le
  have hq_identity :
      X * (2 * (X + 2) - d ^ 2) / ((X + 2) * s ^ 2) =
        (k - v - k * (1 - v) * u) / (v * (1 - k)) := by
    exact flat_mate_q_identity s d k X Y0 hs hk0 hk1 hX hY0 hXY0 hd
  have hqmain :
      (k - v - k * (1 - v) * u) / (v * (1 - k)) < (1 / 3 : ℝ) := by
    rw [← hq_identity]
    exact hq
  have hdenq : 0 < v * (1 - k) := mul_pos hv0 (sub_pos.mpr hk1)
  have hdenr : 0 < v * (1 - (2 - k) * v) := mul_pos hv0 hhv
  let r : ℝ := (k - v) * (1 - 2 * v) / (v * (1 - (2 - k) * v))
  have hqr : r < (k - v - k * (1 - v) * u) / (v * (1 - k)) := by
    dsimp only [r]
    apply (div_lt_div_iff₀ hdenr hdenq).2
    have hprod : 0 < v * k * (1 - v) * (k - v - u * (1 - (2 - k) * v)) :=
      mul_pos (mul_pos (mul_pos hv0 hk0) h1mv) hku
    have hid :
        (k - v - k * (1 - v) * u) * (v * (1 - (2 - k) * v)) -
          (k - v) * (1 - 2 * v) * (v * (1 - k)) =
        v * k * (1 - v) * (k - v - u * (1 - (2 - k) * v)) := by ring
    linarith only [hid, hprod]
  have hrbound : (1 / 3 : ℝ) ≤ r := by
    have h1m2v : 0 ≤ 1 - 2 * v := by linarith only [hvle]
    have hfactor : 0 ≤ (1 - 2 * v) * (1 - v) * (k * (1 + v) - 2 * v) :=
      mul_nonneg (mul_nonneg h1m2v h1mv.le) hkvlin.le
    have hcompare : (1 - 2 * v) ≤ r := by
      dsimp only [r]
      apply (le_div_iff₀ hdenr).2
      have hid :
          (k - v) * (1 - 2 * v) - (1 - 2 * v) *
              (v * (1 - (2 - k) * v)) =
            (1 - 2 * v) * (1 - v) * (k * (1 + v) - 2 * v) := by ring
      linarith only [hid, hfactor]
    have hthird : (1 / 3 : ℝ) ≤ 1 - 2 * v := by linarith only [hvle]
    exact hthird.trans hcompare
  exact (not_lt_of_ge hqmain.le) (lt_of_le_of_lt hrbound hqr)

theorem NativeFlatMateThresholdTransient
    (a b X Y : ℝ)
    (ha : 1 < a) (hb : 1 < b)
    (hX : 0 < X) (hY : 0 < Y)
    (hXY : (a + b) ^ 2 ≤ X * Y)
    (hYX : Y ≤ X)
    (hq : X * (2 * (X + 2) - (a - b) ^ 2) /
      ((X + 2) * (a + b) ^ 2) < (1 / 3 : ℝ)) :
    (1 / 3 : ℝ) <
      (((Real.sqrt (a ^ 2 - 1) + Real.sqrt (b ^ 2 - 1)) / (a + b)) ^ 2) * Y /
        (Y + 2) := by
  let A : ℝ := Real.sqrt (a ^ 2 - 1)
  let B : ℝ := Real.sqrt (b ^ 2 - 1)
  let s : ℝ := a + b
  let d : ℝ := a - b
  let k : ℝ := ((A + B) / s) ^ 2
  have ha0 : 0 < a := by linarith only [ha]
  have hb0 : 0 < b := by linarith only [hb]
  have haarg : 0 < a ^ 2 - 1 := by nlinarith only [ha, sq_nonneg (a - 1)]
  have hbarg : 0 < b ^ 2 - 1 := by nlinarith only [hb, sq_nonneg (b - 1)]
  have hA0 : 0 < A := Real.sqrt_pos.2 haarg
  have hB0 : 0 < B := Real.sqrt_pos.2 hbarg
  have hA2 : A ^ 2 = a ^ 2 - 1 := Real.sq_sqrt haarg.le
  have hB2 : B ^ 2 = b ^ 2 - 1 := Real.sq_sqrt hbarg.le
  have hs : 0 < s := by dsimp only [s]; linarith only [ha0, hb0]
  have htlt : A + B < s := by
    have hAa : A < a := by nlinarith only [hA2, hA0, ha0]
    have hBb : B < b := by nlinarith only [hB2, hB0, hb0]
    dsimp only [s]
    linarith only [hAa, hBb]
  have ht2 : (A + B) ^ 2 < s ^ 2 := by
    have hsum : 0 < s + (A + B) := by linarith only [hs, hA0, hB0]
    have hprod : 0 < (s - (A + B)) * (s + (A + B)) :=
      mul_pos (sub_pos.mpr htlt) hsum
    nlinarith only [hprod]
  have hk0 : 0 < k := by
    dsimp only [k]
    exact sq_pos_of_pos (div_pos (add_pos hA0 hB0) hs)
  have hk1 : k < 1 := by
    dsimp only [k]
    rw [div_pow]
    apply (div_lt_iff₀ (sq_pos_of_pos hs)).2
    simpa only [one_mul] using ht2
  have hAB : 0 < A * B := mul_pos hA0 hB0
  have hrel : (a * b + 1 - A * B) * (a * b + 1 + A * B) = s ^ 2 := by
    calc
      (a * b + 1 - A * B) * (a * b + 1 + A * B) =
          (a * b + 1) ^ 2 - (A * B) ^ 2 := by ring
      _ = s ^ 2 := by
        rw [mul_pow, hA2, hB2]
        dsimp only [s]
        ring
  have hsdiff : s ^ 2 - (A + B) ^ 2 = 2 * (a * b + 1 - A * B) := by
    dsimp only [s]
    nlinarith only [hA2, hB2]
  have hE : 0 < a * b + 1 - A * B := by linarith only [hsdiff, ht2]
  have hD : 0 < a * b + 1 + A * B := by
    have hab : 0 < a * b := mul_pos ha0 hb0
    linarith only [hab, hAB]
  have htd : (A + B) ^ 2 =
      (a * b + 1 - A * B) * (a * b + 1 + A * B - 2) := by
    nlinarith only [hrel, hsdiff]
  have hdelta_base : d ^ 2 =
      (A + B) ^ 2 - 2 * (a * b + 1 + A * B - 2) := by
    dsimp only [d]
    nlinarith only [hA2, hB2]
  have hdelta : d ^ 2 = (A + B) ^ 2 -
      2 * (A + B) ^ 2 / (a * b + 1 - A * B) := by
    have hdiv : 2 * (A + B) ^ 2 / (a * b + 1 - A * B) =
        2 * (a * b + 1 + A * B - 2) := by
      apply (div_eq_iff hE.ne').2
      nlinarith only [htd]
    rw [hdiv]
    exact hdelta_base
  have hkform : k * s ^ 2 = (A + B) ^ 2 := by
    dsimp only [k]
    field_simp [hs.ne']
  have h1mk : 1 - k = 2 * (a * b + 1 - A * B) / s ^ 2 := by
    apply (eq_div_iff (sq_pos_of_pos hs).ne').2
    nlinarith only [hkform, hsdiff]
  have h1mk_clear : (1 - k) * s ^ 2 = 2 * (a * b + 1 - A * B) :=
    (eq_div_iff (sq_pos_of_pos hs).ne').mp h1mk
  have hd : d ^ 2 = k * s ^ 2 - 4 * k / (1 - k) := by
    have hquot : 4 * k / (1 - k) =
        2 * (A + B) ^ 2 / (a * b + 1 - A * B) := by
      apply (div_eq_div_iff (sub_pos.mpr hk1).ne' hE.ne').2
      calc
        4 * k * (a * b + 1 - A * B) = 2 * k * ((1 - k) * s ^ 2) := by
          rw [h1mk_clear]
          ring
        _ = 2 * (k * s ^ 2) * (1 - k) := by ring
        _ = 2 * (A + B) ^ 2 * (1 - k) := by rw [hkform]
    rw [hkform, hquot]
    exact hdelta
  have hflat : s * (1 - k) < 2 := by
    have hDs : s < a * b + 1 + A * B := by
      have habs : s < a * b + 1 := by
        dsimp only [s]
        have hp : 0 < (a - 1) * (b - 1) :=
          mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb)
        nlinarith only [hp]
      linarith only [habs, hAB]
    have hratio : s * (1 - k) = 2 * s / (a * b + 1 + A * B) := by
      apply (eq_div_iff hD.ne').2
      apply mul_right_cancel₀ hs.ne'
      calc
        (s * (1 - k) * (a * b + 1 + A * B)) * s =
            ((1 - k) * s ^ 2) * (a * b + 1 + A * B) := by ring
        _ = (2 * (a * b + 1 - A * B)) * (a * b + 1 + A * B) := by
          rw [h1mk_clear]
        _ = 2 * ((a * b + 1 - A * B) * (a * b + 1 + A * B)) := by ring
        _ = (2 * s) * s := by rw [hrel]; ring
    rw [hratio]
    apply (div_lt_iff₀ hD).2
    linarith only [hDs]
  change (1 / 3 : ℝ) < k * Y / (Y + 2)
  apply flat_mate_scalar_core s d k X Y hs hd hk0 hk1 hflat hX hY
    (by simpa only [s] using hXY) hYX
  simpa only [s, d] using hq
