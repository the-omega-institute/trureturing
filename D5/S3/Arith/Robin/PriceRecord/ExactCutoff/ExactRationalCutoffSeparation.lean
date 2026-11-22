/- GID: D5/S3/Arith/Robin/PriceRecord/ExactCutoff/ExactRationalCutoffSeparation
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ExactCutoff/ExactRationalCutoffSeparation
   mirror-E: none(waiver:elementary-rational-arithmetic)
   anchors: []
   utility: none
   digest: A fixed-clock rational cutoff resonance has a quantitative logarithmic gap. -/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Integer-power separation for the exact rational cutoff forms. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Robin.PriceRecord.ExactCutoff.ExactRationalCutoffSeparation

private theorem cutoff_powers_ne {m h p j : ℕ} (hh : 0 < h) (hhm : h < m)
    (hhp : h < p) (hp3 : p < 3 * h) (hj : 0 < j) :
    ((2 * (m : ℚ)) / ((m : ℚ) + h)) ^ p ≠
      (((j : ℚ) * m) / ((m : ℚ) + p)) ^ h := by
  let A : ℚ := 2 * (m : ℚ) / ((m : ℚ) + h)
  let C : ℚ := (j : ℚ) * m / ((m : ℚ) + p)
  change A ^ p ≠ C ^ h
  have hm : (0 : ℚ) < m := by exact_mod_cast (hh.trans hhm)
  have hhq : (0 : ℚ) < h := by exact_mod_cast hh
  have hhmq : (h : ℚ) < m := by exact_mod_cast hhm
  have hmh : (0 : ℚ) < (m : ℚ) + h := by positivity
  have hmp : (0 : ℚ) < (m : ℚ) + p := by positivity
  have hAgt : 1 < A := by
    change (1 : ℚ) < 2 * (m : ℚ) / ((m : ℚ) + h)
    exact (lt_div_iff₀ hmh).2 (by linarith)
  have hAlt : A < 2 := by
    change 2 * (m : ℚ) / ((m : ℚ) + h) < 2
    exact (div_lt_iff₀ hmh).2 (by linarith)
  have hCpos : 0 < C := by dsimp [C]; positivity
  -- Cancel the common exponent before taking a rational root.
  let d := h.gcd p
  let H := h / d
  let P := p / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left p hh
  have hH : 0 < H := Nat.div_gcd_pos_of_pos_left p hh
  have hHfactor : H * d = h := Nat.div_mul_cancel (Nat.gcd_dvd_left h p)
  have hPfactor : P * d = p := Nat.div_mul_cancel (Nat.gcd_dvd_right h p)
  have hHP : H < P := by
    apply Nat.lt_of_mul_lt_mul_right (a := d)
    rwa [hHfactor, hPfactor]
  have hP3H : P < 3 * H := by
    apply Nat.lt_of_mul_lt_mul_right (a := d)
    rwa [Nat.mul_assoc, hPfactor, hHfactor]
  have hcoprime : H.Coprime P := Nat.coprime_div_gcd_div_gcd hd
  intro heq
  have hApos : 0 < A := zero_lt_one.trans hAgt
  have hreduced : A ^ P = C ^ H := by
    apply (pow_left_inj₀ (pow_pos hApos P).le (pow_pos hCpos H).le hd.ne').1
    rw [← pow_mul, ← pow_mul, hPfactor, hHfactor]
    exact heq
  obtain ⟨root, hAroot, hCroot⟩ := (pow_eq_pow_iff_of_coprime hcoprime.symm).1 hreduced
  let r : ℚ := |root|
  have hrH : r ^ H = A := by
    change |root| ^ H = A
    rw [← abs_pow, ← hAroot, abs_of_pos hApos]
  have hrP : r ^ P = C := by
    change |root| ^ P = C
    rw [← abs_pow, ← hCroot, abs_of_pos hCpos]
  have hr : 1 < r := by
    apply (one_lt_pow_iff_of_nonneg (abs_nonneg root) hH.ne').1
    change 1 < r ^ H
    rw [hrH]
    exact hAgt
  -- Eliminate m before clearing the reduced denominator of r.
  have hAclear : A * ((m : ℚ) + h) = 2 * (m : ℚ) := div_mul_cancel₀ _ hmh.ne'
  have hCclear : C * ((m : ℚ) + p) = (j : ℚ) * m := div_mul_cancel₀ _ hmp.ne'
  have hstep : r ^ (P - H) * A = C := by
    rw [← hrH, ← pow_add, Nat.sub_add_cancel hHP.le, hrP]
  have hCmh : C * ((m : ℚ) + h) = 2 * (m : ℚ) * r ^ (P - H) := by
    rw [← hstep, mul_assoc, hAclear, mul_comm (r ^ (P - H))]
  have hhfactor : (h : ℚ) = (H : ℚ) * (d : ℚ) := by exact_mod_cast hHfactor.symm
  have hpfactor : (p : ℚ) = (P : ℚ) * (d : ℚ) := by exact_mod_cast hPfactor.symm
  have hrel : ((P : ℚ) - (H : ℚ)) * C + (j : ℚ) * H =
      2 * (P : ℚ) * r ^ (P - H) := by
    apply mul_right_cancel₀ hm.ne'
    calc
      _ = C * ((P : ℚ) * ((m : ℚ) + h) - (H : ℚ) * ((m : ℚ) + p)) +
          (H : ℚ) * ((j : ℚ) * m) := by rw [hhfactor, hpfactor]; ring
      _ = (P : ℚ) * (C * ((m : ℚ) + h)) +
          (H : ℚ) * ((j : ℚ) * m - C * ((m : ℚ) + p)) := by ring
      _ = _ := by rw [hCmh, hCclear]; ring
  let u := r.num.natAbs
  let v := r.den
  have hv : 0 < v := r.den_pos
  have huv : u.Coprime v := r.reduced
  have hunum : (u : ℤ) = r.num :=
    Int.natAbs_of_nonneg (Rat.num_nonneg.2 (zero_le_one.trans hr.le))
  have huq : (u : ℚ) = (r.num : ℚ) := by exact_mod_cast hunum
  have hrv : (u : ℚ) / (v : ℚ) = r := by
    rw [huq]
    exact Rat.num_div_den r
  have hvq : (v : ℚ) ≠ 0 := by exact_mod_cast hv.ne'
  have hclear (n : ℕ) : r ^ n * (v : ℚ) ^ n = (u : ℚ) ^ n := by
    rw [← hrv, div_pow]
    exact div_mul_cancel₀ _ (pow_ne_zero _ hvq)
  have hvsplit : (v : ℚ) ^ P = (v : ℚ) ^ (P - H) * (v : ℚ) ^ H := by
    rw [← pow_add, Nat.sub_add_cancel hHP.le]
  have hpolyQ : ((P : ℚ) - (H : ℚ)) * (u : ℚ) ^ P + (j : ℚ) * H * (v : ℚ) ^ P =
      2 * (P : ℚ) * (u : ℚ) ^ (P - H) * (v : ℚ) ^ H := by
    calc
      _ = (((P : ℚ) - (H : ℚ)) * C + (j : ℚ) * H) * (v : ℚ) ^ P := by
        rw [← hclear P, hrP]
        ring
      _ = (2 * (P : ℚ) * r ^ (P - H)) * (v : ℚ) ^ P := by rw [hrel]
      _ = 2 * (P : ℚ) * (r ^ (P - H) * (v : ℚ) ^ (P - H)) * (v : ℚ) ^ H := by
        rw [hvsplit]
        ring
      _ = _ := by rw [hclear]
  have hpoly : (P - H) * u ^ P + j * H * v ^ P = 2 * P * u ^ (P - H) * v ^ H := by
    rw [← Nat.cast_sub hHP.le] at hpolyQ
    exact_mod_cast hpolyQ
  have hvdvd : v ^ H ∣ v ^ P :=
    ⟨v ^ (P - H), by rw [← pow_add, Nat.add_sub_of_le hHP.le]⟩
  have hsumdvd : v ^ H ∣ (P - H) * u ^ P + j * H * v ^ P := by
    rw [hpoly]
    exact Nat.dvd_mul_left _ _
  have hproddvd : v ^ H ∣ (P - H) * u ^ P :=
    (Nat.dvd_add_left (Nat.dvd_mul_left_of_dvd hvdvd (j * H))).1 hsumdvd
  have hcoeffdvd : v ^ H ∣ P - H := (huv.symm.pow H P).dvd_of_dvd_mul_right hproddvd
  have hvone : v = 1 := by
    by_contra hne
    have htwo : 2 ≤ v := by omega
    have hbound : 2 * H ≤ 2 ^ H := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hH.ne'
      rw [hk, pow_succ]
      have hkpow : k < 2 ^ k := Nat.lt_two_pow_self
      omega
    have hlt : P - H < 2 * H := by omega
    have hle : v ^ H ≤ P - H := Nat.le_of_dvd (by omega) hcoeffdvd
    exact (not_lt_of_ge ((hbound.trans (Nat.pow_le_pow_left htwo H)).trans hle)) hlt
  have hru : r = (u : ℚ) := by simpa only [hvone, Nat.cast_one, div_one] using hrv.symm
  have huone : 1 < u := by
    have : (1 : ℚ) < (u : ℚ) := by simpa only [hru] using hr
    exact_mod_cast this
  have hrtwo : (2 : ℚ) ≤ r := by
    rw [hru]
    exact_mod_cast (show 2 ≤ u by omega)
  have hrle : r ≤ r ^ H := le_self_pow₀ hr.le hH.ne'
  rw [hrH] at hrle
  exact (not_lt_of_ge (hrtwo.trans hrle)) hAlt

private theorem cutoff_ratio_identity {K : Type*} [Field K] [CharZero K]
    {m h p j : ℕ} (hm : 0 < m) (hhp : h ≤ p) :
    ((2 ^ p * m ^ (p - h) * (m + p) ^ h : ℕ) : K) /
      ((j ^ h * (m + h) ^ p : ℕ) : K) =
    ((2 * (m : K)) / ((m : K) + h)) ^ p /
      (((j : K) * m) / ((m : K) + p)) ^ h := by
  have hm0 : (m : K) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hpow : (m : K) ^ (p - h) * (m : K) ^ h = (m : K) ^ p := by
    rw [← pow_add, Nat.sub_add_cancel hhp]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat,
    div_pow, mul_pow, div_div_div_eq]
  symm
  calc
    _ = ((2 : K) ^ p * (m : K) ^ (p - h) * ((m : K) + p) ^ h * (m : K) ^ h) /
        (((j : K) ^ h * ((m : K) + h) ^ p) * (m : K) ^ h) := by
      rw [← hpow]
      congr 1 <;> ring
    _ = _ := mul_div_mul_right _ _ (pow_ne_zero _ hm0)

private theorem log_ratio_separation {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (hne : u ≠ v) :
    1 / ((max u v : ℕ) : ℝ) ≤ |Real.log ((u : ℝ) / (v : ℝ))| := by
  have ordered {a b : ℕ} (ha : 0 < a) (hab : a < b) :
      1 / (b : ℝ) ≤ Real.log ((b : ℝ) / (a : ℝ)) := by
    have har : (0 : ℝ) < a := by exact_mod_cast ha
    have hbr : (0 : ℝ) < b := by exact_mod_cast (ha.trans hab)
    have hgap : (a : ℝ) + 1 ≤ (b : ℝ) := by
      exact_mod_cast (show a + 1 ≤ b by omega)
    calc
      _ ≤ ((b : ℝ) - (a : ℝ)) / (b : ℝ) :=
        div_le_div_of_nonneg_right (by linarith only [hgap]) hbr.le
      _ = 1 - ((b : ℝ) / (a : ℝ))⁻¹ := by rw [inv_div, sub_div, div_self hbr.ne']
      _ ≤ _ := Real.one_sub_inv_le_log_of_pos (div_pos hbr har)
  rcases lt_or_gt_of_ne hne with h | h
  · rw [max_eq_right h.le]
    refine (ordered hu h).trans ?_
    rw [← inv_div (u : ℝ) (v : ℝ), Real.log_inv]
    exact neg_le_abs _
  · rw [max_eq_left h.le]
    exact (ordered hv h).trans (le_abs_self _)

/-- The exact finite separation bound for the Robin cutoff label `(m, h, p)`.
The positive natural mode `j` can in particular be `3` or `5`. -/
public theorem cutoff_resonance_separation {m h p j : ℕ} (hh : 0 < h) (hhm : h < m)
    (hhp : h < p) (hp3 : p < 3 * h) (hj : 0 < j) :
    let U : ℕ := 2 ^ p * m ^ (p - h) * (m + p) ^ h
    let W : ℕ := j ^ h * (m + h) ^ p
    U ≠ W ∧
      1 / ((max U W : ℕ) : ℝ) ≤
        |(p : ℝ) * Real.log (2 * (m : ℝ) / ((m : ℝ) + h)) -
          (h : ℝ) * Real.log ((j : ℝ) * m / ((m : ℝ) + p))| := by
  let U : ℕ := 2 ^ p * m ^ (p - h) * (m + p) ^ h
  let W : ℕ := j ^ h * (m + h) ^ p
  have hm : 0 < m := hh.trans hhm
  have hU : 0 < U := by dsimp [U]; positivity
  have hW : 0 < W := by dsimp [W]; positivity
  have hratio {K : Type} [Field K] [CharZero K] :
      (U : K) / (W : K) =
        ((2 * (m : K)) / ((m : K) + h)) ^ p /
          (((j : K) * m) / ((m : K) + p)) ^ h :=
    cutoff_ratio_identity hm hhp.le
  have hne : U ≠ W := by
    intro heq
    have hq := hratio (K := ℚ)
    have hWq : (W : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hW.ne'
    rw [heq, div_self hWq] at hq
    have hC : (0 : ℚ) < (j : ℚ) * m / ((m : ℚ) + p) := by positivity
    exact (cutoff_powers_ne hh hhm hhp hp3 hj)
      ((div_eq_one_iff_eq (pow_ne_zero _ hC.ne')).1 hq.symm)
  have hA : (0 : ℝ) < 2 * (m : ℝ) / ((m : ℝ) + h) := by positivity
  have hC : (0 : ℝ) < (j : ℝ) * m / ((m : ℝ) + p) := by positivity
  have hlog := log_ratio_separation hU hW hne
  rw [hratio (K := ℝ), Real.log_div (pow_ne_zero _ hA.ne') (pow_ne_zero _ hC.ne'),
    Real.log_pow, Real.log_pow] at hlog
  exact ⟨hne, hlog⟩

/-- The literal mode-three residual bound excludes short denominators at the
clock `L` under the stated numerical hypotheses. -/
public theorem mode_three_short_denominator_exclusion {m h p : ℕ} {L C : ℝ}
    (hh : 0 < h) (hhm : h < m) (hhp : h < p) (hp85 : 5 * p ≤ 8 * h)
    (hmClock : (m : ℝ) ≤ 2 * (h : ℝ) * L) (hL : Real.exp 50 ≤ L)
    (hshort : (h : ℝ) ≤ L / (50 * Real.log L)) (hC : 1 ≤ C)
    (hLC : 1500 * Real.log (2 * C) < L) :
    ¬ |(p : ℝ) * Real.log (2 * (m : ℝ) / ((m : ℝ) + h)) -
        (h : ℝ) * Real.log (3 * (m : ℝ) / ((m : ℝ) + p))| ≤
      C * ((L ^ 2)⁻¹ * Real.exp (-(L / 15)) + (h : ℝ) * Real.exp (-(L / 3))) := by
  let R : ℝ := (p : ℝ) * Real.log (2 * (m : ℝ) / ((m : ℝ) + h)) -
    (h : ℝ) * Real.log (3 * (m : ℝ) / ((m : ℝ) + p))
  change ¬ |R| ≤ _
  have hm : 0 < m := hh.trans hhm
  have hp3 : p < 3 * h := by omega
  have hL2 : 2 ≤ L := by
    linarith only [Real.add_one_le_exp 50, hL]
  have hLpos : 0 < L := by linarith only [hL2]
  have hlogL50 : 50 ≤ Real.log L := (Real.le_log_iff_exp_le hLpos).2 hL
  have hlogL0 : 0 ≤ Real.log L := by linarith only [hlogL50]
  have hhR : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hshortMul : (h : ℝ) * (50 * Real.log L) ≤ L :=
    (le_div_iff₀ (by linarith only [hlogL50])).1 hshort
  have hh3 : 3 * (h : ℝ) ≤ L := calc
    _ = (h : ℝ) * 3 := mul_comm _ _
    _ ≤ (h : ℝ) * (50 * Real.log L) :=
      mul_le_mul_of_nonneg_left (by linarith only [hlogL50]) hhR
    _ ≤ L := hshortMul
  have hhL : (h : ℝ) ≤ L := by linarith only [hh3, hhR]
  have hp85R : 5 * (p : ℝ) ≤ 8 * (h : ℝ) := by exact_mod_cast hp85
  have hpRatio : (p : ℝ) ≤ (8 / 5 : ℝ) * (h : ℝ) := by linarith only [hp85R]
  have hpClock : (p : ℝ) ≤ (h : ℝ) * L := calc
    _ ≤ (8 / 5 : ℝ) * (h : ℝ) := hpRatio
    _ ≤ L * (h : ℝ) := mul_le_mul_of_nonneg_right (by linarith only [hL2]) hhR
    _ = _ := mul_comm _ _
  -- The shortness hypothesis supplies the stronger bound m + p ≤ L².
  have hmpSq : (m : ℝ) + (p : ℝ) ≤ L ^ 2 := calc
    _ ≤ 2 * (h : ℝ) * L + (h : ℝ) * L := add_le_add hmClock hpClock
    _ = (3 * (h : ℝ)) * L := by ring
    _ ≤ L * L := mul_le_mul_of_nonneg_right hh3 hLpos.le
    _ = _ := (pow_two L).symm

  let U : ℕ := 2 ^ p * m ^ (p - h) * (m + p) ^ h
  let W : ℕ := 3 ^ h * (m + h) ^ p
  let D : ℝ := ((max U W : ℕ) : ℝ)
  let Q : ℝ := 3 * L ^ 2
  have hWpos : 0 < W := by dsimp [W]; positivity
  have hDpos : 0 < D := by
    have hmax : 0 < max U W := hWpos.trans_le (le_max_right U W)
    dsimp [D]
    exact_mod_cast hmax
  have hQpos : 0 < Q := by dsimp [Q]; positivity
  have hU : U ≤ (2 : ℕ) ^ p * (m + p) ^ p := calc
    _ ≤ 2 ^ p * (m + p) ^ (p - h) * (m + p) ^ h :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (by omega : m ≤ m + p) _))
    _ = _ := by rw [Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel hhp.le]
  have hW : W ≤ (3 : ℕ) ^ h * (m + p) ^ p :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : m + h ≤ m + p) _)
  have hUR : (U : ℝ) ≤ (2 : ℝ) ^ p * ((m : ℝ) + p) ^ p := by exact_mod_cast hU
  have hWR : (W : ℝ) ≤ (3 : ℝ) ^ h * ((m : ℝ) + p) ^ p := by exact_mod_cast hW
  have hmpQ : (m : ℝ) + (p : ℝ) ≤ Q := by
    dsimp [Q]
    nlinarith only [hmpSq, sq_nonneg L]
  have h2mpQ : 2 * ((m : ℝ) + p) ≤ Q := by
    dsimp [Q]
    nlinarith only [hmpSq, sq_nonneg L]
  have hthreePow : (1 : ℝ) ≤ (3 : ℝ) ^ h := one_le_pow₀ (by norm_num)
  have hUBound : (U : ℝ) ≤ (3 : ℝ) ^ h * Q ^ p := calc
    _ ≤ (2 : ℝ) ^ p * ((m : ℝ) + p) ^ p := hUR
    _ = (2 * ((m : ℝ) + p)) ^ p := (mul_pow _ _ _).symm
    _ ≤ Q ^ p := pow_le_pow_left₀ (by positivity) h2mpQ p
    _ ≤ _ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hthreePow (pow_nonneg hQpos.le p)
  have hWBound : (W : ℝ) ≤ (3 : ℝ) ^ h * Q ^ p := hWR.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hmpQ p) (by positivity))
  have hDBound : D ≤ (3 : ℝ) ^ h * Q ^ p := by
    change ((max U W : ℕ) : ℝ) ≤ _
    rw [Nat.cast_max]
    exact max_le hUBound hWBound
  have hHeight : Real.log D ≤ (h : ℝ) * Real.log 3 + (p : ℝ) * Real.log Q := calc
    _ ≤ Real.log ((3 : ℝ) ^ h * Q ^ p) := Real.log_le_log hDpos hDBound
    _ = _ := by
      rw [Real.log_mul (pow_ne_zero h (by norm_num : (3 : ℝ) ≠ 0))
        (pow_ne_zero p hQpos.ne'), Real.log_pow, Real.log_pow]
  have hlogQ : Real.log Q = Real.log 3 + 2 * Real.log L := by
    dsimp [Q]
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (pow_ne_zero 2 hLpos.ne'),
      Real.log_pow, Nat.cast_two]
  have hlogQ0 : 0 ≤ Real.log Q := by
    rw [hlogQ]
    exact add_nonneg (Real.log_nonneg (by norm_num)) (mul_nonneg (by norm_num) hlogL0)
  have hlog3 : Real.log 3 ≤ (3 / 2 : ℝ) :=
    (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 3)).2
      ((by norm_num : (3 : ℝ) ≤ 1 + 3 / 2 + (3 / 2) ^ 2 / 2).trans
        (Real.quadratic_le_exp_of_nonneg (by norm_num)))
  have hlogD : Real.log D ≤ (33 / 500 : ℝ) * L := calc
    _ ≤ (h : ℝ) * Real.log 3 + (p : ℝ) * Real.log Q := hHeight
    _ ≤ (h : ℝ) * Real.log 3 + ((8 / 5 : ℝ) * (h : ℝ)) * Real.log Q :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hpRatio hlogQ0)
    _ = (h : ℝ) * ((16 / 5 : ℝ) * Real.log L + (13 / 5 : ℝ) * Real.log 3) := by
      rw [hlogQ]
      ring
    _ ≤ (h : ℝ) * ((33 / 10 : ℝ) * Real.log L) :=
      mul_le_mul_of_nonneg_left (by linarith only [hlogL50, hlog3]) hhR
    _ = (33 / 500 : ℝ) * ((h : ℝ) * (50 * Real.log L)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hshortMul (by norm_num)
  have hgap : 1 / D ≤ |R| := by
    simpa only [D, U, W, R, Nat.cast_ofNat] using
      (cutoff_resonance_separation (j := 3) hh hhm hhp hp3 (by decide)).2
  have hlower : Real.exp (-((33 / 500 : ℝ) * L)) ≤ |R| := calc
    _ = 1 / Real.exp ((33 / 500 : ℝ) * L) := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / D := one_div_le_one_div_of_le hDpos ((Real.log_le_iff_le_exp hDpos).1 hlogD)
    _ ≤ _ := hgap

  have hlogLRate : Real.log L ≤ 4 * L / 15 := by
    have hquad := Real.quadratic_le_exp_of_nonneg hlogL0
    rw [Real.exp_log hLpos] at hquad
    have hprod := mul_nonneg hlogL0 (sub_nonneg.mpr hlogL50)
    nlinarith only [hquad, hprod, hlogL0]
  have hLsq1 : 1 ≤ L ^ 2 := by
    have hL1 : 1 ≤ L := by linarith only [hL2]
    simpa only [one_pow] using (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hL1 2)
  have hinv : (L ^ 2)⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hLsq1)
  have hfast : (h : ℝ) * Real.exp (-(L / 3)) ≤ Real.exp (-(L / 15)) := calc
    _ ≤ L * Real.exp (-(L / 3)) := mul_le_mul_of_nonneg_right hhL (Real.exp_pos _).le
    _ = Real.exp (Real.log L + -(L / 3)) := by rw [Real.exp_add, Real.exp_log hLpos]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hlogLRate])
  have hfirst : (L ^ 2)⁻¹ * Real.exp (-(L / 15)) ≤ Real.exp (-(L / 15)) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hinv (Real.exp_pos (-(L / 15))).le
  have hupper : C * ((L ^ 2)⁻¹ * Real.exp (-(L / 15)) + (h : ℝ) * Real.exp (-(L / 3))) ≤
      2 * C * Real.exp (-(L / 15)) := calc
    _ ≤ C * (Real.exp (-(L / 15)) + Real.exp (-(L / 15))) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst hfast) (by linarith only [hC])
    _ = _ := by ring
  have h2C : 0 < 2 * C := by linarith only [hC]
  have hstrict : 2 * C * Real.exp (-(L / 15)) < Real.exp (-((33 / 500 : ℝ) * L)) := calc
    _ = Real.exp (Real.log (2 * C) + -(L / 15)) := by rw [Real.exp_add, Real.exp_log h2C]
    _ < _ := Real.exp_lt_exp.mpr (by linarith only [hLC])
  intro hR
  exact (not_lt_of_ge hlower) ((hR.trans hupper).trans_lt hstrict)

end D5.S3.Arith.Robin.PriceRecord.ExactCutoff.ExactRationalCutoffSeparation
