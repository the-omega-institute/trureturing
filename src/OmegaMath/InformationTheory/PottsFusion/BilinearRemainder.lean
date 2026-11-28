module

public import OmegaBuild.Commands
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Omega original.

A corrected rational estimate for common-input information combining.
The parameters `S` and `V` represent the sum and product of two centered
quadratic energies.  The correction removes terms whose calibrated average
vanishes.  A global ratio bound controls small and zero denominators.
-/

compile_only_with_mathlib

@[expose] public section

namespace Omega.InformationTheory.PottsFusion

/-- A corrected ratio has a bilinear remainder under moment bounds. -/
theorem corrected_ratio_bilinear_bound
    (n S V c d e f t H : ℝ)
    (hn : 1 ≤ n) (hS0 : 0 ≤ S) (hSn : S ≤ 2 * n)
    (hc : |c| ≤ t) (ht : t ^ 2 ≤ V)
    (hd : |d| ≤ n * t) (he : |e| ≤ n * t)
    (hf : f ≤ n * V)
    (hnum : 1 / 2 ≤ 1 + c →
      (H + 1) * (1 + c) = 1 + S + 4 * c + 2 * d + 2 * e + f)
    (hglobal : H ≤ n * (1 + c) - 1) :
    H ≤ S + ((3 - S) * c + 2 * d + 2 * e) + 32 * n * V := by
  let L : ℝ := (3 - S) * c + 2 * d + 2 * e
  let k : ℝ := n * V
  have hn0 : 0 ≤ n := by linarith only [hn]
  have ht0 : 0 ≤ t := le_trans (abs_nonneg c) hc
  have hV0 : 0 ≤ V := le_trans (sq_nonneg t) ht
  have hk0 : 0 ≤ k := mul_nonneg hn0 hV0
  have hc_lo : -t ≤ c := (abs_le.mp hc).1
  have hc_hi : c ≤ t := (abs_le.mp hc).2
  have hcV : c ^ 2 ≤ V := by
    have hp := mul_nonneg (sub_nonneg.mpr hc_hi)
      (show 0 ≤ t + c by linarith only [hc_lo])
    nlinarith only [hp, ht]
  have hdc : |d * c| ≤ n * V := by
    calc
      |d * c| = |d| * |c| := abs_mul d c
      _ ≤ (n * t) * t :=
        mul_le_mul hd hc (abs_nonneg c) (mul_nonneg hn0 ht0)
      _ = n * t ^ 2 := by ring
      _ ≤ n * V := mul_le_mul_of_nonneg_left ht hn0
  have hec : |e * c| ≤ n * V := by
    calc
      |e * c| = |e| * |c| := abs_mul e c
      _ ≤ (n * t) * t :=
        mul_le_mul he hc (abs_nonneg c) (mul_nonneg hn0 ht0)
      _ = n * t ^ 2 := by ring
      _ ≤ n * V := mul_le_mul_of_nonneg_left ht hn0
  by_cases hden : 1 / 2 ≤ 1 + c
  · have hpos : 0 < 1 + c := by linarith only [hden]
    have hSc : S * c ^ 2 ≤ 2 * n * V := by
      calc
        S * c ^ 2 ≤ S * V := mul_le_mul_of_nonneg_left hcV hS0
        _ ≤ (2 * n) * V := mul_le_mul_of_nonneg_right hSn hV0
        _ = 2 * n * V := rfl
    have hdneg : -(d * c) ≤ n * V := le_trans (neg_le_abs (d * c)) hdc
    have heneg : -(e * c) ≤ n * V := le_trans (neg_le_abs (e * c)) hec
    have hrem : f - L * c ≤ 7 * k := by
      have hsum :
          f - 3 * c ^ 2 + S * c ^ 2 - 2 * (d * c) - 2 * (e * c) ≤
            7 * (n * V) := by
        nlinarith only [hf, hSc, hdneg, heneg, sq_nonneg c]
      calc
        f - L * c =
            f - 3 * c ^ 2 + S * c ^ 2 - 2 * (d * c) - 2 * (e * c) := by
          dsimp only [L]
          ring
        _ ≤ 7 * (n * V) := hsum
        _ = 7 * k := rfl
    have hid : (H - S - L) * (1 + c) = f - L * c := by
      calc
        (H - S - L) * (1 + c) =
            (H + 1) * (1 + c) - (1 + S + L) * (1 + c) := by ring
        _ = (1 + S + 4 * c + 2 * d + 2 * e + f) -
            (1 + S + L) * (1 + c) := by rw [hnum hden]
        _ = f - L * c := by dsimp only [L]; ring
    have hfloor := mul_nonneg hk0 (sub_nonneg.mpr hden)
    have hmul : (H - S - L) * (1 + c) ≤ (32 * k) * (1 + c) := by
      rw [hid]
      nlinarith only [hrem, hfloor, hk0]
    have hlocal : H - S - L ≤ 32 * k := by
      by_contra hnot
      have hdiff : 0 < H - S - L - 32 * k := by linarith only [hnot]
      have hp := mul_pos hdiff hpos
      nlinarith only [hp, hmul]
    dsimp only [L, k] at hlocal
    nlinarith only [hlocal]
  · have hsmall : 1 + c < 1 / 2 := lt_of_not_ge hden
    have ht_half : 1 / 2 ≤ t := by
      have hcneg := neg_le_abs c
      linarith only [hsmall, hcneg, hc]
    have htV : t ≤ 2 * V := by
      have hp := mul_nonneg ht0 (show 0 ≤ t - 1 / 2 by linarith only [ht_half])
      nlinarith only [hp, ht]
    have hVquarter : 1 / 4 ≤ V := by
      have hp := mul_nonneg
        (show 0 ≤ t - 1 / 2 by linarith only [ht_half])
        (show 0 ≤ t + 1 / 2 by linarith only [ht_half])
      nlinarith only [hp, ht]
    have hcoef : |3 - S| ≤ 3 + S := by
      rw [abs_le]
      constructor <;> linarith only [hS0]
    have hprod : |3 - S| * |c| ≤ (3 + S) * t :=
      mul_le_mul hcoef hc (abs_nonneg c) (by linarith only [hS0])
    have hLbase : |L| ≤ (3 + S) * t + 2 * (n * t) + 2 * (n * t) := by
      calc
        |L| ≤ |(3 - S) * c + 2 * d| + |2 * e| := by
          simpa only [L] using abs_add_le ((3 - S) * c + 2 * d) (2 * e)
        _ ≤ (|(3 - S) * c| + |2 * d|) + |2 * e| :=
          add_le_add (abs_add_le ((3 - S) * c) (2 * d)) (le_refl |2 * e|)
        _ = |3 - S| * |c| + 2 * |d| + 2 * |e| := by norm_num [abs_mul]
        _ ≤ (3 + S) * t + 2 * (n * t) + 2 * (n * t) :=
          add_le_add (add_le_add hprod
            (mul_le_mul_of_nonneg_left hd (by norm_num)))
            (mul_le_mul_of_nonneg_left he (by norm_num))
    have hcoeff : 3 + S + 4 * n ≤ 9 * n := by linarith only [hn, hSn]
    have hscale := mul_le_mul_of_nonneg_right hcoeff ht0
    have hL9 : |L| ≤ 9 * n * t := by nlinarith only [hLbase, hscale]
    have hL18 : |L| ≤ 18 * k := by
      calc
        |L| ≤ 9 * n * t := hL9
        _ ≤ (9 * n) * (2 * V) :=
          mul_le_mul_of_nonneg_left htV (mul_nonneg (by norm_num) hn0)
        _ = 18 * k := by dsimp only [k]; ring
    have hHn : H ≤ n := by
      have hp := mul_le_mul_of_nonneg_left
        (show 1 + c ≤ 1 by linarith only [hsmall]) hn0
      nlinarith only [hglobal, hp]
    have hn4 : n ≤ 4 * k := by
      have hp := mul_le_mul_of_nonneg_left hVquarter hn0
      dsimp only [k]
      nlinarith only [hp]
    have hLneg := neg_le_abs L
    have hfinal : H ≤ S + L + 32 * k := by
      nlinarith only [hHn, hn4, hL18, hLneg, hS0, hk0]
    simpa only [L, k, mul_assoc] using hfinal

end Omega.InformationTheory.PottsFusion
