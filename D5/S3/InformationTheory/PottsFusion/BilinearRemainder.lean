/- GID: D5/S3/InformationTheory/PottsFusion/BilinearRemainder
   generality: G
   mirror-B: none(waiver:covered-by-chi-square-bilinear-fusion-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A corrected rational estimate for common-input information combining. -/

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
    H ≤ S + ((3 - S) * c + 2 * d + 2 * e) + 13 * n * V := by
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
  by_cases hden : 7 / 13 ≤ 1 + c
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
            (1 + S + L) * (1 + c) := by rw [hnum (by linarith only [hden])]
        _ = f - L * c := by dsimp only [L]; ring
    have hfloor := mul_nonneg hk0 (sub_nonneg.mpr hden)
    have hmul : (H - S - L) * (1 + c) ≤ (13 * k) * (1 + c) := by
      rw [hid]
      nlinarith only [hrem, hfloor, hk0]
    have hlocal : H - S - L ≤ 13 * k := by
      by_contra hnot
      have hdiff : 0 < H - S - L - 13 * k := by linarith only [hnot]
      have hp := mul_pos hdiff hpos
      nlinarith only [hp, hmul]
    dsimp only [L, k] at hlocal
    nlinarith only [hlocal]
  · have hsmall : 1 + c < 7 / 13 := lt_of_not_ge hden
    have ht_floor : 6 / 13 ≤ t := by
      have hcneg := neg_le_abs c
      linarith only [hsmall, hcneg, hc]
    have htV : t ≤ (13 / 6) * V := by
      have hp := mul_nonneg ht0 (show 0 ≤ t - 6 / 13 by linarith only [ht_floor])
      nlinarith only [hp, ht]
    let z : ℝ := -c
    have hcn : c < 0 := by linarith only [hsmall]
    have hz_floor : 6 / 13 < z := by
      dsimp only [z]
      linarith only [hsmall]
    have hz_abs : |c| = z := by
      rw [abs_of_neg hcn]
    have hzt : z ≤ t := by
      calc
        z = |c| := hz_abs.symm
        _ ≤ t := hc
    have hd_lo : -(n * t) ≤ d := by
      have hneg := neg_le_neg hd
      have habs := neg_le_abs d
      linarith only [hneg, habs]
    have he_lo : -(n * t) ≤ e := by
      have hneg := neg_le_neg he
      have habs := neg_le_abs e
      linarith only [hneg, habs]
    have hbase : H - S - L ≤
        n - 1 + (3 - n) * z - S * (1 + z) + 4 * n * t := by
      dsimp only [L, z]
      nlinarith only [hglobal, hd_lo, he_lo]
    have hprod : 0 ≤ (n - 1) * (3 * z - 1) := by
      exact mul_nonneg (by linarith only [hn]) (by linarith only [hz_floor])
    have hSz : 0 ≤ S * (1 + z) := by
      exact mul_nonneg hS0 (by linarith only [hz_floor])
    have hmid : n - 1 + (3 - n) * z - S * (1 + z) ≤ 2 * n * z := by
      nlinarith only [hprod, hSz]
    have hzt_mul : 2 * n * z ≤ 2 * n * t := by
      exact mul_le_mul_of_nonneg_left hzt (by nlinarith only [hn])
    have h6 : 2 * n * z + 4 * n * t ≤ 6 * n * t := by
      nlinarith only [hzt_mul]
    have h13 : 6 * n * t ≤ 13 * k := by
      calc
        6 * n * t ≤ (6 * n) * ((13 / 6) * V) :=
          mul_le_mul_of_nonneg_left htV (by nlinarith only [hn])
        _ = 13 * k := by dsimp only [k]; ring
    have hbad : H - S - L ≤ 13 * k := by
      calc
        H - S - L ≤ n - 1 + (3 - n) * z - S * (1 + z) + 4 * n * t := hbase
        _ ≤ 2 * n * z + 4 * n * t := by linarith only [hmid]
        _ ≤ 6 * n * t := h6
        _ ≤ 13 * k := h13
    have hfinal : H ≤ S + L + 13 * k := by
      nlinarith only [hbad]
    simpa only [L, k, mul_assoc] using hfinal

end Omega.InformationTheory.PottsFusion
