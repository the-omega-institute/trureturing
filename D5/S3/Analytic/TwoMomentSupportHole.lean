/- GID: D5/S3/Analytic/TwoMomentSupportHole
   generality: G
   mirror-B: D5/B/S3/Analytic/TwoMomentSupportHole
   mirror-E: none(waiver:continuous-symbolic-support-extremum)
   anchors: []
   utility: none
   digest: Moving positive atoms give exact two-moment optima and an attained quadratic loss from a missing support interval. -/

import D5.S3.Analytic.GoldenTomography.FinitePronyHankelReconstruction
import Mathlib.Tactic

/-!
# Exact two-moment loss from a missing support interval

The feasible sets quantify over arbitrary finite positive laws, not over a
fixed grid. The designated atom is at 1; every residual atom is strictly below
1, so the designated weight is its actual total mass. The competitor may be
any finite probability law in [a,b].

Both maximizers are constructed. A square certifies the moving one-atom
residual. Excluding (l,r) changes the certificate to (X-l)(X-r) and the residual
to a positive two-point interpolation. The resulting loss is exact, including
both endpoints of the support interval.

General moment optimization and quadratic probability bounds are established
background: Bertsimas--Popescu, SIAM J. Optim. 15(3), 2005,
DOI 10.1137/S1052623401399903. The statement here compares two noisy-moment
model classes and constructs the matching support-exclusion penalty.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Analytic.TwoMomentSupportHole

open Set
open scoped BigOperators
open D5.S3.Analytic.GoldenTomography.FinitePronyHankelReconstruction

/-- Actual endpoint masses of finite probability pairs with first and second
raw moment discrepancies at most epsilon. Only the first law must avoid the
specified open support hole; the second law is unrestricted inside [a,b]. -/
def twoMomentMassSet (a b ε : ℝ) (hole : Set ℝ) : Set ℝ :=
  {w | 0 ≤ w ∧ ∃ (n m : ℕ) (z u : Fin n → ℝ) (y v : Fin m → ℝ),
    (∀ i, a ≤ z i ∧ z i < 1 ∧ z i ∉ hole) ∧
    (∀ j, a ≤ y j ∧ y j ≤ b) ∧
    (∀ i, 0 ≤ u i) ∧ (∀ j, 0 ≤ v j) ∧
    w + ∑ i, u i = 1 ∧ (∑ j, v j) = 1 ∧
    |w + pronyMoment z u 1 - pronyMoment y v 1| ≤ ε ∧
    |w + pronyMoment z u 2 - pronyMoment y v 2| ≤ ε}

/-- Exact unrestricted and support-hole maxima, with an explicit positive
construction and an exact loss identity. No optimizing law, polynomial
certificate, moment realization, or duality equality is assumed. -/
theorem two_moment_support_hole_sharp
    (a b l r t : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b < 1)
    (hal : a ≤ l) (hlr : l < r) (hrb : r ≤ b)
    (hlt : l ≤ t) (htr : t ≤ r)
    (hcenter : 2 * t ≤ a + b) (hsum : l + r ≤ a + b) :
    let ε := (1 - b) * (b - t) / (2 + t)
    let c := (1 - b) * (2 + b) / (2 + t)
    let wc := 1 - c / (1 - t)
    let wh := ((b - l) * (b - r) + ε * (1 + l + r)) / ((1 - l) * (1 - r))
    IsGreatest (twoMomentMassSet a b ε ∅) wc ∧
    IsGreatest (twoMomentMassSet a b ε (Ioo l r)) wh ∧
    wc - wh = (1 - wc) * (t - l) * (r - t) / ((1 - l) * (1 - r)) := by
  classical
  let ε := (1 - b) * (b - t) / (2 + t)
  let c := (1 - b) * (2 + b) / (2 + t)
  let wc := 1 - c / (1 - t)
  let wh := ((b - l) * (b - r) + ε * (1 + l + r)) / ((1 - l) * (1 - r))
  let ul := c * (r - t) / ((1 - l) * (r - l))
  let ur := c * (t - l) / ((1 - r) * (r - l))
  change IsGreatest (twoMomentMassSet a b ε ∅) wc ∧
    IsGreatest (twoMomentMassSet a b ε (Ioo l r)) wh ∧
    wc - wh = (1 - wc) * (t - l) * (r - t) / ((1 - l) * (1 - r))
  have hl0 : 0 ≤ l := ha.trans hal
  have ht0 : 0 ≤ t := hl0.trans hlt
  have hr0 : 0 ≤ r := hl0.trans hlr.le
  have hb0 : 0 ≤ b := ha.trans hab.le
  have ht_b : t ≤ b := htr.trans hrb
  have hl_b : l ≤ b := hlr.le.trans hrb
  have ht1 : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_lt ht_b hb)
  have hl1 : 0 < 1 - l := sub_pos.mpr (lt_of_le_of_lt hl_b hb)
  have hr1 : 0 < 1 - r := sub_pos.mpr (lt_of_le_of_lt hrb hb)
  have ht2 : 0 < 2 + t := by linarith
  have hrl : 0 < r - l := sub_pos.mpr hlr
  have nt := ne_of_gt ht1
  have nl := ne_of_gt hl1
  have nr := ne_of_gt hr1
  have nd := ne_of_gt ht2
  have nrl := ne_of_gt hrl
  have hε : 0 ≤ ε :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hb.le) (sub_nonneg.mpr ht_b)) ht2.le
  have hc : 0 < c := div_pos (mul_pos (sub_pos.mpr hb) (by linarith)) ht2
  have hwc_formula : wc = (b - t) * (1 + b + t) / ((1 - t) * (2 + t)) := by
    dsimp [wc, c]
    field_simp [nt, nd] <;> ring
  have hwc0 : 0 ≤ wc := by
    rw [hwc_formula]
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr ht_b) (by linarith)) (mul_pos ht1 ht2).le
  have hwc_res : 0 ≤ 1 - wc := by
    dsimp [wc]
    have := (div_pos hc ht1).le
    linarith
  have hwh0 : 0 ≤ wh := by
    dsimp [wh]
    apply div_nonneg
    · exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr hl_b) (sub_nonneg.mpr hrb))
        (mul_nonneg hε (by linarith))
    · exact (mul_pos hl1 hr1).le
  have hul : 0 ≤ ul := div_nonneg
    (mul_nonneg hc.le (sub_nonneg.mpr htr)) (mul_pos hl1 hrl).le
  have hur : 0 ≤ ur := div_nonneg
    (mul_nonneg hc.le (sub_nonneg.mpr hlt)) (mul_pos hr1 hrl).le
  have hc_first : wc + (1 - wc) * t - b = -ε := by
    dsimp [wc, c, ε]
    field_simp [nt, nd] <;> ring
  have hc_second : wc + (1 - wc) * t ^ 2 - b ^ 2 = ε := by
    dsimp [wc, c, ε]
    field_simp [nt, nd] <;> ring
  have hh_total : wh + ul + ur = 1 := by
    dsimp [wh, ul, ur, c, ε]
    field_simp [nl, nr, nd, nrl] <;> ring
  have hh_first : wh + ul * l + ur * r - b = -ε := by
    dsimp [wh, ul, ur, c, ε]
    field_simp [nl, nr, nd, nrl] <;> ring
  have hh_second : wh + ul * l ^ 2 + ur * r ^ 2 - b ^ 2 = ε := by
    dsimp [wh, ul, ur, c, ε]
    field_simp [nl, nr, nd, nrl] <;> ring
  have hc_contact : wc * (1 - 2 * t + t ^ 2) =
      (b - t) ^ 2 + ε * (1 + 2 * t) := by
    dsimp [wc, c, ε]
    field_simp [nt, nd] <;> ring
  have hh_contact : wh * (1 - (l + r) + l * r) =
      (b - l) * (b - r) + ε * (1 + (l + r)) := by
    dsimp [wh]
    field_simp [nl, nr] <;> ring
  have hc_mass : wc ∈ twoMomentMassSet a b ε ∅ := by
    refine ⟨hwc0, 1, 1, (fun _ => t), (fun _ => 1 - wc),
      (fun _ => b), (fun _ => 1), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact ⟨hal.trans hlt, by linarith, by simp⟩
    · intro j
      exact ⟨hab.le, le_rfl⟩
    · exact fun _ => hwc_res
    · exact fun _ => by norm_num
    · simp
    · simp
    · simpa [pronyMoment] using
        (show |wc + (1 - wc) * t - b| ≤ ε by
          rw [hc_first, abs_neg, abs_of_nonneg hε])
    · simpa [pronyMoment] using
        (show |wc + (1 - wc) * t ^ 2 - b ^ 2| ≤ ε by
          rw [hc_second, abs_of_nonneg hε])
  have hh_mass : wh ∈ twoMomentMassSet a b ε (Ioo l r) := by
    refine ⟨hwh0, 2, 1, ![l, r], ![ul, ur],
      (fun _ => b), (fun _ => 1), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact ⟨hal, by linarith, by simp⟩
      · exact ⟨hal.trans hlr.le, by linarith, by simp⟩
    · intro j
      exact ⟨hab.le, le_rfl⟩
    · intro i
      fin_cases i
      · exact hul
      · exact hur
    · exact fun _ => by norm_num
    · simpa [Fin.sum_univ_two, add_assoc] using hh_total
    · simp
    · simpa [pronyMoment, Fin.sum_univ_two, add_assoc] using
        (show |wh + ul * l + ur * r - b| ≤ ε by
          rw [hh_first, abs_neg, abs_of_nonneg hε])
    · simpa [pronyMoment, Fin.sum_univ_two, add_assoc] using
        (show |wh + ul * l ^ 2 + ur * r ^ 2 - b ^ 2| ≤ ε by
          rw [hh_second, abs_of_nonneg hε])
  -- The two universal comparisons use the actual moment errors. The local
  -- calculation is kept inside the constructive extremum theorem.
  have budget (hole : Set ℝ) (w : ℝ) (hw : w ∈ twoMomentMassSet a b ε hole)
      (s p B : ℝ) (hs : 0 ≤ s)
      (hpos : ∀ z : ℝ, a ≤ z → z < 1 → z ∉ hole → 0 ≤ z ^ 2 - s * z + p)
      (hbound : ∀ y : ℝ, a ≤ y → y ≤ b → y ^ 2 - s * y + p ≤ B) :
      w * (1 - s + p) ≤ B + ε * (1 + s) := by
    rcases hw with ⟨_, n, m, z, u, y, v, hz, hy, hu, hv, hmu, hnu, hnoise1, hnoise2⟩
    have expand {k : ℕ} (q h : Fin k → ℝ) :
        (∑ i, h i * (q i ^ 2 - s * q i + p)) =
          pronyMoment q h 2 - s * pronyMoment q h 1 + p * ∑ i, h i := by
      calc
        _ = ∑ i, (h i * q i ^ 2 - s * (h i * q i) + p * h i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by
          simp only [pronyMoment, pow_one, Finset.sum_add_distrib,
            Finset.sum_sub_distrib, Finset.mul_sum]
    have hzq : 0 ≤ ∑ i, u i * (z i ^ 2 - s * z i + p) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hu i)
        (hpos (z i) (hz i).1 (hz i).2.1 (hz i).2.2)
    have hyq : (∑ j, v j * (y j ^ 2 - s * y j + p)) ≤ B := by
      calc
        _ ≤ ∑ j, v j * B := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hbound (y j) (hy j).1 (hy j).2) (hv j)
        _ = B := by rw [← Finset.sum_mul, hnu, one_mul]
    have htotal : (∑ i, u i) = 1 - w := by linarith
    have hid : w * (1 - s + p) + (∑ i, u i * (z i ^ 2 - s * z i + p)) -
        (∑ j, v j * (y j ^ 2 - s * y j + p)) =
        (w + pronyMoment z u 2 - pronyMoment y v 2) -
          s * (w + pronyMoment z u 1 - pronyMoment y v 1) := by
      rw [expand, expand, htotal, hnu]
      ring
    have he1 := mul_le_mul_of_nonneg_left (abs_le.mp hnoise1).1 hs
    have he2 := (abs_le.mp hnoise2).2
    nlinarith
  have hc_upper (w : ℝ) (hw : w ∈ twoMomentMassSet a b ε ∅) : w ≤ wc := by
    have h := budget ∅ w hw (2 * t) (t ^ 2) ((b - t) ^ 2) (by positivity)
      (fun z _ _ _ => by nlinarith [sq_nonneg (z - t)])
      (fun y hya hyb => by
        have hprod := mul_nonneg (sub_nonneg.mpr hyb)
          (show 0 ≤ b + y - 2 * t by linarith)
        nlinarith)
    have hcoef : 0 < 1 - 2 * t + t ^ 2 := by nlinarith [mul_pos ht1 ht1]
    apply (mul_le_mul_right hcoef).mp
    linarith [hc_contact]
  have hh_upper (w : ℝ) (hw : w ∈ twoMomentMassSet a b ε (Ioo l r)) : w ≤ wh := by
    have h := budget (Ioo l r) w hw (l + r) (l * r) ((b - l) * (b - r)) (by linarith)
      (fun z _ _ hz => by
        have hcases : z ≤ l ∨ r ≤ z := by
          by_cases hzl : z ≤ l
          · exact Or.inl hzl
          · exact Or.inr (le_of_not_gt (fun hzr => hz ⟨lt_of_not_ge hzl, hzr⟩))
        rcases hcases with hzl | hrz
        · have hp := mul_nonneg_of_nonpos_of_nonpos
            (sub_nonpos.mpr hzl) (show z - r ≤ 0 by linarith)
          nlinarith
        · have hp := mul_nonneg (show 0 ≤ z - l by linarith) (sub_nonneg.mpr hrz)
          nlinarith)
      (fun y hya hyb => by
        have hp := mul_nonneg (sub_nonneg.mpr hyb)
          (show 0 ≤ b + y - (l + r) by linarith)
        nlinarith)
    have hcoef : 0 < 1 - (l + r) + l * r := by nlinarith [mul_pos hl1 hr1]
    apply (mul_le_mul_right hcoef).mp
    linarith [hh_contact]
  refine ⟨⟨hc_mass, hc_upper⟩, ⟨hh_mass, hh_upper⟩, ?_⟩
  dsimp [wc, wh, c, ε]
  field_simp [nt, nl, nr, nd] <;> ring

#print axioms twoMomentMassSet
#print axioms two_moment_support_hole_sharp

end D5.S3.Analytic.TwoMomentSupportHole
