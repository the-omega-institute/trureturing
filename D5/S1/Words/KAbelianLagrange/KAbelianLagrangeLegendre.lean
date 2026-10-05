/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeLegendre
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeLegendre
   mirror-E: none(waiver:asymptotic-legendre-supplier)
   anchors: [mathlib/module/Mathlib.Topology.Instances.ENNReal.Lemmas]
   utility: none
   digest: Reduced convergents control both directions of the approximation limsup. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangePrefix
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

open Filter
open scoped ENNReal

/-- Above the Legendre cutoff, the all-denominator approximation limsup is bounded by
the reduced-convergent limsup. Unreduced fractions are allowed: reduction improves the
coefficient, and a finite-prefix exclusion construction forces the convergent indices
to escape every fixed bound as the original denominators grow. -/
theorem lagrange_limsup_upper (x : ℝ) (hx : Irrational x) :
    limsup (fun q : ℕ => ENNReal.ofReal
      (1 / ((q : ℝ) * |(q : ℝ) * x - (round ((q : ℝ) * x) : ℝ)|))) atTop ≤
      max 2 (limsup (fun n : ℕ => ENNReal.ofReal
        (1 / (((x.convergent n).den : ℝ) ^ 2 * |x - (x.convergent n : ℝ)|)))
          atTop) := by
  classical
  have hreduce (c : ℝ) (hc : 2 < c) (N : ℕ) :
      ∀ᶠ q : ℕ in atTop, ∀ p : ℤ,
        c < 1 / ((q : ℝ) * |(q : ℝ) * x - (p : ℝ)|) →
          ∃ n ≥ N, (x.convergent n : ℝ) = (p : ℝ) / (q : ℝ) ∧
            1 / ((q : ℝ) * |(q : ℝ) * x - (p : ℝ)|) ≤
              1 / (((x.convergent n).den : ℝ) ^ 2 *
                |x - (x.convergent n : ℝ)|) := by
    have hcpos : 0 < c := by linarith
    have havoid : ∀ L : ℕ, ∀ᶠ q : ℕ in atTop,
        ∀ n < L, 1 / (c * (q : ℝ) ^ 2) < |x - (x.convergent n : ℝ)| := by
      intro L
      induction L with
      | zero => exact Eventually.of_forall (by intro q n hn; omega)
      | succ L ih =>
          have hd : 0 < |x - (x.convergent L : ℝ)| :=
            abs_pos.mpr (sub_ne_zero.mpr (hx.ne_rat _))
          obtain ⟨K, hK⟩ := exists_nat_gt (max 1 (1 / (c *
            |x - (x.convergent L : ℝ)|)))
          have hlate : ∀ᶠ q : ℕ in atTop,
              1 / (c * (q : ℝ) ^ 2) < |x - (x.convergent L : ℝ)| := by
            refine eventually_atTop.2 ⟨K, ?_⟩
            intro q hq
            have hqK : (K : ℝ) ≤ q := by exact_mod_cast hq
            have hqone : 1 < (q : ℝ) := lt_of_lt_of_le
              (lt_of_le_of_lt (le_max_left _ _) hK) hqK
            have hqdiv : 1 / (c * |x - (x.convergent L : ℝ)|) < (q : ℝ) :=
              lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hK) hqK
            have hprod := (div_lt_iff₀ (mul_pos hcpos hd)).mp hqdiv
            apply (div_lt_iff₀ (mul_pos hcpos (sq_pos_of_pos (by linarith)))).mpr
            have hsq : (q : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
            nlinarith [mul_le_mul_of_nonneg_left hsq (mul_pos hcpos hd).le]
          filter_upwards [ih, hlate] with q hq hlast
          intro n hn
          by_cases hnl : n < L
          · exact hq n hnl
          · have : n = L := by omega
            simpa [this] using hlast
    filter_upwards [havoid N, eventually_ge_atTop 1] with q havoidq hq
    intro p hcoeff
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq
    let r : ℚ := (p : ℚ) / (q : ℚ)
    have hr : (r : ℝ) = (p : ℝ) / (q : ℝ) := by simp [r]
    have hd : 0 < |x - (r : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr (hx.ne_rat r))
    have he : |(q : ℝ) * x - (p : ℝ)| = (q : ℝ) * |x - (r : ℝ)| := by
      rw [hr]
      have hmul : (q : ℝ) * x - (p : ℝ) =
          (q : ℝ) * (x - (p : ℝ) / (q : ℝ)) := by field_simp
      rw [hmul, abs_mul, abs_of_pos hqpos]
    have hcoeff' : c < 1 / ((q : ℝ) ^ 2 * |x - (r : ℝ)|) := by
      simpa only [he, pow_two, mul_assoc] using hcoeff
    have hsmall : |x - (r : ℝ)| < 1 / (c * (q : ℝ) ^ 2) := by
      have hh := (lt_div_iff₀ (mul_pos (sq_pos_of_pos hqpos) hd)).mp hcoeff'
      apply (lt_div_iff₀ (mul_pos hcpos (sq_pos_of_pos hqpos))).mpr
      nlinarith
    have hrden : 0 < (r.den : ℝ) := by exact_mod_cast r.pos
    obtain ⟨d, _hp, hqd⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den p
      (by exact_mod_cast (ne_of_gt hqpos) : (q : ℤ) ≠ 0)
    have hqdint : (q : ℤ) = d * (r.den : ℤ) := by
      simpa only [Int.cast_natCast] using hqd
    have hqd' : (q : ℝ) = (d : ℝ) * (r.den : ℝ) := by
      exact_mod_cast hqdint
    have hdpos : 0 < (d : ℝ) := by nlinarith
    have hdone : (1 : ℝ) ≤ d := by
      exact_mod_cast (show (1 : ℤ) ≤ d by exact_mod_cast hdpos)
    have hdenle : (r.den : ℝ) ≤ q := by nlinarith
    have hsmall' : |x - (r : ℝ)| < 1 / (2 * (r.den : ℝ) ^ 2) := by
      refine lt_trans hsmall ?_
      apply one_div_lt_one_div_of_lt (by positivity)
      have hsq : (r.den : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 :=
        (sq_le_sq₀ hrden.le hqpos.le).mpr hdenle
      have hstrict := mul_lt_mul_of_pos_right hc (sq_pos_of_pos hqpos)
      nlinarith
    obtain ⟨n, hn⟩ := Real.exists_convs_eq_rat hsmall'
    have hn' : x.convergent n = r := by
      apply Rat.cast_injective (α := ℝ)
      simpa only [Real.convs_eq_convergent] using hn
    have hnN : N ≤ n := by
      by_contra hnot
      have hh := havoidq n (by omega)
      rw [hn'] at hh
      linarith
    refine ⟨n, hnN, by simpa only [hn'] using hr, ?_⟩
    rw [he, hn']
    apply one_div_le_one_div_of_le (mul_pos (sq_pos_of_pos hrden) hd)
    have hsq : (r.den : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 :=
      (sq_le_sq₀ hrden.le hqpos.le).mpr hdenle
    nlinarith [mul_le_mul_of_nonneg_right hsq hd.le]
  let u (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal
    (1 / (((x.convergent n).den : ℝ) ^ 2 * |x - (x.convergent n : ℝ)|))
  let v (q : ℕ) : ℝ≥0∞ := ENNReal.ofReal
    (1 / ((q : ℝ) * |(q : ℝ) * x - (round ((q : ℝ) * x) : ℝ)|))
  change limsup v atTop ≤ max 2 (limsup u atTop)
  apply (limsup_le_iff).2
  intro b hb
  obtain ⟨a, ha, hab⟩ := exists_between hb
  have ha2 : (2 : ℝ≥0∞) < a := lt_of_le_of_lt (le_max_left _ _) ha
  have hautop : a ≠ ⊤ := ne_top_of_lt hab
  have hac : ENNReal.ofReal a.toReal = a := ENNReal.ofReal_toReal hautop
  have hc : 2 < a.toReal := by
    rw [← hac] at ha2
    exact ENNReal.ofNat_lt_ofReal.mp ha2
  have hupper : limsup u atTop < a := lt_of_le_of_lt (le_max_right _ _) ha
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt hupper)
  filter_upwards [hreduce a.toReal hc N] with q hq
  by_cases hqa : v q ≤ a
  · exact lt_of_le_of_lt hqa hab
  · have hqa' : a.toReal <
        1 / ((q : ℝ) * |(q : ℝ) * x - (round ((q : ℝ) * x) : ℝ)|) := by
      have hh : ENNReal.ofReal a.toReal < v q := by rw [hac]; exact lt_of_not_ge hqa
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)).mp hh
    obtain ⟨n, hn, _he, hbound⟩ := hq (round ((q : ℝ) * x)) hqa'
    have hle : v q ≤ u n := ENNReal.ofReal_le_ofReal hbound
    exact lt_trans (lt_of_le_of_lt hle (hN n hn)) hab

/-- Reduced convergent denominators escape every finite bound. To prove this without
assuming reducedness of continuant coordinates, construct a positive distance from
`x` to all rationals with bounded denominator, using the nearest integer for each
denominator. Convergence then forces denominator escape, and rounding improves each
convergent's approximation coefficient. -/
theorem lagrange_limsup_lower (x : ℝ) (hx : Irrational x) :
    limsup (fun n : ℕ => ENNReal.ofReal
      (1 / (((x.convergent n).den : ℝ) ^ 2 * |x - (x.convergent n : ℝ)|))) atTop ≤
      limsup (fun q : ℕ => ENNReal.ofReal
        (1 / ((q : ℝ) * |(q : ℝ) * x - (round ((q : ℝ) * x) : ℝ)|))) atTop := by
  have hseparate : ∀ D : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ r : ℚ, r.den ≤ D → ε ≤ |x - (r : ℝ)| := by
    intro D
    induction D with
    | zero =>
        refine ⟨1, zero_lt_one, ?_⟩
        intro r hr
        have := r.pos
        omega
    | succ D ih =>
        obtain ⟨ε, hε, hεr⟩ := ih
        have hd : 0 < ((D + 1 : ℕ) : ℝ) := by positivity
        have hi : Irrational (((D + 1 : ℕ) : ℝ) * x) :=
          irrational_natCast_mul_iff.mpr ⟨by omega, hx⟩
        let η : ℝ := |((D + 1 : ℕ) : ℝ) * x -
          (round (((D + 1 : ℕ) : ℝ) * x) : ℝ)| / ((D + 1 : ℕ) : ℝ)
        have hη : 0 < η := div_pos (abs_pos.mpr (sub_ne_zero.mpr (hi.ne_int _))) hd
        refine ⟨min ε η, lt_min hε hη, ?_⟩
        intro r hr
        by_cases hprev : r.den ≤ D
        · exact le_trans (min_le_left _ _) (hεr r hprev)
        · have hrD : r.den = D + 1 := by omega
          have he : ((D + 1 : ℕ) : ℝ) * |x - (r : ℝ)| =
              |((D + 1 : ℕ) : ℝ) * x - (r.num : ℝ)| := by
            have he0 : ((D + 1 : ℕ) : ℝ) * x - (r.num : ℝ) =
                ((D + 1 : ℕ) : ℝ) * (x - (r : ℝ)) := by
              rw [Rat.cast_def, hrD]
              field_simp
            rw [he0, abs_mul, abs_of_pos hd]
          refine le_trans (min_le_right _ _) ?_
          apply (div_le_iff₀ hd).mpr
          calc
            _ ≤ |((D + 1 : ℕ) : ℝ) * x - (r.num : ℝ)| := round_le _ r.num
            _ = ((D + 1 : ℕ) : ℝ) * |x - (r : ℝ)| := he.symm
            _ = _ := mul_comm _ _
  have hden : Tendsto (fun n => (x.convergent n).den) atTop atTop := by
    apply tendsto_atTop.mpr
    intro D
    obtain ⟨ε, hε, hεr⟩ := hseparate D
    obtain ⟨N, hN⟩ := GenContFract.of_convergence_epsilon x ε hε
    refine eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have hsmall : |x - (x.convergent n : ℝ)| < ε := by
      simpa only [Real.convs_eq_convergent] using hN n hn
    have hlarge : D < (x.convergent n).den := by
      by_contra hnot
      exact not_lt_of_ge (hεr _ (by omega)) hsmall
    exact hlarge.le
  let u (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal
    (1 / (((x.convergent n).den : ℝ) ^ 2 * |x - (x.convergent n : ℝ)|))
  let v (q : ℕ) : ℝ≥0∞ := ENNReal.ofReal
    (1 / ((q : ℝ) * |(q : ℝ) * x - (round ((q : ℝ) * x) : ℝ)|))
  have hpoint : ∀ n : ℕ, u n ≤ v (x.convergent n).den := by
    intro n
    let r := x.convergent n
    have hd : 0 < (r.den : ℝ) := by exact_mod_cast r.pos
    have hi : Irrational ((r.den : ℝ) * x) :=
      irrational_natCast_mul_iff.mpr ⟨Nat.ne_of_gt r.pos, hx⟩
    have hnear : 0 < |(r.den : ℝ) * x - (round ((r.den : ℝ) * x) : ℝ)| :=
      abs_pos.mpr (sub_ne_zero.mpr (hi.ne_int _))
    have he : |(r.den : ℝ) * x - (r.num : ℝ)| = (r.den : ℝ) * |x - (r : ℝ)| := by
      have he0 : (r.den : ℝ) * x - (r.num : ℝ) =
          (r.den : ℝ) * (x - (r : ℝ)) := by
        rw [Rat.cast_def]
        field_simp
      rw [he0, abs_mul, abs_of_pos hd]
    apply ENNReal.ofReal_le_ofReal
    apply one_div_le_one_div_of_le (mul_pos hd hnear)
    have hround := round_le ((r.den : ℝ) * x) r.num
    rw [he] at hround
    have hm := mul_le_mul_of_nonneg_left hround hd.le
    simpa only [u, v, r, pow_two, mul_assoc] using hm
  change limsup u atTop ≤ limsup v atTop
  exact le_trans (limsup_le_limsup (Eventually.of_forall hpoint))
    (hden.limsup_comp_le_limsup (u := v))

end D5.S1.Words.KAbelianLagrange
