/- GID: D5/S1/Words/Mechanical/UnimodularApproximationBound
   generality: G
   mirror-B: none(waiver:open-problem-stage-a)
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Opposite errors of a unimodular pair bound every smaller denominator. -/
/-
Judgement form:
  unimodular_opposite_error_bound:
    proof_shape: content
    escape_witness: ∀ q,p,s,r,m,z : Int, ∀ alpha,d,e : Real, the stated positive
      unimodular/opposite-error hypotheses imply e ≤ |(m : Real)*alpha-z|
    Non-binding step: Creates a uniform arbitrary-integer signed-coordinate exclusion. The
      available continued-fraction results give approximation upper bounds or Legendre
      membership, not this conclusion.
    Direct frozen dependencies: none
  unimodular_gap_error_bound:
    proof_shape: content
    escape_witness: ∀ q,p,s,r,m,z : Int, ∀ alpha,d,e : Real, the stated unimodular gap hypotheses
      imply d+e ≤ |(m : Real)*alpha-z|
    Non-binding step: Creates a uniform arbitrary-integer coordinate classification with three
      excluded denominators. No direct upstream route was located.
    Direct frozen dependencies: none
admission_basis: escape-witness
Escape-audit registration is paused under CLAUDE.md §3.9.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
namespace D5.S1.Words.Mechanical
theorem unimodular_opposite_error_bound
    (q p s r m z : Int) (alpha d e : Real)
    (hq : 0 < q) (hs : 0 < s) (hm : 0 < m) (hmq : m < q)
    (hdet : q * r - p * s = 1)
    (hd : 0 < d) (he : 0 < e)
    (herrq : (q : Real) * alpha - p = d)
    (herrs : (s : Real) * alpha - r = -e) :
    e ≤ |(m : Real) * alpha - z| := by
  let a : Int := m * r - z * s
  let b : Int := z * q - m * p
  have hrepr : a * q + b * s = m := by
    dsimp [a, b]
    linear_combination m * hdet
  have hzrepr : a * p + b * r = z := by
    dsimp [a, b]
    linear_combination z * hdet
  have hreprR : (a : Real) * q + (b : Real) * s = m := by
    exact_mod_cast hrepr
  have hzreprR : (a : Real) * p + (b : Real) * r = z := by
    exact_mod_cast hzrepr
  have herr : (m : Real) * alpha - z = (a : Real) * d - (b : Real) * e := by
    calc
      (m : Real) * alpha - z =
          ((a : Real) * q + (b : Real) * s) * alpha -
            ((a : Real) * p + (b : Real) * r) := by rw [hreprR, hzreprR]
      _ = (a : Real) * ((q : Real) * alpha - p) +
          (b : Real) * ((s : Real) * alpha - r) := by ring
      _ = (a : Real) * d - (b : Real) * e := by rw [herrq, herrs]; ring
  rw [herr]
  have hqR : (0 : Real) < q := by exact_mod_cast hq
  have hsR : (0 : Real) < s := by exact_mod_cast hs
  have hmR : (0 : Real) < m := by exact_mod_cast hm
  by_cases ha : 0 < a
  · have ha1 : (1 : Real) ≤ a := by
      exact_mod_cast (show (1 : Int) ≤ a by omega)
    have hb : b < 0 := by
      by_contra hbn
      have hb0 : (0 : Real) ≤ b := by
        exact_mod_cast (show (0 : Int) ≤ b by omega)
      have hmqR : (m : Real) < q := by exact_mod_cast hmq
      have hqa : (q : Real) ≤ (a : Real) * q := by nlinarith
      have hbs : 0 ≤ (b : Real) * s := mul_nonneg hb0 hsR.le
      linarith
    have hb1 : (b : Real) ≤ -1 := by
      exact_mod_cast (show b ≤ (-1 : Int) by omega)
    have had : 0 ≤ (a : Real) * d := mul_nonneg (by linarith) hd.le
    have hbe : (b : Real) * e ≤ -e := by nlinarith
    have hpos : 0 ≤ (a : Real) * d - (b : Real) * e := by linarith
    rw [abs_of_nonneg hpos]
    linarith
  · have ha0 : (a : Real) ≤ 0 := by
      exact_mod_cast (show a ≤ (0 : Int) by omega)
    have hb : 0 < b := by
      by_contra hbn
      have hb0 : (b : Real) ≤ 0 := by
        exact_mod_cast (show b ≤ (0 : Int) by omega)
      have haq : (a : Real) * q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha0 hqR.le
      have hbs : (b : Real) * s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb0 hsR.le
      linarith
    have hb1 : (1 : Real) ≤ b := by
      exact_mod_cast (show (1 : Int) ≤ b by omega)
    have had : (a : Real) * d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha0 hd.le
    have hbe : e ≤ (b : Real) * e := by nlinarith
    have hneg : (a : Real) * d - (b : Real) * e ≤ 0 := by linarith
    rw [abs_of_nonpos hneg]
    linarith
#print axioms unimodular_opposite_error_bound
theorem unimodular_gap_error_bound
    (q p s r m z : Int) (alpha d e : Real)
    (hq : 0 < q) (hs : 0 < s) (hsq : s < q)
    (hm : q ≤ m) (hmq : m < 2 * q + s)
    (hne1 : m ≠ q) (hne2 : m ≠ 2 * q) (hnes : m ≠ q + s)
    (hdet : q * r - p * s = 1)
    (hd : 0 < d) (hed : 2 * d ≤ e)
    (herrq : (q : Real) * alpha - p = d)
    (herrs : (s : Real) * alpha - r = -e) :
    d + e ≤ |(m : Real) * alpha - z| := by
  let a : Int := m * r - z * s
  let b : Int := z * q - m * p
  have hrepr : a * q + b * s = m := by
    dsimp [a, b]
    linear_combination m * hdet
  have hzrepr : a * p + b * r = z := by
    dsimp [a, b]
    linear_combination z * hdet
  have hreprR : (a : Real) * q + (b : Real) * s = m := by exact_mod_cast hrepr
  have hzreprR : (a : Real) * p + (b : Real) * r = z := by exact_mod_cast hzrepr
  have herr : (m : Real) * alpha - z = (a : Real) * d - (b : Real) * e := by
    calc
      (m : Real) * alpha - z =
          ((a : Real) * q + (b : Real) * s) * alpha -
            ((a : Real) * p + (b : Real) * r) := by rw [hreprR, hzreprR]
      _ = (a : Real) * ((q : Real) * alpha - p) +
          (b : Real) * ((s : Real) * alpha - r) := by ring
      _ = (a : Real) * d - (b : Real) * e := by rw [herrq, herrs]; ring
  have hqR : (0 : Real) < q := by exact_mod_cast hq
  have hsR : (0 : Real) < s := by exact_mod_cast hs
  have hsqR : (s : Real) < q := by exact_mod_cast hsq
  have hmR : (q : Real) ≤ m := by exact_mod_cast hm
  have hmqR : (m : Real) < 2 * q + s := by exact_mod_cast hmq
  have he : 0 < e := by linarith
  rw [herr]
  by_cases hbneg : b < 0
  · have hbR : (b : Real) ≤ -1 := by exact_mod_cast (show b ≤ -1 by omega)
    have ha : 2 ≤ a := by
      by_contra ha
      have haR : (a : Real) ≤ 1 := by exact_mod_cast (show a ≤ 1 by omega)
      nlinarith [hreprR]
    have haR : (2 : Real) ≤ a := by exact_mod_cast ha
    have hbound : d + e ≤ (a : Real) * d - (b : Real) * e := by nlinarith
    exact hbound.trans (le_abs_self _)
  · by_cases hbhigh : 2 ≤ b
    · have hbR : (2 : Real) ≤ b := by exact_mod_cast hbhigh
      have ha : a ≤ 1 := by
        by_contra ha
        have haR : (2 : Real) ≤ a := by exact_mod_cast (show 2 ≤ a by omega)
        nlinarith [hreprR]
      have haR : (a : Real) ≤ 1 := by exact_mod_cast ha
      have hbound : d + e ≤ -((a : Real) * d - (b : Real) * e) := by nlinarith
      exact hbound.trans (neg_le_abs _)
    · have hb : b = 0 ∨ b = 1 := by omega
      rcases hb with hb | hb
      · have hbR : (b : Real) = 0 := by exact_mod_cast hb
        have ha : 1 ≤ a ∧ a ≤ 2 := by
          constructor
          · by_contra ha
            have haR : (a : Real) ≤ 0 := by exact_mod_cast (show a ≤ 0 by omega)
            nlinarith [hreprR]
          · by_contra ha
            have haR : (3 : Real) ≤ a := by exact_mod_cast (show 3 ≤ a by omega)
            nlinarith [hreprR]
        have hac : a = 1 ∨ a = 2 := by omega
        rcases hac with ha | ha
        · apply False.elim
          apply hne1
          simpa only [ha, hb, one_mul, zero_mul, add_zero] using hrepr.symm
        · apply False.elim
          apply hne2
          simpa only [ha, hb, zero_mul, add_zero] using hrepr.symm
      · have hbR : (b : Real) = 1 := by exact_mod_cast hb
        have ha : a = 1 := by
          have ha0 : 1 ≤ a := by
            by_contra ha
            have haR : (a : Real) ≤ 0 := by exact_mod_cast (show a ≤ 0 by omega)
            nlinarith [hreprR]
          have ha2 : a ≤ 1 := by
            by_contra ha
            have haR : (2 : Real) ≤ a := by exact_mod_cast (show 2 ≤ a by omega)
            nlinarith [hreprR]
          omega
        apply False.elim
        apply hnes
        simpa only [ha, hb, one_mul] using hrepr.symm
#print axioms unimodular_gap_error_bound
end D5.S1.Words.Mechanical
