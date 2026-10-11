/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorReferenceScalar
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorReferenceScalar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The isolated PH17 scalar has positive error below one ten-thousandth. -/

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorReferenceScalar

def c : ℝ := 11758471/22781250
def d0 : ℝ := 5261/6750
def completionC : ℝ := 1944/390625
def n0 : ℝ := 295378951/284765625
def s (a : ℝ) : ℝ := 1+a+a^2
def h (a : ℝ) : ℝ := 2*s a+a^3
def e (a : ℝ) : ℝ := (c*a^3-completionC*s a)/h a
def f (a : ℝ) : ℝ := n0*(1+a)/(a*h a+n0)-d0
def lower : ℝ := 2333613/10000000
def upper : ℝ := 2333615/10000000

/-- Primitive integer polynomial of the exact source intersection. -/
def rootPolynomial (a : ℝ) : ℝ :=
  37528353857303001 - 46250119027071999*a - 298256135098165749*a^2 -
  612650690444841200*a^3 - 756018048213281250*a^4 -
  588125803735546875*a^5 - 336119787664453125*a^6 -
  105058389814453125*a^7

private theorem polynomial_strict (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    rootPolynomial b < rootPolynomial a := by
  have h2 := pow_le_pow_left₀ ha hab.le 2
  have h3 := pow_le_pow_left₀ ha hab.le 3
  have h4 := pow_le_pow_left₀ ha hab.le 4
  have h5 := pow_le_pow_left₀ ha hab.le 5
  have h6 := pow_le_pow_left₀ ha hab.le 6
  have h7 := pow_le_pow_left₀ ha hab.le 7
  dsimp [rootPolynomial]
  nlinarith only [hab,h2,h3,h4,h5,h6,h7]

private theorem isolated_exists : ∃ a : ℝ,
    lower < a ∧ a < upper ∧ rootPolynomial a = 0 := by
  have hc : Continuous rootPolynomial := by unfold rootPolynomial; fun_prop
  have hp : 0 < rootPolynomial lower := by norm_num [rootPolynomial,lower]
  have hn : rootPolynomial upper < 0 := by norm_num [rootPolynomial,upper]
  obtain ⟨a,ha,he⟩ := intermediate_value_Icc' (by norm_num [lower,upper]) hc.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (rootPolynomial upper) (rootPolynomial lower) from ⟨hn.le,hp.le⟩)
  refine ⟨a,lt_of_le_of_ne ha.1 ?_,lt_of_le_of_ne ha.2 ?_,he⟩
  · intro hl; rw [hl,he] at hp; exact (lt_irrefl _ hp)
  · intro hu; rw [← hu,he] at hn; exact (lt_irrefl _ hn)

def aStar : ℝ := Classical.choose isolated_exists
def tStar : ℝ := e aStar

private theorem scalar_interval (a : ℝ) (ha : lower < a) (hb : a < upper) :
    0 < e a ∧ e a < 1/10000 := by
  have hl0 : 0 ≤ lower := by norm_num [lower]
  have ha0 : 0 ≤ a := hl0.trans ha.le
  have h2l := pow_le_pow_left₀ hl0 ha.le 2
  have h2u := pow_le_pow_left₀ ha0 hb.le 2
  have h3l := pow_le_pow_left₀ hl0 ha.le 3
  have h3u := pow_le_pow_left₀ ha0 hb.le 3
  have hs0 : 0 < s a := by dsimp [s]; positivity
  have hh : 2 ≤ h a := by dsimp [h,s]; nlinarith only [ha0, sq_nonneg a, pow_nonneg ha0 3]
  have hh0 : 0 < h a := by linarith
  have hnum0 : 0 < c*a^3-completionC*s a := by
    have hcert : 0 < c*lower^3-completionC*s upper := by norm_num [c,completionC,s,lower,upper]
    dsimp [s] at hcert ⊢
    norm_num [lower,upper,c,completionC] at h2l h2u h3l h3u ⊢
    nlinarith only [ha.le,hb.le,h3l,h2u,hcert]
  have hnumu : c*a^3-completionC*s a < (1/10000)*h a := by
    have hcert : c*upper^3-completionC*s lower < (1/10000 : ℝ)*2 := by
      norm_num [c,completionC,s,lower,upper]
    have hbound : c*a^3-completionC*s a ≤ c*upper^3-completionC*s lower := by
      dsimp [s]
      norm_num [c,completionC,lower,upper] at h2l h3u ⊢
      nlinarith only [ha.le,h3u,h2l]
    nlinarith only [hcert,hbound,hh]
  exact ⟨div_pos hnum0 hh0,(div_lt_iff₀ hh0).mpr hnumu⟩

/-- Exact root identity, uniqueness on the positive line, and the needed scalar
    bounds. No minimax or irrationality assertion is part of this statement. -/
theorem exact_reference_scalar :
    lower < aStar ∧ aStar < upper ∧ rootPolynomial aStar = 0 ∧
    (∀ a : ℝ, 0 ≤ a → rootPolynomial a = 0 → a = aStar) ∧
    e aStar = f aStar ∧ 0 < tStar ∧ tStar < 1/10000 := by
  obtain ⟨hl,hu,hp⟩ := Classical.choose_spec isolated_exists
  change lower < aStar at hl
  change aStar < upper at hu
  change rootPolynomial aStar = 0 at hp
  have ha0 : 0 ≤ aStar := (by norm_num [lower] : (0 : ℝ) ≤ lower).trans hl.le
  refine ⟨hl,hu,hp,?_,?_,(scalar_interval _ hl hu).1,(scalar_interval _ hl hu).2⟩
  · intro a ha he
    rcases lt_trichotomy a aStar with hlt | heq | hgt
    · have ht := polynomial_strict a aStar ha hlt
      rw [he,hp] at ht
      exact (lt_irrefl _ ht).elim
    · exact heq
    · have ht := polynomial_strict aStar a ha0 hgt
      rw [he,hp] at ht
      exact (lt_irrefl _ ht).elim
  · have hh0 : 0 < h aStar := by dsimp [h,s]; positivity
    have hden : 0 < aStar*h aStar+n0 := by unfold n0; positivity
    have hpoly :
        n0*(1+aStar)*h aStar-(aStar*h aStar+n0)*
          ((2*d0-completionC)*s aStar+(d0+c)*aStar^3) = 0 := by
      have hid (a : ℝ) :
          n0*(1+a)*h a-(a*h a+n0)*
            ((2*d0-completionC)*s a+(d0+c)*a^3) =
              rootPolynomial a/81091461181640625 := by
        unfold n0 h s d0 completionC c rootPolynomial
        ring
      rw [hid,hp]
      norm_num
    unfold e f
    apply (div_eq_iff (ne_of_gt hh0)).mpr
    field_simp
    unfold h s at hpoly ⊢
    nlinarith only [hpoly]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorReferenceScalar
