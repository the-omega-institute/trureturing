/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportRepeatedCubicIntervals
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportRepeatedCubicIntervals
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full repeated cubic unit intervals and the unbounded fourth-index tail. -/

import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportRepeatedBlocks
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! Original unbounded cubic interval, the complete boundary family and
fourth-index inequality. The finite lower index arithmetic remains separate. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportRepeatedCubicIntervals

open SixSupportRepeatedBlocks
open SixSupportIdealIntersectionLift (exponents)
open IdealIntersectionSupport IdealIntersectionObstructions

/-- The original exact rational cutoff for the symmetric cubic. -/
def cutoff (a : ℝ) : ℝ := (a^3+2*a^2+2*a+1)/(a*(2*a+1))

private theorem strict_root {f : ℝ → ℝ} (l u : ℝ) (hlu : l < u)
    (hf : Continuous f) (hl : f l < 0) (hu : 0 < f u) :
    ∃ x, l < x ∧ x < u ∧ f x = 0 := by
  obtain ⟨x,hx,hfx⟩ := intermediate_value_Icc hlu.le hf.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (f l) (f u) from ⟨hl.le,hu.le⟩)
  refine ⟨x,?_,?_,hfx⟩
  · have hn : l ≠ x := by intro heq; rw [← heq] at hfx; linarith
    exact lt_of_le_of_ne hx.1 hn
  · have hn : x ≠ u := by intro heq; rw [heq] at hfx; linarith
    exact lt_of_le_of_ne hx.2 hn

/-- Every real a,b≥1 below the original exact cutoff has a cubic root
strictly between the original consecutive-integer expressions. -/
theorem result (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hcut : b < cutoff a) :
    ∃ r : ℝ, 2*a*b-1 < r ∧ r < 2*a*b ∧ cubic a b r = 0 := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hden : 0 < a*(2*a+1) := by positivity
  have hcut' : a*(2*a+1)*b < a^3+2*a^2+2*a+1 := by
    have hh := (lt_div_iff₀ hden).mp hcut
    nlinarith only [hh]
  have hl : cubic a b (2*a*b-1) < 0 := by
    have heq : cubic a b (2*a*b-1) =
        -(a+b+1)*(a^3+2*a^2+2*a+1-a*(2*a+1)*b) := by dsimp [cubic]; ring
    rw [heq]
    exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
  have hu : 0 < cubic a b (2*a*b) := by
    have heq : cubic a b (2*a*b) = 2*a^2*b^2 := by dsimp [cubic]; ring
    rw [heq]
    positivity
  exact strict_root (2*a*b-1) (2*a*b) (by linarith) (by unfold cubic; fun_prop) hl hu

/-- The exact boundary cutoff C=(a-1)(2a-1), for every real a≥3. -/
theorem boundary_interval (a : ℝ) (ha : 3 ≤ a) :
    ∃ r : ℝ, 2*a^3-2*a^2+2*a-2 < r ∧ r < 2*a^3-2*a^2+2*a-1 ∧
      cubic a ((a-1)*(2*a-1)) r = 0 := by
  have hm : 0 ≤ a-3 := by linarith
  have ha1 : 0 < a-1 := by linarith
  have ha2 : 0 < a+2 := by linarith
  have hP : 0 < 5*a^4-10*a^3+7*a^2-1 := by
    have heq : 5*a^4-10*a^3+7*a^2-1 =
      5*(a-3)^4+50*(a-3)^3+187*(a-3)^2+312*(a-3)+197 := by ring
    rw [heq]; positivity
  have hQ : 0 < 2*a^4-7*a^3+7*a^2-a-3 := by
    have heq : 2*a^4-7*a^3+7*a^2-a-3 =
      2*(a-3)^4+17*(a-3)^3+52*(a-3)^2+68*(a-3)+30 := by ring
    rw [heq]; positivity
  have hl : cubic a ((a-1)*(2*a-1)) (2*a^3-2*a^2+2*a-2) < 0 := by
    have heq : cubic a ((a-1)*(2*a-1)) (2*a^3-2*a^2+2*a-2) =
      -2*(a-1)*(a+2)*(2*a^4-7*a^3+7*a^2-a-3) := by dsimp [cubic]; ring
    rw [heq]
    have : 0 < 2*(a-1)*(a+2)*(2*a^4-7*a^3+7*a^2-a-3) := by positivity
    nlinarith
  have hu : 0 < cubic a ((a-1)*(2*a-1)) (2*a^3-2*a^2+2*a-1) := by
    have heq : cubic a ((a-1)*(2*a-1)) (2*a^3-2*a^2+2*a-1) =
      2*(5*a^4-10*a^3+7*a^2-1) := by dsimp [cubic]; ring
    rw [heq]; positivity
  exact strict_root _ _ (by linarith) (by unfold cubic; fun_prop) hl hu

/-- A direct real interval also supplies a noninteger root at that boundary. -/
theorem boundary_two_interval : ∃ r : ℝ, 15 < r ∧ r < 16 ∧ cubic 2 3 r = 0 := by
  obtain ⟨r,hrl,hru,hr⟩ := strict_root (f := fun x : ℝ => -cubic 2 3 x) 15 16
    (by norm_num) (by unfold cubic; fun_prop) (by norm_num [cubic]) (by norm_num [cubic])
  exact ⟨r,hrl,hru,by linarith⟩

/-- The original fourth-index rational upper bound. -/
def fourthBound (a : ℝ) : ℝ := (a-5)*(2*a-5)/(4*a+5)

/-- The entire real fourth-index bound lies below the uniform cubic cutoff. -/
theorem fourth_bound_lt_cutoff (a : ℝ) (ha : 2 ≤ a) : fourthBound a < cutoff a := by
  have ha0 : 0 < a := by linarith
  have h1 : 0 < 2*a+1 := by linarith
  have h2 : 0 < 4*a+5 := by linarith
  have hm : 0 ≤ a-2 := by linarith
  have hP : 0 < 41*a^3-17*a^2-11*a+5 := by
    have heq : 41*a^3-17*a^2-11*a+5 =
      41*(a-2)^3+229*(a-2)^2+413*(a-2)+243 := by ring
    rw [heq]; positivity
  have heq : cutoff a-fourthBound a =
      (41*a^3-17*a^2-11*a+5)/(a*(2*a+1)*(4*a+5)) := by
    dsimp [cutoff,fourthBound]
    field_simp
    <;> ring
  have : 0 < cutoff a-fourthBound a := by rw [heq]; positivity
  linarith

/-- Every complete factor pair beyond the fourth index satisfies the bound;
there is no truncation in a,b,d or e. -/
theorem fourth_factor_bound (a b d e : ℝ) (ha : 2 ≤ a)
    (hd : 4*a+5 ≤ d) (hde : d ≤ e) (hprod : d*e = a^3*(2*a+1))
    (hsum : d+e = (a+1)^2*b+a*(3*a+1)) : b ≤ fourthBound a := by
  have hnonneg : 0 ≤ (d-(4*a+5))*(e-(4*a+5)) := mul_nonneg (by linarith) (by linarith)
  have hid : (d-(4*a+5))*(e-(4*a+5)) =
      (a+1)^2*((a-5)*(2*a-5)-(4*a+5)*b) := by
    calc
      _ = d*e-(4*a+5)*(d+e)+(4*a+5)^2 := by ring
      _ = _ := by rw [hprod,hsum]; ring
  rw [hid] at hnonneg
  have hsq : 0 < (a+1)^2 := by positivity
  have hinner := (mul_nonneg_iff_of_pos_left hsq).mp hnonneg
  have hden : 0 < 4*a+5 := by linarith
  apply (le_div_iff₀ hden).mpr
  nlinarith only [hinner]

/-- All integer triples below the full uniform cutoff act on actual ideals. -/
theorem actual_below_cutoff (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hcut : (b : ℝ) < cutoff a) :
    ¬ActualLaplacianIntegral (modulus p (exponents a a b)) := by
  obtain ⟨r,hrl,hru,hr⟩ := result a b (by exact_mod_cast ha) (by exact_mod_cast hb) hcut
  exact actual_nonintegral_of_unit_root p hp hinj a b ha hb r hr (2*(a : ℤ)*b-1)
    (by exact_mod_cast hrl) (by push_cast; linarith)

#print axioms result
#print axioms boundary_interval
#print axioms boundary_two_interval
#print axioms fourth_bound_lt_cutoff
#print axioms fourth_factor_bound
#print axioms actual_below_cutoff

end D5.S3.Combinatorics.SpectralGraph.SixSupportRepeatedCubicIntervals
