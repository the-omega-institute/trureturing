/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportRepeatedCompletion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportRepeatedCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete unbounded repeated-exponent classification on actual ideal graphs. -/

import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportRepeatedFactorPairs
import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportRepeatedCubicIntervals
import Mathlib.Tactic

/-! Reza Nikandish's boundary family and the supplied subsequent complete
factor-index proof. The finite cases below exhaust indices one through three;
the fourth-index estimate covers all remaining indices, without an exponent
cutoff. No arithmetic report is used as a Lean hypothesis. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportRepeatedCompletion

open SixSupportRepeatedBlocks SixSupportRepeatedQuadratic
open SixSupportRepeatedFactorPairs SixSupportRepeatedCubicIntervals
open SixSupportIdealIntersectionLift (exponents)
open IdealIntersectionSupport IdealIntersectionObstructions

/-- Exact source identity for every factor index and exponent. -/
theorem index_identity (a j : ℤ) :
    j^4*factorM a-(j+1)^3*(j+2) = (j*(a+1)+1)*
      (2*j^3*a^3-j^2*(j+2)*a^2+j*(j+1)*(j+2)*a-(j+1)^2*(j+2)) := by
  dsimp [factorM]
  ring

/-- The exact divisor consequence has no bound on the index or exponent. -/
theorem index_divisor (a j d e : ℤ) (hd : d = j*(a+1)+1)
    (hp : d*e = factorM a) : d ∣ (j+1)^3*(j+2) := by
  refine ⟨j^4*e-(2*j^3*a^3-j^2*(j+2)*a^2+
    j*(j+1)*(j+2)*a-(j+1)^2*(j+2)), ?_⟩
  have hi := index_identity a j
  rw [← hd, ← hp] at hi
  nlinarith only [hi]

/-- All positive cases of the first three indices, over every exponent.
The source constants are exactly 24,108,320, rather than a sampled range. -/
theorem first_indices (a b : ℕ) (j d e : ℤ) (ha : 2 ≤ a) (hb : 0 < b)
    (hj : 1 ≤ j) (hj3 : j ≤ 3) (hd : d = j*((a : ℤ)+1)+1)
    (hp : d*e = factorM a) (hs : d+e = factorA a b) :
    (a = 4 ∧ b = 2) ∨ (a = 6 ∧ b = 5) ∨ (a = 10 ∧ b = 12) ∨
    (a = 22 ∧ b = 35) ∨ (a = 12 ∧ b = 7) ∨
    (a = 12 ∧ b = 4) ∨ (a = 20 ∧ b = 9) ∨ (a = 52 ∧ b = 30) := by
  have hdiv := index_divisor a j d e hd hp
  have hd0 : 0 < d := by
    rw [hd]
    have hj0 : 0 < j := by omega
    positivity
  have hk : (j+1)^3*(j+2) ≤ 320 := by interval_cases j <;> norm_num
  have hk0 : 0 < (j+1)^3*(j+2) := by
    have hj0 : 0 < j := by omega
    positivity
  have hdK : d ≤ (j+1)^3*(j+2) := Int.le_of_dvd hk0 hdiv
  have hlin : (a : ℤ)+2 ≤ d := by
    nlinarith [mul_nonneg (show 0 ≤ j-1 by omega)
      (show 0 ≤ (a : ℤ)+1 by positivity)]
  have ha318 : a ≤ 318 := by omega
  subst d
  interval_cases j <;> interval_cases a <;>
    norm_num [factorM, factorA] at hp hs ⊢ <;> omega

private theorem integer_interval_root (a b : ℝ) (q : ℤ)
    (hl : cubic a b (q : ℝ) < 0) (hu : 0 < cubic a b ((q : ℝ)+1)) :
    ∃ r : ℝ, (q : ℝ) < r ∧ r < (q : ℝ)+1 ∧ cubic a b r = 0 := by
  obtain ⟨r,hr,hr0⟩ := intermediate_value_Icc
    (show (q : ℝ) ≤ (q : ℝ)+1 by linarith)
    (show ContinuousOn (cubic a b) (Set.Icc (q : ℝ) ((q : ℝ)+1)) by unfold cubic; fun_prop)
    (show (0 : ℝ) ∈ Set.Icc (cubic a b q) (cubic a b ((q : ℝ)+1)) from ⟨hl.le,hu.le⟩)
  refine ⟨r,?_,?_,hr0⟩
  · have hn : (q : ℝ) ≠ r := by intro h; rw [← h] at hr0; linarith
    exact lt_of_le_of_ne hr.1 hn
  · have hn : r ≠ (q : ℝ)+1 := by intro h; rw [h] at hr0; linarith
    exact lt_of_le_of_ne hr.2 hn

/-- A real root in an open integer interval for all initial-index cases. -/
theorem first_index_root (a b : ℕ)
    (hc : (a = 4 ∧ b = 2) ∨ (a = 6 ∧ b = 5) ∨ (a = 10 ∧ b = 12) ∨
      (a = 22 ∧ b = 35) ∨ (a = 12 ∧ b = 7) ∨
      (a = 12 ∧ b = 4) ∨ (a = 20 ∧ b = 9) ∨ (a = 52 ∧ b = 30)) :
    ∃ q : ℤ, ∃ r : ℝ, (q : ℝ) < r ∧ r < (q : ℝ)+1 ∧ cubic (a : ℝ) b r = 0 := by
  rcases hc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨15, integer_interval_root 4 2 15 (by norm_num [cubic]) (by norm_num [cubic])⟩
  · exact ⟨57, integer_interval_root 6 5 57 (by norm_num [cubic]) (by norm_num [cubic])⟩
  · exact ⟨220, integer_interval_root 10 12 220 (by norm_num [cubic]) (by norm_num [cubic])⟩
  · exact ⟨1271, integer_interval_root 22 35 1271 (by norm_num [cubic]) (by norm_num [cubic])⟩
  · exact ⟨166, integer_interval_root 12 7 166 (by norm_num [cubic]) (by norm_num [cubic])⟩
  · exact ⟨95, integer_interval_root 12 4 95 (by norm_num [cubic]) (by norm_num [cubic])⟩
  · exact ⟨359, integer_interval_root 20 9 359 (by norm_num [cubic]) (by norm_num [cubic])⟩
  · exact ⟨3118, integer_interval_root 52 30 3118 (by norm_num [cubic]) (by norm_num [cubic])⟩

/-- Complete repeated-exponent nonintegrality for all positive exponents
and every injective triple of primes, on the actual ideal-intersection graph. -/
theorem result (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ActualLaplacianIntegral (modulus p (exponents a a b)) := by
  by_cases ha1 : a = 1
  · subst a
    exact two_unit_actual p hp hinj b hb
  have ha2 : 2 ≤ a := by omega
  by_cases hD : IsSquare (discriminant a b)
  · obtain ⟨d,e,s,hd,hde,hprod,hsum,hgap,hs⟩ :=
      (SixSupportRepeatedFactorPairs.result a b ha hb).mp hD
    obtain ⟨j,hj⟩ := (factor_congruences a b ha d e s hprod hsum hgap).1
    have hj0 : 0 ≤ j := by nlinarith
    have hdj : d = j*((a : ℤ)+1)+1 := by nlinarith only [hj]
    by_cases hjZ : j = 0
    · subst j
      have hd1 : d = 1 := by simpa using hdj
      subst d
      have he : e = factorM a := by simpa using hprod
      rw [he] at hsum
      have hbmul : ((a : ℤ)+1)^2*((b : ℤ)-boundary a) = 0 := by
        dsimp [factorM,factorA,boundary] at hsum ⊢
        nlinarith only [hsum]
      have hbe : (b : ℤ) = boundary a := sub_eq_zero.mp
        ((mul_eq_zero.mp hbmul).resolve_left (by positivity))
      have hbR : (b : ℝ) = ((a : ℝ)-1)*(2*(a : ℝ)-1) := by
        dsimp [boundary] at hbe
        exact_mod_cast hbe
      by_cases ha3 : 3 ≤ a
      · obtain ⟨r,hrl,hru,hr⟩ := boundary_interval (a : ℝ) (by exact_mod_cast ha3)
        rw [← hbR] at hr
        exact actual_nonintegral_of_unit_root p hp hinj a b ha hb r hr
          (2*(a : ℤ)^3-2*(a : ℤ)^2+2*(a : ℤ)-2)
          (by exact_mod_cast hrl) (by push_cast; convert hru using 1 <;> ring)
      · have haeq : a = 2 := by omega
        subst a
        have hbeq : b = 3 := by norm_num [boundary] at hbe; omega
        subst b
        obtain ⟨r,hrl,hru,hr⟩ := boundary_two_interval
        exact actual_nonintegral_of_unit_root p hp hinj 2 3 ha hb r hr 15
          (by norm_num at hrl ⊢; exact hrl) (by norm_num at hru ⊢; exact hru)
    · by_cases hj3 : j ≤ 3
      · have hcases := first_indices a b j d e ha2 hb (by omega) hj3 hdj hprod hsum
        obtain ⟨q,r,hrl,hru,hr⟩ := first_index_root a b hcases
        exact actual_nonintegral_of_unit_root p hp hinj a b ha hb r hr q hrl hru
      · have hbound : (b : ℝ) ≤ fourthBound a := fourth_factor_bound a b d e
          (by exact_mod_cast ha2) (by exact_mod_cast (show 4*(a : ℤ)+5 ≤ d by nlinarith))
          (by exact_mod_cast hde)
          (by dsimp [factorM] at hprod; exact_mod_cast hprod)
          (by dsimp [factorA] at hsum; exact_mod_cast hsum)
        exact actual_below_cutoff p hp hinj a b ha hb
          (hbound.trans_lt (fourth_bound_lt_cutoff a (by exact_mod_cast ha2)))
  · exact (SixSupportRepeatedQuadratic.result p hp hinj a b ha hb hD).2

#print axioms index_identity
#print axioms first_indices
#print axioms result

end D5.S3.Combinatorics.SpectralGraph.SixSupportRepeatedCompletion
