/- GID: D5/S3/Combinatorics/SpectralGraph/SixSupportSmallMinima
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportSmallMinima
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete distinct unit and minimum-two branches of the actual three-prime graph. -/

import D5.S3.Combinatorics.SpectralGraph.SixSupportUniformTail
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! The original unit-exponent and minimum-two source arguments, at their
unbounded domains. Repeated triples are handled by the separate complete
factor-index theorem, rather than a premise in these interval calculations. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportSmallMinima

open SixSupportClassificationAlgebra SixSupportUniformTail
open SixSupportIdealIntersectionLift (exponents)
open IdealIntersectionSupport IdealIntersectionObstructions

private theorem root_between (a b c l u : ℝ) (hlu : l < u)
    (hl : h a b c l < 0) (hu : 0 < h a b c u) :
    ∃ e : ℝ, l < e ∧ e < u ∧ h a b c e = 0 := by
  obtain ⟨e,he,hez⟩ := intermediate_value_Icc hlu.le
    (show ContinuousOn (h a b c) (Set.Icc l u) by unfold h; fun_prop)
    (show (0 : ℝ) ∈ Set.Icc (h a b c l) (h a b c u) from ⟨hl.le,hu.le⟩)
  refine ⟨e,?_,?_,hez⟩
  · have hn : l ≠ e := by intro hn; rw [← hn] at hez; linarith
    exact lt_of_le_of_ne he.1 hn
  · have hn : e ≠ u := by intro hn; rw [hn] at hez; linarith
    exact lt_of_le_of_ne he.2 hn

/-- The exact source endpoint identity on the full unit-exponent plane. -/
theorem unit_identity {R : Type*} [CommRing R] (b c : R) :
    h 1 b c 1 = b^2*c^2*(b+c-3) := by rw [h_eq_value]; dsimp [value]; ring

/-- Every positive real unit-exponent pair above the exact exceptional sum
has the original root in (0,1). -/
theorem unit_interval (b c : ℝ) (hb : 0 < b) (hc : 0 < c) (hs : 3 < b+c) :
    ∃ e : ℝ, 0 < e ∧ e < 1 ∧ h 1 b c e = 0 := by
  apply root_between 1 b c 0 1 (by norm_num) (zero_negative 1 b c (by norm_num) hb hc)
  rw [unit_identity]
  positivity

/-- Actual ideal-graph consumption of the entire unbounded unit branch. -/
theorem unit_actual (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (b c : ℕ) (hb : 0 < b) (hc : 0 < c)
    (hs : 3 < b+c) :
    ¬ActualLaplacianIntegral (modulus p (exponents 1 b c)) := by
  obtain ⟨e,he0,he1,he⟩ := unit_interval b c (by exact_mod_cast hb)
    (by exact_mod_cast hc) (by exact_mod_cast hs)
  exact nonintegral_of_unit_root p hp hinj 1 b c (by decide) hb hc e he0.ne'
    (by simpa using he) 0
    (by simpa using he0) (by simpa using he1)

/-- The first of the two complete positive shifted source identities. -/
theorem minimum_two_first (v : ℝ) (hv : 0 ≤ v) : 0 < h 2 3 (5+v) 1 := by
  have heq : h 2 3 (5+v) 1 = 12*v^3+112*v^2+268*v+120 := by
    rw [h_eq_value]; dsimp [value]; ring
  rw [heq]
  positivity

/-- The full two-variable positive shifted identity; no parameter scan. -/
theorem minimum_two_second (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < h 2 (4+u) (5+u+v) 1 := by
  have heq : h 2 (4+u) (5+u+v) 1 =
      (u^2+8*u+19)*v^3+(4*u^3+38*u^2+128*u+170)*v^2+
      (5*u^4+62*u^3+271*u^2+502*u+368)*v+
      2*u^5+32*u^4+190*u^3+504*u^2+552*u+160 := by
    rw [h_eq_value]; dsimp [value]; ring
  rw [heq]
  positivity

/-- Every distinct sorted minimum-two triple, including (2,3,4). -/
theorem minimum_two_actual (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (b c : ℕ) (hb : 2 < b) (hbc : b < c) :
    ¬ActualLaplacianIntegral (modulus p (exponents 2 b c)) := by
  by_cases hexc : b = 3 ∧ c = 4
  · rcases hexc with ⟨rfl,rfl⟩
    obtain ⟨e,he1,heU,he⟩ := root_between 2 3 4 1 (3/2) (by norm_num)
      (by norm_num [h_eq_value,value]) (by norm_num [h_eq_value,value])
    exact nonintegral_of_unit_root p hp hinj 2 3 4 (by decide) (by decide) (by decide)
      e (by linarith) he 1 (by simpa using he1) (by norm_num; linarith)
  · have hp1 : 0 < h (2 : ℝ) b c 1 := by
      by_cases hb3 : b = 3
      · subst b
        have hc5 : 5 ≤ c := by omega
        have hcR : (5 : ℝ) ≤ c := by exact_mod_cast hc5
        have h := minimum_two_first ((c : ℝ)-5) (by linarith)
        convert h using 1 <;> ring
      · have hb4 : 4 ≤ b := by omega
        have hbR : (4 : ℝ) ≤ b := by exact_mod_cast hb4
        have hbcR : (b : ℝ)+1 ≤ c := by exact_mod_cast (show b+1 ≤ c by omega)
        have hu : 0 ≤ (b : ℝ)-4 := by linarith
        have hv : 0 ≤ (c : ℝ)-b-1 := by linarith
        have h := minimum_two_second ((b : ℝ)-4) ((c : ℝ)-b-1) hu hv
        convert h using 1 <;> ring
    obtain ⟨e,he0,he1,he⟩ := root_between 2 b c 0 1 (by norm_num)
      (zero_negative 2 b c (by norm_num) (by exact_mod_cast (show 0 < b by omega))
        (by exact_mod_cast (show 0 < c by omega))) hp1
    exact nonintegral_of_unit_root p hp hinj 2 b c (by decide) (by omega) (by omega)
      e he0.ne' he 0 (by simpa using he0) (by simpa using he1)

#print axioms unit_interval
#print axioms minimum_two_actual
end D5.S3.Combinatorics.SpectralGraph.SixSupportSmallMinima
