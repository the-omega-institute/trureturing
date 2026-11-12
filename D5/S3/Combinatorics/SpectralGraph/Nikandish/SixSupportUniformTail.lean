/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportUniformTail
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportUniformTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The complete real uniform cutoff and actual ideal-graph nonintegrality. -/

import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportEndpointSmallGaps
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! The source uniform cutoff c≥4a²-2a is unbounded in both other exponents.
Its characteristic signs are consumed by the actual ideal graph. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace D5.S3.Combinatorics.SpectralGraph.SixSupportUniformTail

open D5.S3.Combinatorics.SpectralGraph.SixSupportClassificationAlgebra
open D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointSmallGaps
open D5.S3.Combinatorics.SpectralGraph.SixSupportIdealIntersectionLift
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSupport
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions

/-- The actual complement quintic is strictly negative at zero for all
positive real support weights. -/
theorem zero_negative (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    h a b c 0 < 0 := by
  have hs : 0 < a+b+c := by positivity
  have ht : 0 < a*b+a*c+b*c := by positivity
  have hu : 0 < a*b*c := by positivity
  have heq : h a b c 0 = -((a+b+c)^2*(a*b*c)+(a+b+c)*(a*b+a*c+b*c)*(a*b*c)) := by
    simp [h, quintic]
  rw [heq]
  have : 0 < (a+b+c)^2*(a*b*c)+(a+b+c)*(a*b+a*c+b*c)*(a*b*c) := by positivity
  linarith

/-- Exact full real uniform endpoint sign, at the source cutoff. -/
theorem one_positive (a b c : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hc : 4*a^2-2*a ≤ c) : 0 < h a b c 1 := by
  let A := a^2+b^2-1
  let B := a^3-4*a^2*b^2+2*a^2*b-a^2+2*a*b^2+a*b-3*a+b^3-b^2-3*b+3
  let D := (a-1)*(b-1)*(2*a*b+3*a+3*b-3)
  let E := (a-1)*(b-1)*(a+b-1)*(a*b+a+b-1)
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have ha1 : 0 < a-1 := by linarith
  have hb1 : 0 < b-1 := by linarith
  have hA : 0 < A := by dsimp [A]; nlinarith [sq_nonneg (a-2),sq_nonneg b]
  have hD : 0 < D := by
    dsimp [D]
    have : 0 < 2*a*b+3*a+3*b-3 := by nlinarith [mul_pos ha0 hb0]
    positivity
  have hE : 0 < E := by
    dsimp [E]
    have h1 : 0 < a+b-1 := by linarith
    have h2 : 0 < a*b+a+b-1 := by nlinarith [mul_pos ha0 hb0]
    positivity
  have hm : 0 ≤ a-2 := by linarith
  have hK : 0 < 4*a^4-a^3-5*a^2-a+3 := by
    have heq : 4*a^4-a^3-5*a^2-a+3 =
        4*(a-2)^4+31*(a-2)^3+85*(a-2)^2+95*(a-2)+37 := by ring
    rw [heq]
    positivity
  have hlinear : 0 < B+(4*a^2-2*a)*A := by
    have heq : B+(4*a^2-2*a)*A =
        b^2*(b-1)+(2*a^2+a-3)*b+(4*a^4-a^3-5*a^2-a+3) := by
      dsimp [A,B]
      ring
    have hq : 0 < 2*a^2+a-3 := by nlinarith [sq_nonneg (a-2)]
    rw [heq]
    positivity
  have hAcB : 0 < A*c+B := by
    have hmono : 0 ≤ A*(c-(4*a^2-2*a)) := mul_nonneg hA.le (by linarith)
    nlinarith only [hlinear,hmono]
  have heq : h a b c 1 = (A*c+B)*c^2+D*c+E := by
    rw [endpoint_identity]
    dsimp [A,B,D,E,cubic]
    ring
  rw [heq]
  positivity

/-- A root strictly between zero and one on the entire original real tail. -/
theorem result (a b c : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hc : 4*a^2-2*a ≤ c) :
    ∃ e : ℝ, 0 < e ∧ e < 1 ∧ h a b c e = 0 := by
  have h0 := zero_negative a b c (by linarith) (by linarith) (by linarith)
  have h1 := one_positive a b c ha hab hbc hc
  obtain ⟨e, he, hroot⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
    (show ContinuousOn (fun x : ℝ => h a b c x) (Set.Icc 0 1) by unfold h; fun_prop)
    (show (0 : ℝ) ∈ Set.Icc (h a b c 0) (h a b c 1) from ⟨h0.le,h1.le⟩)
  refine ⟨e, ?_, ?_, hroot⟩
  · have hn : e ≠ 0 := by intro heq; subst e; linarith
    exact lt_of_le_of_ne he.1 (Ne.symm hn)
  · have hn : e ≠ 1 := by intro heq; subst e; linarith
    exact lt_of_le_of_ne he.2 hn

/-- Actual graphs consume the full integer tail, with every three distinct primes. -/
theorem actual_nonintegral (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 2 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c) (hc : 4*a*a-2*a ≤ c) :
    ¬ActualLaplacianIntegral (modulus p (exponents a b c)) := by
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  have hc0 : 0 < c := by omega
  have hreal : (4 : ℝ)*(a : ℝ)^2-2*a ≤ c := by
    have hn : 4*a*a ≤ c+2*a := Nat.sub_le_iff_le_add.mp hc
    have hnR : (4 : ℝ)*(a : ℝ)*(a : ℝ) ≤ (c : ℝ)+2*(a : ℝ) := by exact_mod_cast hn
    nlinarith only [hnR]
  obtain ⟨e, he0, he1, heroot⟩ := result a b c (by exact_mod_cast ha)
    (by exact_mod_cast hab) (by exact_mod_cast hbc) hreal
  exact nonintegral_of_unit_root p hp hinj a b c ha0 hb0 hc0 e he0.ne' heroot 0
    (by simpa using he0) (by simpa using he1)

#print axioms one_positive
#print axioms result
#print axioms actual_nonintegral

end D5.S3.Combinatorics.SpectralGraph.SixSupportUniformTail
