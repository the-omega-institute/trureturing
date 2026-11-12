/- GID: D5/S3/Combinatorics/SpectralGraph/SixSupportRepeatedFactorPairs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportRepeatedFactorPairs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact complete square-discriminant factor pairs and congruence, with actual consumers. -/

import D5.S3.Combinatorics.SpectralGraph.SixSupportRepeatedQuadratic
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic

/-! The source exact divisor criterion has no truncation in either exponent.
Positive integer factors are represented in Z, with positivity explicit;
these are exactly the positive natural factors. Every arithmetic branch
retains its actual ideal-graph consumer. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportRepeatedFactorPairs

open SixSupportRepeatedQuadratic
open SixSupportIdealIntersectionLift (exponents)
open IdealIntersectionSupport IdealIntersectionObstructions

/-- The exact source product M. -/
def factorM (a : ℤ) : ℤ := a^3*(2*a+1)

/-- The exact source sum A. -/
def factorA (a b : ℤ) : ℤ := (a+1)^2*b+a*(3*a+1)

/-- The original square-discriminant boundary. -/
def boundary (a : ℤ) : ℤ := (a-1)*(2*a-1)

/-- The full source polynomial identity behind the divisor reduction. -/
theorem discriminant_identity (a b : ℕ) :
    (factorA a b)^2-(a+1 : ℤ)^2*(discriminant a b : ℤ) = 4*factorM a := by
  dsimp [factorA,factorM,discriminant]
  push_cast
  ring

/-- Both directions of the exact integer factor-pair criterion. -/
theorem result (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    IsSquare (discriminant a b) ↔
      ∃ d e s : ℤ, 0 < d ∧ d ≤ e ∧ d*e = factorM a ∧
        d+e = factorA a b ∧ e-d = (a+1 : ℤ)*s ∧ 0 ≤ s := by
  have haI : (0 : ℤ) < a := by exact_mod_cast ha
  have hbI : (0 : ℤ) < b := by exact_mod_cast hb
  have hh : (0 : ℤ) < a+1 := by omega
  have hA : 0 < factorA a b := by dsimp [factorA]; positivity
  have hM : 0 < factorM a := by dsimp [factorM]; positivity
  have hid := discriminant_identity a b
  constructor
  · rintro ⟨s,hs⟩
    have hsI : (discriminant a b : ℤ) = (s : ℤ)*s := by exact_mod_cast hs
    have hprod : (factorA a b-(a+1 : ℤ)*s)*(factorA a b+(a+1 : ℤ)*s) = 4*factorM a := by
      rw [hsI] at hid
      nlinarith only [hid]
    have hs0 : (0 : ℤ) ≤ s := Int.natCast_nonneg _
    have hy : 0 < factorA a b+(a+1 : ℤ)*s := by positivity
    have hx : 0 < factorA a b-(a+1 : ℤ)*s := by
      apply (mul_pos_iff_of_pos_right hy).mp
      rw [hprod]
      positivity
    have heven : Even ((factorA a b-(a+1 : ℤ)*s)*(factorA a b+(a+1 : ℤ)*s)) := by
      refine ⟨2*factorM a, ?_⟩
      rw [hprod]
      ring
    have hxEven : Even (factorA a b-(a+1 : ℤ)*s) := by
      rcases Int.even_mul.mp heven with h | h
      · exact h
      · obtain ⟨e,he⟩ := h
        exact ⟨e-(a+1 : ℤ)*s,by linear_combination he⟩
    obtain ⟨d,hd⟩ := hxEven
    let e := d+(a+1 : ℤ)*s
    have hAeq : factorA a b = 2*d+(a+1 : ℤ)*s := by linarith only [hd]
    have hdeprod : d*e = factorM a := by
      rw [hAeq] at hprod
      dsimp [e]
      nlinarith only [hprod]
    refine ⟨d,e,s,?_,?_,hdeprod,?_,?_,hs0⟩
    · nlinarith only [hx,hd]
    · dsimp [e]
      have : 0 ≤ (a+1 : ℤ)*s := mul_nonneg hh.le hs0
      linarith
    · dsimp [e]
      linarith only [hAeq]
    · dsimp [e]
      ring
  · rintro ⟨d,e,s,hd,hde,hprod,hsum,hgap,hs⟩
    have hformula : (d+e)^2-(e-d)^2 = 4*(d*e) := by ring
    rw [hprod,hsum,hgap] at hformula
    have hmul : (a+1 : ℤ)^2*((discriminant a b : ℤ)-s*s) = 0 := by
      linear_combination hformula-hid
    have hnonzero : (a+1 : ℤ)^2 ≠ 0 := by positivity
    have hsq : (discriminant a b : ℤ) = s*s :=
      sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hnonzero)
    exact Int.isSquare_natCast_iff.mp ⟨s,hsq⟩

/-- The exact strong product identity at every admissible factor pair. -/
theorem strong_product (a b : ℕ) (d e : ℤ)
    (hprod : d*e = factorM a) (hsum : d+e = factorA a b) :
    (d-1)*(e-1) = (a+1 : ℤ)^2*(boundary a-b) := by
  calc
    _ = d*e-(d+e)+1 := by ring
    _ = _ := by rw [hprod,hsum]; dsimp [factorM,factorA,boundary]; ring

/-- Both factors have residue one modulo a+1, for every admissible pair.
The parity step is derived from the exact strong product, including even a+1. -/
theorem factor_congruences (a b : ℕ) (ha : 0 < a) (d e s : ℤ)
    (hprod : d*e = factorM a) (hsum : d+e = factorA a b)
    (hgap : e-d = (a+1 : ℤ)*s) :
    (a+1 : ℤ) ∣ d-1 ∧ (a+1 : ℤ) ∣ e-1 := by
  let k := (a+1 : ℤ)*b+3*a-2-s
  have h2d : 2*(d-1) = (a+1 : ℤ)*k := by
    dsimp [k]
    dsimp [factorA] at hsum
    linear_combination hsum-hgap
  have h2e : 2*(e-1) = (a+1 : ℤ)*(k+2*s) := by
    linear_combination h2d+2*hgap
  have hstrong := strong_product a b d e hprod hsum
  have h4 : (2*(d-1))*(2*(e-1)) = 4*((d-1)*(e-1)) := by ring
  rw [h2d,h2e,hstrong] at h4
  have hmul : (a+1 : ℤ)^2*(k*(k+2*s)-4*(boundary a-b)) = 0 := by linear_combination h4
  have hh : (a+1 : ℤ)^2 ≠ 0 := by positivity
  have hEq : k*(k+2*s) = 4*(boundary a-b) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hh)
  have hEven : Even (k*(k+2*s)) := ⟨2*(boundary a-b),by linarith only [hEq]⟩
  have hkEven : Even k := by
    rcases Int.even_mul.mp hEven with h | h
    · exact h
    · obtain ⟨t,ht⟩ := h
      exact ⟨t-s,by linear_combination ht⟩
  obtain ⟨t,ht⟩ := hkEven
  rw [ht] at h2d
  have hdt : d-1 = (a+1 : ℤ)*t := by nlinarith only [h2d]
  exact ⟨⟨t,hdt⟩,⟨t+s,by nlinarith only [hgap,hdt]⟩⟩

/-- The source quadratic bound for all positive repeated and third exponents. -/
theorem quadratic_bound (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hD : IsSquare (discriminant a b)) : (b : ℤ) ≤ boundary a := by
  obtain ⟨d,e,s,hd,hde,hprod,hsum,hgap,hs⟩ := (result a b ha hb).mp hD
  have hnonneg : 0 ≤ (d-1)*(e-1) := mul_nonneg (by omega) (by omega)
  rw [strong_product a b d e hprod hsum] at hnonneg
  have hpos : (0 : ℤ) < (a+1 : ℤ)^2 := by positivity
  have hi := (mul_nonneg_iff_of_pos_left hpos).mp hnonneg
  linarith

/-- The entire unbounded region above the source quadratic bound has an
actual ideal-graph consumer, without a parameter scan. -/
theorem actual_above_quadratic_bound (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hbound : boundary a < (b : ℤ)) :
    ¬ActualLaplacianIntegral (modulus p (exponents a a b)) := by
  have hD : ¬IsSquare (discriminant a b) := by
    intro hD
    have h := quadratic_bound a b ha hb hD
    omega
  exact (SixSupportRepeatedQuadratic.result p hp hinj a b ha hb hD).2

#print axioms result
#print axioms strong_product
#print axioms factor_congruences
#print axioms quadratic_bound
#print axioms actual_above_quadratic_bound

end D5.S3.Combinatorics.SpectralGraph.SixSupportRepeatedFactorPairs
