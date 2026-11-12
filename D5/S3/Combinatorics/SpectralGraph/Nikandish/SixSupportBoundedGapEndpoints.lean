/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportBoundedGapEndpoints
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportBoundedGapEndpoints
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportBoundedGapEndpoints.second_nonzero; instance=D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportBoundedGapEndpoints.modular_rootfree
   digest: Entire original endpoint identities and root-free modular certificates for four gap families. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportClassificationAlgebra
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Source: complete low-spectrum section, revision
b93becea662a746badeadba42fdc3d3eb3db9382,
blob10576d85188447cea8efba1549722d8e14c050f2. These supplementary
arithmetic identities are retained independently of the full classification. -/
set_option autoImplicit false
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportBoundedGapEndpoints
open D5.S3.Combinatorics.SpectralGraph.SixSupportClassificationAlgebra

def f12 {R : Type*} [CommRing R] (a : R) : R :=
  a^5-9*a^4-14*a^3+93*a^2+67*a+6

def f13 {R : Type*} [CommRing R] (a : R) : R :=
  a^4-6*a^3-42*a^2-39*a-10

def f23 {R : Type*} [CommRing R] (a : R) : R :=
  a^5-5*a^4-48*a^3-59*a^2-39*a-54

def f34 {R : Type*} [CommRing R] (a : R) : R :=
  a^6-a^5-74*a^4-375*a^3-967*a^2-1220*a-340

/-- Exact second-endpoint identities over every commutative coefficient ring. -/
theorem second_endpoints {R : Type*} [CommRing R] (a : R) :
    h a (a+1) (a+2) 2 = -a*f12 a ∧
    h a (a+1) (a+3) 2 = -(a-2)*(a+1)*f13 a ∧
    h a (a+2) (a+3) 2 = -a*f23 a ∧
    h a (a+3) (a+4) 2 = -f34 a := by
  simp only [h_eq_value,value,f12,f13,f23,f34]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- Full first-endpoint positive-coefficient certificates shifted at minimum4. -/
theorem first_endpoints {R : Type*} [CommRing R] (u : R) :
    h (u+4) (u+5) (u+6) 1 =
      -4*(u+4)*(u+5)*(u^4+18*u^3+116*u^2+314*u+294) ∧
    h (u+4) (u+5) (u+7) 1 =
      -4*(u+4)*(u+5)*(u+7)*(u^3+13*u^2+51*u+57) ∧
    h (u+4) (u+6) (u+7) 1 =
      -4*(u+6)*(u^5+25*u^4+242*u^3+1126*u^2+2484*u+2022) ∧
    h (u+4) (u+7) (u+8) 1 =
      -4*(u+7)*(u^5+28*u^4+302*u^3+1550*u^2+3699*u+3126) := by
  simp only [h_eq_value,value]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- These exhaust each entire prime field; they are not exponent scans. -/
theorem modular_rootfree :
    (∀ a : ZMod 7, f12 a ≠ 0) ∧ (∀ a : ZMod 11, f13 a ≠ 0) ∧
    (∀ a : ZMod 7, f23 a ≠ 0) ∧ (∀ a : ZMod 13, f34 a ≠ 0) := by
  decide +kernel

/-- Exact integer root exclusion from the original full modular certificates. -/
theorem integer_rootfree (a : ℤ) :
    f12 a ≠ 0 ∧ f13 a ≠ 0 ∧ f23 a ≠ 0 ∧ f34 a ≠ 0 := by
  constructor
  · intro h
    apply modular_rootfree.1 (a : ZMod 7)
    simpa [f12] using congrArg (Int.castRingHom (ZMod 7)) h
  constructor
  · intro h
    apply modular_rootfree.2.1 (a : ZMod 11)
    simpa [f13] using congrArg (Int.castRingHom (ZMod 11)) h
  constructor
  · intro h
    apply modular_rootfree.2.2.1 (a : ZMod 7)
    simpa [f23] using congrArg (Int.castRingHom (ZMod 7)) h
  · intro h
    apply modular_rootfree.2.2.2 (a : ZMod 13)
    simpa [f34] using congrArg (Int.castRingHom (ZMod 13)) h

/-- All four first endpoints are strictly negative throughout the original real minimum domain. -/
theorem first_negative (a : ℝ) (ha : 4 ≤ a) :
    h a (a+1) (a+2) 1 < 0 ∧ h a (a+1) (a+3) 1 < 0 ∧
    h a (a+2) (a+3) 1 < 0 ∧ h a (a+3) (a+4) 1 < 0 := by
  let u := a-4
  have hu : 0 ≤ u := sub_nonneg.mpr ha
  have hea : a = u+4 := by dsimp [u]; ring
  rw [hea]
  have h := first_endpoints u
  have he1 : u+4+1 = u+5 := by ring
  have he2 : u+4+2 = u+6 := by ring
  have he3 : u+4+3 = u+7 := by ring
  have he4 : u+4+4 = u+8 := by ring
  rw [he1,he2,he3,he4]
  rw [h.1,h.2.1,h.2.2.1,h.2.2.2]
  constructor
  · exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) (by positivity))
        (by positivity)) (by positivity)
  constructor
  · exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) (by positivity))
          (by positivity)) (by positivity)) (by positivity)
  constructor <;> exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (by norm_num) (by positivity)) (by positivity)

/-- Full second-endpoint exclusion for every integer minimum at least4. -/
theorem second_nonzero (a : ℤ) (ha : 4 ≤ a) :
    h a (a+1) (a+2) 2 ≠ 0 ∧ h a (a+1) (a+3) 2 ≠ 0 ∧
    h a (a+2) (a+3) 2 ≠ 0 ∧ h a (a+3) (a+4) 2 ≠ 0 := by
  have hf := integer_rootfree a
  have ha0 : a ≠ 0 := by omega
  have ha2 : a-2 ≠ 0 := by omega
  have ha1 : a+1 ≠ 0 := by omega
  rw [(second_endpoints a).1,(second_endpoints a).2.1,
    (second_endpoints a).2.2.1,(second_endpoints a).2.2.2]
  exact ⟨mul_ne_zero (neg_ne_zero.mpr ha0) hf.1,
    mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr ha2) ha1) hf.2.1,
    mul_ne_zero (neg_ne_zero.mpr ha0) hf.2.2.1,neg_ne_zero.mpr hf.2.2.2⟩

#print axioms modular_rootfree
#print axioms integer_rootfree
#print axioms second_nonzero
end D5.S3.Combinatorics.SpectralGraph.SixSupportBoundedGapEndpoints
