/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSProjectionResultant
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSProjectionResultant
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.Resultant.Basic]
   utility: none
   digest: A nonzero elimination polynomial contains all projected common zeros. -/
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! Relative primality gives a nonzero resultant before specialization. A
monic first polynomial retains its degree in every fiber. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSProjectionResultant

open Polynomial IsLocalization
open scoped nonZeroDivisors

private theorem fraction_coprime {R K : Type*} [CommRing R] [IsDomain R]
    [NormalizedGCDMonoid R] [Field K] [Algebra R K] [IsFractionRing R K]
    {p q : R[X]} (hp : p ≠ 0) (h : IsRelPrime p q) :
    IsCoprime (p.map (algebraMap R K)) (q.map (algebraMap R K)) := by
  apply IsRelPrime.isCoprime
  intro d hdp hdq
  have hd : d ≠ 0 := by
    intro hz
    have hz' : p.map (algebraMap R K) = 0 := by simpa [hz] using hdp
    apply hp
    apply Polynomial.map_injective _ (IsFractionRing.injective R K)
    simpa only [Polynomial.map_zero] using hz'
  let c := (integerNormalization R⁰ d).primPart
  have hprim : c.IsPrimitive := (integerNormalization R⁰ d).isPrimitive_primPart
  have hcd : c.map (algebraMap R K) ∣ d := by
    obtain ⟨b, hb, he⟩ := integerNormalization_spec R⁰ d
    rw [Algebra.smul_def, algebraMap_apply] at he
    have hb' : IsUnit (C (algebraMap R K b)) :=
      Polynomial.isUnit_C.mpr <| isUnit_iff_ne_zero.mpr <| by
        simpa only [map_zero] using
          (IsFractionRing.injective R K).ne (mem_nonZeroDivisors_iff_ne_zero.mp hb)
    apply hb'.dvd_mul_left.mp
    rw [← he, (integerNormalization R⁰ d).eq_C_content_mul_primPart, Polynomial.map_mul]
    exact dvd_mul_left _ _
  have hcp := hprim.dvd_of_fraction_map_dvd_fraction_map (hcd.trans hdp)
  have hcq := hprim.dvd_of_fraction_map_dvd_fraction_map (hcd.trans hdq)
  exact isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart hd (h hcp hcq)

/-- Without a common nonunit polynomial factor the resultant is nonzero, even
when the coefficients form a domain rather than a field. -/
theorem resultant_ne_zero_of_isRelPrime {R : Type*} [CommRing R] [IsDomain R]
    [NormalizedGCDMonoid R] {p q : R[X]} (hp : p ≠ 0) (h : IsRelPrime p q) :
    p.resultant q ≠ 0 := by
  let K := FractionRing R
  let f : R →+* K := algebraMap R K
  have hf := IsFractionRing.injective R K
  have hres := resultant_ne_zero _ _ (fraction_coprime (K := K) hp h)
  rw [natDegree_map_eq_of_injective hf, natDegree_map_eq_of_injective hf,
    resultant_map_map] at hres
  intro hz
  exact hres (by rw [hz, map_zero])

private theorem resultant_zero_of_eval_eq_zero {K : Type*} [Field K]
    {p q : K[X]} (hp : p ≠ 0) (x : K) (hpx : p.eval x = 0) (hqx : q.eval x = 0)
    (n : ℕ) (hn : q.natDegree ≤ n) :
    p.resultant q p.natDegree n = 0 := by
  have hc : ¬ IsCoprime p q := by
    rintro ⟨a, b, h⟩
    have he := congrArg (evalRingHom x) h
    simp [map_add, map_mul, hpx, hqx] at he
  have hres : p.resultant q = 0 := resultant_eq_zero_iff.mpr ⟨.inl hp, hc⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [resultant_add_right_deg _ _ _ _ _ le_rfl, hres, mul_zero]

/-- Under any coefficient specialization, a common root forces the resultant
to vanish as long as the first polynomial is monic. -/
theorem map_resultant_zero_of_common_root {R K : Type*} [CommRing R] [Field K]
    (f : R →+* K) {p q : R[X]} (hp : p.Monic) (x : K)
    (hpx : p.eval₂ f x = 0) (hqx : q.eval₂ f x = 0) :
    f (p.resultant q) = 0 := by
  rw [← resultant_map_map]
  have hd := hp.natDegree_map f
  rw [← hd]
  apply resultant_zero_of_eval_eq_zero (hp.map f).ne_zero x
  · simpa [eval_map] using hpx
  · simpa [eval_map] using hqx
  · exact natDegree_map_le

end D5.S3.Quantum.TensorNetworks.PeriodicMPSProjectionResultant
