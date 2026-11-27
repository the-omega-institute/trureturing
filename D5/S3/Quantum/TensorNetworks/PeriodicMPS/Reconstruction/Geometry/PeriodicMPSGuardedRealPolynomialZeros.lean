/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSGuardedRealPolynomialZeros
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSGuardedRealPolynomialZeros
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: A guard containing the common divisors gives a three-dimensional real zero-set cover. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSRealPolynomialZeros
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! A guard that contains every common irreducible factor gives a real
codimension-two cover for the common zeros of a nonzero polynomial ideal. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSRealPolynomialZeros

open Set UniqueFactorizationMonoid

private def powSaturation {R : Type*} [CommRing R] (I : Ideal R) (g : R) : Ideal R where
  carrier := {x | ∃ k : ℕ, g ^ k * x ∈ I}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨j, hx⟩ ⟨k, hy⟩
    refine ⟨j + k, ?_⟩
    rw [mul_add]
    apply I.add_mem
    · rw [pow_add, mul_comm (g ^ j) (g ^ k), mul_assoc]
      exact I.mul_mem_left _ hx
    · rw [pow_add, mul_assoc]
      exact I.mul_mem_left _ hy
  smul_mem' := by
    rintro a x ⟨k, hx⟩
    refine ⟨k, ?_⟩
    rw [smul_eq_mul, mul_left_comm]
    exact I.mul_mem_left _ hx

/-- If every common irreducible divisor of a nonzero ideal divides the guard,
the ideal saturated by powers of that guard contains a relatively prime pair. -/
theorem exists_relPrime_of_common_irreducible_dvd_guard
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    {I : Ideal R} (hI : I ≠ ⊥) {g : R}
    (hguard : ∀ r : R, Irreducible r → (∀ a ∈ I, r ∣ a) → r ∣ g) :
    ∃ p q : R, p ≠ 0 ∧ IsRelPrime p q ∧
      (∃ j : ℕ, g ^ j * p ∈ I) ∧ (∃ k : ℕ, g ^ k * q ∈ I) := by
  classical
  let : StrongNormalizationMonoid R := UniqueFactorizationMonoid.strongNormalizationMonoid
  let J := powSaturation I g
  have hIJ : I ≤ J := fun a ha => ⟨0, by simpa using ha⟩
  obtain ⟨a, ha, ha₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨p, hp, hmin⟩ := (wellFounded_dvdNotUnit (α := R)).has_min
    {x | x ∈ J ∧ x ≠ 0} ⟨a, hIJ ha, ha₀⟩
  obtain ⟨hpJ, hp₀⟩ := hp
  let factors := (normalizedFactors p).toFinset
  let P (r : R) := Ideal.span ({r} : Set R)
  have hprime (r : R) (hr : r ∈ factors) : Prime r :=
    prime_of_normalized_factor r (Multiset.mem_toFinset.mp hr)
  have havoid (r : R) (hr : r ∈ factors) : ¬J ≤ P r := by
    intro hle
    have hrg := hguard r (hprime r hr).irreducible
      (fun b hb => Ideal.mem_span_singleton.mp (hle (hIJ hb)))
    obtain ⟨s, hs⟩ := dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hr)
    have hs₀ : s ≠ 0 := by
      intro h
      exact hp₀ (by simp [hs, h])
    have hsJ : s ∈ J := by
      obtain ⟨k, hk⟩ := hpJ
      obtain ⟨t, ht⟩ := hrg
      refine ⟨k + 1, ?_⟩
      have he : g ^ (k + 1) * s = t * (g ^ k * p) := by
        rw [pow_succ, hs]
        calc
          g ^ k * g * s = g ^ k * (r * t) * s :=
            congrArg (fun z => g ^ k * z * s) ht
          _ = t * (g ^ k * (r * s)) := by ac_rfl
      rw [he]
      exact I.mul_mem_left _ hk
    exact hmin s ⟨hsJ, hs₀⟩ ⟨hs₀, r, (hprime r hr).not_isUnit, hs.trans (mul_comm _ _)⟩
  have hnot : ¬(J : Set R) ⊆ ⋃ r ∈ (factors : Set R), P r := by
    intro h
    obtain ⟨r, hr, hle⟩ := (Ideal.subset_union_prime (f := P) 0 0
      (fun r hr _ _ => (Ideal.span_singleton_prime (hprime r hr).ne_zero).mpr
        (hprime r hr))).mp h
    exact havoid r hr hle
  obtain ⟨q, hqJ, hq⟩ := Set.not_subset.mp hnot
  refine ⟨p, q, hp₀, (isRelPrime_iff_no_prime_factors hp₀).mpr ?_, hpJ, hqJ⟩
  intro r hrp hrq hr
  obtain ⟨s, hs, hrs⟩ := exists_mem_normalizedFactors_of_dvd hp₀ hr.irreducible hrp
  exact hq (Set.mem_iUnion₂.mpr ⟨s, Multiset.mem_toFinset.mpr hs,
    Ideal.mem_span_singleton.mpr (hrs.dvd_iff_dvd_left.mp hrq)⟩)

/-- The real common zeros of an ideal at which the guard is nonzero. -/
def guardedRealZeroSet {σ : Type*} (I : Ideal (MvPolynomial σ ℂ))
    (g : MvPolynomial σ ℂ) : Set (σ → ℝ) :=
  {x | MvPolynomial.eval (fun i => (x i : ℂ)) g ≠ 0 ∧
    ∀ p ∈ I, MvPolynomial.eval (fun i => (x i : ℂ)) p = 0}

/-- A nonzero ideal whose common irreducible divisors all divide the guard
has a countable differentiable cover in two fewer real coordinates on the
guarded slice. In particular, five variables give a cover from three. -/
theorem cover_guarded_real_common_zeros
    {n : ℕ} {I : Ideal (MvPolynomial (Fin (n + 2)) ℂ)} (hI : I ≠ ⊥)
    {g : MvPolynomial (Fin (n + 2)) ℂ}
    (hguard : ∀ r, Irreducible r → (∀ a ∈ I, r ∣ a) → r ∣ g) :
    ∃ (ι : Type) (_ : Countable ι) (D : ι → Set (Fin n → ℝ))
      (f : ι → (Fin n → ℝ) → (Fin (n + 2) → ℝ)),
      (∀ i, DifferentiableOn ℝ (f i) (D i)) ∧
        guardedRealZeroSet I g ⊆ ⋃ i, f i '' D i := by
  obtain ⟨p, q, hp, hrel, hpI, hqI⟩ :=
    exists_relPrime_of_common_irreducible_dvd_guard hI hguard
  obtain ⟨ι, hι, D, f, hdf, hcover⟩ := cover_real_common_zeros hp hrel
  refine ⟨ι, hι, D, f, hdf, fun x hx => hcover ?_⟩
  have vanish (a : MvPolynomial (Fin (n + 2)) ℂ) (ha : ∃ k : ℕ, g ^ k * a ∈ I) :
      MvPolynomial.eval (fun i => (x i : ℂ)) a = 0 := by
    obtain ⟨k, hk⟩ := ha
    have he := hx.2 _ hk
    rw [map_mul, map_pow] at he
    exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ hx.1)
  exact ⟨vanish p hpI, vanish q hqI⟩

end D5.S3.Quantum.TensorNetworks.PeriodicMPSRealPolynomialZeros
