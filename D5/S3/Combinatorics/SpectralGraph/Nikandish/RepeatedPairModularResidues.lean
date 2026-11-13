/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairModularResidues
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairModularResidues
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full odd-prime discriminant and binary parity consequences of tensor splitting. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.RepeatedPairModular

/-! Source: repeated-pair-modular, PR9
6d491f77b35dec808fc777b69939c56cdae5dc02. Residue tests remain necessary
conditions only. The arbitrary-prime theorem is supplied by
RepeatedPairModular; finite prime rows are its actual graph consumers.
The escape audit is unfinished, disclosed in issue #28398. -/
set_option autoImplicit false
noncomputable section
open Finset Matrix Polynomial
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.RepeatedPairModularResidues
open RepeatedPairSupport RepeatedPairModular
open IdealIntersectionSupport IdealIntersectionObstructions
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The full trace-one quadratic has a root exactly when it splits. -/
theorem quadratic_splits_iff_root {F : Type*} [Field F] (k : F) :
    (X^2-X-C k).Splits ↔ ∃ r : F, r^2-r-k=0 := by
  have hd : (X^2-X-C k).natDegree=2 := by compute_degree <;> norm_num
  constructor
  · intro hs
    obtain ⟨r,hr⟩ := hs.exists_eval_eq_zero
      (Polynomial.degree_ne_of_natDegree_ne (by rw [hd]; norm_num))
    exact ⟨r,by simpa using hr⟩
  · rintro ⟨r,hr⟩
    apply Polynomial.Splits.of_natDegree_eq_two hd
    simpa using hr

/-- Completing the square, with zero discriminant explicitly allowed. -/
theorem quadratic_splits_iff_square {F : Type*} [Field F] (k : F)
    (h2 : (2 : F) ≠ 0) :
    (X^2-X-C k).Splits ↔ IsSquare (1+4*k) := by
  rw [quadratic_splits_iff_root]
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨2*r-1,?_⟩
    linear_combination -4*hr
  · rintro ⟨u,hu⟩
    refine ⟨(u+1)/2,?_⟩
    field_simp [h2]
    linear_combination -hu

/-- Binary splitting is equivalent to even tail exponent. -/
theorem binary_splits_iff (k : ℕ) :
    (X^2-X-C (k : ZMod 2)).Splits ↔ 2 ∣ k := by
  rw [quadratic_splits_iff_root]
  constructor
  · rintro ⟨r,hr⟩
    have hzero : ∀ x : ZMod 2, x^2-x=0 := by decide +kernel
    have hk : (k : ZMod 2)=0 := by
      linear_combination hzero r-hr
    exact (ZMod.natCast_eq_zero_iff _ _).mp hk
  · intro hk
    refine ⟨0,?_⟩
    have hz : (k : ZMod 2)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr hk
    simp [hz]

/-- All tails must be even whenever the repeated exponent is odd. -/
theorem actual_binary_tails (p : Fin 2 ⊕ ι → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (a : ℕ) (k : ι → ℕ) (ha : 0 < a) (hk : ∀ i, 0 < k i)
    (H : ActualLaplacianIntegral (modulus p (pairExponents a k)))
    (ha2 : 2 ∣ a+1) : ∀ i, 2 ∣ k i := by
  intro i
  exact (binary_splits_iff (k i)).mp (actual_prime_splits p hp hinj a k ha hk H 2 ha2 i)

/-- Any odd tail rules out actual integrality, for every finite tail set. -/
theorem actual_odd_pair_obstruction (p : Fin 2 ⊕ ι → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (a : ℕ) (k : ι → ℕ) (ha : 0 < a) (hk : ∀ i, 0 < k i)
    (ha2 : a%2=1) (i : ι) (hi : k i%2=1) :
    ¬ActualLaplacianIntegral (modulus p (pairExponents a k)) := by
  intro H
  have h := actual_binary_tails p hp hinj a k ha hk H (by omega) i
  exact (Nat.dvd_iff_mod_eq_zero.mp h |> fun h => by omega)

/-- Every odd characteristic prime divisor imposes the exact square test. -/
theorem actual_prime_discriminant (p : Fin 2 ⊕ ι → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (a : ℕ) (k : ι → ℕ) (ha : 0 < a) (hk : ∀ i, 0 < k i)
    (H : ActualLaplacianIntegral (modulus p (pairExponents a k)))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ∣ a+1) (hodd : ℓ ≠ 2) :
    ∀ i, IsSquare (1+4*(k i : ZMod ℓ)) := by
  have h2 : (2 : ZMod ℓ) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 ℓ).mp h
    exact hodd ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left
      ((Fact.out : ℓ.Prime).ne_one))
  intro i
  exact (quadratic_splits_iff_square _ h2).mp
    (actual_prime_splits p hp hinj a k ha hk H ℓ hℓ i)

end D5.S3.Combinatorics.SpectralGraph.RepeatedPairModularResidues
