/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformOrderedCoverNative
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformOrderedCoverNative
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: An irreducible common native cofactor divisor off the basic guard avoids both special spectral equations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformGuardZeroDimension
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformSpecialDivisorExclusion
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformGuardedCriticalDimension

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformOrderedCoverLift

open MvPolynomial
open scoped Matrix
open PeriodicMPSUniformSpecialDivisorExclusion
  (Variable AmbientPolynomials ambientGuard ambientU ambientK coefficientSubstitution
    spectralCoefficients nativeSliceSubstitution Ambient ambientClass ambientNativeCofactor
    nativeCofactor_prime_avoids_special_equations exists_ambientNativeCofactor_not_mem_pullback)
open PeriodicMPSUniformSpecialSpectralBases
  (discriminant eval_discriminant)
open PeriodicMPSUniformSpecialSpectralDomains (Divisor)
open PeriodicMPSUniformSpectralRadicalAlgebra (Determinant)
open PeriodicMPSUniformGuardedCriticalDimension (nativeCofactor)
open PeriodicMPSUniformGuardZeroDimension (NativePolynomials nativeSliceEquiv nativeSliceEquiv_apply)
open private map_spectralCoefficients offDivisorPoint offDivisorPoint_coefficients
  offDivisorQuartic_separable
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformSpecialDivisorExclusion

noncomputable section

/-- The guard for the complex points covered by the simple, nonzero ordered spectrum. -/
def coverGuard : AmbientPolynomials :=
  ambientGuard * coefficientSubstitution (X 2) * coefficientSubstitution discriminant

private theorem eval_coefficientSubstitution (x : Variable → ℂ)
    (p : PeriodicMPSUniformSpecialSpectralBases.CoefficientRing ℂ) :
    eval x (coefficientSubstitution p) = eval (spectralCoefficients x) p := by
  have h : (eval x).comp coefficientSubstitution = eval (spectralCoefficients x) := by
    apply MvPolynomial.ringHom_ext
    · simp [coefficientSubstitution]
    · intro i
      simp only [RingHom.comp_apply, coefficientSubstitution, eval₂Hom_X',
        map_spectralCoefficients, eval_X]
      rw [show (eval x) ∘ (X : Variable → AmbientPolynomials) = x by
        funext j; exact eval_X j]
  exact RingHom.congr_fun h p

theorem eval_coverGuard (x : Variable → ℂ) :
    eval x coverGuard =
      x (some .d) * x (some .db) * x none *
        (spectralCoefficients x 2 - spectralCoefficients x 1 ^ 2) *
        spectralCoefficients x 2 * eval (spectralCoefficients x) discriminant := by
  simp [coverGuard, ambientGuard, ambientU, ambientK, eval_coefficientSubstitution,
    PeriodicMPSUniformSpecialSpectralBases.eval_guard]

theorem coverGuard_ne_zero : coverGuard ≠ 0 := by
  have hdisc : eval ![(-1 : ℂ), 1, 2] discriminant ≠ 0 := by
    rw [eval_discriminant]
    exact fun hz => ((Polynomial.resultant_eq_zero_iff.mp hz).2) offDivisorQuartic_separable
  have hg : eval offDivisorPoint coverGuard ≠ 0 := by
    rw [eval_coverGuard, offDivisorPoint_coefficients]
    norm_num [offDivisorPoint, Fin.isValue] at ⊢
    exact hdisc
  exact fun hz => hg (by rw [hz, map_zero])

def nativeCoverGuard : NativePolynomials := nativeSliceEquiv.symm coverGuard

/-- Away from the basic guard, neither special spectral equation can carry a
native cofactor divisor for the certified lengths. -/
theorem native_commonDivisor_avoids_special {m : ℕ} (hm : 5 ≤ m)
    {r : NativePolynomials} (hr : Irreducible r)
    (hbasic : ¬ nativeSliceEquiv r ∣ ambientGuard)
    (hcof : ∀ i : Fin 10, r ∣ nativeCofactor m i) (z : Divisor) :
    ¬ nativeSliceEquiv r ∣ coefficientSubstitution
      (PeriodicMPSUniformSpecialDivisorExclusion.spectralEquation z) := by
  classical
  let s := nativeSliceEquiv r
  have hs : Irreducible s := hr.map nativeSliceEquiv
  let J : Ideal AmbientPolynomials := Ideal.span {s}
  have hJ : J.IsPrime := Ideal.isPrime_span_singleton_of_prime hs.prime
  have hdisj : Disjoint (Submonoid.powers ambientGuard : Set AmbientPolynomials) ↑J := by
    rw [Set.disjoint_left]
    intro f hf hmem
    obtain ⟨n, rfl⟩ := hf
    exact hbasic (hs.prime.dvd_of_dvd_pow (Ideal.mem_span_singleton.mp hmem))
  let P : Ideal Ambient := J.map ambientClass
  let : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers ambientGuard) Ambient J hJ hdisj
  have hz : ambientClass s ≠ 0 := by
    intro h
    have hg : ambientGuard ≠ 0 := fun e => hbasic (e ▸ dvd_zero s)
    exact hs.ne_zero (IsLocalization.injective Ambient
      (powers_le_nonZeroDivisors_of_noZeroDivisors hg) (h.trans (map_zero _).symm))
  have hspan : P = Ideal.span {ambientClass s} := by
    change J.map ambientClass = _
    rw [show J = Ideal.span {s} by rfl, Ideal.map_span, Set.image_singleton]
  let : Fintype Determinant := Fintype.ofList [.d, .db, .e, .eb] (by
    intro i
    cases i <;> simp)
  let : IsNoetherianRing Ambient :=
    IsLocalization.isNoetherianRing (Submonoid.powers ambientGuard) Ambient inferInstance
  have hP : P.height = 1 := by
    rw [hspan]
    apply Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hz)
    exact fun hu => ‹P.IsPrime›.ne_top (hspan.trans (Ideal.span_singleton_eq_top.mpr hu))
  have hle : PeriodicMPSUniformSpecialDivisorExclusion.nativeCofactorIdeal m ≤ P := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hd := map_dvd nativeSliceEquiv (hcof i)
    rw [nativeSliceEquiv_apply] at hd
    exact Ideal.mem_map_of_mem ambientClass (Ideal.mem_span_singleton.mpr hd)
  intro h
  apply nativeCofactor_prime_avoids_special_equations hm P hP hle z
  exact Ideal.mem_map_of_mem ambientClass (Ideal.mem_span_singleton.mpr h)

/-- The native cofactor ideal is nonzero at every length certified by the special tests. -/
theorem nativeCofactorIdeal_ne_bot {m : ℕ} (hm : 5 ≤ m) :
    PeriodicMPSUniformGuardedCriticalDimension.nativeCofactorIdeal m ≠ ⊥ := by
  obtain ⟨i, hi⟩ := exists_ambientNativeCofactor_not_mem_pullback hm
  intro h
  have hmem : nativeCofactor m i ∈ PeriodicMPSUniformGuardedCriticalDimension.nativeCofactorIdeal m :=
    Ideal.subset_span ⟨i, rfl⟩
  have hz : nativeCofactor m i = 0 := Ideal.mem_bot.mp (h ▸ hmem)
  apply hi .zeroRoot
  change ambientClass (nativeSliceSubstitution (nativeCofactor m i)) ∈ _
  rw [hz, map_zero, map_zero]
  exact Ideal.zero_mem _

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformOrderedCoverLift
