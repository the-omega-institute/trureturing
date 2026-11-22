/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteProjectiveLine
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteProjectiveLine
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.Resultant.Basic]
   utility: none
   digest: The two six-site critical minors have coprime full-degree line restrictions. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteLineBezout
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteWeightedMinors
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! The residual-minor identities interpolate over the residue field and lift by a resultant. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteProjectiveLine

open PeriodicMPSFiveSiteLineMinors (line)
open Polynomial PeriodicMPSSixSiteLineBezout PeriodicMPSSixSiteLineMinors
  PeriodicMPSSixSiteWeightedMinors

local instance : Fact (Nat.Prime 1009) := ⟨by norm_num⟩

noncomputable section

/-- The integral polynomial restriction of a residual minor. -/
def linePolynomial (k : Fin 10) : ℤ[X] := residualMinor (Polynomial.X : ℤ[X]) k

private abbrev reduceCoefficients : ℤ →+* F := Int.castRingHom F

private theorem degree_bound (k : Fin 10) (hk : k = 0 ∨ k = 1) :
    (linePolynomial k).natDegree ≤ 93 := by
  rw [linePolynomial, ← evaluated_symbolicMinor]
  exact line_degree_bound k hk

private theorem distinct_points : Function.Injective (fun t : Fin 94 => ((t : ℕ) : F)) := by
  intro x y h
  apply Fin.ext
  have hx : (x : ℕ) < 1009 := x.isLt.trans (by decide)
  have hy : (y : ℕ) < 1009 := y.isLt.trans (by decide)
  simpa only [ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy] using congrArg ZMod.val h

private theorem identify_modular_polynomial (k : Fin 10) (hk : k = 0 ∨ k = 1)
    (p : F[X]) (hp : p.natDegree = 93)
    (heval : ∀ t : Fin 94, residualMinor ((t : ℕ) : F) k = p.eval ((t : ℕ) : F)) :
    (linePolynomial k).map reduceCoefficients = p := by
  apply eq_of_natDegree_lt_card_of_eval_eq _ _ distinct_points
  · intro t
    rw [eval_map, linePolynomial, eval₂_minor]
    exact heval t
  · have hle : ((linePolynomial k).map reduceCoefficients).natDegree ≤ 93 :=
      natDegree_map_le.trans (degree_bound k hk)
    simpa [Fintype.card_fin, hp] using Nat.lt_succ_of_le (max_le hle hp.le)

private theorem full_integral_degree (k : Fin 10) (hk : k = 0 ∨ k = 1)
    (p : F[X]) (hp : p.natDegree = 93) (hmap : (linePolynomial k).map reduceCoefficients = p) :
    (linePolynomial k).natDegree = 93 := by
  refine le_antisymm (degree_bound k hk) ?_
  rw [← hp, ← hmap]
  exact natDegree_map_le

theorem integral_certificate_of_point_values
    (h₀ : ∀ t : Fin 94, residualMinor ((t : ℕ) : F) 0 = firstValue ((t : ℕ) : F))
    (h₁ : ∀ t : Fin 94, residualMinor ((t : ℕ) : F) 1 = secondValue ((t : ℕ) : F)) :
    (linePolynomial 0).natDegree = 93 ∧ (linePolynomial 1).natDegree = 93 ∧
      resultant (linePolynomial 0) (linePolynomial 1) 93 93 ≠ 0 := by
  have hm₀ := identify_modular_polynomial 0 (.inl rfl) firstPolynomial first_natDegree
    (fun t => (h₀ t).trans (first_eval _).symm)
  have hm₁ := identify_modular_polynomial 1 (.inr rfl) secondPolynomial second_natDegree
    (fun t => (h₁ t).trans (second_eval _).symm)
  refine ⟨full_integral_degree 0 (.inl rfl) _ first_natDegree hm₀,
    full_integral_degree 1 (.inr rfl) _ second_natDegree hm₁, ?_⟩
  intro hz
  have hne := resultant_ne_zero _ _ coprime_line_restrictions
  rw [first_natDegree, second_natDegree, ← hm₀, ← hm₁, resultant_map_map, hz, map_zero] at hne
  exact hne rfl

/-- Full-degree integral restrictions with a nonzero resultant stay coprime over
every characteristic-zero field. -/
theorem charZero_certificate_of_integral {K : Type*} [Field K] [CharZero K]
    (h₀ : (linePolynomial 0).natDegree = 93) (h₁ : (linePolynomial 1).natDegree = 93)
    (hres : resultant (linePolynomial 0) (linePolynomial 1) 93 93 ≠ 0) :
    IsCoprime (residualMinor (Polynomial.X : K[X]) 0) (residualMinor (Polynomial.X : K[X]) 1) := by
  let f : ℤ →+* K := Int.castRingHom K
  have hf : Function.Injective f := Int.cast_injective
  have hmap (k : Fin 10) :
      (linePolynomial k).map f = residualMinor (Polynomial.X : K[X]) k := by
    simpa [linePolynomial] using map_minor (Polynomial.mapRingHom f) Polynomial.X k
  rw [← hmap, ← hmap]
  by_contra hc
  have hz := resultant_eq_zero_iff.mpr
    ⟨.inl (by
      intro hz
      have hd := natDegree_map_eq_of_injective hf (p := linePolynomial 0)
      rw [hz, natDegree_zero, h₀] at hd
      omega), hc⟩
  rw [natDegree_map_eq_of_injective hf, natDegree_map_eq_of_injective hf, h₀, h₁,
    resultant_map_map] at hz
  exact hres (hf (hz.trans (map_zero f).symm))

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteProjectiveLine
