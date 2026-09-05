/- GID: D5/S3/Weil/ZetaBridge/RationalWeilJetBudget
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/RationalWeilJetBudget
   mirror-E: none(waiver:rational-two-jet-budget-verifier)
   anchors: []
   digest: Compute the family majorant from rational two-jet enclosures and a scalar spectral budget, then certify the exact common depth and support radius on the actual full Gram. -/

import D5.S3.Weil.ZetaBridge.UnitSupportBurnolPacket

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Weil.ZetaBridge.RationalWeilJetBudget

open scoped BigOperators
variable {ι : Type*} [Fintype ι]

/-- Executable rational arithmetic on a finite list of certified data. -/
def rationalJetMajorant (J0 J2 : ι → ℚ) (H Theta : ℚ) : ℚ :=
  (∑ i, 3 * (J0 i + J2 i)) ^ 2 * (H + Theta)

/-- Finite spectral-head arithmetic from multiplicity upper bounds and
nonnegative lower bounds on absolute ordinates. -/
def rationalSpectralHead (E : Finset ℕ) (M : ℕ → ℕ) (lower : ℕ → ℚ) : ℚ :=
  ∑ n ∈ E, (M n : ℚ) / (1 + lower n ^ 2) ^ 2

noncomputable section
open Set MeasureTheory Matrix
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZetaBridge.FiniteEvenWeilOddInterpolation
open D5.S3.Weil.ZetaBridge.FiniteOrbitBurnolPacket
open D5.S3.Weil.ZetaBridge.FiniteMixedWeilMajorant
open D5.S3.Weil.ZetaBridge.MultiOrbitBurnolUniformRemainder
open D5.S3.Weil.ZetaBridge.QuantitativeMultiOrbitWeilNegativeCertificate
open D5.S3.Weil.ZetaBridge.WeilFullGramInertia
open D5.S3.Weil.ZetaBridge.WeilMixedHeadTailBudget
open D5.S3.Weil.ZetaBridge.BurnolRationalDepthBudget
open D5.S3.Weil.ZetaBridge.UnitSupportBurnolPacket
open scoped Matrix

/-- A certified lower ordinate and upper multiplicity give one rational
head contribution. Endpoints use ordinary full multiplicity, with no half weights. -/
theorem fourthMomentSummand_le_rational_enclosure
    (Z : ZeroData) (n M : ℕ) (lower : ℚ)
    (hl : 0 ≤ lower) (hm : Z.multiplicity n ≤ M)
    (ht : (lower : ℝ) ≤ |(Z.gamma n).re|) :
    fourthMomentSummand Z n ≤ ((M : ℚ) / (1 + lower ^ 2) ^ 2 : ℚ) := by
  have hl' : (0 : ℝ) ≤ lower := by exact_mod_cast hl
  have hm' : (Z.multiplicity n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hm
  have hs : (lower : ℝ) ^ 2 ≤ (Z.gamma n).re ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr ht)
      (add_nonneg (abs_nonneg (Z.gamma n).re) hl')
    nlinarith [sq_abs (Z.gamma n).re]
  have hden : (1 + (lower : ℝ) ^ 2) ^ 2 ≤ (1 + (Z.gamma n).re ^ 2) ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hs)
      (show 0 ≤ 2 + (Z.gamma n).re ^ 2 + (lower : ℝ) ^ 2 by positivity)
    nlinarith
  have heq : fourthMomentSummand Z n =
      (Z.multiplicity n : ℝ) / (1 + (Z.gamma n).re ^ 2) ^ 2 := by
    unfold fourthMomentSummand inverseQuadraticEnvelope
    rw [← inv_pow, div_eq_mul_inv]
  rw [heq]
  have hcast : (((M : ℚ) / (1 + lower ^ 2) ^ 2 : ℚ) : ℝ) =
      (M : ℝ) / (1 + (lower : ℝ) ^ 2) ^ 2 := by push_cast; rfl
  rw [hcast]
  exact (div_le_div_of_nonneg_right hm' (by positivity)).trans
    (div_le_div_of_nonneg_left (Nat.cast_nonneg M) (by positivity) hden)

/-- Summing certified enclosures yields the finite spectral head used below. -/
theorem rationalSpectralHead_sound
    (Z : ZeroData) (E : Finset ℕ) (M : ℕ → ℕ) (lower : ℕ → ℚ)
    (hl : ∀ n ∈ E, 0 ≤ lower n)
    (hm : ∀ n ∈ E, Z.multiplicity n ≤ M n)
    (ht : ∀ n ∈ E, (lower n : ℝ) ≤ |(Z.gamma n).re|) :
    (∑ n ∈ E, fourthMomentSummand Z n) ≤ (rationalSpectralHead E M lower : ℝ) := by
  unfold rationalSpectralHead
  push_cast
  apply Finset.sum_le_sum
  intro n hn
  have h := fourthMomentSummand_le_rational_enclosure Z n (M n) (lower n)
    (hl n hn) (hm n hn) (ht n hn)
  push_cast at h
  exact h

/-- The actual infinite mixed-majorant bound follows from a finite rational
calculation and the stated analytic enclosures. There is no assumed C-bound. -/
theorem rationalJetMajorant_sound
    (Z : ZeroData) (g : ι → WeilTestFunction) (E : Finset ℕ)
    (J0 J2 : ι → ℚ) (H Theta : ℚ)
    (hs : ∀ i, tsupport (g i : ℝ → ℂ) ⊆ Icc (-1) 1)
    (hJ0 : ∀ i, (∫ x : ℝ, ‖g i x‖) ≤ (J0 i : ℝ))
    (hJ2 : ∀ i, (∫ x : ℝ, ‖((deriv^[2]) (g i : ℝ → ℂ)) x‖) ≤ (J2 i : ℝ))
    (hhead : (∑ n ∈ E, fourthMomentSummand Z n) ≤ (H : ℝ))
    (hspectral : Summable (fun n : {n : ℕ // n ∉ E} => fourthMomentSummand Z n.1))
    (htail : (∑' n : {n : ℕ // n ∉ E}, fourthMomentSummand Z n.1) ≤ (Theta : ℝ)) :
    finiteMixedMajorantTotal Z g ≤ (rationalJetMajorant J0 J2 H Theta : ℝ) := by
  have hb := finiteMixedMajorantTotal_le_unit_support_jets Z g E
    (fun i => (J0 i : ℝ)) (fun i => (J2 i : ℝ)) (Theta : ℝ) hs hJ0 hJ2 hspectral htail
  have hc := mul_le_mul_of_nonneg_left (add_le_add_right hhead (Theta : ℝ))
    (sq_nonneg (∑ i, 3 * ((J0 i : ℝ) + (J2 i : ℝ))))
  have hcast : (rationalJetMajorant J0 J2 H Theta : ℝ) =
      (∑ i, 3 * ((J0 i : ℝ) + (J2 i : ℝ))) ^ 2 * ((H : ℝ) + (Theta : ℝ)) := by
    simp [rationalJetMajorant]
  rw [hcast]
  exact hb.trans hc

/-- The rational budget controls the actual full Gram and the support at every
computed admissible depth. The only infinite analytic input is the scalar
spectral tail; a citation to BPT alone does not discharge that premise. -/
theorem rational_unit_packet_support_and_margin
    {Z : ZeroData} [DecidableEq ι]
    (F : FiniteEvenWeilOrbitFrame Z ι) (P : OrbitBurnolPacket F)
    (E : Finset ℕ) (J0 J2 : ι → ℚ) (H Theta : ℚ)
    (hpSupport : tsupport (P.peak : ℝ → ℂ) ⊆ Icc (-1) 1)
    (hkSupport : ∀ i, tsupport (P.killer i : ℝ → ℂ) ⊆ Icc (-1) 1)
    (hJ0 : ∀ i, (∫ x : ℝ, ‖P.killer i x‖) ≤ (J0 i : ℝ))
    (hJ2 : ∀ i, (∫ x : ℝ, ‖((deriv^[2]) (P.killer i : ℝ → ℂ)) x‖) ≤ (J2 i : ℝ))
    (hhead : (∑ n ∈ E, fourthMomentSummand Z n) ≤ (H : ℝ))
    (hspectral : Summable (fun n : {n : ℕ // n ∉ E} => fourthMomentSummand Z n.1))
    (htail : (∑' n : {n : ℕ // n ∉ E}, fourthMomentSummand Z n.1) ≤ (Theta : ℝ))
    (c d p q : ℕ) (hd : 0 < d) (hp : 0 < p) (hq : 0 < q)
    (hround : rationalJetMajorant J0 J2 H Theta ≤ (c : ℚ) / (d : ℚ))
    (N : ℕ) (hN : rationalQuarterDepth c d p q ≤ N) (a : ι → ℂ) :
    tsupport (burnolSynthesis F P N a : ℝ → ℂ) ⊆
        Icc (-((N : ℝ) + 2)) ((N : ℝ) + 2) ∧
      (star a ⬝ᵥ ((fullWeilGram Z (burnolBasis F P N)) *ᵥ a)).re ≤
        -(4 - (p : ℝ) / (q : ℝ)) * finiteComplexEnergy a := by
  have hb := rationalJetMajorant_sound Z P.killer E J0 J2 H Theta
    hkSupport hJ0 hJ2 hhead hspectral htail
  have hr : (rationalJetMajorant J0 J2 H Theta : ℝ) ≤ (c : ℝ) / (d : ℝ) := by
    exact_mod_cast hround
  exact ⟨unit_support_burnol_radius F P hpSupport hkSupport N a,
    rationalQuarterDepth_full_gram_margin F P c d p q hd hp hq (hb.trans hr) N hN a⟩

-- Arithmetic-only regression. These values are not measurements of any zeta frame.
example : rationalQuarterDepth 1000000 1 1 2 = 10 := by decide
example : rationalBurnolRadius 1 1 10 = 12 := by norm_num [rationalBurnolRadius]

#print axioms fourthMomentSummand_le_rational_enclosure
#print axioms rationalSpectralHead_sound
#print axioms rationalJetMajorant_sound
#print axioms rational_unit_packet_support_and_margin

end
end D5.S3.Weil.ZetaBridge.RationalWeilJetBudget
