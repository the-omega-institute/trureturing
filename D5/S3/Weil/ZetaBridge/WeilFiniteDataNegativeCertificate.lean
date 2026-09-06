/- GID: D5/S3/Weil/ZetaBridge/WeilFiniteDataNegativeCertificate
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilFiniteDataNegativeCertificate
   mirror-E: none(waiver:finite-data-full-negative-certificate)
   anchors: []
   digest: Discharge the infinite spectral-tail premises of the actual sparse Burnol construction using a proved rational zeta tail; retain only finite geometric and arithmetic certificates. -/

import D5.S3.Weil.ZetaBridge.ExplicitWeilFourthMomentTail
import D5.S3.Weil.ZetaBridge.SparseBurnolPacketJets

/-!
# Full negative certificates from finite data

The actual scalar fourth-moment tail is now proved, rather than supplied.
The first consumer applies it to an already constructed packet. The second
constructs the sparse packet and its derivative budgets from finite nodal
certificates, reusing the existing full-Gram and exact-integer depth owners.
No peak, killer, derivative norm, summability, or infinite tail premise is
supplied to the second theorem. The valid off-line frame and certified finite
node geometry remain genuine inputs; their existence is not asserted.

The numerical cutoff condition T+1<=U is a sufficient finite condition. It
never changes an already constructed exceptional set or assumes that its
killers vanish on additional unhandled nodes. For an independent existing
packet the explicit finite set containment remains visible.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Weil.ZetaBridge.WeilFiniteDataNegativeCertificate

open D5.S3.Weil.ZetaBridge.ExplicitWeilFourthMomentTail
open D5.S3.Weil.ZetaBridge.WeilBurnolCauchyTailBudget

/-- A finite rational calculation: no freely supplied scalar tail remains. -/
def rationalComputedWeilBudget {ι : Type*} [Fintype ι]
    (J0 J2 : ι → ℚ) (T : ℕ) : ℚ :=
  rationalCauchyTailBudget J0 J2 (rationalFourthMomentTail T)

noncomputable section
open Set MeasureTheory Matrix
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.TestFunctions.QuantitativeEvenSeed
open D5.S3.Weil.TestFunctions.SparseEvenInterpolationJets
open D5.S3.Weil.ZetaBridge.FiniteEvenWeilOddInterpolation
open D5.S3.Weil.ZetaBridge.FiniteOrbitBurnolPacket
open D5.S3.Weil.ZetaBridge.MultiOrbitBurnolUniformRemainder
open D5.S3.Weil.ZetaBridge.WeilFullGramInertia
open D5.S3.Weil.ZetaBridge.WeilMixedHeadTailBudget
open D5.S3.Weil.ZetaBridge.BurnolRationalDepthBudget
open D5.S3.Weil.ZetaBridge.QuantitativeMultiOrbitWeilNegativeCertificate
open D5.S3.Weil.ZetaBridge.QuantitativeFiniteWeilPacket
open D5.S3.Weil.ZetaBridge.SparseBurnolPacketJets
open scoped BigOperators Matrix

variable {Z : ZeroData} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual full Gram bound for a supplied packet now needs only its finite
support, two-jet enclosures, finite cutoff containment and rational arithmetic.
Both infinite spectral obligations are derived from zeta's explicit count. -/
theorem computed_packet_full_gram_margin
    (F : FiniteEvenWeilOrbitFrame Z ι) (P : OrbitBurnolPacket F)
    (T : ℕ) (hT : 5 ≤ T)
    (hE : Z.symmetricIndices ((T : ℝ) + 1) ⊆ P.exceptional)
    (J0 J2 : ι → ℚ)
    (hs : ∀ i, tsupport (P.killer i : ℝ → ℂ) ⊆ Icc (-1) 1)
    (h0 : ∀ i, (∫ x : ℝ, ‖P.killer i x‖) ≤ (J0 i : ℝ))
    (h2 : ∀ i, (∫ x : ℝ, ‖((deriv^[2]) (P.killer i : ℝ → ℂ)) x‖) ≤ (J2 i : ℝ))
    (c den p q : ℕ) (hden : 0 < den) (hp : 0 < p) (hq : 0 < q)
    (hround : rationalComputedWeilBudget J0 J2 T ≤ (c : ℚ) / (den : ℚ))
    (N : ℕ) (hN : rationalQuarterDepth c den p q ≤ N) (a : ι → ℂ) :
    (star a ⬝ᵥ ((fullWeilGram Z (burnolBasis F P N)) *ᵥ a)).re ≤
      -(4 - (p : ℝ) / (q : ℝ)) * finiteComplexEnergy a := by
  obtain ⟨hspectral, htail⟩ := zeroData_fourth_moment_tail_rational Z T hT P.exceptional hE
  have hroundQ : rationalCauchyTailBudget J0 J2 (rationalFourthMomentTail T) ≤
      (c : ℚ) / (den : ℚ) := hround
  have hroundR : (rationalCauchyTailBudget J0 J2 (rationalFourthMomentTail T) : ℝ) ≤
      (c : ℝ) / (den : ℝ) := by exact_mod_cast hroundQ
  rw [rationalCauchyTailBudget_cast] at hroundR
  exact cauchy_budget_full_gram_margin F P
    (fun i => (J0 i : ℝ)) (fun i => (J2 i : ℝ)) (rationalFourthMomentTail T)
    hs h0 h2 hspectral htail c den p q hden hp hq hroundR N hN a

/-- Full finite-data assembly. All analytic tail, smooth interpolation and
localization premises are proved in the imported owners. What remains is a
valid actual frame, certified finite radii and nodal gaps, a finite cutoff
comparison, and an exact budget comparison. No RH assumption is used. -/
theorem finite_data_sparse_negative_certificate
    (F : FiniteEvenWeilOrbitFrame Z ι) (R sigma tau : ℝ)
    (hR : 0 ≤ R) (hsigma : 0 < sigma) (htau : 0 < tau)
    (hz : ∀ u : Sum ι ι, ‖(F.nodeEquiv u).1‖ ≤ R)
    (hgap : ∀ u v : Sum ι ι, u ≠ v →
      sigma ≤ ‖(F.nodeEquiv u).1 ^ 2 - (F.nodeEquiv v).1 ^ 2‖)
    (hcross : ∀ u : Sum ι ι, ∀ n ∈ sparsePacketExceptions F R sigma,
      tau ≤ ‖(F.nodeEquiv u).1 ^ 2 - Z.gamma n ^ 2‖)
    (T : ℕ) (hT : 5 ≤ T)
    (hcut : (T : ℝ) + 1 ≤ quantitativePeakRadius (Fintype.card (Sum ι ι)) R sigma)
    (c den p q : ℕ) (hden : 0 < den) (hp : 0 < p) (hq : 0 < q) (hpq : p < 4 * q)
    (hround :
      let J := fun s => sparseJetBudget (Fintype.card (Sum ι ι))
        (sparsePacketExceptions F R sigma).card R
        (quantitativePeakRadius (Fintype.card (Sum ι ι)) R sigma) sigma tau 1 s
      (Fintype.card ι : ℝ) * (3 * (J 0 + J 2)) ^ 2 *
        (rationalFourthMomentTail T : ℝ) ≤ (c : ℝ) / (den : ℝ)) :
    ∃ P : OrbitBurnolPacket F, ∀ N : ℕ, rationalQuarterDepth c den p q ≤ N →
      (-fullWeilGram Z (burnolBasis F P N)).PosDef ∧
      RHLinalg.negIndex (fullWeilGram_isHermitian Z (burnolBasis F P N)) = Fintype.card ι ∧
      ∀ a : ι → ℂ,
        tsupport (burnolSynthesis F P N a : ℝ → ℂ) ⊆
          Icc (-(((N : ℝ) + 2) * quantitativeSeedRadius R))
            (((N : ℝ) + 2) * quantitativeSeedRadius R) ∧
        (star a ⬝ᵥ ((fullWeilGram Z (burnolBasis F P N)) *ᵥ a)).re ≤
          -(4 - (p : ℝ) / (q : ℝ)) * finiteComplexEnergy a := by
  let U := quantitativePeakRadius (Fintype.card (Sum ι ι)) R sigma
  let E := Z.symmetricIndices U ∪ frameTargetIndices F
  have hE : Z.symmetricIndices ((T : ℝ) + 1) ⊆ E := by
    intro n hn
    refine Finset.mem_union_left (frameTargetIndices F) ?_
    apply Z.mem_symmetricIndices.mpr
    exact (Z.mem_symmetricIndices.mp hn).trans hcut
  obtain ⟨hspectral, htail⟩ := zeroData_fourth_moment_tail_rational Z T hT E hE
  exact sparse_packet_computed_support_margin_and_inertia
    F R sigma tau (rationalFourthMomentTail T) hR hsigma htau hz hgap hcross
    hspectral htail c den p q hden hp hq hpq hround

-- These are arithmetic regressions, not numerical zero certificates.
example : fourthTailLogCeiling 20 = 5 := by decide
example : rationalFourthMomentTail 20 = (47 / 375 : ℚ) := by
  norm_num [rationalFourthMomentTail,
    show fourthTailLogCeiling 20 = 5 by decide]

#print axioms computed_packet_full_gram_margin
#print axioms finite_data_sparse_negative_certificate

end
end D5.S3.Weil.ZetaBridge.WeilFiniteDataNegativeCertificate
