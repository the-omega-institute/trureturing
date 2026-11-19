/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFixedEnergy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianFixedEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact original energy coefficient of the literal limiting sewn Gaussian. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFixedExternalCoefficient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open scoped BigOperators Topology
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFixedEnergy
open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open LatticeInvolution SignedOscillatorWick LatticeAllStateField
open SourceBPZ.OriginalSourceCoevaluation
open OriginalNormalRowSource OriginalCorrectedRowRecompositionSource
open OriginalAffineRecompositionSource OriginalFourMChargeCoset
open LatticeHalfFockChargedCoefficients LatticeHalfFockChargedTensorCoefficients
open OriginalChargedRowSource OriginalGaussianExternalBlocks OriginalGaussianSourceMeans
open OriginalGaussianSourceGerm OriginalGaussianSewnAnalytic OriginalGaussianSourceRestriction
open OriginalGaussianFixedExternalCoefficient OriginalSourceInverseCoefficient
open FactorialFockMetric (weight)
open MvPolynomial

/-- The exact original fixed-energy Wick contraction is the twice-energy
ordinary coefficient of the literal limiting sewn Gaussian. Both charge
scalars, four external factorials and the two Laurent selectors remain
literal. The full opposite-charge inverse transport is taken before frequency
restriction. The coefficient divides by (2*n)!, including at n=0. -/
theorem original_fixed_energy_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (betaL gammaL betaR gammaR : Exponent D) (eL eR : ℤ) (n : ℕ) :
    (∑ᶠ alpha : Exponent D, if oscillatorEnergy alpha = n then
      chargeScalar D a * chargeScalar D (-a) *
        wick D (monomial gammaL 1) (oscillatorCorrected D hu a eL
          (monomial alpha 1) (monomial betaL 1)) *
        wick D (monomial gammaR 1) (oscillatorCorrected D hu (-a) eR
          (dualOscillatorMonomial D alpha) (monomial betaR 1)) else 0) =
    let F := fourSupport D betaL gammaL betaR gammaR
    chargeScalar D a * chargeScalar D (-a) *
      (weight betaL : ℂ) * (weight gammaL : ℂ) *
      (weight betaR : ℂ) * (weight gammaR : ℂ) *
      (if eL + chargeNorm D a = -2 * (n : ℤ) -
        Finsupp.weight (fun b => (omega D b : ℤ)) betaL +
        Finsupp.weight (fun b => (omega D b : ℤ)) gammaL then (1 : ℂ) else 0) *
      (if eR + chargeNorm D (-a) = -2 * (n : ℤ) -
        Finsupp.weight (fun b => (omega D b : ℤ)) betaR +
        Finsupp.weight (fun b => (omega D b : ℤ)) gammaR then (1 : ℂ) else 0) *
      coefficient (2 * n) (sewn D a (compactExternal D F)
        (externalOccupation D F betaL gammaL betaR gammaR)) := by
  classical
  let F := fourSupport D betaL gammaL betaR gammaR
  let e := compactExternal D F
  let h := (restricted D F betaL).sumElim (restricted D F gammaL)
  let k := (restricted D F betaR).sumElim (restricted D F gammaR)
  let W : ℂ := chargeScalar D a * chargeScalar D (-a) *
    (weight betaL : ℂ) * (weight gammaL : ℂ) *
    (weight betaR : ℂ) * (weight gammaR : ℂ) *
    (if eL + chargeNorm D a = -2 * (n : ℤ) -
      Finsupp.weight (fun b => (omega D b : ℤ)) betaL +
      Finsupp.weight (fun b => (omega D b : ℤ)) gammaL then (1 : ℂ) else 0) *
    (if eR + chargeNorm D (-a) = -2 * (n : ℤ) -
      Finsupp.weight (fun b => (omega D b : ℤ)) betaR +
      Finsupp.weight (fun b => (omega D b : ℤ)) gammaR then (1 : ℂ) else 0)
  let L : ℂ := ∑ᶠ alpha : Exponent D, if oscillatorEnergy alpha = n then
    chargeScalar D a * chargeScalar D (-a) *
      wick D (monomial gammaL 1) (oscillatorCorrected D hu a eL
        (monomial alpha 1) (monomial betaL 1)) *
      wick D (monomial gammaR 1) (oscillatorCorrected D hu (-a) eR
        (dualOscillatorMonomial D alpha) (monomial betaR 1)) else 0
  change L = W * coefficient (2 * n) (sewn D a e (h.sumElim k))
  have he : ∀ᶠ N : ℕ in atTop,
      L = W * coefficient (2 * n) (finiteSewn D a e (h.sumElim k) N) := by
    filter_upwards [eventually_ge_atTop (max (n + 1) (F.sup (fun b => b.2) + 1))] with N hN
    have hn : n < N := by omega
    have hF : ∀ b ∈ F, b.2 < N := by
      intro b hb
      have hb' : b.2 ≤ F.sup (fun b => b.2) := Finset.le_sup hb
      omega
    have hc := original_fixed_energy_compact D hu a betaL gammaL betaR gammaR eL eR n N hn hF
    have hf := original_finiteSewn_coefficient D hu a N e h k n
    change L = W * _ at hc
    change coefficient (2 * n) (finiteSewn D a e (h.sumElim k) N) = _ at hf
    rw [hf]
    exact hc
  have ht : Tendsto (fun N => W * coefficient (2 * n)
      (finiteSewn D a e (h.sumElim k) N)) atTop
      (𝓝 (W * coefficient (2 * n) (sewn D a e (h.sumElim k)))) :=
    tendsto_const_nhds.mul (finiteSewn_coefficient_tendsto D hu a e (h.sumElim k) (2 * n))
  have ht' : Tendsto (fun _ : ℕ => L) atTop
      (𝓝 (W * coefficient (2 * n) (sewn D a e (h.sumElim k)))) :=
    ht.congr' (he.mono (fun N hN => hN.symm))
  exact tendsto_nhds_unique tendsto_const_nhds ht'

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFixedEnergy
