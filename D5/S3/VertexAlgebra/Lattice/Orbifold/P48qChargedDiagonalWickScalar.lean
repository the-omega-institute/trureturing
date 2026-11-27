/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qChargedDiagonalWickScalar
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integrated singleton and pair contractions recover the charged scalar logarithm. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qAllJetWickField
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedDiagonalScalar
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedFieldTranslation

/-!
The singleton and pair weights of the P48q Wick field recover the charged
diagonal scalar logarithm after integration over the positive jet levels.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

open LatticeGeneratingFieldLocality (Charge bilinear)
open P48qTwistedChargeAction (lattice g Momentum)
open P48qTwistedHeisenberg (project projectAt projectAt_eq_fourier project_action project_of_action)
open ThirdEigenspacePairing (p48qForm)
open P48qAllJetWickField (singletonWeight pairWeight)
open P48qIntegratedJetKernels (integratedScalarKernel integratedScalarKernel_zero
  integratedPairKernel oppositeResidue_cancellation)
open P48qChargedFieldTranslation (weighted_projection_pairing_eq_neg_bShift)
open Finset.HasAntidiagonal (antidiagonal)
open PowerSeries (C)
open scoped BigOperators

open private formSymmetric zetaPrimitive from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
open private project_adjoint from D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg
open private momentumExponent_div from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedFieldTranslation

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "bShift" => ThirdTwistedChargeAction.bShift lattice g
local notation "A" => fun a c (j : ℕ) =>
  p48qForm (projectAt (j : ℤ) (chargeVector a)) (chargeVector c)

/-- Integrate the actual singleton weight in each positive jet degree. -/
def integratedJetMean (a c : Charge lattice) : PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    if hn : 0 < n then singletonWeight c (chargeVector a, ⟨n, hn⟩) / (n : ℂ) else 0

/-- Integrate the actual pair weight and sum over the positive antidiagonal. -/
def integratedJetPair (a : Charge lattice) : PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    ∑ v ∈ antidiagonal n,
      if hv : 0 < v.1 ∧ 0 < v.2 then
        pairWeight (chargeVector a, ⟨v.1, hv.1⟩) (chargeVector a, ⟨v.2, hv.2⟩) /
          ((v.1 : ℂ) * (v.2 : ℂ))
      else 0

private theorem integratedJetMean_eq (a c : Charge lattice) :
    integratedJetMean a c =
      ∑ j ∈ Finset.range 3, A a c j • integratedScalarKernel ((j : ℂ) / 3) := by
  apply PowerSeries.ext
  intro n
  simp only [integratedJetMean, PowerSeries.coeff_mk, map_sum, PowerSeries.coeff_smul,
    P48qIntegratedJetKernels.coeff_integratedScalarKernel]
  by_cases hn : n = 0
  · simp [hn]
  · rw [dite_eq_left (Nat.pos_of_ne_zero hn)]
    simp only [singletonWeight, PNat.mk_coe, ite_eq_right hn,
      div_eq_mul_inv, Finset.sum_mul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring

private theorem moving_self_pairings (a : Charge lattice) :
    A a a 1 = -(bShift a : ℂ) ∧ A a a 2 = -(bShift a : ℂ) ∧
      p48qForm (projectAt 1 (chargeVector a)) (projectAt 2 (chargeVector a)) =
        -(bShift a : ℂ) := by
  let u := chargeVector a
  have hζ : ζ ^ 3 = 1 := zetaPrimitive.pow_eq_one
  have hζ₂ : (ζ ^ 2) ^ 3 = 1 := by rw [pow_right_comm, hζ, one_pow]
  have hproj₁ : projectAt 1 u = project ζ u := by
    rw [projectAt_eq_fourier, show ((1 : ℤ) % 3).toNat = 1 by decide, pow_one]
  have hproj₂ : projectAt 2 u = project (ζ ^ 2) u := by
    rw [projectAt_eq_fourier, show ((2 : ℤ) % 3).toNat = 2 by decide]
  have hself : A a a 1 = A a a 2 := by
    change p48qForm (projectAt 1 u) u = p48qForm (projectAt 2 u) u
    rw [hproj₁, hproj₂]
    exact (project_adjoint ζ hζ u u).trans (formSymmetric.eq _ _)
  have hweighted := weighted_projection_pairing_eq_neg_bShift a
  change (1 / 3 : ℂ) * A a a 1 + (2 / 3 : ℂ) * A a a 2 = _ at hweighted
  rw [← hself] at hweighted
  have hshift : A a a 1 = -(bShift a : ℂ) := by linear_combination hweighted
  refine ⟨hshift, hself.symm.trans hshift, ?_⟩
  change p48qForm (projectAt 1 u) (projectAt 2 u) = _
  rw [hproj₁, hproj₂]
  calc
    _ = p48qForm u (project (ζ ^ 2) u) := by
      rw [project_adjoint ζ hζ,
        project_of_action _ hζ₂ _ (project_action _ hζ₂ u)]
    _ = A a a 1 := by
      change _ = p48qForm (projectAt 1 u) u
      rw [hproj₁]
      exact (project_adjoint ζ hζ u u).symm
    _ = _ := hshift

private theorem integratedJetPair_eq (a : Charge lattice) :
    integratedJetPair a = (-(bShift a : ℂ)) •
      (integratedPairKernel ((1 : ℂ) / 3) + integratedPairKernel ((2 : ℂ) / 3)) := by
  obtain ⟨_, _, hpair⟩ := moving_self_pairings a
  have hswap : p48qForm (projectAt 2 (chargeVector a)) (projectAt 1 (chargeVector a)) =
      -(bShift a : ℂ) :=
    (formSymmetric.eq _ _).trans hpair
  apply PowerSeries.ext
  intro n
  simp only [integratedJetPair, integratedPairKernel, PowerSeries.coeff_mk,
    PowerSeries.coeff_smul, map_add, smul_eq_mul, ← Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : 0 < v.1 ∧ 0 < v.2
  · simp only [dite_eq_left hv, ite_eq_left hv, pairWeight, PNat.mk_coe,
      hpair, hswap, div_eq_mul_inv]
    ring
  · simp [hv]

/-- The charged diagonal logarithm is the input zero mode, the integrated
singleton weight on the total charge, and half the integrated pair weight. -/
theorem chargedIterateLog_eq_jetKernels (a b : Charge lattice) (p : Momentum) :
    chargedIterateLog a b p =
      C ((bilinear lattice a p.1 : ℂ) / 3) * PowerSeries.log ℂ +
        integratedJetMean a (a + b) + C ((1 : ℂ) / 2) * integratedJetPair a := by
  have hcharge : chargeVector (a + b) = chargeVector a + chargeVector b := by
    funext i
    exact Int.cast_add (a i) (b i)
  have hAdd (j : ℕ) : A a (a + b) j = A a a j + A a b j := by
    simp only [hcharge, LinearMap.BilinForm.add_right]
  obtain ⟨h₁, h₂, _⟩ := moving_self_pairings a
  change p48qForm (projectAt 1 (chargeVector a)) (chargeVector a) = _ at h₁
  change p48qForm (projectAt 2 (chargeVector a)) (chargeVector a) = _ at h₂
  have hcancel := oppositeResidue_cancellation ((1 : ℂ) / 3) (-(bShift a : ℂ))
    (p48qForm (projectAt 1 (chargeVector a)) (chargeVector b))
    (p48qForm (projectAt 2 (chargeVector a)) (chargeVector b))
  rw [show 1 - (1 : ℂ) / 3 = (2 : ℂ) / 3 by ring, neg_neg] at hcancel
  simp only [chargedIterateLog, integratedJetMean_eq, integratedJetPair_eq,
    ← PowerSeries.smul_eq_C_mul, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.cast_zero, zero_div, integratedScalarKernel_zero, smul_zero, Nat.cast_one, Nat.cast_ofNat,
    hAdd, h₁, h₂, momentumExponent_div, smul_smul]
  rw [add_smul, show ((1 : ℂ) / 2) * -(bShift a : ℂ) = (-(bShift a : ℂ)) / 2 by ring]
  conv_rhs => rw [add_assoc, hcancel]
  abel

#print axioms integratedJetMean
#print axioms integratedJetPair
#print axioms chargedIterateLog_eq_jetKernels

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
