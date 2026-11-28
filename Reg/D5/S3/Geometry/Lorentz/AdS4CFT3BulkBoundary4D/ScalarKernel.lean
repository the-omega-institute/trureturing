import D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D
import Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.Common

/-! Source laws and interventions for the AdS scalar kernel. -/

open _root_.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Real Set Filter
open OmegaMath.ConformalHalfSpaceKernel hiding metric
open scoped Matrix Topology

namespace Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace KleinGordon

abbrev signature : Signature := operandSignature (ℝ) (ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {σ Δ z t x y : ℝ} (L : ℝ) (hσ : σ ^ 2 = 1) (hz : 0 < z)
    (hs : 0 < denominator σ z t x y),
    let S := denominator σ z t x y
    let K := ads4Propagator σ Δ z t x y
    let fz := fun u => ads4Propagator σ Δ u t x y
    let ft := fun u => ads4Propagator σ Δ z u x y
    let fx := fun u => ads4Propagator σ Δ z t u y
    let fy := fun u => ads4Propagator σ Δ z t x u
    (HasDerivAt fz (radialSlope Δ z S * K) z ∧
      HasDerivAt (deriv fz) (radialCurvature Δ z S * K) z) ∧
    (HasDerivAt ft (transverseSlope Δ σ t S * K) t ∧
      HasDerivAt (deriv ft) (transverseCurvature Δ σ t S * K) t) ∧
    (HasDerivAt fx (transverseSlope Δ 1 x S * K) x ∧
      HasDerivAt (deriv fx) (transverseCurvature Δ 1 x S * K) x) ∧
    (HasDerivAt fy (transverseSlope Δ 1 y S * K) y ∧
      HasDerivAt (deriv fy) (transverseCurvature Δ 1 y S * K) y) ∧
    ads4Wave σ L z t x y (ads4Propagator σ Δ) =
      R.readout () () L Δ * ads4Propagator σ Δ z t x y

def family : Registration arena (type_of% (@ads4_propagator_solves_klein_gordon)) :=
  adsFamily% arena (@ads4_propagator_solves_klein_gordon) (adsObserve% (ads4MassFromDim))
    (adsObserve% (fun _ _ => 0))
    (by
      intro h
      have hs : 0 < denominator 1 1 0 0 0 := by norm_num [denominator]
      have e := h (σ := 1) (Δ := 1) 1 (by norm_num) (by norm_num) hs
      have e' := ads4_propagator_solves_klein_gordon (σ := 1) (Δ := 1) 1
        (by norm_num) (by norm_num) hs
      have q := e'.2.2.2.2.symm.trans e.2.2.2.2
      norm_num [realize, ads4MassFromDim, ads4Propagator, kernel, denominator, Real.rpow_one] at q)
    (by
      refine ⟨(), 1, 2, ?_⟩
      intro h
      have e := congrFun h 1
      norm_num [realize, ads4MassFromDim] at e)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ads4_propagator_solves_klein_gordon) (Realization signature) Unit Unit :=
  adsBind% `D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.ads4_propagator_solves_klein_gordon.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.KleinGordon.family
    arena family (adsObserve% (ads4MassFromDim)) #[]
    #[{ path := adsPath% ads4_propagator_solves_klein_gordon ads4MassFromDim 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end KleinGordon

namespace BoundaryLimit

abbrev signature : Signature := operandSignature (ℝ) (ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (Δ t x y : ℝ) (hr : 0 < t ^ 2 + x ^ 2 + y ^ 2),
    Tendsto (fun z : ℝ => z ^ (-Δ) * R.readout () () 1 Δ z t x y) (𝓝[>] 0)
      (𝓝 (sqrt (t ^ 2 + x ^ 2 + y ^ 2) ^ (-2 * Δ)))

def family : Registration arena (type_of% (@ads4_propagator_boundary_limit)) :=
  adsFamily% arena (@ads4_propagator_boundary_limit) (adsObserve% (ads4Propagator))
    (adsObserve% (fun _ _ _ _ _ _ => 0))
    (by
      intro h
      have e := h 1 1 0 0 (by norm_num)
      have e' : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
        simpa [realize] using e
      exact zero_ne_one (tendsto_const_nhds_iff.mp e'))
    (by
      refine ⟨(), 1, -1, ?_⟩
      intro h
      have e := congrArg (fun f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ => f 1 2 1 0 0) h
      norm_num [realize, ads4Propagator, kernel, denominator, Real.rpow_one] at e)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ads4_propagator_boundary_limit) (Realization signature) Unit Unit :=
  adsBind% `D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.ads4_propagator_boundary_limit.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.BoundaryLimit.family
    arena family (adsObserve% (ads4Propagator)) #[]
    #[{ path := adsPath% ads4_propagator_boundary_limit ads4Propagator 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end BoundaryLimit

namespace ScalingAndInversion

abbrev signature : Signature := operandSignature (ℝ) (ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {σ Δ L z t x y : ℝ} (dz dt dx dy : ℝ) (hz : 0 < z)
    (hs : 0 < denominator σ z t x y),
    let S := denominator σ z t x y
    let dS := denominatorVelocity σ z t x y dz dt dx dy
    (∀ a > 0, R.readout () () σ Δ (a * z) (a * t) (a * x) (a * y) =
       a ^ (-Δ) * ads4Propagator σ Δ z t x y) ∧
    (0 < inverseCoordinate S z ∧
      denominator σ (inverseCoordinate S z) (inverseCoordinate S t)
        (inverseCoordinate S x) (inverseCoordinate S y) = 1 / S) ∧
    OmegaMath.ConformalHalfSpaceKernel.metric σ L (inverseCoordinate S z)
      (inverseVelocity S dS z dz) (inverseVelocity S dS t dt)
      (inverseVelocity S dS x dx) (inverseVelocity S dS y dy) =
        OmegaMath.ConformalHalfSpaceKernel.metric σ L z dz dt dx dy ∧
    ads4Propagator σ Δ z t x y = inverseCoordinate S z ^ Δ ∧
    (let S' := denominator σ (inverseCoordinate S z) (inverseCoordinate S t)
        (inverseCoordinate S x) (inverseCoordinate S y)
     inverseCoordinate S' (inverseCoordinate S z) = z ∧
       inverseCoordinate S' (inverseCoordinate S t) = t ∧
       inverseCoordinate S' (inverseCoordinate S x) = x ∧
       inverseCoordinate S' (inverseCoordinate S y) = y)

def family : Registration arena (type_of% (@ads4_propagator_boundary_scaling_and_inversion)) :=
  adsFamily% arena (@ads4_propagator_boundary_scaling_and_inversion) (adsObserve% (ads4Propagator))
    (adsObserve% (fun _ _ _ _ _ _ => 0))
    (by
      intro h
      have hs : 0 < denominator 1 1 0 0 0 := by norm_num [denominator]
      have e := (h (σ := 1) (Δ := 1) (L := 1) 0 0 0 0 (by norm_num) hs).1 1 (by norm_num)
      norm_num [realize, ads4Propagator, kernel, denominator, Real.rpow_one] at e)
    (by
      refine ⟨(), 1, -1, ?_⟩
      intro h
      have e := congrArg (fun f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ => f 1 2 1 0 0) h
      norm_num [realize, ads4Propagator, kernel, denominator, Real.rpow_one] at e)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ads4_propagator_boundary_scaling_and_inversion) (Realization signature) Unit Unit :=
  adsBind% `D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.ads4_propagator_boundary_scaling_and_inversion.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.ScalingAndInversion.family
    arena family (adsObserve% (ads4Propagator)) #[]
    #[{ path := adsPath% ads4_propagator_boundary_scaling_and_inversion ads4Propagator 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end ScalingAndInversion

end
end Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D
