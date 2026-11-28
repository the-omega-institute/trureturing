import D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D
import Reg.Support.UnitSixO.Common

/-! Exact source observations for forces and inverse-distance potentials. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D
open _root_.Reg.Support.UnitSixO (operandSignature)
open OmegaMath.InverseDistanceThree LeanInformationAudit Filter
open scoped BigOperators Topology

namespace Reg.D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.Extremal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

abbrev ForceSignature : Signature := operandSignature ℝ (ℝ → ℝ → ℝ → ℝ → ℝ)

def forceActual : Realization ForceSignature := unitObserve% netBPSForce

private theorem force_dependence :
    ∃ p x y, forceActual.readout () p x ≠ forceActual.readout () p y := by
  refine ⟨(), 0, 1, fun h => ?_⟩
  have he := congrFun (congrFun (congrFun (congrFun h 0) 1) 0) 1
  norm_num [forceActual, realize, netBPSForce] at he

namespace Balance

abbrev arena : Arena where
  signature := ForceSignature
  Law R := ∀ {m₁ q₁ m₂ q₂ r : ℝ},
    0 < m₁ → 0 < m₂ → 0 < r →
    ((q₁ = m₁ ∧ q₂ = m₂) ∨ (q₁ = -m₁ ∧ q₂ = -m₂)) →
    R.readout () () m₁ q₁ m₂ q₂ r = 0 ∧
      coulombForceMagnitude q₁ q₂ r = gravitationalForce m₁ m₂ r ∧
      0 < gravitationalForce m₁ m₂ r ∧
      _root_.D5.S3.Geometry.Lorentz.BlackHoleThermodynamics4D.surfaceGravity m₁ 0 q₁ = 0 ∧
      _root_.D5.S3.Geometry.Lorentz.BlackHoleThermodynamics4D.surfaceGravity m₂ 0 q₂ = 0

def family : Registration arena (type_of% (@bps_extremal_force_cancellation)) :=
  unitFamily% arena (@bps_extremal_force_cancellation) (unitObserve% netBPSForce)
    (unitObserve% (fun _ _ _ _ _ => 1))
    (by
      intro h
      have hh := (h (m₁ := 1) (m₂ := 1) (q₁ := 1) (q₂ := 1) (r := 1)
        (by norm_num) (by norm_num) (by norm_num) (Or.inl ⟨rfl, rfl⟩)).1
      norm_num [realize] at hh)
    force_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bps_extremal_force_cancellation) (Realization ForceSignature) Unit Unit :=
  unitBindOptics%
    `D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.bps_extremal_force_cancellation.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.Extremal.Balance.family
    arena family (unitObserve% netBPSForce) #[]
    #[{ path := unitPath% bps_extremal_force_cancellation netBPSForce 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end Balance

namespace Attraction

abbrev arena : Arena where
  signature := ForceSignature
  Law R := ∀ {m₁ q₁ m₂ q₂ r : ℝ},
    |q₁| < m₁ → |q₂| ≤ m₂ → 0 < m₂ → 0 < r → R.readout () () m₁ q₁ m₂ q₂ r < 0

def family : Registration arena (type_of% (@bps_subextremal_attraction)) :=
  unitFamily% arena (@bps_subextremal_attraction) (unitObserve% netBPSForce)
    (unitObserve% (fun _ _ _ _ _ => 0))
    (by
      intro h
      have hh := h (m₁ := 1) (m₂ := 1) (q₁ := 0) (q₂ := 0) (r := 1)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      norm_num [realize] at hh)
    force_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bps_subextremal_attraction) (Realization ForceSignature) Unit Unit :=
  unitBindOptics%
    `D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.bps_subextremal_attraction.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.Extremal.Attraction.family
    arena family (unitObserve% netBPSForce) #[]
    #[{ path := unitPath% bps_subextremal_attraction netBPSForce 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end Attraction

namespace Charge

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun n => Fin n → ℝ) (fun _ => ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} {m q : Fin N → ℝ}, (∀ i, q i = m i) →
    R.readout () N m = ∑ i, q i

def actual : Realization signature :=
  realize signature (fun _ _ f => ∑ i, f i) (fun e => nomatch e)

def family : Registration arena (type_of% (@bps_superposition_charge_bound)) :=
  unitFamily% arena (@bps_superposition_charge_bound) (realize signature (fun _ _ f => ∑ i, f i) (fun e => nomatch e))
    (realize signature (fun _ _ _ => 0) (fun e => nomatch e))
    (by
      intro h
      have hh := h (m := fun _ : Fin 1 => (1 : ℝ)) (q := fun _ => 1) (fun _ => rfl)
      norm_num [realize] at hh)
    (by
      refine ⟨1, fun _ => 0, fun _ => 1, ?_⟩
      norm_num [actual, realize])

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bps_superposition_charge_bound) (Realization signature) Unit Unit :=
  unitBindOptics%
    `D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.bps_superposition_charge_bound.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.Extremal.Charge.family
    arena family (realize signature (fun _ _ f => ∑ i, f i) (fun e => nomatch e)) #[0]
    #[{ path := unitPath% bps_superposition_charge_bound Finset.sum 4 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end Charge

private theorem axis_ne : axis 0 ≠ (0 : Point) := by
  intro h
  have h0 := congrFun h 0
  norm_num [axis] at h0

private theorem axis_radius : r3 (axis 0) 0 = 1 := by
  norm_num [radius, squareDistance, Fin.sum_univ_succ, axis]

namespace Inverse

abbrev signature : Signature := operandSignature Point (Point → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x c : Point}, x ≠ c →
    (∀ j : Fin 3,
      HasDerivAt (fun t => 1 / R.readout () () (line x j t) c) (-(x j - c j) / r3 x c ^ 3) 0 ∧
      HasDerivAt (fun t => coordinateDerivative (fun y => 1 / r3 y c) j (line x j t))
        (3 * (x j - c j) ^ 2 / r3 x c ^ 5 - 1 / r3 x c ^ 3) 0) ∧
    laplacian (fun y => 1 / r3 y c) x = 0

def family : Registration arena (type_of% (@inv_r3_harmonic_3d)) :=
  unitFamily% arena (@inv_r3_harmonic_3d) (unitObserve% r3)
    (unitObserve% (fun _ _ => 1))
    (by
      intro h
      have hh := ((h axis_ne).1 0).1
      have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 := hasDerivAt_const _ _
      have hd : HasDerivAt (fun _ : ℝ => (1 : ℝ)) (-1) 0 := by
        simpa [realize, axis_radius, axis] using hh
      have he := hd.deriv.symm.trans hconst.deriv
      norm_num at he)
    (by
      refine ⟨(), 0, axis 0, fun h => ?_⟩
      have hh := congrFun h 0
      change r3 0 0 = r3 (axis 0) 0 at hh
      rw [axis_radius] at hh
      norm_num [radius, squareDistance] at hh)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@inv_r3_harmonic_3d) (Realization signature) Unit Unit :=
  unitBindOptics%
    `D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.inv_r3_harmonic_3d.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.Extremal.Inverse.family
    arena family (unitObserve% r3) #[]
    #[{ path := unitPath% inv_r3_harmonic_3d r3 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end Inverse

namespace Potential

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun n => Fin n → ℝ)
    (fun n => (Fin n → Point) → Point → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} (m : Fin N → ℝ) (c : Fin N → Point),
    (∀ x, (∀ i, x ≠ c i) → laplacian (mpPotential m c) x = 0) ∧
    (∀ x, (∀ i, x ≠ c i) → (∀ i, 0 ≤ m i) → (∃ i, 0 < m i) →
      1 < R.readout () N m c x) ∧
    (∀ u, r3 u 0 = 1 → Tendsto (fun R : ℝ => mpPotential m c (R • u)) atTop (𝓝 1))

def family : Registration arena (type_of% (@majumdar_papapetrou_harmonic)) :=
  unitFamily% arena (@majumdar_papapetrou_harmonic) (realize signature (fun _ _ => mpPotential) (fun e => nomatch e))
    (realize signature (fun _ _ _ _ _ => 1) (fun e => nomatch e))
    (by
      intro h
      have hh := (h (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 0)).2.1
        (axis 0) (fun _ => axis_ne) (fun _ => by norm_num) ⟨0, by norm_num⟩
      norm_num [realize] at hh)
    (by
      refine ⟨1, fun _ => 0, fun _ => 1, fun h => ?_⟩
      have hh := congrFun (congrFun h (fun _ => 0)) (axis 0)
      change mpPotential (fun _ : Fin 1 => (0 : ℝ)) (fun _ => 0) (axis 0) =
        mpPotential (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 0) (axis 0) at hh
      norm_num [mpPotential, axis_radius] at hh)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@majumdar_papapetrou_harmonic) (Realization signature) Unit Unit :=
  unitBindOptics%
    `D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.majumdar_papapetrou_harmonic.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.Extremal.Potential.family
    arena family (realize signature (fun _ _ => mpPotential) (fun e => nomatch e)) #[0]
    #[{ path := unitPath% majumdar_papapetrou_harmonic mpPotential 1 1
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end Potential

end
end Reg.D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.Extremal
