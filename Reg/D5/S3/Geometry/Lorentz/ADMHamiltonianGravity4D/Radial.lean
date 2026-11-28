import D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D
import Reg.Support.UnitSixO

/-! Readouts for the radial operator, areal radius, and mass observables. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D
open _root_.D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D (r3)
open _root_.Reg.Support.UnitSixO (operandSignature)
open OmegaMath.InverseDistanceThree LeanInformationAudit Filter
open scoped BigOperators Topology

namespace Reg.D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D.Radial

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

macro "bindRadial% " unit:term:max familyName:term:max arena:term:max family:term:max
    actual:term:max coordinates:term:max path:term:max : term =>
  `({ unitName := $unit
      realizationName := $familyName
      realizationSource := none
      generated := false
      arena := .source ⟨$arena⟩
      objectArena := .source ⟨$arena⟩
      catalog := Lean.Name.anonymous
      localNames := false
      realization := .source $arena ⟨$family⟩
      correspondence := ⟨.evidence, .evidence⟩
      bundleNonempty := .absent
      readout := some $actual
      variation := .absent
      sensitivity := .absent
      partialSensitivity := none
      escapeFrom := none
      sourceSelection := some {
        owner := `D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D
        definition := none
        coordinates := $coordinates
        readouts := #[{ path := $path
                        stateBinder := 0
                        functionOperand := true
                        stateOperand := none
                        booleanPredicate := false }] }
      continuation := .unknown
      familyRecord := none
      options := #[] })

namespace Curvature

abbrev signature : Signature := operandSignature (ℝ → ℝ) (ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : ℝ) {r : ℝ}, 0 < r →
    R.readout () () (schwPsi M) r = 0 ∧ conformalScalarCurvature (schwPsi M) r = 0

def family : Registration arena (type_of% (@lichnerowicz_radial_harmonic_vanishing)) :=
  unitFamily% arena (@lichnerowicz_radial_harmonic_vanishing) (unitObserve% radialLaplacian)
    (unitObserve% (fun _ _ => 1))
    (by
      intro h
      have hh := (h 0 (r := 1) (by norm_num)).1
      norm_num [realize] at hh)
    (by
      refine ⟨(), fun _ => 0, id, fun he => ?_⟩
      have h := congrFun he 1
      change radialLaplacian (fun _ => 0) 1 = radialLaplacian id 1 at h
      norm_num [radialLaplacian, deriv_id', deriv_const] at h)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@lichnerowicz_radial_harmonic_vanishing) (Realization signature) Unit Unit :=
  bindRadial%
    `D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D.lichnerowicz_radial_harmonic_vanishing.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D.Radial.Curvature.family
    arena family (unitObserve% radialLaplacian) #[]
    (unitPath% lichnerowicz_radial_harmonic_vanishing radialLaplacian 0 0)

end Curvature

private theorem arealRadius_dependence :
    ∃ p x y, (unitObserve% isotropicArealRadius : Realization (operandSignature ℝ (ℝ → ℝ))).readout
      () p x ≠ (unitObserve% isotropicArealRadius : Realization (operandSignature ℝ (ℝ → ℝ))).readout
      () p y := by
  refine ⟨(), 0, 2, fun he => ?_⟩
  have h := congrFun he 1
  norm_num [realize, isotropicArealRadius, schwPsi] at h

namespace Inversion

abbrev signature : Signature := operandSignature ℝ (ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {M r : ℝ}, 0 < M → 0 < r →
    R.readout () () M (isotropicInversion M r) = isotropicArealRadius M r ∧
    (schwPsi M (isotropicInversion M r)) ^ 4 * (deriv (isotropicInversion M) r) ^ 2 =
      (schwPsi M r) ^ 4 ∧
    isotropicInversion M (isotropicInversion M r) = r ∧
    (isotropicInversion M r < M / 2 ↔ M / 2 < r) ∧
    (r < M / 2 ↔ M / 2 < isotropicInversion M r) ∧
    2 * M ≤ isotropicArealRadius M r ∧ (isotropicArealRadius M r = 2 * M ↔ r = M / 2)

def family : Registration arena (type_of% (@isotropic_schwarzschild_throat_and_inversion_isometry)) :=
  unitFamily% arena (@isotropic_schwarzschild_throat_and_inversion_isometry)
    (unitObserve% isotropicArealRadius) (unitObserve% (fun _ _ => 0))
    (by
      intro h
      have hh := (h (M := 2) (r := 1) (by norm_num) (by norm_num)).1
      norm_num [realize, isotropicArealRadius, schwPsi] at hh)
    arealRadius_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@isotropic_schwarzschild_throat_and_inversion_isometry) (Realization signature) Unit Unit :=
  bindRadial%
    `D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D.isotropic_schwarzschild_throat_and_inversion_isometry.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D.Radial.Inversion.family
    arena family (unitObserve% isotropicArealRadius) #[]
    (unitPath% isotropic_schwarzschild_throat_and_inversion_isometry isotropicArealRadius 0 0)

end Inversion

namespace Mass

abbrev signature : Signature := operandSignature (ℝ → ℝ) (ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ M : ℝ,
    (∀ r > 0, R.readout () () (schwPsi M) r = M * (1 + M / (2 * r)) ^ 3) ∧
    Tendsto (conformalADMMass (schwPsi M)) atTop (𝓝 M) ∧
    (∀ r > 0, komarSchwarzschildMass M r = M)

def family : Registration arena (type_of% (@schwarzschild_adm_mass_limit_and_komar_invariance)) :=
  unitFamily% arena (@schwarzschild_adm_mass_limit_and_komar_invariance) (unitObserve% conformalADMMass)
    (unitObserve% (fun _ _ => 0))
    (by
      intro h
      have hh := (h 2).1 1 (by norm_num)
      norm_num [realize] at hh)
    (by
      refine ⟨(), fun _ => 0, id, fun he => ?_⟩
      have h := congrFun he 1
      change conformalADMMass (fun _ => 0) 1 = conformalADMMass id 1 at h
      norm_num [conformalADMMass, deriv_id'] at h)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@schwarzschild_adm_mass_limit_and_komar_invariance) (Realization signature) Unit Unit :=
  bindRadial%
    `D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D.schwarzschild_adm_mass_limit_and_komar_invariance.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D.Radial.Mass.family
    arena family (unitObserve% conformalADMMass) #[]
    (unitPath% schwarzschild_adm_mass_limit_and_komar_invariance conformalADMMass 0 0)

end Mass

namespace MultiCenter

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun n => Fin n → ℝ) (fun _ => ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} (m : Fin N → ℝ) (c : Fin N → Point),
    (∀ x, (∀ a, x ≠ c a) → laplacian (blPsi m c) x = 0) ∧
    (0 < N → (∀ a, 0 < m a) → 0 < R.readout () N m) ∧
    (∀ u, r3 u 0 = 1 →
      Tendsto (fun r : ℝ => -2 * r ^ 2 * (blPsi m c (r • u)) ^ 3 *
        deriv (fun s : ℝ => blPsi m c (s • u)) r) atTop (𝓝 (blADMMass m))) ∧
    blADMMass m - ∑ a, blBareMass m c a =
      -(1 / 2 : ℝ) * ∑ a, ∑ b ∈ Finset.univ.erase a, (m a * m b) / r3 (c a) (c b) ∧
    (2 ≤ N → (∀ a, 0 < m a) → Function.Injective c →
      blADMMass m < ∑ a, blBareMass m c a)

def actual : Realization signature :=
  realize signature (fun _ _ => blADMMass) (fun e => nomatch e)

def family : Registration arena (type_of% (@brill_lindquist_harmonic_positive_mass_and_binding_energy)) :=
  unitFamily% arena (@brill_lindquist_harmonic_positive_mass_and_binding_energy) actual
    (realize signature (fun _ _ _ => 0) (fun e => nomatch e))
    (by
      intro h
      have hh := (h (fun _ : Fin 1 => 1) (fun _ => 0)).2.1 (by norm_num) (fun _ => by norm_num)
      norm_num [realize] at hh)
    (by
      refine ⟨1, fun _ => 0, fun _ => 1, ?_⟩
      norm_num [actual, realize, blADMMass])

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@brill_lindquist_harmonic_positive_mass_and_binding_energy) (Realization signature) Unit Unit :=
  bindRadial%
    `D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D.brill_lindquist_harmonic_positive_mass_and_binding_energy.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D.Radial.MultiCenter.family
    arena family (realize signature (fun _ _ => blADMMass) (fun e => nomatch e)) #[0]
    (unitPath% brill_lindquist_harmonic_positive_mass_and_binding_energy blADMMass 1 0)

end MultiCenter

namespace Area

abbrev signature : Signature := operandSignature ℝ (ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {M : ℝ}, 0 < M →
    let A := 4 * Real.pi * (R.readout () () M (M / 2)) ^ 2
    A = 16 * Real.pi * M ^ 2 ∧ Real.sqrt (A / (16 * Real.pi)) = M ∧
    (∀ U V : ℝ, (V + U) / 2 = 0 →
      U * V = _root_.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.kruskalF M
        (isotropicArealRadius M (M / 2)) → (V - U) / 2 = 0)

def family : Registration arena (type_of% (@riemannian_penrose_inequality_schwarzschild_saturation)) :=
  unitFamily% arena (@riemannian_penrose_inequality_schwarzschild_saturation) (unitObserve% isotropicArealRadius)
    (unitObserve% (fun _ _ => 0))
    (by
      intro h
      have hh := (h (M := 1) (by norm_num)).1
      norm_num [realize] at hh)
    arealRadius_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@riemannian_penrose_inequality_schwarzschild_saturation) (Realization signature) Unit Unit :=
  bindRadial%
    `D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D.riemannian_penrose_inequality_schwarzschild_saturation.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D.Radial.Area.family
    arena family (unitObserve% isotropicArealRadius) #[]
    (unitPath% riemannian_penrose_inequality_schwarzschild_saturation isotropicArealRadius 0 0)

end Area

end
end Reg.D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D.Radial
