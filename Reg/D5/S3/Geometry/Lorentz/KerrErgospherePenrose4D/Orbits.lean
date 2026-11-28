import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D
import Reg.Support.SingleDependentReadout

/-! Radius-dependent readouts for equatorial photon and marginal stability equations. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D
open LeanInformationAudit

namespace Reg.D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.Orbits

set_option autoImplicit false

noncomputable section

abbrev radiusSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def zeroOrbit : Realization radiusSignature :=
  realize radiusSignature (fun _ _ _ => 0) (fun e => nomatch e)

def photonActual : Realization radiusSignature :=
  realize radiusSignature (fun _ M r => kerrPhotonPoly M M r) (fun e => nomatch e)

abbrev photonArena : Arena where
  signature := radiusSignature
  Law R := ∀ {M r : ℝ}, 0 < r →
    (kerrPhotonPoly M 0 r = 0 ↔ r = 3 * M) ∧
      (kerrPhotonPoly M 0 r = 0 ↔ deriv (_root_.D5.S3.Geometry.Lorentz.SchwarzschildOpticalGeodesics4D.nullPotential M) r = 0) ∧
      R.readout () M r = (r - M) ^ 2 * (r - 4 * M) ∧
      (kerrPhotonPoly M M r = 0 ↔ r = M ∨ r = 4 * M)

private theorem zero_orbit_loses_factorization : ¬ photonArena.Law zeroOrbit := by
  intro h
  have he := (h (M := 1) (r := 2) (by norm_num)).2.2.1
  change (0 : ℝ) = (2 - 1) ^ 2 * (2 - 4 * 1) at he
  norm_num at he

def photonFamily : Registration photonArena (type_of% (@kerr_photon_orbit_benchmarks)) where
  actual := photonActual
  bridge := Iff.rfl
  variation := ⟨@kerr_photon_orbit_benchmarks, zeroOrbit, zero_orbit_loses_factorization⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    photonArena.Law photonActual zeroOrbit zero_orbit_loses_factorization
  dependence := by
    intro _
    refine ⟨1, 1, 2, ?_⟩
    change kerrPhotonPoly 1 1 1 ≠ kerrPhotonPoly 1 1 2
    norm_num [kerrPhotonPoly]

def signedPhotonActual : Realization radiusSignature :=
  realize radiusSignature (fun _ M r => circularPhotonEquation M M 1 r) (fun e => nomatch e)

abbrev signedPhotonArena : Arena where
  signature := radiusSignature
  Law R := ∀ {M r : ℝ}, 0 < M → 0 < r →
    (R.readout () M r = 0 ↔ r = M) ∧
      (circularPhotonEquation M M (-1) r = 0 ↔ r = 4 * M)

private theorem zero_orbit_loses_photon_direction : ¬ signedPhotonArena.Law zeroOrbit := by
  intro h
  have he := (h (M := 1) (r := 4) (by norm_num) (by norm_num)).1.mp rfl
  norm_num at he

private theorem sqrt_four : Real.sqrt 4 = 2 := by
  have h := Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)
  norm_num at h
  exact h

private theorem sqrt_nine : Real.sqrt 9 = 3 := by
  have h := Real.sqrt_sq (show (0 : ℝ) ≤ 3 by norm_num)
  norm_num at h
  exact h

def signedPhotonFamily : Registration signedPhotonArena (type_of% (@extremal_photon_orbit_directions)) where
  actual := signedPhotonActual
  bridge := Iff.rfl
  variation := ⟨@extremal_photon_orbit_directions, zeroOrbit, zero_orbit_loses_photon_direction⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    signedPhotonArena.Law signedPhotonActual zeroOrbit zero_orbit_loses_photon_direction
  dependence := by
    intro _
    refine ⟨1, 1, 4, ?_⟩
    change circularPhotonEquation 1 1 1 1 ≠ circularPhotonEquation 1 1 1 4
    norm_num [circularPhotonEquation, sqrt_four]

def extremalISCOActual : Realization radiusSignature :=
  realize radiusSignature (fun _ M r => kerrISCOPoly M M (-1) r) (fun e => nomatch e)

abbrev extremalISCOArena : Arena where
  signature := radiusSignature
  Law R := ∀ {M r : ℝ}, 0 < M → 0 < r →
    (kerrISCOPoly M M 1 r = 0 ↔ r = M) ∧ (R.readout () M r = 0 ↔ r = 9 * M)

private theorem zero_orbit_loses_isco_uniqueness : ¬ extremalISCOArena.Law zeroOrbit := by
  intro h
  have he := (h (M := 1) (r := 1) (by norm_num) (by norm_num)).2.mp rfl
  norm_num at he

def extremalISCOFamily : Registration extremalISCOArena (type_of% (@extremal_isco_radii_unique)) where
  actual := extremalISCOActual
  bridge := Iff.rfl
  variation := ⟨@extremal_isco_radii_unique, zeroOrbit, zero_orbit_loses_isco_uniqueness⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    extremalISCOArena.Law extremalISCOActual zeroOrbit zero_orbit_loses_isco_uniqueness
  dependence := by
    intro _
    refine ⟨1, 1, 9, ?_⟩
    change kerrISCOPoly 1 1 (-1) 1 ≠ kerrISCOPoly 1 1 (-1) 9
    norm_num [kerrISCOPoly, sqrt_nine]

abbrev iscoBenchmarkSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def iscoBenchmarkActual : Realization iscoBenchmarkSignature :=
  realize iscoBenchmarkSignature (fun _ p r => kerrISCOPoly p.1 0 p.2 r) (fun e => nomatch e)

def zeroISCOBenchmark : Realization iscoBenchmarkSignature :=
  realize iscoBenchmarkSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev iscoBenchmarkArena : Arena where
  signature := iscoBenchmarkSignature
  Law R := ∀ {M r : ℝ} (s : ℝ), 0 < M → 0 < r →
    (R.readout () ⟨M, s⟩ r = 0 ↔ r = 6 * M) ∧
      kerrISCOPoly M M 1 M = 0 ∧ kerrISCOPoly M M (-1) (9 * M) = 0 ∧
      iscoEfficiency 6 = 1 - 2 * Real.sqrt 2 / 3 ∧
      iscoEfficiency 1 = 1 - 1 / Real.sqrt 3 ∧
      iscoEfficiency 9 = 1 - 5 / (3 * Real.sqrt 3) ∧
      (0 < iscoEfficiency 9 ∧ iscoEfficiency 9 < iscoEfficiency 6 ∧
        iscoEfficiency 6 < iscoEfficiency 1 ∧ iscoEfficiency 1 < 1 / 2)

private theorem zero_orbit_loses_isco_benchmark : ¬ iscoBenchmarkArena.Law zeroISCOBenchmark := by
  intro h
  have he := (h (M := 1) (r := 1) 1 (by norm_num) (by norm_num)).1.mp rfl
  norm_num at he

def iscoBenchmarkFamily : Registration iscoBenchmarkArena
    (type_of% (@kerr_isco_benchmarks_and_binding_efficiency)) where
  actual := iscoBenchmarkActual
  bridge := Iff.rfl
  variation := ⟨@kerr_isco_benchmarks_and_binding_efficiency, zeroISCOBenchmark,
    zero_orbit_loses_isco_benchmark⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    iscoBenchmarkArena.Law iscoBenchmarkActual zeroISCOBenchmark zero_orbit_loses_isco_benchmark
  dependence := by
    intro _
    refine ⟨⟨1, 1⟩, 1, 6, ?_⟩
    change kerrISCOPoly 1 0 1 1 ≠ kerrISCOPoly 1 0 1 6
    norm_num [kerrISCOPoly]

def photonRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@kerr_photon_orbit_benchmarks) (Realization radiusSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.kerr_photon_orbit_benchmarks.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.Orbits.photonFamily
  realizationSource := none
  generated := false
  arena := .source ⟨photonArena⟩
  objectArena := .source ⟨photonArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source photonArena ⟨photonFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize radiusSignature
    (fun _ M r => kerrPhotonPoly M M r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def signedPhotonRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@extremal_photon_orbit_directions) (Realization radiusSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.extremal_photon_orbit_directions.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.Orbits.signedPhotonFamily
  realizationSource := none
  generated := false
  arena := .source ⟨signedPhotonArena⟩
  objectArena := .source ⟨signedPhotonArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source signedPhotonArena ⟨signedPhotonFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize radiusSignature
    (fun _ M r => circularPhotonEquation M M 1 r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def extremalISCORegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@extremal_isco_radii_unique) (Realization radiusSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.extremal_isco_radii_unique.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.Orbits.extremalISCOFamily
  realizationSource := none
  generated := false
  arena := .source ⟨extremalISCOArena⟩
  objectArena := .source ⟨extremalISCOArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source extremalISCOArena ⟨extremalISCOFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize radiusSignature
    (fun _ M r => kerrISCOPoly M M (-1) r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def iscoBenchmarkRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@kerr_isco_benchmarks_and_binding_efficiency) (Realization iscoBenchmarkSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.kerr_isco_benchmarks_and_binding_efficiency.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.Orbits.iscoBenchmarkFamily
  realizationSource := none
  generated := false
  arena := .source ⟨iscoBenchmarkArena⟩
  objectArena := .source ⟨iscoBenchmarkArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source iscoBenchmarkArena ⟨iscoBenchmarkFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize iscoBenchmarkSignature
    (fun _ p r => kerrISCOPoly p.1 0 p.2 r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.Orbits
