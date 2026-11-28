import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D
import Reg.Support.SingleDependentReadout

/-! Source registrations for charge quantization and modular transport. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D
open _root_.Reg.Support.SingleDependentReadout
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.Charges

set_option autoImplicit false

noncomputable section

abbrev AngularParameters := Σ _ : ℝ, Σ _ : ℝ, ℝ
abbrev angularSignature : Signature := signature AngularParameters (fun _ ↦ ℝ) (fun _ ↦ ℝ)

def angularReadout (f : ℝ → ℝ → ℝ → ℝ → ℝ) : Realization angularSignature :=
  realize angularSignature (fun _ p g₂ ↦ f p.1 p.2.1 p.2.2 g₂) (fun e ↦ nomatch e)

abbrev angularArena : Arena where
  signature := angularSignature
  Law R := ∀ q₁ g₁ q₂ g₂ : ℝ,
    (∃ n : ℤ, dszPairing q₁ g₁ q₂ g₂ = 2 * Real.pi * n) ↔
      (∃ n : ℤ, R.readout () ⟨q₁, g₁, q₂⟩ g₂ = (n : ℝ) / 2)

private theorem angularConstantFails : ¬ angularArena.Law (angularReadout fun _ _ _ _ ↦ 1 / 4) := by
  intro h
  obtain ⟨n, hn⟩ := (h 0 0 0 0).mp ⟨0, by simp [dszPairing]⟩
  change (1 / 4 : ℝ) = (n : ℝ) / 2 at hn
  have hn' : (2 : ℤ) * n = 1 := by exact_mod_cast (show (2 : ℝ) * n = 1 by linarith)
  omega

def angularFamily : Registration angularArena (type_of% (@dsz_half_integer_angMom_iff)) where
  actual := angularReadout emAngularMomentum
  bridge := Iff.rfl
  variation := ⟨dsz_half_integer_angMom_iff, _, angularConstantFails⟩
  sensitivity := sensitivity angularArena.Law _ _ angularConstantFails
  dependence := by
    intro _
    refine ⟨⟨1, 0, 0⟩, 0, 1, ?_⟩
    change emAngularMomentum 1 0 0 0 ≠ emAngularMomentum 1 0 0 1
    simp [emAngularMomentum, dszPairing, Real.pi_ne_zero]

def angularRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@dsz_half_integer_angMom_iff) (Realization angularSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.dsz_half_integer_angMom_iff.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.Charges.angularFamily
  realizationSource := none
  generated := false
  arena := .source ⟨angularArena⟩
  objectArena := .source ⟨angularArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source angularArena ⟨angularFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize angularSignature (fun _ p g₂ ↦ emAngularMomentum p.1 p.2.1 p.2.2 g₂) (fun e ↦ nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev quantumSignature : Signature := signature Unit (fun _ ↦ ℝ) (fun _ ↦ ℝ)

def quantumReadout (f : ℝ → ℝ) : Realization quantumSignature :=
  realize quantumSignature (fun _ _ g ↦ f g) (fun e ↦ nomatch e)

def diracActual : Realization quantumSignature :=
  quantumReadout (fun g ↦ 2 * Real.pi / g)

abbrev diracArena : Arena where
  signature := quantumSignature
  Law R := ∀ q g : ℝ, g ≠ 0 →
    (∃ n : ℤ, dszPairing q 0 0 g = 2 * Real.pi * n) →
      q ∈ Set.range (fun n : ℤ ↦ R.readout () () g * n)

private theorem diracConstantFails : ¬ diracArena.Law (quantumReadout fun _ ↦ 0) := by
  intro h
  obtain ⟨n, hn⟩ := h (2 * Real.pi) 1 one_ne_zero ⟨1, by simp [dszPairing]⟩
  change 0 * (n : ℝ) = 2 * Real.pi at hn
  linarith [Real.pi_pos]

def diracFamily : Registration diracArena (type_of% (@dirac_charge_quantization)) where
  actual := diracActual
  bridge := Iff.rfl
  variation := ⟨dirac_charge_quantization, _, diracConstantFails⟩
  sensitivity := sensitivity diracArena.Law _ _ diracConstantFails
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change (2 * Real.pi / 0 : ℝ) ≠ 2 * Real.pi / 1
    simp [Real.pi_ne_zero]

def diracRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@dirac_charge_quantization) (Realization quantumSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.dirac_charge_quantization.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.Charges.diracFamily
  realizationSource := none
  generated := false
  arena := .source ⟨diracArena⟩
  objectArena := .source ⟨diracArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source diracArena ⟨diracFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize quantumSignature (fun _ _ g ↦ 2 * Real.pi / g) (fun e ↦ nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev actionSignature : Signature := signature Unit (fun _ ↦ ChargePair) (fun _ ↦ ChargePair)

def actionReadout (f : ChargePair → ChargePair) : Realization actionSignature :=
  realize actionSignature (fun _ _ n ↦ f n) (fun e ↦ nomatch e)

abbrev actionArena : Arena where
  signature := actionSignature
  Law R := ∀ (M N : ModularMatrix) (n : ChargePair), R.readout () () n = n ∧
    sl2zCharge (M * N) n = sl2zCharge M (sl2zCharge N n)

private theorem actionConstantFails : ¬ actionArena.Law (actionReadout fun _ ↦ (0, 0)) := by
  intro h
  have hz := congrArg Prod.fst (h 1 1 (1, 0)).1
  exact Int.zero_ne_one hz

def actionFamily : Registration actionArena (type_of% (@sl2z_charge_action)) where
  actual := actionReadout (sl2zCharge 1)
  bridge := Iff.rfl
  variation := ⟨sl2z_charge_action, _, actionConstantFails⟩
  sensitivity := sensitivity actionArena.Law _ _ actionConstantFails
  dependence := by
    intro _
    refine ⟨(), (0, 0), (1, 0), ?_⟩
    change sl2zCharge 1 (0, 0) ≠ sl2zCharge 1 (1, 0)
    rw [(sl2z_charge_action 1 1 (0, 0)).1, (sl2z_charge_action 1 1 (1, 0)).1]
    exact fun h ↦ Int.zero_ne_one (congrArg Prod.fst h)

def actionRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sl2z_charge_action) (Realization actionSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.sl2z_charge_action.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.Charges.actionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨actionArena⟩
  objectArena := .source ⟨actionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source actionArena ⟨actionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize actionSignature (fun _ _ n ↦ sl2zCharge 1 n) (fun e ↦ nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev pairingSignature : Signature := signature ChargePair (fun _ ↦ ChargePair) (fun _ ↦ ℤ)

def pairingReadout (f : ChargePair → ChargePair → ℤ) : Realization pairingSignature :=
  realize pairingSignature (fun _ n m ↦ f n m) (fun e ↦ nomatch e)

abbrev pairingArena : Arena where
  signature := pairingSignature
  Law R := ∀ (M : ModularMatrix), M.det = 1 → ∀ n m : ChargePair,
    dszLatticePairing (sl2zCharge M n) (sl2zCharge M m) = R.readout () n m

private theorem pairingConstantFails : ¬ pairingArena.Law (pairingReadout fun _ _ ↦ 1) := by
  intro h
  have hz := h 1 (Matrix.det_one) (0, 0) (0, 0)
  rw [(sl2z_charge_action 1 1 (0, 0)).1] at hz
  exact Int.zero_ne_one hz

def pairingFamily : Registration pairingArena (type_of% (@dsz_pairing_sl2z_invariant)) where
  actual := pairingReadout dszLatticePairing
  bridge := Iff.rfl
  variation := ⟨dsz_pairing_sl2z_invariant, _, pairingConstantFails⟩
  sensitivity := sensitivity pairingArena.Law _ _ pairingConstantFails
  dependence := by
    intro _
    exact ⟨(1, 0), (0, 0), (0, 1), Int.zero_ne_one⟩

def pairingRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@dsz_pairing_sl2z_invariant) (Realization pairingSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.dsz_pairing_sl2z_invariant.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.Charges.pairingFamily
  realizationSource := none
  generated := false
  arena := .source ⟨pairingArena⟩
  objectArena := .source ⟨pairingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pairingArena ⟨pairingFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pairingSignature (fun _ n m ↦ dszLatticePairing n m) (fun e ↦ nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev halfPlaneSignature : Signature := signature ModularMatrix (fun _ ↦ ℂ) (fun _ ↦ ℝ)

def halfPlaneReadout (f : ModularMatrix → ℂ → ℝ) : Realization halfPlaneSignature :=
  realize halfPlaneSignature (fun _ M τ ↦ f M τ) (fun e ↦ nomatch e)

def halfPlaneActual : Realization halfPlaneSignature :=
  halfPlaneReadout (fun M τ ↦ (sl2zAct M τ).im)

abbrev halfPlaneArena : Arena where
  signature := halfPlaneSignature
  Law R := ∀ (M : ModularMatrix), M.det = 1 → ∀ τ : ℂ, 0 < τ.im →
    0 < R.readout () M τ ∧ (sl2zAct M τ).im = τ.im / ‖sl2zDenom M τ‖ ^ 2

private theorem halfPlaneConstantFails : ¬ halfPlaneArena.Law (halfPlaneReadout fun _ _ ↦ 0) := by
  intro h
  exact (lt_irrefl (0 : ℝ)) (h 1 Matrix.det_one Complex.I (by simp)).1

def halfPlaneFamily : Registration halfPlaneArena (type_of% (@sl2z_preserves_upper_half_plane)) where
  actual := halfPlaneActual
  bridge := Iff.rfl
  variation := ⟨sl2z_preserves_upper_half_plane, _, halfPlaneConstantFails⟩
  sensitivity := sensitivity halfPlaneArena.Law _ _ halfPlaneConstantFails
  dependence := by
    intro _
    refine ⟨1, 0, Complex.I, ?_⟩
    change (sl2zAct 1 0).im ≠ (sl2zAct 1 Complex.I).im
    simp [sl2zAct, sl2zDenom]

def halfPlaneRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sl2z_preserves_upper_half_plane) (Realization halfPlaneSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.sl2z_preserves_upper_half_plane.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.Charges.halfPlaneFamily
  realizationSource := none
  generated := false
  arena := .source ⟨halfPlaneArena⟩
  objectArena := .source ⟨halfPlaneArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source halfPlaneArena ⟨halfPlaneFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize halfPlaneSignature (fun _ M τ ↦ (sl2zAct M τ).im) (fun e ↦ nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private theorem bpsMass_electric_one : bpsDyonMass 1 Complex.I 1 0 = 1 := by
  norm_num [bpsDyonMass, Complex.I_im]

private theorem bpsMass_magnetic_one : bpsDyonMass 1 Complex.I 0 1 = 1 := by
  norm_num [bpsDyonMass, Complex.I_im, Complex.norm_I]

abbrev dualitySignature : Signature := signature (Σ _ : ℝ, ℂ) (fun _ ↦ ChargePair) (fun _ ↦ ℝ)

def dualityReadout (f : ℝ → ℂ → ChargePair → ℝ) : Realization dualitySignature :=
  realize dualitySignature (fun _ p n ↦ f p.1 p.2 n) (fun e ↦ nomatch e)

def dualityActual : Realization dualitySignature :=
  dualityReadout (fun v τ n ↦ bpsDyonMass v τ n.1 n.2)

abbrev dualityArena : Arena where
  signature := dualitySignature
  Law R := ∀ (M : ModularMatrix), M.det = 1 → ∀ (v : ℝ) (τ : ℂ), 0 < τ.im → ∀ n : ChargePair,
    bpsDyonMass v (sl2zAct M τ) (sl2zCharge M n).1 (sl2zCharge M n).2 = R.readout () ⟨v, τ⟩ n

private theorem dualityConstantFails : ¬ dualityArena.Law (dualityReadout fun _ _ _ ↦ 0) := by
  intro h
  have hb := h 1 Matrix.det_one 1 Complex.I (by simp) (1, 0)
  have ha := bpsDyonMass_sl2z_invariant 1 Matrix.det_one 1 Complex.I (by simp) (1, 0)
  exact one_ne_zero (bpsMass_electric_one ▸ ha.symm.trans hb)

def dualityFamily : Registration dualityArena (type_of% (@bpsDyonMass_sl2z_invariant)) where
  actual := dualityActual
  bridge := Iff.rfl
  variation := ⟨bpsDyonMass_sl2z_invariant, _, dualityConstantFails⟩
  sensitivity := sensitivity dualityArena.Law _ _ dualityConstantFails
  dependence := by
    intro _
    refine ⟨⟨1, Complex.I⟩, (0, 0), (1, 0), ?_⟩
    change bpsDyonMass 1 Complex.I 0 0 ≠ bpsDyonMass 1 Complex.I 1 0
    rw [bpsMass_electric_one]
    simp [bpsDyonMass]

def dualityRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bpsDyonMass_sl2z_invariant) (Realization dualitySignature) Unit Unit where
  unitName := `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.bpsDyonMass_sl2z_invariant.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.Charges.dualityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨dualityArena⟩
  objectArena := .source ⟨dualityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source dualityArena ⟨dualityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize dualitySignature (fun _ p n ↦ bpsDyonMass p.1 p.2 n.1 n.2) (fun e ↦ nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D
    definition := none
    coordinates := #[2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev GeneratorParameters := Σ _ : ℝ, Σ _ : ℂ, ℤ
abbrev generatorSignature : Signature := signature GeneratorParameters (fun _ ↦ ℤ) (fun _ ↦ ℝ)

def generatorReadout (f : ℝ → ℂ → ℤ → ℤ → ℝ) : Realization generatorSignature :=
  realize generatorSignature (fun _ p nM ↦ f p.1 p.2.1 p.2.2 nM) (fun e ↦ nomatch e)

private theorem generatorDependence :
    ObservationalDependence generatorSignature (generatorReadout bpsDyonMass) := by
  intro _
  refine ⟨⟨1, Complex.I, 0⟩, 0, 1, ?_⟩
  change bpsDyonMass 1 Complex.I 0 0 ≠ bpsDyonMass 1 Complex.I 0 1
  rw [bpsMass_magnetic_one]
  simp [bpsDyonMass]

abbrev sDualityArena : Arena where
  signature := generatorSignature
  Law R := ∀ (v : ℝ) (τ : ℂ), 0 < τ.im → ∀ nE nM : ℤ,
    bpsDyonMass v (-1 / τ) nM (-nE) = R.readout () ⟨v, τ, nE⟩ nM

private theorem sDualityConstantFails : ¬ sDualityArena.Law (generatorReadout fun _ _ _ _ ↦ 0) := by
  intro h
  have hb := h 1 Complex.I (by simp) 1 0
  have ha := bpsDyonMass_S_duality 1 Complex.I (by simp) 1 0
  exact one_ne_zero (bpsMass_electric_one ▸ ha.symm.trans hb)

def sDualityFamily : Registration sDualityArena (type_of% (@bpsDyonMass_S_duality)) where
  actual := generatorReadout bpsDyonMass
  bridge := Iff.rfl
  variation := ⟨bpsDyonMass_S_duality, _, sDualityConstantFails⟩
  sensitivity := sensitivity sDualityArena.Law _ _ sDualityConstantFails
  dependence := generatorDependence

def sDualityRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bpsDyonMass_S_duality) (Realization generatorSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.bpsDyonMass_S_duality.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.Charges.sDualityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨sDualityArena⟩
  objectArena := .source ⟨sDualityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sDualityArena ⟨sDualityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize generatorSignature (fun _ p nM ↦ bpsDyonMass p.1 p.2.1 p.2.2 nM) (fun e ↦ nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev tDualityArena : Arena where
  signature := generatorSignature
  Law R := ∀ (v : ℝ) (τ : ℂ), 0 < τ.im → ∀ nE nM : ℤ,
    bpsDyonMass v (τ + 1) (nE - nM) nM = R.readout () ⟨v, τ, nE⟩ nM

private theorem tDualityConstantFails : ¬ tDualityArena.Law (generatorReadout fun _ _ _ _ ↦ 0) := by
  intro h
  have hb := h 1 Complex.I (by simp) 1 0
  have ha := bpsDyonMass_T_duality 1 Complex.I (by simp) 1 0
  exact one_ne_zero (bpsMass_electric_one ▸ ha.symm.trans hb)

def tDualityFamily : Registration tDualityArena (type_of% (@bpsDyonMass_T_duality)) where
  actual := generatorReadout bpsDyonMass
  bridge := Iff.rfl
  variation := ⟨bpsDyonMass_T_duality, _, tDualityConstantFails⟩
  sensitivity := sensitivity tDualityArena.Law _ _ tDualityConstantFails
  dependence := generatorDependence

def tDualityRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bpsDyonMass_T_duality) (Realization generatorSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.bpsDyonMass_T_duality.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.Charges.tDualityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨tDualityArena⟩
  objectArena := .source ⟨tDualityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source tDualityArena ⟨tDualityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize generatorSignature (fun _ p nM ↦ bpsDyonMass p.1 p.2.1 p.2.2 nM) (fun e ↦ nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def strongActual : Realization quantumSignature :=
  quantumReadout (fun g ↦ (imaginaryCoupling g).im)

abbrev strongArena : Arena where
  signature := quantumSignature
  Law R := ∀ g : ℝ, 0 < g → 0 < R.readout () () g ∧
    sl2zAct (ModularGroup.S : ModularMatrix) (imaginaryCoupling g) =
      imaginaryCoupling (4 * Real.pi / g)

private theorem strongConstantFails : ¬ strongArena.Law (quantumReadout fun _ ↦ 0) := by
  intro h
  exact (lt_irrefl (0 : ℝ)) (h 1 one_pos).1

def strongFamily : Registration strongArena (type_of% (@sl2z_weak_strong_coupling)) where
  actual := strongActual
  bridge := Iff.rfl
  variation := ⟨sl2z_weak_strong_coupling, _, strongConstantFails⟩
  sensitivity := sensitivity strongArena.Law _ _ strongConstantFails
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change (imaginaryCoupling 0).im ≠ (imaginaryCoupling 1).im
    rw [show imaginaryCoupling 0 = 0 by simp [imaginaryCoupling]]
    exact (sl2z_weak_strong_coupling 1 one_pos).1.ne

def strongRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sl2z_weak_strong_coupling) (Realization quantumSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.sl2z_weak_strong_coupling.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.Charges.strongFamily
  realizationSource := none
  generated := false
  arena := .source ⟨strongArena⟩
  objectArena := .source ⟨strongArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source strongArena ⟨strongFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize quantumSignature (fun _ _ g ↦ (imaginaryCoupling g).im) (fun e ↦ nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.Charges
