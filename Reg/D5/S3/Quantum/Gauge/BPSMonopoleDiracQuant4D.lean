import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D
import Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.Charges
import Reg.Support.SingleDependentReadout

/-! Source registrations for the monopole energy, radial solution and charge lattice. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D
open Filter MeasureTheory Set
open LeanInformationAudit
open scoped Topology

namespace Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D

set_option autoImplicit false

noncomputable section

universe p s o u

private abbrev signature (P : Type p) (X : P → Type s) (Y : P → Type o) : Signature where
  Params := P
  State := X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := Y
  Anchor := Empty
  finiteAnchor := inferInstance

private theorem singleSensitivity {P : Type p} {X : P → Type s} {Y : P → Type o}
    (law : Realization (signature P X Y) → Prop)
    (actual erased : Realization (signature P X Y)) (h : ¬ law erased) :
    Sensitivity ⟨signature P X Y, law⟩ actual := by
  refine ⟨fun _ ↦ ⟨erased, ?_, ?_, h⟩, fun e ↦ nomatch e⟩
  · intro j hj
    exact (hj (Subsingleton.elim _ _)).elim
  · funext e
    exact nomatch e

local macro "bindSource% " unit:term:max familyName:term:max arena:term:max family:term:max
    actual:term:max coordinates:term:max path:term:max state:term:max operand:term:max : term =>
  `({ unitName := $unit
      realizationName := $familyName
      realizationSource := none
      generated := false
      arena := .source ⟨$arena⟩
      objectArena := .source ⟨$arena⟩
      catalog := Lean.Name.anonymous
      localNames := false
      realization := .source $arena ⟨$family⟩
      correspondence := { stage := .evidence, objectStage := .evidence }
      bundleNonempty := .absent
      readout := some $actual
      variation := .absent
      sensitivity := .absent
      partialSensitivity := none
      escapeFrom := none
      sourceSelection := some {
        owner := `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D
        definition := none
        coordinates := $coordinates
        readouts := #[{
          path := $path
          stateBinder := $state
          functionOperand := $operand
          stateOperand := none
          booleanPredicate := false }] }
      continuation := .unknown
      familyRecord := none
      options := #[] })

abbrev EnergyParameters := Σ ι : Type u, Σ _ : Fintype ι, Σ _ : ι → ℝ, ι → ℝ

abbrev energySignature : Signature :=
  signature EnergyParameters (fun p ↦ p.1 → ℝ) (fun _ ↦ ℝ)

def energyActual : Realization energySignature :=
  realize energySignature
    (fun _ p DPhi ↦ @ymhEnergyDensity p.1 p.2.1 p.2.2.1 p.2.2.2 DPhi)
    (fun e ↦ nomatch e)

def energyConstant (c : ℝ) : Realization energySignature :=
  realize energySignature (fun _ _ _ ↦ c) (fun e ↦ nomatch e)

private theorem energyDependence : ObservationalDependence energySignature.{u} energyActual := by
  rintro ⟨⟩
  refine ⟨⟨ULift.{u} (Fin 1), inferInstance, 0, 0⟩, 0, 1, ?_⟩
  norm_num [energyActual, realize, ymhEnergyDensity, fieldNormSq, fieldDot, Pi.zero_apply,
    Pi.one_apply]
  change (0 : ℝ) * 0 ≠ 1 * 1
  norm_num

abbrev completionArena : Arena where
  signature := energySignature.{u}
  Law R := ∀ {ι : Type u} [i : Fintype ι] (E B DPhi : ι → ℝ) (α : ℝ),
    R.readout () ⟨ι, i, E, B⟩ DPhi =
      (1 / 2) * fieldNormSq (fun k ↦ E k - Real.sin α * DPhi k) +
      (1 / 2) * fieldNormSq (fun k ↦ B k - Real.cos α * DPhi k) +
      Real.sin α * fieldDot E DPhi + Real.cos α * fieldDot B DPhi

private theorem completionConstantFails : ¬ completionArena.{u}.Law (energyConstant 1) := by
  intro h
  have hz := @h (ULift.{u} (Fin 1)) _ 0 0 0 0
  norm_num [energyConstant, realize, fieldNormSq, fieldDot] at hz

def completionFamily : Registration completionArena (type_of% (@bogomolny_dyon_completion.{u})) where
  actual := energyActual
  bridge := Iff.rfl
  variation := ⟨bogomolny_dyon_completion, energyConstant 1, completionConstantFails⟩
  sensitivity := singleSensitivity completionArena.Law energyActual _ completionConstantFails
  dependence := energyDependence

def completionRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bogomolny_dyon_completion.{u}) (Realization energySignature.{u}) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.bogomolny_dyon_completion.__information_unit
    `Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.completionFamily
    completionArena completionFamily (realize energySignature
      (fun _ p DPhi ↦ @ymhEnergyDensity p.1 p.2.1 p.2.2.1 p.2.2.2 DPhi) (fun e ↦ nomatch e)) #[0, 2, 3]
    #["body", "body", "body", "body", "body", "body", "fn", "arg"] 4 false

abbrev lowerBoundArena : Arena where
  signature := energySignature.{u}
  Law R := ∀ {ι : Type u} [i : Fintype ι] (E B DPhi : ι → ℝ),
    Real.sqrt (fieldDot E DPhi ^ 2 + fieldDot B DPhi ^ 2) ≤ R.readout () ⟨ι, i, E, B⟩ DPhi

private theorem lowerBoundConstantFails : ¬ lowerBoundArena.{u}.Law (energyConstant (-1)) := by
  intro h
  have hz := @h (ULift.{u} (Fin 1)) _ 0 0 0
  norm_num [energyConstant, realize, fieldDot] at hz

def lowerBoundFamily : Registration lowerBoundArena (type_of% (@bogomolny_dyon_lower_bound.{u})) where
  actual := energyActual
  bridge := Iff.rfl
  variation := ⟨bogomolny_dyon_lower_bound, energyConstant (-1), lowerBoundConstantFails⟩
  sensitivity := singleSensitivity lowerBoundArena.Law energyActual _ lowerBoundConstantFails
  dependence := energyDependence

def lowerBoundRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bogomolny_dyon_lower_bound.{u}) (Realization energySignature.{u}) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.bogomolny_dyon_lower_bound.__information_unit
    `Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.lowerBoundFamily
    lowerBoundArena lowerBoundFamily (realize energySignature
      (fun _ p DPhi ↦ @ymhEnergyDensity p.1 p.2.1 p.2.2.1 p.2.2.2 DPhi) (fun e ↦ nomatch e)) #[0, 2, 3]
    #["body", "body", "body", "body", "body", "arg"] 4 false

abbrev saturationArena : Arena where
  signature := energySignature.{u}
  Law R := ∀ {ι : Type u} [i : Fintype ι] (E B DPhi : ι → ℝ),
    R.readout () ⟨ι, i, E, B⟩ DPhi = Real.sqrt (fieldDot E DPhi ^ 2 + fieldDot B DPhi ^ 2) ↔
      ∃ α : ℝ, (∀ k, E k = Real.sin α * DPhi k) ∧ (∀ k, B k = Real.cos α * DPhi k) ∧
        0 ≤ Real.sin α * fieldDot E DPhi + Real.cos α * fieldDot B DPhi

private theorem saturationConstantFails : ¬ saturationArena.{u}.Law (energyConstant 1) := by
  intro h
  have hz := (@h (ULift.{u} (Fin 1)) _ 0 0 0).mpr ⟨0, by simp [fieldDot]⟩
  norm_num [energyConstant, realize, fieldDot] at hz

def saturationFamily : Registration saturationArena
    (type_of% (@bogomolny_dyon_saturation_iff.{u})) where
  actual := energyActual
  bridge := Iff.rfl
  variation := ⟨bogomolny_dyon_saturation_iff, energyConstant 1, saturationConstantFails⟩
  sensitivity := singleSensitivity saturationArena.Law energyActual _ saturationConstantFails
  dependence := energyDependence

def saturationRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bogomolny_dyon_saturation_iff.{u}) (Realization energySignature.{u}) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.bogomolny_dyon_saturation_iff.__information_unit
    `Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.saturationFamily
    saturationArena saturationFamily (realize energySignature
      (fun _ p DPhi ↦ @ymhEnergyDensity p.1 p.2.1 p.2.2.1 p.2.2.2 DPhi) (fun e ↦ nomatch e)) #[0, 2, 3]
    #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"] 4 false

abbrev MonopoleParameters := Σ ι : Type u, Σ _ : Fintype ι, ι → ℝ

abbrev monopoleSignature : Signature :=
  signature MonopoleParameters (fun p ↦ p.1 → ℝ) (fun _ ↦ ℝ)

def monopoleActual : Realization monopoleSignature :=
  realize monopoleSignature (fun _ p DPhi ↦ @ymhEnergyDensity p.1 p.2.1 0 p.2.2 DPhi)
    (fun e ↦ nomatch e)

def monopoleConstant : Realization monopoleSignature :=
  realize monopoleSignature (fun _ _ _ ↦ -1) (fun e ↦ nomatch e)

abbrev monopoleArena : Arena where
  signature := monopoleSignature.{u}
  Law R := ∀ {ι : Type u} [i : Fintype ι] (B DPhi : ι → ℝ),
    |fieldDot B DPhi| ≤ R.readout () ⟨ι, i, B⟩ DPhi ∧
      (ymhEnergyDensity 0 B DPhi = |fieldDot B DPhi| ↔ B = DPhi ∨ B = -DPhi)

private theorem monopoleConstantFails : ¬ monopoleArena.{u}.Law monopoleConstant := by
  intro h
  have hz := (@h (ULift.{u} (Fin 1)) _ 0 0).1
  norm_num [monopoleConstant, realize, fieldDot] at hz

def monopoleFamily : Registration monopoleArena (type_of% (@bogomolny_monopole_bound.{u})) where
  actual := monopoleActual
  bridge := Iff.rfl
  variation := ⟨bogomolny_monopole_bound, monopoleConstant, monopoleConstantFails⟩
  sensitivity := singleSensitivity monopoleArena.Law monopoleActual _ monopoleConstantFails
  dependence := by
    rintro ⟨⟩
    refine ⟨⟨ULift.{u} (Fin 1), inferInstance, 0⟩, 0, 1, ?_⟩
    norm_num [monopoleActual, realize, ymhEnergyDensity, fieldNormSq, fieldDot, Pi.zero_apply,
      Pi.one_apply]
    change (0 : ℝ) * 0 ≠ 1 * 1
    norm_num

def monopoleRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bogomolny_monopole_bound.{u}) (Realization monopoleSignature.{u}) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.bogomolny_monopole_bound.__information_unit
    `Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.monopoleFamily
    monopoleArena monopoleFamily (realize monopoleSignature
      (fun _ p DPhi ↦ @ymhEnergyDensity p.1 p.2.1 0 p.2.2 DPhi) (fun e ↦ nomatch e)) #[0, 2]
    #["body", "body", "body", "body", "fn", "arg", "arg"] 3 false

abbrev realSignature : Signature := signature Unit (fun _ ↦ ℝ) (fun _ ↦ ℝ)

def realReadout (f : ℝ → ℝ) : Realization realSignature :=
  realize realSignature (fun _ _ x ↦ f x) (fun e ↦ nomatch e)

private theorem realDependence (f : ℝ → ℝ) (h : f 0 ≠ f 1) :
    ObservationalDependence realSignature (realReadout f) := fun _ ↦ ⟨(), 0, 1, h⟩

abbrev odeArena : Arena where
  signature := realSignature
  Law R := ∀ (u : ℝ), 0 < u →
    HasDerivAt psK (-(R.readout () () u * psH u) / u) u ∧
      HasDerivAt psH ((psH u - (psK u ^ 2 - 1)) / u) u

private theorem psK_one_pos : 0 < psK 1 := by
  exact div_pos (by norm_num) (Real.sinh_pos_iff.mpr (by norm_num))

private theorem odeConstantFails : ¬ odeArena.Law (realReadout fun _ ↦ 0) := by
  intro h
  have hz : deriv psK 1 = 0 := by
    simpa [realReadout, realize] using (h 1 (by norm_num)).1.deriv
  have hd := (ps_solves_bogomolny_ode 1 (by norm_num)).1.deriv
  have hH : 0 < psH 1 := by
    have hs : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr (by norm_num)
    have hsc : Real.sinh 1 < Real.cosh 1 := by
      rw [Real.sinh_eq, Real.cosh_eq]
      linarith [Real.exp_pos (-1)]
    rw [psH, one_mul, sub_pos]
    exact (one_lt_div hs).mpr hsc
  rw [hz] at hd
  have hneg : -(psK 1 * psH 1) / 1 < 0 := by
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos psK_one_pos hH)) (by norm_num)
  linarith

def odeFamily : Registration odeArena (type_of% (@ps_solves_bogomolny_ode)) where
  actual := realReadout psK
  bridge := Iff.rfl
  variation := ⟨ps_solves_bogomolny_ode, _, odeConstantFails⟩
  sensitivity := singleSensitivity odeArena.Law _ _ odeConstantFails
  dependence := realDependence psK (by
    rw [show psK 0 = 0 by simp [psK]]
    exact psK_one_pos.ne)

def odeRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ps_solves_bogomolny_ode) (Realization realSignature) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.ps_solves_bogomolny_ode.__information_unit
    `Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.odeFamily
    odeArena odeFamily (realize realSignature (fun _ _ x ↦ psK x) (fun e ↦ nomatch e)) #[]
    #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "fn", "arg"] 0 false

private theorem energy_one_pos : 0 < psEnergyDensity 1 := by
  have hk : psK 1 < 1 := (div_lt_one (Real.sinh_pos_iff.mpr (by norm_num))).mpr
    (Real.self_lt_sinh_iff.mpr (by norm_num))
  have hrad : 0 < (1 - psK 1 ^ 2) := by nlinarith [mul_pos (sub_pos.mpr hk) psK_one_pos]
  unfold psEnergyDensity
  have hpos : 0 < ((1 - psK 1 ^ 2) / 1) ^ 2 / 2 := by positivity
  have hmag : 0 ≤ (-(psK 1 * psH 1) / 1) ^ 2 := by positivity
  have hhiggs : 0 ≤ ((psH 1 - (psK 1 ^ 2 - 1) - psH 1) / 1) ^ 2 / 2 := by positivity
  have hmix : 0 ≤ (psK 1 * psH 1 / 1) ^ 2 := by positivity
  linarith only [hpos, hmag, hhiggs, hmix]

private theorem radialEnergyDependence :
    ObservationalDependence realSignature (realReadout psEnergyDensity) :=
  realDependence psEnergyDensity (by
    rw [show psEnergyDensity 0 = 0 by simp [psEnergyDensity]]
    exact energy_one_pos.ne)

abbrev radialArena : Arena where
  signature := realSignature
  Law R := ∀ (u : ℝ), 0 < u →
    R.readout () () u =
      deriv psK u ^ 2 + ((1 - psK u ^ 2) / u) ^ 2 / 2 +
        ((u * deriv psH u - psH u) / u) ^ 2 / 2 + (psK u * psH u / u) ^ 2

private theorem radialConstantFails : ¬ radialArena.Law (realReadout fun _ ↦ 0) := by
  intro h
  exact energy_one_pos.ne' ((ps_radial_energy_exact_deriv 1 (by norm_num)).trans
    (h 1 (by norm_num)).symm)

def radialFamily : Registration radialArena (type_of% (@ps_radial_energy_exact_deriv)) where
  actual := realReadout psEnergyDensity
  bridge := Iff.rfl
  variation := ⟨ps_radial_energy_exact_deriv, _, radialConstantFails⟩
  sensitivity := singleSensitivity radialArena.Law _ _ radialConstantFails
  dependence := radialEnergyDependence

def radialRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ps_radial_energy_exact_deriv) (Realization realSignature) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.ps_radial_energy_exact_deriv.__information_unit
    `Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.radialFamily
    radialArena radialFamily (realize realSignature (fun _ _ x ↦ psEnergyDensity x) (fun e ↦ nomatch e)) #[]
    #["body", "body", "fn", "arg"] 0 false

abbrev derivativeArena : Arena where
  signature := realSignature
  Law R := ∀ (u : ℝ), 0 < u → HasDerivAt psBoundary (R.readout () () u) u

private theorem derivativeConstantFails : ¬ derivativeArena.Law (realReadout fun _ ↦ 0) := by
  intro h
  exact energy_one_pos.ne' ((ps_total_deriv 1 (by norm_num)).unique (h 1 (by norm_num)))

def derivativeFamily : Registration derivativeArena (type_of% (@ps_total_deriv)) where
  actual := realReadout psEnergyDensity
  bridge := Iff.rfl
  variation := ⟨ps_total_deriv, _, derivativeConstantFails⟩
  sensitivity := singleSensitivity derivativeArena.Law _ _ derivativeConstantFails
  dependence := radialEnergyDependence

def derivativeRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ps_total_deriv) (Realization realSignature) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.ps_total_deriv.__information_unit
    `Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.derivativeFamily
    derivativeArena derivativeFamily (realize realSignature (fun _ _ x ↦ psEnergyDensity x) (fun e ↦ nomatch e)) #[]
    #["body", "body", "fn", "arg"] 0 false

abbrev boundaryArena : Arena where
  signature := realSignature
  Law R := Tendsto psBoundary (𝓝[>] 0) (𝓝 0) ∧ Tendsto (R.readout () ()) atTop (𝓝 1)

private theorem zero_does_not_tendsto_one :
    ¬ Tendsto (fun _ : ℝ ↦ (0 : ℝ)) atTop (𝓝 1) := by
  intro h
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds h)

private theorem boundaryConstantFails : ¬ boundaryArena.Law (realReadout fun _ ↦ 0) :=
  fun h ↦ zero_does_not_tendsto_one h.2

def boundaryFamily : Registration boundaryArena (type_of% (@ps_origin_and_infinity_limits)) where
  actual := realReadout psBoundary
  bridge := Iff.rfl
  variation := ⟨ps_origin_and_infinity_limits, _, boundaryConstantFails⟩
  sensitivity := singleSensitivity boundaryArena.Law _ _ boundaryConstantFails
  dependence := by
    intro _
    by_contra! h
    have hc : psBoundary = fun _ ↦ 0 := by
      funext x
      have hx : psBoundary x = psBoundary 0 := h () x 0
      simpa [psBoundary] using hx
    exact zero_does_not_tendsto_one (hc ▸ ps_origin_and_infinity_limits.2)

def boundaryRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ps_origin_and_infinity_limits) (Realization realSignature) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.ps_origin_and_infinity_limits.__information_unit
    `Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.boundaryFamily
    boundaryArena boundaryFamily (realize realSignature (fun _ _ x ↦ psBoundary x) (fun e ↦ nomatch e)) #[]
    #["arg", "fn", "fn", "arg"] 0 true

abbrev massSignature : Signature := signature ℝ (fun _ ↦ ℝ) (fun _ ↦ ℝ)

def massReadout (f : ℝ → ℝ → ℝ) : Realization massSignature :=
  realize massSignature (fun _ g v ↦ f g v) (fun e ↦ nomatch e)

def monopoleMassActual : Realization massSignature :=
  massReadout (fun g v ↦ 4 * Real.pi * v / g)

abbrev monopoleMassArena : Arena where
  signature := massSignature
  Law R := ∀ g v : ℝ, 0 < g → 0 < v →
    IntegrableOn psEnergyDensity (Ioi 0) ∧ (∫ u in Ioi 0, psEnergyDensity u) = 1 ∧
      (4 * Real.pi * v / g) * (∫ u in Ioi 0, psEnergyDensity u) = R.readout () g v ∧
      0 < 4 * Real.pi * v / g

private theorem monopoleMassConstantFails :
    ¬ monopoleMassArena.Law (massReadout fun _ _ ↦ 0) := by
  intro h
  have hb := (h 1 1 (by norm_num) (by norm_num)).2.2.1
  have ha := (ps_monopole_exact_mass 1 1 (by norm_num) (by norm_num)).2.2
  exact ha.2.ne' (ha.1.symm.trans hb)

def monopoleMassFamily :
    Registration monopoleMassArena (type_of% (@ps_monopole_exact_mass)) where
  actual := monopoleMassActual
  bridge := Iff.rfl
  variation := ⟨ps_monopole_exact_mass, _, monopoleMassConstantFails⟩
  sensitivity := singleSensitivity monopoleMassArena.Law _ _ monopoleMassConstantFails
  dependence := by
    intro _
    refine ⟨1, 0, 1, ?_⟩
    change (4 * Real.pi * 0 / 1 : ℝ) ≠ 4 * Real.pi * 1 / 1
    simp only [mul_zero, mul_one, div_one, ne_eq]
    exact ne_of_lt (by positivity)

def monopoleMassRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ps_monopole_exact_mass) (Realization massSignature) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.ps_monopole_exact_mass.__information_unit
    `Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D.monopoleMassFamily
    monopoleMassArena monopoleMassFamily (realize massSignature
      (fun _ g v ↦ 4 * Real.pi * v / g) (fun e ↦ nomatch e)) #[0]
    #["body", "body", "body", "body", "arg", "arg", "fn", "arg", "arg"] 1 false

end

end Reg.D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D
