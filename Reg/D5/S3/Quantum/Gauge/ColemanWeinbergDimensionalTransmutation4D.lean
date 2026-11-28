import D5.S3.Quantum.Gauge.ColemanWeinbergDimensionalTransmutation4D
import Reg.Support.UnitSixO.Common

/-! Dependent observations of the analytic functions in the source statements. -/

open LeanInformationAudit Filter Set
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Gauge.ColemanWeinbergDimensionalTransmutation4D
open _root_.Reg.Support.UnitSixO (operandSignature)
open _root_.D5.S3.Quantum.Gauge

namespace Reg.D5.S3.Quantum.Gauge.ColemanWeinbergDimensionalTransmutation4D

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

local macro "bindSource% " source:ident group:ident arena:term:max family:term:max
    operand:ident occurrence:num : term => do
  let owner := `D5.S3.Quantum.Gauge.ColemanWeinbergDimensionalTransmutation4D
  let unitName := owner ++ source.getId ++ `__information_unit
  let familyName := `Reg.D5.S3.Quantum.Gauge.ColemanWeinbergDimensionalTransmutation4D ++ group.getId ++ `family
  `({ unitName := $(Lean.quote unitName)
      realizationName := $(Lean.quote familyName)
      realizationSource := none
      generated := false
      arena := .source ⟨$arena⟩
      objectArena := .source ⟨$arena⟩
      catalog := Lean.Name.anonymous
      localNames := false
      realization := .source $arena ⟨$family⟩
      correspondence := ⟨.evidence, .evidence⟩
      bundleNonempty := .absent
      readout := some (unitObserve% $operand)
      variation := .absent
      sensitivity := .absent
      partialSensitivity := none
      escapeFrom := none
      sourceSelection := some {
        owner := `D5.S3.Quantum.Gauge.ColemanWeinbergDimensionalTransmutation4D
        definition := none
        coordinates := #[]
        readouts := #[{
          path := unitPath% $source $operand 0 $occurrence
          stateBinder := 0
          functionOperand := true
          stateOperand := none
          booleanPredicate := false }] }
      continuation := .unknown
      familyRecord := none
      options := #[] })

namespace Renormalization

abbrev Observation : Signature := operandSignature ℝ (ℝ → ℝ → ℝ → ℝ)

abbrev arena : Arena where
  signature := Observation
  Law R := ∀ {M : ℝ} (hM : 0 < M) (lam B : ℝ),
    iteratedDeriv 4 (fun φ => φ ^ 4 * Real.log (φ ^ 2 / M ^ 2)) M = 100 ∧
    iteratedDeriv 4 (fun φ => φ ^ 4 * (Real.log (φ ^ 2 / M ^ 2) - 25 / 6)) M = 0 ∧
    iteratedDeriv 4 ((R.readout () ()) lam B M) M = lam ∧
    (B ≠ 0 → ∀ c : ℝ, iteratedDeriv 4 (fun φ => lam / 24 * φ ^ 4 +
      B * φ ^ 4 * (Real.log (φ ^ 2 / M ^ 2) - c)) M = lam ↔ c = 25 / 6)

def family : Registration arena (type_of% (@cw_fourth_derivative_renormalization_condition)) :=
  unitFamily% arena (@cw_fourth_derivative_renormalization_condition) (unitObserve% cwPotential)
    (unitObserve% (fun _ _ _ _ => 0))
    (by
      intro h
      have hz := (h (M := 1) (by norm_num) 1 0).2.2.1
      change iteratedDeriv 4 (fun _ : ℝ => (0 : ℝ)) 1 = 1 at hz
      norm_num [iteratedDeriv_fun_const_zero] at hz)
    (by
      refine ⟨(), 0, 24, fun h => ?_⟩
      have he := congrFun (congrFun (congrFun h 0) 1) 1
      change cwPotential 0 0 1 1 = cwPotential 24 0 1 1 at he
      norm_num [cwPotential] at he)

def registration : Contract.Registration.{
    _, _, _, 0, 0, 0, _, _, _, _, _, 0} (@cw_fourth_derivative_renormalization_condition) (Realization Observation) Unit Unit :=
  bindSource% cw_fourth_derivative_renormalization_condition Renormalization arena family cwPotential 0

end Renormalization

namespace Scale

abbrev Observation : Signature := operandSignature ℝ (ℝ → ℝ → ℝ)

abbrev arena : Arena where
  signature := Observation
  Law R := ∀ {B M : ℝ} (hB : 0 < B) (hM : 0 < M) (lam e : ℝ),
    0 < (R.readout () ()) lam B M ∧
    (∀ φ : ℝ, cwPotential lam B M φ = cwUniversal B (cwVev lam B M) φ) ∧
    ContinuousAt (cwPotential lam B M) 0 ∧
    (M = cwVev lam B M ↔ lam = 88 * B) ∧
    (B = cwCoeff e → (M = cwVev lam B M ↔ lam = 33 * e ^ 4 / (8 * Real.pi ^ 2)))

def family : Registration arena (type_of% (@cw_dimensional_transmutation_and_coupling_lock)) :=
  unitFamily% arena (@cw_dimensional_transmutation_and_coupling_lock) (unitObserve% cwVev)
    (unitObserve% (fun _ _ _ => 0))
    (by
      intro h
      have hz := (h (B := 1) (M := 1) (by norm_num) (by norm_num) 88 0).1
      change (0 : ℝ) < 0 at hz
      exact (lt_irrefl 0) hz)
    (by
      refine ⟨(), 0, 88, fun h => ?_⟩
      have he := congrFun (congrFun h 1) 1
      change cwVev 0 1 1 = cwVev 88 1 1 at he
      have hc : Real.exp (11 / 6 : ℝ) ≠ 1 :=
        ne_of_gt (Real.one_lt_exp_iff.mpr (by norm_num))
      simp only [cwVev, zero_div, sub_zero, one_mul] at he
      rw [show (11 / 6 : ℝ) - 88 / (48 * 1) = 0 by norm_num, Real.exp_zero] at he
      exact hc he)

def registration : Contract.Registration.{
    _, _, _, 0, 0, 0, _, _, _, _, _, 0} (@cw_dimensional_transmutation_and_coupling_lock) (Realization Observation) Unit Unit :=
  bindSource% cw_dimensional_transmutation_and_coupling_lock Scale arena family cwVev 0

end Scale

namespace Minimum

abbrev Observation : Signature := operandSignature ℝ (ℝ → ℝ → ℝ)

abbrev arena : Arena where
  signature := Observation
  Law R := ∀ {B v : ℝ} (hB : 0 < B) (hv : 0 < v),
    (∀ φ : ℝ, HasDerivAt ((R.readout () ()) B v) (4 * B * φ ^ 3 * Real.log (φ ^ 2 / v ^ 2)) φ) ∧
    (∀ φ : ℝ, cwUniversal B v v ≤ cwUniversal B v φ) ∧
    (∀ φ : ℝ, cwUniversal B v φ = cwUniversal B v v ↔ φ = v ∨ φ = -v) ∧
    cwUniversal B v v = -(1 / 2) * B * v ^ 4 ∧
    cwUniversal B v v < 0 ∧ cwUniversal B v 0 = 0

def family : Registration arena (type_of% (@cw_radiative_global_minimum_and_symmetry_breaking)) :=
  unitFamily% arena (@cw_radiative_global_minimum_and_symmetry_breaking) (unitObserve% cwUniversal)
    (unitObserve% (fun _ _ _ => 0))
    (by
      intro h
      have hh := h (B := 1) (v := 1) (by norm_num) (by norm_num)
      have hd := (hh.1 2).deriv
      change deriv (fun _ : ℝ => (0 : ℝ)) 2 = 4 * 1 * 2 ^ 3 * Real.log (2 ^ 2 / 1 ^ 2) at hd
      have hp : 0 < Real.log 4 := Real.log_pos (by norm_num)
      norm_num at hd <;> linarith)
    (by
      refine ⟨(), 0, 1, fun h => ?_⟩
      have he := congrFun (congrFun h 1) 1
      change cwUniversal 0 1 1 = cwUniversal 1 1 1 at he
      norm_num [cwUniversal] at he)

def registration : Contract.Registration.{
    _, _, _, 0, 0, 0, _, _, _, _, _, 0} (@cw_radiative_global_minimum_and_symmetry_breaking) (Realization Observation) Unit Unit :=
  bindSource% cw_radiative_global_minimum_and_symmetry_breaking Minimum arena family cwUniversal 0

end Minimum

namespace Curvature

abbrev Observation : Signature := operandSignature ℝ (ℝ → ℝ → ℝ)

abbrev arena : Arena where
  signature := Observation
  Law R := ∀ {B v e : ℝ} (hB : 0 < B) (hv : 0 < v) (he : 0 < e),
    HasDerivAt (deriv ((R.readout () ()) B v)) (8 * B * v ^ 2) v ∧
    deriv (deriv (cwUniversal B v)) v = 8 * B * v ^ 2 ∧
    0 < deriv (deriv (cwUniversal B v)) v ∧
    ElectroweakHiggsMechanism4D.mWSq (2 * e) v = e ^ 2 * v ^ 2 ∧
    (B = cwCoeff e →
      deriv (deriv (cwUniversal B v)) v / (e ^ 2 * v ^ 2) = 3 * e ^ 2 / (8 * Real.pi ^ 2) ∧
      3 * e ^ 2 / (8 * Real.pi ^ 2) = 3 * (e ^ 2 / (4 * Real.pi)) / (2 * Real.pi))

def family : Registration arena (type_of% (@cw_radiative_scalar_to_vector_mass_ratio)) :=
  unitFamily% arena (@cw_radiative_scalar_to_vector_mass_ratio) (unitObserve% cwUniversal)
    (unitObserve% (fun _ _ _ => 0))
    (by
      intro h
      have hd := (h (B := 1) (v := 1) (e := 1) (by norm_num) (by norm_num) (by norm_num)).1.deriv
      change deriv (deriv (fun _ : ℝ => (0 : ℝ))) 1 = 8 * 1 * 1 ^ 2 at hd
      have hz : deriv (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := funext fun x => deriv_const x 0
      rw [hz, deriv_const] at hd
      norm_num at hd)
    (by
      refine ⟨(), 0, 1, fun h => ?_⟩
      have he := congrFun (congrFun h 1) 1
      change cwUniversal 0 1 1 = cwUniversal 1 1 1 at he
      norm_num [cwUniversal] at he)

def registration : Contract.Registration.{
    _, _, _, 0, 0, 0, _, _, _, _, _, 0} (@cw_radiative_scalar_to_vector_mass_ratio) (Realization Observation) Unit Unit :=
  bindSource% cw_radiative_scalar_to_vector_mass_ratio Curvature arena family cwUniversal 0

end Curvature

namespace Running

abbrev Observation : Signature := operandSignature ℝ (ℝ → ℝ → ℝ → ℝ)

abbrev arena : Arena where
  signature := Observation
  Law R := ∀ {B M₀ M : ℝ} (hB : 0 < B) (hM₀ : 0 < M₀) (hM : 0 < M) (lam₀ e : ℝ),
    M * deriv ((R.readout () ()) lam₀ B M₀) M = 48 * B ∧
    (B = cwCoeff e → 48 * B = 9 * e ^ 4 / (4 * Real.pi ^ 2)) ∧
    cwVev (cwRunningLam lam₀ B M₀ M) B M = cwVev lam₀ B M₀ ∧
    (∀ φ : ℝ, cwPotential (cwRunningLam lam₀ B M₀ M) B M φ = cwPotential lam₀ B M₀ φ)

def family : Registration arena (type_of% (@cw_callan_symanzik_rg_invariance)) :=
  unitFamily% arena (@cw_callan_symanzik_rg_invariance) (unitObserve% cwRunningLam)
    (unitObserve% (fun _ _ _ _ => 0))
    (by
      intro h
      have hz := (h (B := 1) (M₀ := 1) (M := 1) (by norm_num) (by norm_num) (by norm_num) 0 0).1
      change 1 * deriv (fun _ : ℝ => (0 : ℝ)) 1 = 48 * 1 at hz
      rw [deriv_const] at hz
      norm_num at hz)
    (by
      refine ⟨(), 0, 1, fun h => ?_⟩
      have he := congrFun (congrFun (congrFun h 1) 1) 1
      change cwRunningLam 0 1 1 1 = cwRunningLam 1 1 1 1 at he
      norm_num [cwRunningLam] at he)

def registration : Contract.Registration.{
    _, _, _, 0, 0, 0, _, _, _, _, _, 0} (@cw_callan_symanzik_rg_invariance) (Realization Observation) Unit Unit :=
  bindSource% cw_callan_symanzik_rg_invariance Running arena family cwRunningLam 0

end Running

namespace Stability

abbrev Observation : Signature := operandSignature ℝ (ℝ → ℝ → ℝ)

abbrev arena : Arena where
  signature := Observation
  Law R := ∀ {M : ℝ} (hM : 0 < M) (lam B e y_t Nc : ℝ),
    (0 < (R.readout () ()) e y_t Nc ↔ 4 * Nc * y_t ^ 4 < 3 * e ^ 4) ∧
    (0 < B → Tendsto (cwPotential lam B M) atTop atTop ∧ BddBelow (Set.range (cwPotential lam B M))) ∧
    (B < 0 → Tendsto (cwPotential lam B M) atTop atBot)

def family : Registration arena (type_of% (@cw_yukawa_vacuum_stability_threshold)) :=
  unitFamily% arena (@cw_yukawa_vacuum_stability_threshold) (unitObserve% cwEffCoeff)
    (unitObserve% (fun _ _ _ => 0))
    (by
      intro h
      have hh := (h (M := 1) (by norm_num) 0 1 1 0 1).1.mpr (by norm_num)
      change (0 : ℝ) < 0 at hh
      exact (lt_irrefl 0) hh)
    (by
      refine ⟨(), 0, 1, fun h => ?_⟩
      have he := congrFun (congrFun h 0) 1
      change cwEffCoeff 0 0 1 = cwEffCoeff 1 0 1 at he
      have hp : 0 < cwEffCoeff 1 0 1 :=
        ((cw_yukawa_vacuum_stability_threshold (M := 1) (by norm_num) 0 1 1 0 1).1).mpr (by norm_num)
      have hz : cwEffCoeff 0 0 1 = 0 := by simp [cwEffCoeff]
      exact hp.ne' (he.symm.trans hz))

def registration : Contract.Registration.{
    _, _, _, 0, 0, 0, _, _, _, _, _, 0} (@cw_yukawa_vacuum_stability_threshold) (Realization Observation) Unit Unit :=
  bindSource% cw_yukawa_vacuum_stability_threshold Stability arena family cwEffCoeff 0

end Stability

end

end Reg.D5.S3.Quantum.Gauge.ColemanWeinbergDimensionalTransmutation4D
