import D5.S3.Geometry.Lorentz.HawkingUnruhThermalRadiation4D
import Reg.Support.UnitSixO.Common

/-! Dependent observations of the analytic functions in the source statements. -/

open LeanInformationAudit Filter MeasureTheory Set
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Lorentz.HawkingUnruhThermalRadiation4D
open _root_.Reg.Support.UnitSixO (operandSignature)
open _root_.D5.S3.Geometry.Lorentz.BlackHoleThermodynamics4D

namespace Reg.D5.S3.Geometry.Lorentz.HawkingUnruhThermalRadiation4D

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

local macro "bindSource% " source:ident group:ident arena:term:max family:term:max
    operand:ident occurrence:num : term => do
  let owner := `D5.S3.Geometry.Lorentz.HawkingUnruhThermalRadiation4D
  let unitName := owner ++ source.getId ++ `__information_unit
  let familyName := `Reg.D5.S3.Geometry.Lorentz.HawkingUnruhThermalRadiation4D ++ group.getId ++ `family
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
        owner := `D5.S3.Geometry.Lorentz.HawkingUnruhThermalRadiation4D
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

namespace Conical

abbrev Observation : Signature := operandSignature ℝ (ℝ → ℝ → ℝ)

abbrev arena : Arena where
  signature := Observation
  Law R := ∀ {κ β ρ : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hρ : 0 < ρ),
    (R.readout () ()) κ β ρ / (2 * Real.pi * ρ) = κ * β / (2 * Real.pi) ∧
    (euclideanCircumference κ β ρ / (2 * Real.pi * ρ) = 1 ↔ β = 2 * Real.pi / κ) ∧
    (β = 2 * Real.pi / κ ↔ 1 / β = hawkingTemp 1 κ)

def family : Registration arena (type_of% (@gibbons_hawking_conical_periodicity)) :=
  unitFamily% arena (@gibbons_hawking_conical_periodicity) (unitObserve% euclideanCircumference)
    (unitObserve% (fun _ _ _ => 0))
    (by
      intro h
      have he := (h (κ := 1) (β := 1) (ρ := 1) (by norm_num) (by norm_num) (by norm_num)).1
      change 0 / (2 * Real.pi * 1) = 1 * 1 / (2 * Real.pi) at he
      simp only [zero_div, mul_one, one_mul] at he
      exact (by positivity : 0 < 1 / (2 * Real.pi)).ne' he.symm)
    (by
      refine ⟨(), 0, 1, fun h => ?_⟩
      have he := congrFun (congrFun h 1) 1
      change euclideanCircumference 0 1 1 = euclideanCircumference 1 1 1 at he
      have hr := (gibbons_hawking_conical_periodicity (κ := 1) (β := 1) (ρ := 1)
        (by norm_num) (by norm_num) (by norm_num)).1
      have hz : euclideanCircumference 0 1 1 = 0 := by simp [euclideanCircumference]
      rw [← he, hz] at hr
      simp only [zero_div, mul_one, one_mul] at hr
      exact (by positivity : 0 < 1 / (2 * Real.pi)).ne' hr.symm)

def registration : Contract.Registration.{
    _, _, _, 0, 0, 0, _, _, _, _, _, 0} (@gibbons_hawking_conical_periodicity) (Realization Observation) Unit Unit :=
  bindSource% gibbons_hawking_conical_periodicity Conical arena family euclideanCircumference 0

end Conical

namespace Spectra

abbrev Observation : Signature := operandSignature ℝ (ℝ)

abbrev arena : Arena where
  signature := Observation
  Law R := ∀ {β ω : ℝ} (hβ : 0 < β) (hω : 0 < ω),
    (∀ A B : ℝ, A - B = 1 → A = (R.readout () ()) (β * ω) * B →
      B = 1 / (Real.exp (β * ω) - 1) ∧ 0 < B ∧
      A = Real.exp (β * ω) / (Real.exp (β * ω) - 1) ∧ A = 1 + B ∧
      B / (1 + B) = Real.exp (-(β * ω))) ∧
    (∀ A B : ℝ, A + B = 1 → A = Real.exp (β * ω) * B →
      B = 1 / (Real.exp (β * ω) + 1) ∧ 0 < B ∧ B < 1 / 2 ∧
      A = Real.exp (β * ω) / (Real.exp (β * ω) + 1) ∧ A = 1 - B ∧
      B / (1 - B) = Real.exp (-(β * ω)) ∧
      A = NullConeGravity.NullModularKMSUniqueness.thermal β ω) ∧
    Tendsto (fun x : ℝ => x / (Real.exp (β * x) - 1)) (𝓝[>] 0) (𝓝 (1 / β)) ∧
    Tendsto (fun x : ℝ => Real.exp (β * x) * (1 / (Real.exp (β * x) - 1))) atTop (𝓝 1)

def family : Registration arena (type_of% (@bogoliubov_planck_and_fermi_dirac_spectra)) :=
  unitFamily% arena (@bogoliubov_planck_and_fermi_dirac_spectra) (unitObserve% Real.exp)
    (unitObserve% (fun _ => 2))
    (by
      intro h
      have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
      have hE : Real.exp (Real.log 3) = 3 := Real.exp_log (by norm_num)
      have hh := (h (β := 1) (ω := Real.log 3) (by norm_num) hlog).1 2 1
        (by norm_num) (by change (2 : ℝ) = 2 * 1; norm_num)
      norm_num [one_mul, hE] at hh)
    (by
      refine ⟨(), 0, 1, fun h => ?_⟩
      change Real.exp 0 = Real.exp 1 at h
      have hp := Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)
      rw [Real.exp_zero] at h
      exact hp.ne h)

def registration : Contract.Registration.{
    _, _, _, 0, 0, 0, _, _, _, _, _, 0} (@bogoliubov_planck_and_fermi_dirac_spectra) (Realization Observation) Unit Unit :=
  bindSource% bogoliubov_planck_and_fermi_dirac_spectra Spectra arena family Real.exp 0

end Spectra

namespace Moments

abbrev Observation : Signature := operandSignature ℝ (ℝ)

abbrev arena : Arena where
  signature := Observation
  Law R := (∫ x in Ioi (0 : ℝ), x ^ 3 / ((R.readout () ()) x - 1)) = Real.pi ^ 4 / 15 ∧
    (∫ x in Ioi (0 : ℝ), x ^ 3 / (Real.exp x + 1)) = (7 / 8) * (Real.pi ^ 4 / 15)

def family : Registration arena (type_of% (@stefan_boltzmann_4d_bose_and_fermi_integrals)) :=
  unitFamily% arena (@stefan_boltzmann_4d_bose_and_fermi_integrals) (unitObserve% Real.exp)
    (unitObserve% (fun _ => 1))
    (by
      intro h
      have he := h.1
      change (∫ x in Ioi (0 : ℝ), x ^ 3 / ((1 : ℝ) - 1)) = Real.pi ^ 4 / 15 at he
      simp only [sub_self, div_zero, integral_zero] at he
      exact (by positivity : 0 < Real.pi ^ 4 / 15).ne' he.symm)
    (by
      refine ⟨(), 0, 1, fun h => ?_⟩
      change Real.exp 0 = Real.exp 1 at h
      have hp := Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)
      rw [Real.exp_zero] at h
      exact hp.ne h)

def registration : Contract.Registration.{
    _, _, _, 0, 0, 0, _, _, _, _, _, 0} (@stefan_boltzmann_4d_bose_and_fermi_integrals) (Realization Observation) Unit Unit :=
  bindSource% stefan_boltzmann_4d_bose_and_fermi_integrals Moments arena family Real.exp 0

end Moments

namespace Luminosity

abbrev Observation : Signature := operandSignature ℝ (ℝ → ℝ)

abbrev arena : Arena where
  signature := Observation
  Law R := ∀ (g : ℝ) {M : ℝ} (hM : 0 < M),
    hawkingTemp 1 (surfaceGravity M 0 0) = 1 / (8 * Real.pi * M) ∧
    (R.readout () ()) g M =
      g * (Real.pi ^ 2 / 120) * (16 * Real.pi * M ^ 2) * (1 / (8 * Real.pi * M)) ^ 4 ∧
    hawkingLuminosity g M = g / (30720 * Real.pi * M ^ 2)

def family : Registration arena (type_of% (@hawking_luminosity_inverse_square_law)) :=
  unitFamily% arena (@hawking_luminosity_inverse_square_law) (unitObserve% hawkingLuminosity)
    (unitObserve% (fun _ _ => 0))
    (by
      intro h
      have he := (h 1 (M := 1) (by norm_num)).2.1
      change (0 : ℝ) = 1 * (Real.pi ^ 2 / 120) *
        (16 * Real.pi * 1 ^ 2) * (1 / (8 * Real.pi * 1)) ^ 4 at he
      exact (by positivity : 0 < 1 * (Real.pi ^ 2 / 120) *
        (16 * Real.pi * 1 ^ 2) * (1 / (8 * Real.pi * 1)) ^ 4).ne' he.symm)
    (by
      refine ⟨(), 0, 1, fun h => ?_⟩
      have he := congrFun h 1
      change hawkingLuminosity 0 1 = hawkingLuminosity 1 1 at he
      rw [show hawkingLuminosity 0 1 = 0 by simp [hawkingLuminosity],
        (hawking_luminosity_inverse_square_law 1 (M := 1) (by norm_num)).2.2] at he
      exact (by positivity : 0 < 1 / (30720 * Real.pi * (1 : ℝ) ^ 2)).ne' he.symm)

def registration : Contract.Registration.{
    _, _, _, 0, 0, 0, _, _, _, _, _, 0} (@hawking_luminosity_inverse_square_law) (Realization Observation) Unit Unit :=
  bindSource% hawking_luminosity_inverse_square_law Luminosity arena family hawkingLuminosity 0

end Luminosity

namespace Trajectory

abbrev Observation : Signature := operandSignature ℝ (ℝ → ℝ → ℝ)

abbrev arena : Arena where
  signature := Observation
  Law R := ∀ {M₀ α : ℝ} (hM₀ : 0 < M₀) (hα : 0 < α),
    (R.readout () ()) M₀ α 0 = M₀ ∧
    (∀ t ∈ Ico 0 (evapTime M₀ α), 0 < evapMass M₀ α t ∧
      HasDerivAt (evapMass M₀ α) (-α / (evapMass M₀ α t) ^ 2) t) ∧
    Tendsto (evapMass M₀ α) (𝓝[<] evapTime M₀ α) (𝓝 0) ∧
    Tendsto (fun t => 1 / (8 * Real.pi * evapMass M₀ α t))
      (𝓝[<] evapTime M₀ α) atTop

def family : Registration arena (type_of% (@hawking_evaporation_trajectory_and_runaway_heating)) :=
  unitFamily% arena (@hawking_evaporation_trajectory_and_runaway_heating) (unitObserve% evapMass)
    (unitObserve% (fun _ _ _ => 0))
    (by
      intro h
      have he := (h (M₀ := 1) (α := 1) (by norm_num) (by norm_num)).1
      change (0 : ℝ) = 1 at he
      norm_num at he)
    (by
      refine ⟨(), 0, 1, fun h => ?_⟩
      have he := congrFun (congrFun h 1) 0
      change evapMass 0 1 0 = evapMass 1 1 0 at he
      simp [evapMass] at he)

def registration : Contract.Registration.{
    _, _, _, 0, 0, 0, _, _, _, _, _, 0} (@hawking_evaporation_trajectory_and_runaway_heating) (Realization Observation) Unit Unit :=
  bindSource% hawking_evaporation_trajectory_and_runaway_heating Trajectory arena family evapMass 0

end Trajectory

namespace Entropy

abbrev Observation : Signature := operandSignature ℝ (ℝ → ℝ → ℝ)

abbrev arena : Arena where
  signature := Observation
  Law R := ∀ {M₀ α : ℝ} (hM₀ : 0 < M₀) (hα : 0 < α),
    (∀ t ∈ Ico 0 (evapTime M₀ α),
      let M := evapMass M₀ α t
      let P := hawkingPower α M
      let T := schwarzschildTemp 1 1 M
      schwarzschildEntropy M = 4 * Real.pi * M ^ 2 ∧
      HasDerivAt (fun s => 4 * Real.pi * (evapMass M₀ α s) ^ 2) (-P / T) t ∧
      -P / T = -8 * Real.pi * α / M ∧ -P / T < 0 ∧
      (R.readout () ()) M₀ α t = (4 / 3) * (P / T) ∧
      evaporationEntropyFlux M₀ α t + (-P / T) = (1 / 3) * (P / T) ∧
      (1 / 3) * (P / T) = (8 * Real.pi / 3) * (α / M) ∧
      0 < (1 / 3) * (P / T)) ∧
    IntervalIntegrable (evaporationEntropyFlux M₀ α) volume 0 (evapTime M₀ α) ∧
    (∫ t in 0..evapTime M₀ α, evaporationEntropyFlux M₀ α t) =
      (4 / 3) * schwarzschildEntropy M₀ ∧
    (∫ t in 0..evapTime M₀ α, evaporationEntropyFlux M₀ α t) - schwarzschildEntropy M₀ =
      (1 / 3) * schwarzschildEntropy M₀ ∧
    0 < (1 / 3) * schwarzschildEntropy M₀

def family : Registration arena (type_of% (@zurek_generalized_second_law_irreversible_entropy_production)) :=
  unitFamily% arena (@zurek_generalized_second_law_irreversible_entropy_production) (unitObserve% evaporationEntropyFlux)
    (unitObserve% (fun _ _ _ => 0))
    (by
      intro h
      have ht : (0 : ℝ) ∈ Ico 0 (evapTime 1 1) := by norm_num [evapTime]
      have he := ((h (M₀ := 1) (α := 1) (by norm_num) (by norm_num)).1 0 ht).2.2.2.2.1
      change (0 : ℝ) = (4 / 3) * (hawkingPower 1 (evapMass 1 1 0) /
        schwarzschildTemp 1 1 (evapMass 1 1 0)) at he
      simp only [show evapMass 1 1 0 = 1 by simp [evapMass]] at he
      have hp : 0 < (4 / 3) * (hawkingPower 1 1 / schwarzschildTemp 1 1 1) := by
        unfold hawkingPower schwarzschildTemp
        positivity
      exact hp.ne' he.symm)
    (by
      refine ⟨(), 0, 1, fun h => ?_⟩
      have he := congrFun (congrFun h 1) 0
      change evaporationEntropyFlux 0 1 0 = evaporationEntropyFlux 1 1 0 at he
      have h₀ : evapMass 0 1 0 = 0 := by simp [evapMass]
      have h₁ : evapMass 1 1 0 = 1 := by simp [evapMass]
      have hz : evaporationEntropyFlux 0 1 0 = 0 := by
        simp [evaporationEntropyFlux, radiationEntropyFlux, hawkingPower, h₀]
      have hp : 0 < evaporationEntropyFlux 1 1 0 := by
        unfold evaporationEntropyFlux
        rw [h₁]
        unfold radiationEntropyFlux hawkingPower schwarzschildTemp
        positivity
      exact hp.ne' (he.symm.trans hz))

def registration : Contract.Registration.{
    _, _, _, 0, 0, 0, _, _, _, _, _, 0} (@zurek_generalized_second_law_irreversible_entropy_production) (Realization Observation) Unit Unit :=
  bindSource% zurek_generalized_second_law_irreversible_entropy_production Entropy arena family evaporationEntropyFlux 0

end Entropy

end

end Reg.D5.S3.Geometry.Lorentz.HawkingUnruhThermalRadiation4D
