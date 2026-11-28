import D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D
import Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.Common

open _root_.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter MeasureTheory Set
open scoped Topology

namespace Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace CircularRadial

abbrev signature : Signature := operandSignature (ℝ) (ℕ → ℝ → ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℝ) (k : ℕ) {ζ r : ℝ}
      (hζ : 0 < ζ) (hζk : ζ < (k : ℝ)) (hr : 0 < r),
    let G := R.readout () () m k ζ
    let F := circularF m k ζ
    let rate := circularGamma k ζ / r - circularDecay m k ζ
    HasDerivAt G (rate * G r) r ∧ HasDerivAt F (rate * F r) r ∧
      radialDiracAt m (circularEnergy m k ζ) ζ (-(k : ℤ)) G F r

def actual : Realization signature := diracObserve% (circularG)

def family : Registration arena (type_of% (@dirac_circular_solves_coupled_radial_ode)) :=
  diracFamily% arena (@dirac_circular_solves_coupled_radial_ode) actual
    (diracObserve% (fun _ _ _ _ => 1))
    (by
      intro h
      have hd := (h 0 1 (ζ := 1 / 2) (r := 1)
        (by norm_num) (by norm_num) (by norm_num)).1.deriv
      have hpos : 0 < Real.sqrt (1 - ((2 : ℝ) ^ 2)⁻¹) := by positivity
      simp [realize, circularGamma, circularDecay] at hd
      exact hpos.ne' hd.symm)
    (by
      refine ⟨(), 0, 1, ?_⟩
      intro h
      have e := congrArg (fun f : ℕ → ℝ → ℝ → ℝ => f 1 (1 / 2) 1) h
      have he : Real.exp (-(1 / 2 : ℝ)) < Real.exp 0 := Real.exp_lt_exp.mpr (by norm_num)
      rw [Real.exp_zero] at he
      norm_num [actual, realize, circularG, circularDecay] at e
      exact he.ne e.symm)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@dirac_circular_solves_coupled_radial_ode) (Realization signature) Unit Unit :=
  diracBind% `D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.dirac_circular_solves_coupled_radial_ode.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.CircularRadial.family
    arena family (diracObserve% (circularG))
    #[]
    #[{ path := diracPath% dirac_circular_solves_coupled_radial_ode circularG 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end CircularRadial

namespace GroundRadial

abbrev signature : Signature := operandSignature (ℝ) (ℕ → ℝ → ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℝ) {ζ r : ℝ}
      (hζ : 0 < ζ) (hζk : ζ < 1) (hr : 0 < r),
    let G := R.readout () () m 1 ζ
    let F := circularF m 1 ζ
    let rate := Real.sqrt (1 - ζ ^ 2) / r - m * ζ
    HasDerivAt G (rate * G r) r ∧ HasDerivAt F (rate * F r) r ∧
      radialDiracAt m (m * Real.sqrt (1 - ζ ^ 2)) ζ (-1) G F r

def actual : Realization signature := diracObserve% (circularG)

def family : Registration arena (type_of% (@dirac_1s_solves_coupled_radial_ode)) :=
  diracFamily% arena (@dirac_1s_solves_coupled_radial_ode) actual
    (diracObserve% (fun _ _ _ _ => 1))
    (by
      intro h
      have hd := (h 0 (ζ := 1 / 2) (r := 1)
        (by norm_num) (by norm_num) (by norm_num)).1.deriv
      have hpos : 0 < Real.sqrt (1 - ((2 : ℝ) ^ 2)⁻¹) := by positivity
      simp [realize, circularGamma, circularDecay] at hd
      exact hpos.ne' hd.symm)
    (by
      refine ⟨(), 0, 1, ?_⟩
      intro h
      have e := congrArg (fun f : ℕ → ℝ → ℝ → ℝ => f 1 (1 / 2) 1) h
      have he : Real.exp (-(1 / 2 : ℝ)) < Real.exp 0 := Real.exp_lt_exp.mpr (by norm_num)
      rw [Real.exp_zero] at he
      norm_num [actual, realize, circularG, circularDecay] at e
      exact he.ne e.symm)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@dirac_1s_solves_coupled_radial_ode) (Realization signature) Unit Unit :=
  diracBind% `D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.dirac_1s_solves_coupled_radial_ode.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.GroundRadial.family
    arena family (diracObserve% (circularG))
    #[]
    #[{ path := diracPath% dirac_1s_solves_coupled_radial_ode circularG 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end GroundRadial

namespace ExcitedRadial

abbrev signature : Signature := operandSignature (ℝ) (ℕ → ℝ → ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℝ) {ζ r : ℝ}
      (hζ : 0 < ζ) (hζk : ζ < 2) (hr : 0 < r),
    let G := R.readout () () m 2 ζ
    let F := circularF m 2 ζ
    let rate := Real.sqrt (4 - ζ ^ 2) / r - m * ζ / 2
    HasDerivAt G (rate * G r) r ∧ HasDerivAt F (rate * F r) r ∧
      radialDiracAt m (m * Real.sqrt (4 - ζ ^ 2) / 2) ζ (-2) G F r

def actual : Realization signature := diracObserve% (circularG)

def family : Registration arena (type_of% (@dirac_2p_solves_coupled_radial_ode)) :=
  diracFamily% arena (@dirac_2p_solves_coupled_radial_ode) actual
    (diracObserve% (fun _ _ _ _ => 1))
    (by
      intro h
      have hd := (h 0 (ζ := 1 / 2) (r := 1)
        (by norm_num) (by norm_num) (by norm_num)).1.deriv
      have hpos : 0 < Real.sqrt (4 - ((2 : ℝ) ^ 2)⁻¹) := by positivity
      simp [realize, circularGamma, circularDecay] at hd
      exact hpos.ne' hd.symm)
    (by
      refine ⟨(), 0, 1, ?_⟩
      intro h
      have e := congrArg (fun f : ℕ → ℝ → ℝ → ℝ => f 1 (1 / 2) 1) h
      have he : Real.exp (-(1 / 2 : ℝ)) < Real.exp 0 := Real.exp_lt_exp.mpr (by norm_num)
      rw [Real.exp_zero] at he
      norm_num [actual, realize, circularG, circularDecay] at e
      exact he.ne e.symm)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@dirac_2p_solves_coupled_radial_ode) (Realization signature) Unit Unit :=
  diracBind% `D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.dirac_2p_solves_coupled_radial_ode.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.ExcitedRadial.family
    arena family (diracObserve% (circularG))
    #[]
    #[{ path := diracPath% dirac_2p_solves_coupled_radial_ode circularG 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end ExcitedRadial

namespace GroundNorm

abbrev signature : Signature := operandSignature (ℝ) (ℕ → ℝ → ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m ζ : ℝ} (hm : 0 < m) (hζ : 0 < ζ) (hζ1 : ζ < 1),
    let γ := circularGamma 1 ζ
    let G := R.readout () () m 1 ζ
    let F := circularF m 1 ζ
    (∀ r > 0, |F r / G r| = (1 - γ) / ζ) ∧
      (1 - γ) / ζ = Real.sqrt ((1 - γ) / (1 + γ)) ∧ (1 - γ) / ζ < 1 ∧
      IntegrableOn (fun r => (G r) ^ 2 + (F r) ^ 2) (Ioi 0)

def actual : Realization signature := diracObserve% (circularG)

def family : Registration arena (type_of% (@dirac_1s_normalizable_and_small_component_ratio)) :=
  diracFamily% arena (@dirac_1s_normalizable_and_small_component_ratio) actual
    (diracObserve% (fun _ _ _ _ => 0))
    (by
      intro h
      have e := (h (m := 1) (ζ := 3 / 5) (by norm_num) (by norm_num) (by norm_num)).1 1
        (by norm_num)
      have hs : Real.sqrt (1 - (3 / 5 : ℝ) ^ 2) = 4 / 5 := by
        rw [show 1 - (3 / 5 : ℝ) ^ 2 = (4 / 5 : ℝ)^2 by norm_num,
          Real.sqrt_sq (by norm_num)]
      simp only [realize, div_zero, abs_zero, circularGamma, Nat.cast_one, one_pow, hs] at e
      norm_num at e)
    (by
      refine ⟨(), 0, 1, ?_⟩
      intro h
      have e := congrArg (fun f : ℕ → ℝ → ℝ → ℝ => f 1 (1 / 2) 1) h
      have he : Real.exp (-(1 / 2 : ℝ)) < Real.exp 0 := Real.exp_lt_exp.mpr (by norm_num)
      rw [Real.exp_zero] at he
      norm_num [actual, realize, circularG, circularDecay] at e
      exact he.ne e.symm)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@dirac_1s_normalizable_and_small_component_ratio) (Realization signature) Unit Unit :=
  diracBind% `D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.dirac_1s_normalizable_and_small_component_ratio.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.GroundNorm.family
    arena family (diracObserve% (circularG))
    #[]
    #[{ path := diracPath% dirac_1s_normalizable_and_small_component_ratio circularG 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end GroundNorm

namespace SmallCoupling

abbrev signature : Signature := operandSignature (ℝ) (ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := Tendsto (fun ζ : ℝ => ((1 - R.readout () () ζ) / ζ) / ζ) (𝓝[>] 0) (𝓝 (1 / 2))

def actual : Realization signature := diracObserve% (circularGamma 1)

def family : Registration arena (type_of% (@dirac_1s_ratio_asymptotic)) :=
  diracFamily% arena (@dirac_1s_ratio_asymptotic) actual
    (diracObserve% (fun _ => 1))
    (by
      intro h
      have he : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0) := tendsto_const_nhds
      have h' : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 (1 / 2)) := by
        simpa [realize] using h
      have e := tendsto_nhds_unique he h'
      norm_num at e)
    (by
      refine ⟨(), 0, 1, ?_⟩
      norm_num [actual, realize, circularGamma])

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@dirac_1s_ratio_asymptotic) (Realization signature) Unit Unit :=
  diracBind% `D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.dirac_1s_ratio_asymptotic.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.SmallCoupling.family
    arena family (diracObserve% (circularGamma 1))
    #[]
    #[{ path := diracPath% dirac_1s_ratio_asymptotic circularGamma 1 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end SmallCoupling


end

end Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D
