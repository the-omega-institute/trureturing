import D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D
import Reg.Support.UnitSixO.Common

/-! Readouts for angular and axion potential families. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D
open _root_.Reg.Support.UnitSixO (operandSignature)
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.Axion

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

macro "bindAxion% " unit:term:max familyName:term:max arena:term:max family:term:max
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
        owner := `D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D
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

private theorem thetaEnergy_at_zero_ne : qcdThetaEnergy 1 1 1 1 0 ≠ 0 := by
  change -1 * 1 ^ 2 * Real.sqrt ((1 : ℝ) ^ 2 + 1 ^ 2 + 2 * 1 * 1 * Real.cos 0) ≠ 0
  rw [Real.cos_zero]
  positivity

private theorem thetaEnergy_dependence :
    qcdThetaEnergy 0 ≠ qcdThetaEnergy 1 := by
  intro h
  have hh := (congrFun (congrFun (congrFun (congrFun h 1) 1) 1) 0).symm
  rw [show qcdThetaEnergy 0 1 1 1 0 = 0 by simp [qcdThetaEnergy]] at hh
  exact thetaEnergy_at_zero_ne hh

private theorem axionPotential_dependence :
    axionPotential 0 ≠ axionPotential 1 := by
  intro h
  have hh := (congrFun (congrFun (congrFun (congrFun (congrFun (congrFun h 1) 1) 1) 0) 1) 0).symm
  apply thetaEnergy_at_zero_ne
  rw [show axionPotential 0 1 1 1 0 1 0 = 0 by simp [axionPotential, qcdThetaEnergy]] at hh
  simpa [axionPotential] using hh

namespace Susceptibility

abbrev signature : Signature := operandSignature ℝ (ℝ → ℝ → ℝ → ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {fπ mᵤ m_d : ℝ}, 0 < fπ → 0 < mᵤ + m_d → ∀ B₀ : ℝ,
    let V := R.readout () () B₀ fπ mᵤ m_d
    let mPiSq := B₀ * (mᵤ + m_d)
    HasDerivAt V 0 0 ∧
    HasDerivAt (deriv V) (B₀ * fπ ^ 2 * (mᵤ * m_d / (mᵤ + m_d))) 0 ∧
    deriv V 0 = 0 ∧
    deriv (deriv V) 0 = B₀ * fπ ^ 2 * (mᵤ * m_d / (mᵤ + m_d)) ∧
    deriv (deriv V) 0 = (mᵤ * m_d / (mᵤ + m_d) ^ 2) * (mPiSq * fπ ^ 2)

def family : Registration arena (type_of% (@qcd_topological_susceptibility_exact)) :=
  unitFamily% arena (@qcd_topological_susceptibility_exact) (unitObserve% qcdThetaEnergy)
    (unitObserve% (fun _ _ _ _ x => x))
    (by
      intro h
      have hd := (h (fπ := 1) (mᵤ := 1) (m_d := 1) (by norm_num) (by norm_num) 1).1
      have he := hd.unique (hasDerivAt_id' (0 : ℝ))
      norm_num at he)
    (by exact ⟨(), 0, 1, thetaEnergy_dependence⟩)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@qcd_topological_susceptibility_exact) (Realization signature) Unit Unit :=
  bindAxion%
    `D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.qcd_topological_susceptibility_exact.__information_unit
    `Reg.D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.Axion.Susceptibility.family
    arena family (unitObserve% qcdThetaEnergy) #[]
    (unitPath% qcd_topological_susceptibility_exact qcdThetaEnergy 0 0)

end Susceptibility

namespace Relaxation

abbrev signature : Signature := operandSignature ℝ (ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {B₀ fπ mᵤ m_d fₐ : ℝ},
    0 < B₀ → 0 < fπ → 0 < mᵤ → 0 < m_d → 0 < fₐ → ∀ θ₀ : ℝ,
    let V := R.readout () () B₀ fπ mᵤ m_d θ₀ fₐ
    let mₐSq := deriv (deriv V) (-fₐ * θ₀)
    let mPiSq := B₀ * (mᵤ + m_d)
    θ₀ + (-fₐ * θ₀) / fₐ = 0 ∧
    (∀ a, (∀ b, V a ≤ V b) ↔ ∃ k : ℤ, (k : ℝ) * (2 * Real.pi) = θ₀ + a / fₐ) ∧
    mₐSq * fₐ ^ 2 = (mᵤ * m_d / (mᵤ + m_d) ^ 2) * (mPiSq * fπ ^ 2) ∧
    Real.sqrt mₐSq * fₐ =
      (Real.sqrt (mᵤ * m_d) / (mᵤ + m_d)) * Real.sqrt mPiSq * fπ ∧
    mₐSq * fₐ ^ 2 ≤ (1 / 4) * mPiSq * fπ ^ 2 ∧
    (mₐSq * fₐ ^ 2 = (1 / 4) * mPiSq * fπ ^ 2 ↔ mᵤ = m_d)

def family : Registration arena (type_of% (@peccei_quinn_relaxation_and_axion_mass)) :=
  unitFamily% arena (@peccei_quinn_relaxation_and_axion_mass) (unitObserve% axionPotential)
    (unitObserve% (fun _ _ _ _ _ _ _ => 0))
    (by
      intro h
      have he := (h (B₀ := 1) (fπ := 1) (mᵤ := 1) (m_d := 1) (fₐ := 1)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0).2.2.1
      norm_num [realize, deriv_const] at he)
    (by exact ⟨(), 0, 1, axionPotential_dependence⟩)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@peccei_quinn_relaxation_and_axion_mass) (Realization signature) Unit Unit :=
  bindAxion%
    `D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.peccei_quinn_relaxation_and_axion_mass.__information_unit
    `Reg.D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.Axion.Relaxation.family
    arena family (unitObserve% axionPotential) #[]
    (unitPath% peccei_quinn_relaxation_and_axion_mass axionPotential 0 0)

end Relaxation

namespace Quartic

abbrev arena : Arena where
  signature := Relaxation.signature
  Law R := ∀ {B₀ fπ mᵤ m_d fₐ : ℝ},
    0 < B₀ → 0 < fπ → 0 < mᵤ → 0 < m_d → 0 < fₐ → ∀ θ₀ : ℝ,
    let V := R.readout () () B₀ fπ mᵤ m_d θ₀ fₐ
    let mₐSq := deriv (deriv V) (-fₐ * θ₀)
    let quartic := iteratedDeriv 4 V (-fₐ * θ₀)
    quartic = -(mₐSq / fₐ ^ 2) * ((mᵤ ^ 2 - mᵤ * m_d + m_d ^ 2) / (mᵤ + m_d) ^ 2) ∧
    quartic < 0 ∧ -(mₐSq / fₐ ^ 2) < quartic ∧ quartic ≤ -(1 / 4) * (mₐSq / fₐ ^ 2) ∧
    (quartic = -(1 / 4) * (mₐSq / fₐ ^ 2) ↔ mᵤ = m_d)

def family : Registration arena (type_of% (@axion_quartic_self_coupling_exact_and_attractive)) :=
  unitFamily% arena (@axion_quartic_self_coupling_exact_and_attractive) (unitObserve% axionPotential)
    (unitObserve% (fun _ _ _ _ _ _ _ => 0))
    (by
      intro h
      have he := (h (B₀ := 1) (fπ := 1) (mᵤ := 1) (m_d := 1) (fₐ := 1)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0).2.1
      norm_num [realize] at he)
    (by exact ⟨(), 0, 1, axionPotential_dependence⟩)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@axion_quartic_self_coupling_exact_and_attractive) (Realization Relaxation.signature) Unit Unit :=
  bindAxion%
    `D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.axion_quartic_self_coupling_exact_and_attractive.__information_unit
    `Reg.D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.Axion.Quartic.family
    arena family (unitObserve% axionPotential) #[]
    (unitPath% axion_quartic_self_coupling_exact_and_attractive axionPotential 0 0)

end Quartic

namespace Instanton

abbrev signature : Signature := operandSignature ℝ (ℝ → ℝ → ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {K g ρ : ℝ}, 0 < K → 0 < g → 0 < ρ →
    let V := R.readout () () K g ρ
    (∀ θ, V θ = -2 * K * Real.exp (-(8 * Real.pi ^ 2) / g ^ 2) * Real.cos θ) ∧
    Function.Periodic V (2 * Real.pi) ∧
    Real.exp (-(8 * Real.pi ^ 2) / g ^ 2) < 1 ∧
    ∀ θ, V 0 ≤ V θ ∧ (V 0 = V θ ↔ ∃ k : ℤ, (k : ℝ) * (2 * Real.pi) = θ)

def family : Registration arena (type_of% (@instanton_dilute_gas_bridge)) :=
  unitFamily% arena (@instanton_dilute_gas_bridge) (unitObserve% instantonPotential)
    (unitObserve% (fun _ _ _ _ => 0))
    (by
      intro h
      have he := (h (K := 1) (g := 1) (ρ := 1) (by norm_num) (by norm_num) (by norm_num)).1 0
      norm_num [realize, Real.exp_ne_zero] at he)
    (by
      refine ⟨(), 0, 1, fun h => ?_⟩
      have he := congrFun (congrFun (congrFun h 1) 1) 0
      change instantonPotential 0 1 1 0 = instantonPotential 1 1 1 0 at he
      norm_num [instantonPotential, Real.exp_ne_zero] at he)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@instanton_dilute_gas_bridge) (Realization signature) Unit Unit :=
  bindAxion%
    `D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.instanton_dilute_gas_bridge.__information_unit
    `Reg.D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.Axion.Instanton.family
    arena family (unitObserve% instantonPotential) #[]
    (unitPath% instanton_dilute_gas_bridge instantonPotential 0 0)

end Instanton

namespace DomainWall

abbrev signature : Signature := operandSignature ℝ (ℝ → ℝ → ℝ → ℝ → ℝ → ℕ → ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {B₀ fπ mᵤ m_d fPQ : ℝ} {d : ℕ},
    0 < B₀ → 0 < fπ → 0 < mᵤ → 0 < m_d → 0 < fPQ → 0 < d → ∀ θ₀ : ℝ,
    let V := R.readout () () B₀ fπ mᵤ m_d θ₀ fPQ d
    let fₐ := fPQ / (d : ℝ)
    let step := 2 * Real.pi * fₐ
    let offset := -θ₀ * fₐ
    V = axionPotential B₀ fπ mᵤ m_d θ₀ fₐ ∧
    (∀ t, Function.Periodic V t ↔ ∃ k : ℤ, t = step * k) ∧
    (∀ left,
      let reps := OmegaMath.AffineLattice.representative offset step left (n := d)
      Function.Injective reps ∧ Set.range reps =
        {a ∈ Set.Ico left (left + 2 * Real.pi * fPQ) | ∀ b, V a ≤ V b}) ∧
    (∀ k : Fin d, OmegaMath.AffineLattice.representative offset step offset k =
      (2 * k.val * Real.pi - θ₀) * fPQ / d) ∧
    Real.sqrt (deriv (deriv V) offset) * fₐ =
      (Real.sqrt (mᵤ * m_d) / (mᵤ + m_d)) * Real.sqrt (B₀ * (mᵤ + m_d)) * fπ

def family : Registration arena (type_of% (@domain_wall_vacuum_count_and_fa_invariance)) :=
  unitFamily% arena (@domain_wall_vacuum_count_and_fa_invariance) (unitObserve% pqPotential)
    (unitObserve% (fun _ _ _ _ _ _ _ _ => 0))
    (by
      intro h
      have he := (h (B₀ := 1) (fπ := 1) (mᵤ := 1) (m_d := 1) (fPQ := 1) (d := 1)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0).1
      have e0 := congrFun he 0
      change (0 : ℝ) = axionPotential 1 1 1 1 0 (1 / (1 : ℕ)) 0 at e0
      exact thetaEnergy_at_zero_ne (by simpa [axionPotential] using e0.symm))
    (by
      refine ⟨(), 0, 1, fun h => ?_⟩
      have he := congrFun (congrFun (congrFun (congrFun (congrFun (congrFun (congrFun h 1) 1) 1) 0) 1) 1) 0
      change pqPotential 0 1 1 1 0 1 1 0 = pqPotential 1 1 1 1 0 1 1 0 at he
      have hx : pqPotential 0 1 1 1 0 1 1 0 = 0 := by simp [pqPotential, qcdThetaEnergy]
      rw [hx] at he
      exact thetaEnergy_at_zero_ne (by simpa [pqPotential] using he.symm))

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@domain_wall_vacuum_count_and_fa_invariance) (Realization signature) Unit Unit :=
  bindAxion%
    `D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.domain_wall_vacuum_count_and_fa_invariance.__information_unit
    `Reg.D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.Axion.DomainWall.family
    arena family (unitObserve% pqPotential) #[]
    (unitPath% domain_wall_vacuum_count_and_fa_invariance pqPotential 0 0)

end DomainWall

end

end Reg.D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.Axion
