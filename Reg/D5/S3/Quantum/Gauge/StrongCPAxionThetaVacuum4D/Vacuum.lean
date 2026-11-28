import D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D
import Reg.Support.UnitSixO

/-! Typed observations of chiral potentials, determinant phases, and vacuum energy. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D (SU2 CMat2 chiralPotential)
open _root_.D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D
open _root_.Reg.Support.UnitSixO (operandSignature)
open LeanInformationAudit Filter Matrix Set
open scoped Matrix ComplexConjugate Topology

namespace Reg.D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.Vacuum

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

local macro "bindVacuum% " unit:term:max familyName:term:max arena:term:max family:term:max
    actual:term:max coordinates:term:max readouts:term:max : term =>
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
        readouts := $readouts }
      continuation := .unknown
      familyRecord := none
      options := #[] })

private def massPhase (φ : ℝ) : ℂ := Complex.exp ((φ : ℂ) * Complex.I)

abbrev PotentialSignature : Signature := operandSignature ℝ (ℝ → ℝ → ℝ → ℝ → CMat2 → ℝ)
abbrev EnergySignature : Signature := operandSignature ℝ (ℝ → ℝ → ℝ → ℝ → ℝ)
abbrev PhaseSignature : Signature := operandSignature ℝ (ℝ → ℝ)

private theorem phase_depends :
    (unitObserve% thetaBar : Realization PhaseSignature).readout () () 0 ≠
      (unitObserve% thetaBar : Realization PhaseSignature).readout () () 1 := by
  intro h
  have he := congrFun h 0
  norm_num [realize, thetaBar] at he

private theorem energy_one : qcdThetaEnergy 1 1 1 1 0 = -2 := by
  change -1 * 1 ^ 2 * Real.sqrt (1 ^ 2 + 1 ^ 2 + 2 * 1 * 1 * Real.cos 0) = -2
  norm_num [show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq]; norm_num]

private theorem potential_one : thetaChiralPotential 1 1 1 1 0 (1 : CMat2) = -2 := by
  rw [thetaChiralPotential_zero_eq_chiralPotential]
  norm_num [chiralPotential, Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.diagonal_apply]

private theorem energy_depends :
    (unitObserve% qcdThetaEnergy : Realization EnergySignature).readout () () 1 ≠
      (unitObserve% qcdThetaEnergy : Realization EnergySignature).readout () () 0 := by
  intro h
  have he := congrFun (congrFun (congrFun (congrFun h 1) 1) 1) 0
  change qcdThetaEnergy 1 1 1 1 0 = qcdThetaEnergy 0 1 1 1 0 at he
  have hz : qcdThetaEnergy 0 1 1 1 0 = 0 := by simp [qcdThetaEnergy]
  norm_num [energy_one, hz] at he

private theorem potential_depends :
    (unitObserve% thetaChiralPotential : Realization PotentialSignature).readout () () 1 ≠
      (unitObserve% thetaChiralPotential : Realization PotentialSignature).readout () () 0 := by
  intro h
  have he := congrFun (congrFun (congrFun (congrFun (congrFun h 1) 1) 1) 0) (1 : CMat2)
  change thetaChiralPotential 1 1 1 1 0 (1 : CMat2) = thetaChiralPotential 0 1 1 1 0 (1 : CMat2) at he
  norm_num [potential_one, thetaChiralPotential] at he

namespace Zero

abbrev arena : Arena where
  signature := PotentialSignature
  Law R := ∀ (B f u d : ℝ) (U : CMat2), R.readout () () B f u d 0 U = chiralPotential B f u d U

def family : Registration arena (type_of% (@thetaChiralPotential_zero_eq_chiralPotential)) :=
  unitFamily% arena (@thetaChiralPotential_zero_eq_chiralPotential) (unitObserve% thetaChiralPotential)
    (unitObserve% (fun _ _ _ _ _ _ => 0))
    (by
      intro h
      have he := h 1 1 1 1 (1 : CMat2)
      rw [← thetaChiralPotential_zero_eq_chiralPotential, potential_one] at he
      norm_num [realize] at he)
    (⟨(), 1, 0, potential_depends⟩)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@thetaChiralPotential_zero_eq_chiralPotential) (Realization PotentialSignature) Unit Unit :=
  bindVacuum%
    `D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.thetaChiralPotential_zero_eq_chiralPotential.__information_unit
    `Reg.D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.Vacuum.Zero.family
    arena family (unitObserve% thetaChiralPotential) #[]
    #[{ path := unitPath% thetaChiralPotential_zero_eq_chiralPotential thetaChiralPotential 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end Zero

namespace Phase

abbrev arena : Arena where
  signature := PhaseSignature
  Law R := ∀ (θ arg αᵤ α_d φ α : ℝ) (M U : CMat2),
    R.readout () () (θ - (αᵤ + α_d)) (arg + (αᵤ + α_d)) = thetaBar θ arg ∧
      (Matrix.diagonal ![massPhase αᵤ, massPhase α_d] * M).det =
        massPhase (αᵤ + α_d) * M.det ∧
      (Matrix.diagonal ![massPhase φ, massPhase (-φ)] * U).det = U.det ∧
      ((massPhase α • (1 : CMat2)) * U).det = massPhase (2 * α) * U.det ∧
      thetaBar (θ - 2 * α) (arg + 2 * α) = thetaBar θ arg

def family : Registration arena (type_of% (@thetaBar_chiral_rotation_invariant)) :=
  unitFamily% arena (@thetaBar_chiral_rotation_invariant) (unitObserve% thetaBar)
    (unitObserve% (fun _ _ => 0))
    (by
      intro h
      have he := (h 1 0 0 0 0 0 1 1).1
      norm_num [realize, thetaBar] at he)
    (⟨(), 0, 1, phase_depends⟩)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@thetaBar_chiral_rotation_invariant) (Realization PhaseSignature) Unit Unit :=
  bindVacuum%
    `D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.thetaBar_chiral_rotation_invariant.__information_unit
    `Reg.D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.Vacuum.Phase.family
    arena family (unitObserve% thetaBar) #[]
    #[{ path := unitPath% thetaBar_chiral_rotation_invariant thetaBar 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end Phase

namespace Massless

abbrev arena : Arena where
  signature := EnergySignature
  Law R := ∀ {B f d : ℝ}, 0 < B → 0 < f → 0 < d → ∀ θ : ℝ,
    R.readout () () B f 0 d θ = -B * f ^ 2 * d ∧
      ∃ U₀ : SU2, (U₀ : CMat2) = Matrix.diagonal ![massPhase (θ / 2), massPhase (-(θ / 2))] ∧
        thetaChiralPotential B f 0 d θ U₀ = -B * f ^ 2 * d

def family : Registration arena (type_of% (@massless_quark_theta_unobservable)) :=
  unitFamily% arena (@massless_quark_theta_unobservable) (unitObserve% qcdThetaEnergy)
    (unitObserve% (fun _ _ _ _ _ => 0))
    (by
      intro h
      have he := (h (B := 1) (f := 1) (d := 1) (by norm_num) (by norm_num) (by norm_num) 0).1
      norm_num [realize] at he)
    (⟨(), 1, 0, energy_depends⟩)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@massless_quark_theta_unobservable) (Realization EnergySignature) Unit Unit :=
  bindVacuum%
    `D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.massless_quark_theta_unobservable.__information_unit
    `Reg.D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.Vacuum.Massless.family
    arena family (unitObserve% qcdThetaEnergy) #[]
    #[{ path := unitPath% massless_quark_theta_unobservable qcdThetaEnergy 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end Massless

namespace LowerBound

abbrev arena : Arena where
  signature := EnergySignature
  Law R := ∀ {B f u d θ : ℝ}, 0 < B → 0 < f → ∀ U : SU2,
    R.readout () () B f u d θ ≤ thetaChiralPotential B f u d θ U

def family : Registration arena (type_of% (@thetaChiralPotential_ge_qcdThetaEnergy)) :=
  unitFamily% arena (@thetaChiralPotential_ge_qcdThetaEnergy) (unitObserve% qcdThetaEnergy)
    (unitObserve% (fun _ _ _ _ _ => 1))
    (by
      intro h
      have he := h (B := 1) (f := 1) (u := 1) (d := 1) (θ := 0) (by norm_num) (by norm_num) 1
      change 1 ≤ thetaChiralPotential 1 1 1 1 0 (1 : CMat2) at he
      norm_num [potential_one] at he)
    (⟨(), 1, 0, energy_depends⟩)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@thetaChiralPotential_ge_qcdThetaEnergy) (Realization EnergySignature) Unit Unit :=
  bindVacuum%
    `D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.thetaChiralPotential_ge_qcdThetaEnergy.__information_unit
    `Reg.D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.Vacuum.LowerBound.family
    arena family (unitObserve% qcdThetaEnergy) #[]
    #[{ path := unitPath% thetaChiralPotential_ge_qcdThetaEnergy qcdThetaEnergy 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end LowerBound

namespace Attainment

abbrev arena : Arena where
  signature := EnergySignature
  Law S := ∀ {B f u d θ : ℝ}, 0 < B → 0 < f →
    0 < u ^ 2 + d ^ 2 + 2 * u * d * Real.cos θ →
    let R := Real.sqrt (u ^ 2 + d ^ 2 + 2 * u * d * Real.cos θ)
    let a := (u + d) * Real.cos (θ / 2) / R
    let z := (d - u) * Real.sin (θ / 2) / R
    ∃ U₀ : SU2, (U₀ : CMat2) = Matrix.diagonal ![(⟨a, z⟩ : ℂ), ⟨a, -z⟩] ∧
      ∀ U : SU2, thetaChiralPotential B f u d θ U = S.readout () () B f u d θ ↔ U = U₀

def family : Registration arena (type_of% (@qcdThetaEnergy_attained_on_diagonal_su2)) :=
  unitFamily% arena (@qcdThetaEnergy_attained_on_diagonal_su2) (unitObserve% qcdThetaEnergy)
    (unitObserve% (fun _ _ _ _ _ => 0))
    (by
      intro h
      have hpos : 0 < (1 : ℝ) ^ 2 + 1 ^ 2 + 2 * 1 * 1 * Real.cos 0 := by norm_num
      obtain ⟨U₀, hmat, heq⟩ := h (B := 1) (f := 1) (u := 1) (d := 1) (θ := 0)
        (by norm_num) (by norm_num) hpos
      obtain ⟨V₀, hv, hmin⟩ := qcdThetaEnergy_attained_on_diagonal_su2
        (B₀ := 1) (fπ := 1) (by norm_num) (by norm_num) hpos
      have he : U₀ = V₀ := Subtype.ext (hmat.trans hv.symm)
      have hzero := (heq U₀).2 rfl
      change thetaChiralPotential 1 1 1 1 0 U₀ = 0 at hzero
      rw [he, (hmin V₀).2 rfl, energy_one] at hzero
      norm_num at hzero)
    (⟨(), 1, 0, energy_depends⟩)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@qcdThetaEnergy_attained_on_diagonal_su2) (Realization EnergySignature) Unit Unit :=
  bindVacuum%
    `D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.qcdThetaEnergy_attained_on_diagonal_su2.__information_unit
    `Reg.D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.Vacuum.Attainment.family
    arena family (unitObserve% qcdThetaEnergy) #[]
    #[{ path := unitPath% qcdThetaEnergy_attained_on_diagonal_su2 qcdThetaEnergy 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end Attainment

namespace CPMinimum

abbrev arena : Arena where
  signature := EnergySignature
  Law R := ∀ {B f u d : ℝ}, 0 < B → 0 < f → 0 < u → 0 < d → ∀ θ : ℝ,
    R.readout () () B f u d 0 ≤ qcdThetaEnergy B f u d θ ∧
      (qcdThetaEnergy B f u d 0 = qcdThetaEnergy B f u d θ ↔ Real.cos θ = 1)

def family : Registration arena (type_of% (@vafa_witten_cp_conserving_minimum)) :=
  unitFamily% arena (@vafa_witten_cp_conserving_minimum) (unitObserve% qcdThetaEnergy)
    (unitObserve% (fun _ _ _ _ _ => 0))
    (by
      intro h
      have he := (h (B := 1) (f := 1) (u := 1) (d := 1)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0).1
      norm_num [realize, energy_one] at he)
    (⟨(), 1, 0, energy_depends⟩)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@vafa_witten_cp_conserving_minimum) (Realization EnergySignature) Unit Unit :=
  bindVacuum%
    `D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.vafa_witten_cp_conserving_minimum.__information_unit
    `Reg.D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.Vacuum.CPMinimum.family
    arena family (unitObserve% qcdThetaEnergy) #[]
    #[{ path := unitPath% vafa_witten_cp_conserving_minimum qcdThetaEnergy 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end CPMinimum

namespace Periodic

abbrev arena : Arena where
  signature := EnergySignature
  Law R := ∀ {B f u d : ℝ}, 0 < B → 0 < f → 0 < u → 0 < d →
    Function.Periodic (qcdThetaEnergy B f u d) (2 * Real.pi) ∧
      (∀ θ, qcdThetaEnergy B f u d (-θ) = qcdThetaEnergy B f u d θ) ∧
      (∀ θ, qcdThetaEnergy B f u d θ ≤ qcdThetaEnergy B f u d Real.pi) ∧
      R.readout () () B f u d Real.pi = -B * f ^ 2 * |u - d|

def family : Registration arena (type_of% (@qcdThetaEnergy_periodic_and_even)) :=
  unitFamily% arena (@qcdThetaEnergy_periodic_and_even) (unitObserve% qcdThetaEnergy)
    (unitObserve% (fun _ _ _ _ _ => 1))
    (by
      intro h
      have he := (h (B := 1) (f := 1) (u := 1) (d := 1)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2.2.2
      norm_num [realize] at he)
    (⟨(), 1, 0, energy_depends⟩)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@qcdThetaEnergy_periodic_and_even) (Realization EnergySignature) Unit Unit :=
  bindVacuum%
    `D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.qcdThetaEnergy_periodic_and_even.__information_unit
    `Reg.D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.Vacuum.Periodic.family
    arena family (unitObserve% qcdThetaEnergy) #[]
    #[{ path := unitPath% qcdThetaEnergy_periodic_and_even qcdThetaEnergy 0 5
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end Periodic

namespace Dashen

abbrev arena : Arena where
  signature := EnergySignature
  Law R := ∀ {B f m : ℝ}, 0 < B → 0 < f → 0 < m →
    (∀ θ, R.readout () () B f m m θ = -2 * B * f ^ 2 * m * |Real.cos (θ / 2)|) ∧
      (∀ U : SU2, thetaChiralPotential B f m m Real.pi U = 0) ∧
      HasDerivWithinAt (qcdThetaEnergy B f m m) (-B * f ^ 2 * m) (Ici Real.pi) Real.pi ∧
      HasDerivWithinAt (qcdThetaEnergy B f m m) (B * f ^ 2 * m) (Iic Real.pi) Real.pi ∧
      (¬ DifferentiableAt ℝ (qcdThetaEnergy B f m m) Real.pi) ∧
      ∃ U₁ U₂ : SU2, (U₁ : CMat2) = Matrix.diagonal ![Complex.I, -Complex.I] ∧
        (U₂ : CMat2) = Matrix.diagonal ![-Complex.I, Complex.I] ∧ (U₁ : CMat2)ᴴ = U₂

def family : Registration arena (type_of% (@dashen_degenerate_cusp_and_spontaneous_cp_breaking)) :=
  unitFamily% arena (@dashen_degenerate_cusp_and_spontaneous_cp_breaking) (unitObserve% qcdThetaEnergy)
    (unitObserve% (fun _ _ _ _ _ => 0))
    (by
      intro h
      have he := (h (B := 1) (f := 1) (m := 1) (by norm_num) (by norm_num) (by norm_num)).1 0
      norm_num [realize] at he)
    (⟨(), 1, 0, energy_depends⟩)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@dashen_degenerate_cusp_and_spontaneous_cp_breaking) (Realization EnergySignature) Unit Unit :=
  bindVacuum%
    `D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.dashen_degenerate_cusp_and_spontaneous_cp_breaking.__information_unit
    `Reg.D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.Vacuum.Dashen.family
    arena family (unitObserve% qcdThetaEnergy) #[]
    #[{ path := unitPath% dashen_degenerate_cusp_and_spontaneous_cp_breaking qcdThetaEnergy 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end Dashen

namespace Smooth

abbrev arena : Arena where
  signature := EnergySignature
  Law R := ∀ {B f u d : ℝ}, 0 < u → 0 < d → u ≠ d →
    Differentiable ℝ (qcdThetaEnergy B f u d) ∧ deriv (R.readout () () B f u d) Real.pi = 0

def family : Registration arena (type_of% (@nondegenerate_smooth_at_pi)) :=
  unitFamily% arena (@nondegenerate_smooth_at_pi) (unitObserve% qcdThetaEnergy)
    (unitObserve% (fun _ _ _ _ θ => θ))
    (by
      intro h
      have he := (h (B := 1) (f := 1) (u := 1) (d := 2) (by norm_num) (by norm_num) (by norm_num)).2
      change deriv (fun θ : ℝ => θ) Real.pi = 0 at he
      simp at he)
    (⟨(), 1, 0, energy_depends⟩)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@nondegenerate_smooth_at_pi) (Realization EnergySignature) Unit Unit :=
  bindVacuum%
    `D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.nondegenerate_smooth_at_pi.__information_unit
    `Reg.D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.Vacuum.Smooth.family
    arena family (unitObserve% qcdThetaEnergy) #[]
    #[{ path := unitPath% nondegenerate_smooth_at_pi qcdThetaEnergy 0 1
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end Smooth

end

end Reg.D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D.Vacuum
