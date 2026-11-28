import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Fourier.HexagonalThetaMinimum
import Reg.Support.ThetaVerticalPositive
import Reg.Support.PlanarThetaFoundation

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.Support.ThetaVerticalTail

namespace Reg.Support.ThetaVerticalTail
noncomputable section

def negativeRejected : Realization negativeSignature :=
  realize negativeSignature (fun _ t y => (91 / 15) * verticalScale t y)
    (fun e => nomatch e)

def negativeArena : Arena where
  signature := negativeSignature
  Law R := ∀ {t y : ℝ}, 1 ≤ t → Real.sqrt 3 / 2 ≤ y →
    R.readout () t y < (91 / 15) * verticalScale t y

private theorem negative_bridge : (type_of% (@vertical_negative_bound)) ↔
    negativeArena.Law negativeActual := Iff.rfl

private theorem height_one : Real.sqrt 3 / 2 ≤ (1 : ℝ) := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  nlinarith [Real.sqrt_nonneg (3 : ℝ)]

private theorem negative_rejected : ¬ negativeArena.Law negativeRejected := by
  intro h
  have h1 := h (t := 1) (y := 1) (by norm_num) height_one
  exact (lt_irrefl _) h1

def negativeRegistration : Registration negativeArena
    (type_of% (@vertical_negative_bound)) where
  actual := negativeActual
  bridge := negative_bridge
  variation := ⟨@vertical_negative_bound, negativeRejected, negative_rejected⟩
  sensitivity := ⟨fun i => ⟨negativeRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, negative_rejected⟩, fun e => nomatch e⟩
  dependence := negative_dependence

end
end Reg.Support.ThetaVerticalTail

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.Support.ThetaVerticalPositive
open Reg.Support.PlanarThetaFoundation
open scoped BigOperators

namespace Reg.Support.HexagonalThetaMinimum
noncomputable section

def zeroRejected : Realization heightSignature :=
  realize heightSignature (fun _ _ _ => 0) (fun e => nomatch e)

def marginArena : Arena where
  signature := heightSignature
  Law R := ∀ {t y : ℝ}, 1 ≤ t → Real.sqrt 3 / 2 ≤ y →
    verticalScale t y * (20 * Real.pi * t / 9 - 91 / 15) <
      deriv (fun b => deriv (fun z => R.readout () z t) b) y +
        (2 / y) * deriv (fun z => R.readout () z t) y

private theorem margin_bridge : (type_of% (@hexagonal_vertical_differential_bound)) ↔
    marginArena.Law heightActual := Iff.rfl

private theorem margin_rejected : ¬ marginArena.Law zeroRejected := by
  intro h
  have h0 := h (t := 1) (y := Real.sqrt 3 / 2) (by norm_num) le_rfl
  have hK : 0 < verticalScale 1 (Real.sqrt 3 / 2) := by
    dsimp [verticalScale]
    positivity
  have hz : deriv (fun b => deriv (fun z : ℝ => (0 : ℝ)) b)
      (Real.sqrt 3 / 2) + (2 / (Real.sqrt 3 / 2)) *
        deriv (fun z : ℝ => (0 : ℝ)) (Real.sqrt 3 / 2) = 0 := by simp
  change verticalScale 1 (Real.sqrt 3 / 2) *
    (20 * Real.pi * 1 / 9 - 91 / 15) < _ at h0
  simp only [zeroRejected, realize] at h0
  rw [hz] at h0
  have hp : 0 < 20 * Real.pi * 1 / 9 - 91 / 15 := by nlinarith [Real.pi_gt_three]
  have hh := mul_pos hK hp
  linarith

def derivativeArena : Arena where
  signature := heightSignature
  Law R := ∀ {t y : ℝ}, 0 < t → Real.sqrt 3 / 2 < y →
    0 < deriv (fun z => R.readout () z t) y

private theorem derivative_bridge : (type_of% (@height_derivative_pos)) ↔
    derivativeArena.Law heightActual := Iff.rfl

private theorem hex_lt_one : Real.sqrt 3 / 2 < (1 : ℝ) := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]

private theorem derivative_rejected : ¬ derivativeArena.Law zeroRejected := by
  intro h
  have h0 := h (t := 1) (y := 1) (by norm_num) hex_lt_one
  norm_num [zeroRejected, realize] at h0
  rw [(hasDerivAt_const (1 : ℝ) (0 : ℝ)).deriv] at h0
  exact (lt_irrefl (0 : ℝ)) h0

def negativeHeight : Realization heightSignature :=
  realize heightSignature (fun _ _ _ => -1) (fun e => nomatch e)

def heightArena : Arena where
  signature := heightSignature
  Law R := ∀ {t y : ℝ}, 0 < t → Real.sqrt 3 / 2 ≤ y →
    F t (1 / 2) (Real.sqrt 3 / 2) ≤ R.readout () y t ∧
      (R.readout () y t = F t (1 / 2) (Real.sqrt 3 / 2) ↔ y = Real.sqrt 3 / 2)

private theorem height_bridge : (type_of% (@hexagonal_height_minimum)) ↔
    heightArena.Law heightActual := Iff.rfl

private theorem hex_nonneg : 0 ≤ F 1 (1 / 2) (Real.sqrt 3 / 2) :=
  tsum_nonneg (fun _ => (Real.exp_pos _).le)

private theorem height_rejected : ¬ heightArena.Law negativeHeight := by
  intro h
  have h0 := (h (t := 1) (y := Real.sqrt 3 / 2) (by norm_num) le_rfl).1
  change F 1 (1 / 2) (Real.sqrt 3 / 2) ≤ -1 at h0
  linarith [hex_nonneg]

def negativeTheta : Realization thetaSignature :=
  realize thetaSignature (fun _ _ _ => -1) (fun e => nomatch e)

def reducedArena : Arena where
  signature := thetaSignature
  Law R := ∀ {t x y : ℝ}, 0 < t → 0 ≤ x → x ≤ 1 / 2 → Real.sqrt 3 / 2 ≤ y →
    F t (1 / 2) (Real.sqrt 3 / 2) ≤ R.readout () ⟨x, y⟩ t ∧
      (R.readout () ⟨x, y⟩ t = F t (1 / 2) (Real.sqrt 3 / 2) ↔
        x = 1 / 2 ∧ y = Real.sqrt 3 / 2)

private theorem reduced_bridge : (type_of% (@reduced_theta_minimum)) ↔
    reducedArena.Law thetaActual := Iff.rfl

private theorem reduced_rejected : ¬ reducedArena.Law negativeTheta := by
  intro h
  have h0 := (h (t := 1) (x := 1 / 2) (y := Real.sqrt 3 / 2)
    (by norm_num) (by norm_num) le_rfl le_rfl).1
  change F 1 (1 / 2) (Real.sqrt 3 / 2) ≤ -1 at h0
  linarith [hex_nonneg]

def marginRegistration : Registration marginArena
    (type_of% (@hexagonal_vertical_differential_bound)) where
  actual := heightActual
  bridge := margin_bridge
  variation := ⟨@hexagonal_vertical_differential_bound, zeroRejected, margin_rejected⟩
  sensitivity := ⟨fun i => ⟨zeroRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, margin_rejected⟩, fun e => nomatch e⟩
  dependence := height_dependence

def derivativeRegistration : Registration derivativeArena
    (type_of% (@height_derivative_pos)) where
  actual := heightActual
  bridge := derivative_bridge
  variation := ⟨@height_derivative_pos, zeroRejected, derivative_rejected⟩
  sensitivity := ⟨fun i => ⟨zeroRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, derivative_rejected⟩, fun e => nomatch e⟩
  dependence := height_dependence

def heightRegistration : Registration heightArena
    (type_of% (@hexagonal_height_minimum)) where
  actual := heightActual
  bridge := height_bridge
  variation := ⟨@hexagonal_height_minimum, negativeHeight, height_rejected⟩
  sensitivity := ⟨fun i => ⟨negativeHeight,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, height_rejected⟩, fun e => nomatch e⟩
  dependence := height_dependence

def reducedRegistration : Registration reducedArena (type_of% (@reduced_theta_minimum)) where
  actual := thetaActual
  bridge := reduced_bridge
  variation := ⟨@reduced_theta_minimum, negativeTheta, reduced_rejected⟩
  sensitivity := ⟨fun i => ⟨negativeTheta,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, reduced_rejected⟩, fun e => nomatch e⟩
  dependence := theta_dependence

end
end Reg.Support.HexagonalThetaMinimum
