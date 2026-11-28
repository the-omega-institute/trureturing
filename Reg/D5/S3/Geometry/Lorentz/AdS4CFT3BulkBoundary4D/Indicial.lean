import D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D
import Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.Common

/-! Source laws and interventions for the AdS indicial equations. -/

open _root_.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Real Set Filter
open scoped Matrix Topology

namespace Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace RealRoot

abbrev signature : Signature := operandSignature (ℝ) (ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ μ : ℝ, (∃ Δ : ℝ, R.readout () () Δ = μ) ↔ -(9 / 4 : ℝ) ≤ μ

def family : Registration arena (type_of% (@bf_bound_real_dimension_iff)) :=
  adsFamily% arena (@bf_bound_real_dimension_iff) (adsObserve% (fun Δ : ℝ => Δ * (Δ - 3)))
    (adsObserve% (fun _ => 0))
    (by
      intro h
      obtain ⟨value, e⟩ := (h 1).2 (by norm_num)
      norm_num [realize] at e)
    (by
      refine ⟨(), 0, 1, ?_⟩
      norm_num [realize])

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bf_bound_real_dimension_iff) (Realization signature) Unit Unit :=
  adsBind% `D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.bf_bound_real_dimension_iff.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.RealRoot.family
    arena family (adsObserve% (fun Δ : ℝ => Δ * (Δ - 3))) #[]
    #[{ path := adsPath% bf_bound_real_dimension_iff HMul.hMul 6 0
        stateBinder := 1
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }]

end RealRoot

namespace ExplicitRoots

abbrev signature : Signature := operandSignature (ℝ) (ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {μ : ℝ} (hμ : -(9 / 4 : ℝ) ≤ μ),
    (∀ Δ : ℝ, Δ * (Δ - 3) = μ ↔ Δ = R.readout () () μ ∨ Δ = bfDeltaPlus μ) ∧
      bfDeltaPlus μ + bfDeltaMinus μ = 3 ∧ bfDeltaPlus μ * bfDeltaMinus μ = -μ

def family : Registration arena (type_of% (@bf_indicial_roots)) :=
  adsFamily% arena (@bf_indicial_roots) (adsObserve% (bfDeltaMinus))
    (adsObserve% (fun _ => 0))
    (by
      intro h
      have e := ((h (μ := -2) (by norm_num)).1 0).2 (Or.inl rfl)
      norm_num at e)
    (by
      refine ⟨(), -(9 / 4), -(5 / 4), ?_⟩
      norm_num [realize, bfDeltaMinus])

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bf_indicial_roots) (Realization signature) Unit Unit :=
  adsBind% `D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.bf_indicial_roots.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.ExplicitRoots.family
    arena family (adsObserve% (bfDeltaMinus)) #[]
    #[{ path := adsPath% bf_indicial_roots bfDeltaMinus 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end ExplicitRoots

namespace RootSeparation

abbrev signature : Signature := operandSignature (ℝ) (ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ μ : ℝ,
    (R.readout () () μ < bfDeltaPlus μ ↔ -(9 / 4 : ℝ) < μ) ∧
      bfDeltaMinus (-(9 / 4)) = 3 / 2 ∧ bfDeltaPlus (-(9 / 4)) = 3 / 2

def family : Registration arena (type_of% (@bf_root_separation)) :=
  adsFamily% arena (@bf_root_separation) (adsObserve% (bfDeltaMinus))
    (adsObserve% (fun _ => 0))
    (by
      intro h
      have e := (h (-(9 / 4))).1.mp (by norm_num [realize, bfDeltaPlus])
      exact lt_irrefl _ e)
    (by
      refine ⟨(), -(9 / 4), -(5 / 4), ?_⟩
      norm_num [realize, bfDeltaMinus])

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bf_root_separation) (Realization signature) Unit Unit :=
  adsBind% `D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.bf_root_separation.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.RootSeparation.family
    arena family (adsObserve% (bfDeltaMinus)) #[]
    #[{ path := adsPath% bf_root_separation bfDeltaMinus 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end RootSeparation

namespace UnitarityWindow

abbrev signature : Signature := operandSignature (ℝ) (ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ μ : ℝ,
    ((∃ Δ : ℝ, Δ * (Δ - 3) = μ) ∧
        1 / 2 ≤ R.readout () () μ ∧ 1 / 2 ≤ bfDeltaPlus μ) ↔
      -(9 / 4 : ℝ) ≤ μ ∧ μ ≤ -(5 / 4 : ℝ)

def family : Registration arena (type_of% (@bf_unitarity_dual_quantization_window)) :=
  adsFamily% arena (@bf_unitarity_dual_quantization_window) (adsObserve% (bfDeltaMinus))
    (adsObserve% (fun _ => 0))
    (by
      intro h
      have e := ((h (-2)).mpr (by constructor <;> norm_num)).2.1
      norm_num [realize] at e)
    (by
      refine ⟨(), -(9 / 4), -(5 / 4), ?_⟩
      norm_num [realize, bfDeltaMinus])

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bf_unitarity_dual_quantization_window) (Realization signature) Unit Unit :=
  adsBind% `D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.bf_unitarity_dual_quantization_window.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.UnitarityWindow.family
    arena family (adsObserve% (bfDeltaMinus)) #[]
    #[{ path := adsPath% bf_unitarity_dual_quantization_window bfDeltaMinus 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end UnitarityWindow

namespace StrictLowerDimension

abbrev signature : Signature := operandSignature (ℝ) (ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {μ : ℝ} (hμ : μ < -(5 / 4 : ℝ)),
    1 / 2 < R.readout () () μ

def family : Registration arena (type_of% (@bf_strict_lower_dimension)) :=
  adsFamily% arena (@bf_strict_lower_dimension) (adsObserve% (bfDeltaMinus))
    (adsObserve% (fun _ => 0))
    (by
      intro h
      have e := h (μ := -2) (by norm_num)
      norm_num [realize] at e)
    (by
      refine ⟨(), -(9 / 4), -(5 / 4), ?_⟩
      norm_num [realize, bfDeltaMinus])

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bf_strict_lower_dimension) (Realization signature) Unit Unit :=
  adsBind% `D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.bf_strict_lower_dimension.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.StrictLowerDimension.family
    arena family (adsObserve% (bfDeltaMinus)) #[]
    #[{ path := adsPath% bf_strict_lower_dimension bfDeltaMinus 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end StrictLowerDimension

namespace ConformalMass

abbrev signature : Signature := operandSignature (ℝ) (ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (-2) = 1 ∧ bfDeltaPlus (-2) = 2

def family : Registration arena (type_of% (@bf_conformal_mass)) :=
  adsFamily% arena (@bf_conformal_mass) (adsObserve% (bfDeltaMinus))
    (adsObserve% (fun _ => 0))
    (by
      intro h
      have e := h.1
      norm_num [realize] at e)
    (by
      refine ⟨(), -(9 / 4), -(5 / 4), ?_⟩
      norm_num [realize, bfDeltaMinus])

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bf_conformal_mass) (Realization signature) Unit Unit :=
  adsBind% `D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.bf_conformal_mass.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.ConformalMass.family
    arena family (adsObserve% (bfDeltaMinus)) #[]
    #[{ path := adsPath% bf_conformal_mass bfDeltaMinus 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end ConformalMass

end
end Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D
