import Reg.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D.Petrov

/-! Dependent readouts for the causal cone and chiral rotations. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D
open _root_.Reg.Support.UnitSixO (operandSignature)
open Omega.BinaryQuarticSpinor

namespace Reg.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D.Causal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private abbrev t : V4 := coordinateVector 0

private theorem time_causal : futureCausal t := by
  norm_num [futureCausal, coordinateVector, Pi.single_apply]

private theorem energyN : belRobinson (psiN 1) t t t t = 1 := by
  change superenergy (psiN 1) = 1
  rw [(belRobinson_superenergy_positive_definite (psiN 1)).1]
  norm_num [psiN]

private theorem energyZero : belRobinson 0 t t t t = 0 :=
  (belRobinson_superenergy_positive_definite (0 : Coefficients)).2.2.mpr rfl

namespace Dominance

abbrev signature : Signature := operandSignature Coefficients ((Fin 4 → V4) → ℂ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (ψ : Coefficients) (u : Fin 4 → V4),
    (∀ i, futureCausal (u i)) → 0 ≤ (R.readout () () ψ u).re

def family : Registration arena (type_of% (@belRobinson_dominant_superenergy_condition)) :=
  unitFamily% arena (@belRobinson_dominant_superenergy_condition)
    (unitObserve% belRobinsonComplex)
    (unitObserve% (fun (_ : Coefficients) (_ : Fin 4 → V4) => (-1 : ℂ)))
    (by
      intro h
      have hh := h 0 (fun _ => t) (fun _ => time_causal)
      norm_num [realize] at hh)
    (by
      refine ⟨(), psiN 1, 0, fun h => ?_⟩
      have hh := congrArg Complex.re (congrFun h ![t, t, t, t])
      change belRobinson (psiN 1) t t t t = belRobinson 0 t t t t at hh
      rw [energyN, energyZero] at hh
      norm_num at hh)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@belRobinson_dominant_superenergy_condition) (Realization signature) Unit Unit :=
  bindPetrov% belRobinson_dominant_superenergy_condition
    `Reg.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D.Causal.Dominance.family arena family
    belRobinsonComplex
    #[petrovRead% belRobinson_dominant_superenergy_condition belRobinsonComplex 0]

end Dominance

namespace Duality

abbrev signature : Signature := operandSignature Coefficients (V4 → V4 → V4 → V4 → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (ψ : Coefficients) (θ : ℝ) (u₁ u₂ u₃ u₄ : V4),
    R.readout () () (Complex.exp ((θ : ℂ) * Complex.I) • ψ) u₁ u₂ u₃ u₄ =
      R.readout () () ψ u₁ u₂ u₃ u₄

def family : Registration arena (type_of% (@belRobinson_so2_duality_invariant)) :=
  unitFamily% arena (@belRobinson_so2_duality_invariant)
    (unitObserve% belRobinson)
    (unitObserve% (fun ψ (_ _ _ _ : V4) => (ψ 4).re))
    (by
      intro h
      have hh := h (psiN 1) Real.pi t t t t
      norm_num [realize, Complex.exp_pi_mul_I, Pi.smul_apply, psiN] at hh)
    (by
      refine ⟨(), psiN 1, 0, fun h => ?_⟩
      have hh := congrFun (congrFun (congrFun (congrFun h t) t) t) t
      change belRobinson (psiN 1) t t t t = belRobinson 0 t t t t at hh
      rw [energyN, energyZero] at hh
      norm_num at hh)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@belRobinson_so2_duality_invariant) (Realization signature) Unit Unit :=
  bindPetrov% belRobinson_so2_duality_invariant
    `Reg.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D.Causal.Duality.family arena family
    belRobinson #[petrovRead% belRobinson_so2_duality_invariant belRobinson 0]

end Duality

end
end Reg.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D.Causal
