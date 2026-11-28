import Reg.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D.Petrov

/-! Typed observations for the complex contraction and the causal Pauli realization. -/

open LeanInformationAudit Matrix Omega.BinaryQuarticSpinor Omega.HermitianSpinorContraction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Lorentz
open _root_.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D
open _root_.Reg.Support.UnitSixO (operandSignature)
open scoped ComplexOrder ComplexConjugate

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D.SpinorGeometry

private abbrev rest : Fin 4 → V4 :=
  ![coordinateVector 0, coordinateVector 0, coordinateVector 0, coordinateVector 0]

namespace Symmetry

abbrev signature : Signature := operandSignature Coefficients ((Fin 4 → V4) → ℂ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (ψ : Coefficients) (u : Fin 4 → V4),
    (R.readout () () ψ u).im = 0 ∧
    (∀ σ : Equiv.Perm (Fin 4), belRobinsonComplex ψ (u ∘ σ) = belRobinsonComplex ψ u) ∧
    belRobinsonMultilinear ψ u = (belRobinsonComplex ψ u).re

def family : Registration arena (type_of% (@belRobinson_totally_symmetric_and_real)) :=
  unitFamily% arena (@belRobinson_totally_symmetric_and_real) (unitObserve% belRobinsonComplex)
    (unitObserve% (fun _ _ => Complex.I))
    (by
      intro h
      have hh := (h (psiD 0) rest).1
      change (1 : ℝ) = 0 at hh
      norm_num at hh)
    (by
      refine ⟨(), psiD 0, psiD 1, fun h => ?_⟩
      have he := congrArg Complex.re (congrFun h rest)
      change superenergy (psiD 0) = superenergy (psiD 1) at he
      rw [(belRobinson_superenergy_positive_definite (psiD 0)).1,
        (belRobinson_superenergy_positive_definite (psiD 1)).1] at he
      norm_num [psiD] at he)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@belRobinson_totally_symmetric_and_real) (Realization signature) Unit Unit :=
  bindPetrov% belRobinson_totally_symmetric_and_real
    `Reg.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D.SpinorGeometry.Symmetry.family arena family
    belRobinsonComplex #[petrovRead% belRobinson_totally_symmetric_and_real belRobinsonComplex 0]

end Symmetry

abbrev PauliSignature : Signature := operandSignature V4 H2

private theorem pauli_dependence : ∃ p x y,
    (unitObserve% σMat : Realization PauliSignature).readout () p x ≠
      (unitObserve% σMat : Realization PauliSignature).readout () p y := by
  refine ⟨(), 0, coordinateVector 0, fun h => ?_⟩
  change σMat 0 = σMat (coordinateVector 0) at h
  have hh := congrArg (fun A : H2 => A 0 0) h
  norm_num [σMat, SL2CLorentzCover4D.pauliHerm, coordinateVector] at hh

namespace Decomposition

abbrev arena : Arena where
  signature := PauliSignature
  Law R := ∀ v : V4, futureCausal v →
    ∃ α β : Fin 2 → ℂ, R.readout () () v = rankOne α + rankOne β

def family : Registration arena (type_of% (@future_causal_spinor_decomposition)) :=
  unitFamily% arena (@future_causal_spinor_decomposition) (unitObserve% σMat)
    (unitObserve% (fun _ => -(1 : H2)))
    (by
      intro h
      obtain ⟨α, β, hab⟩ := h 0 (by simp [futureCausal])
      have he := congrArg (fun A : H2 => (A 0 0).re) hab
      change ((-(1 : H2)) 0 0).re = _ at he
      simp [Complex.mul_conj, Complex.add_re] at he
      linarith [Complex.normSq_nonneg (α 0), Complex.normSq_nonneg (β 0)])
    pauli_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@future_causal_spinor_decomposition) (Realization PauliSignature) Unit Unit :=
  bindPetrov% future_causal_spinor_decomposition
    `Reg.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D.SpinorGeometry.Decomposition.family arena family
    σMat #[petrovRead% future_causal_spinor_decomposition σMat 0]

end Decomposition

namespace Positivity

abbrev arena : Arena where
  signature := PauliSignature
  Law R := ∀ v : V4, (R.readout () () v).PosSemidef ↔ futureCausal v

def family : Registration arena (type_of% (@pauli_positive_semidefinite_iff)) :=
  unitFamily% arena (@pauli_positive_semidefinite_iff) (unitObserve% σMat)
    (unitObserve% (fun _ => 0))
    (by
      intro h
      have hn := (h ![-1, 0, 0, 0]).mp Matrix.PosSemidef.zero
      norm_num [futureCausal] at hn)
    pauli_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pauli_positive_semidefinite_iff) (Realization PauliSignature) Unit Unit :=
  bindPetrov% pauli_positive_semidefinite_iff
    `Reg.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D.SpinorGeometry.Positivity.family arena family
    σMat #[petrovRead% pauli_positive_semidefinite_iff σMat 0]

end Positivity

end Reg.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D.SpinorGeometry
