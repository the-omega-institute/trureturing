import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.CorrectedInversion.NormalReadout

/-!
Faithful source reconstruction for all three public readout theorems.
This attempts the source-law part of the four-slot audit. It asserts no
Contract.Registration or declared_validated status: whole-family variation,
sensitivity, observational dependence and current source-selector binding
remain obligations. The linked audit issue is recorded in the delivery.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.CorrectedInversion.NormalReadout
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFiniteCorrection
open HalfFock.NormalScalarTranspose TwistedGround.ActualChargedAdjoint
open _root_.D5.S3.VertexAlgebra.CorrectedInversion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MvPolynomial
open scoped BigOperators

namespace PolynomialReadout
abbrev Parameters := Σ D : LatticeData, ℕ → Module.Dual ℂ (Oscillator D)
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Parameters
  (fun t => Polynomial (Oscillator t.1)) (fun _ => ℂ)
def actual : Realization signature := realize signature
  (fun _ t p => readPolynomial t.1 t.2 p) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law readout := ∀ t p, readout.readout () t p =
    ∑ j ∈ p.support, t.2 j (p.coeff j)
theorem source_bridge : (type_of% (@readPolynomial_support)) ↔ arena.Law actual := by
  constructor
  · intro source t p
    exact source t.1 t.2 p
  · intro law D ell p
    exact law ⟨D, ell⟩ p
abbrev realizationObligation := Registration arena (type_of% (@readPolynomial_support))
end PolynomialReadout

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature LatticeData
  (fun D => Oscillator D) (fun D => Polynomial (Oscillator D))
def actual : Realization signature := realize signature
  (fun _ D p => normalP D p) (fun e => nomatch e)

def generatorArena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (i : Index D),
    readout.readout () D (X i) = ∑ s : Fin (i.2 + 1),
      Polynomial.monomial (i.2 - s.val)
        (((-1 : ℂ)^(i.2 + 1) * ((i.2 + 1).choose (s.val + 1) : ℂ)) • X (i.1, s.val))
theorem generator_source_bridge : (type_of% (@normalP_X)) ↔ generatorArena.Law actual := Iff.rfl
abbrev generatorRealizationObligation := Registration generatorArena (type_of% (@normalP_X))

def scalarArena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (p : Oscillator D) (R : ℕ),
    IsWeightedHomogeneous (sourceWeight D) p R →
    ∀ (e : ℤ) (x y : ActualTensor D hu),
      normalLeft D hu a e x y p = paritySign (chargeNorm D a / 2) *
        readPolynomial D (fun j => normalRight D hu a (shiftIndex D a R j - e) x y)
          (readout.readout () D p)
theorem scalar_source_bridge : (type_of% (@normal_homogeneous_readout)) ↔ scalarArena.Law actual :=
  Iff.rfl
abbrev scalarRealizationObligation := Registration scalarArena (type_of% (@normal_homogeneous_readout))

end Reg.D5.S3.VertexAlgebra.CorrectedInversion.NormalReadout
