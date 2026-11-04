import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.HalfFock.ActualCorrCovariance

set_option autoImplicit false

/- Faithful source-reconstruction stage of the escape audit. No
Contract.Registration is asserted here: variation, sensitivity, actual
observational dependence and current selector binding remain unfinished.
Unfinished audit: https://github.com/the-omega-institute/trureturing/issues/21172.
The delivery uses this CLAUDE 3.9 issue rather than treating these
source bridges as declared_validated registrations. -/
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.HalfFock.ActualCorrCovariance
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.VertexAlgebra.HalfFock.ActualCorrCovariance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MvPolynomial
open scoped BigOperators

abbrev Parameters := Σ D : LatticeData, Charge D

namespace Covariance
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Parameters
  (fun parameter => Oscillator parameter.1) (fun parameter => CorrectionPolynomial parameter.1)

def actual : Realization signature := realize signature
  (fun _ parameter p => normalReflection parameter.1 (Cbar parameter.1 parameter.2 p))
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ parameter p,
    readout.readout () parameter p = corrLift parameter.1 parameter.2
      (affineSource parameter.1 parameter.2 p)

theorem source_bridge : (type_of% (@correctionPolynomial_reflection)) ↔ arena.Law actual := by
  constructor
  · intro source parameter p
    exact source parameter.1 parameter.2 p
  · intro law D q p
    exact law ⟨D, q⟩ p

abbrev realizationObligation := Registration arena (type_of% (@correctionPolynomial_reflection))
end Covariance

namespace Coefficients
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Parameters
  (fun parameter => Oscillator parameter.1 × ℕ) (fun parameter => Oscillator parameter.1)

def actual : Realization signature := realize signature
  (fun _ parameter state => Corr parameter.1 parameter.2 state.1 state.2)
  (fun empty => nomatch empty)

def degreeArena : Arena where
  signature := signature
  Law readout := ∀ parameter p R,
    IsWeightedHomogeneous (sourceWeight parameter.1) p R → ∀ s m,
      (readout.readout () parameter (p, s)).coeff m ≠ 0 →
        s + Finsupp.weight (sourceWeight parameter.1) m = R

theorem degree_source_bridge : (type_of% (@Corr_coefficient_bidegree)) ↔ degreeArena.Law actual := by
  constructor
  · intro source parameter p R hp s m hn
    exact source parameter.1 parameter.2 p R hp s m hn
  · intro law D q p R hp s m hn
    exact law ⟨D, q⟩ p R hp s m hn

abbrev degreeRealizationObligation := Registration degreeArena (type_of% (@Corr_coefficient_bidegree))
end Coefficients

namespace Scalar
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature LatticeData
  (fun D => Oscillator D) (fun D => Polynomial (Oscillator D))

def actual : Realization signature := realize signature
  (fun _ D p => optionEquivLeft ℂ (Index D) (normalReflection D (embed D p)))
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (q : Charge D) (p : Oscillator D)
      (ell : ℕ → Module.Dual ℂ (Oscillator D)),
    (∑ s ∈ (Corr D q p).support,
      ∑ t ∈ (readout.readout () D (Corr D q p s)).support,
        ell (s + t) ((readout.readout () D (Corr D q p s)).coeff t)) =
    ∑ t ∈ (optionEquivLeft ℂ (Index D) (affineSource D q p)).support,
      ∑ s ∈ (Corr D q ((optionEquivLeft ℂ (Index D) (affineSource D q p)).coeff t)).support,
        ell (t + s) (Corr D q ((optionEquivLeft ℂ (Index D) (affineSource D q p)).coeff t) s)

theorem source_bridge : (type_of% (@Corr_reflection_readout)) ↔ arena.Law actual := Iff.rfl

abbrev realizationObligation := Registration arena (type_of% (@Corr_reflection_readout))
end Scalar

end Reg.D5.S3.VertexAlgebra.HalfFock.ActualCorrCovariance
