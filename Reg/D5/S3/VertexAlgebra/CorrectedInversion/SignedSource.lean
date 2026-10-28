import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.CorrectedInversion.SignedSource

/-!
Faithful source-law reconstruction for the signed coefficient and cutoff laws.
No Contract.Registration or declared_validated status is asserted. Whole-family
variation, sensitivity, observational dependence and selector binding remain
obligations under the delivery's linked audit issue.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.CorrectedInversion.SignedSource
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockFiniteCorrection
open _root_.D5.S3.VertexAlgebra.CorrectedInversion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MvPolynomial

abbrev Parameters := Σ D : LatticeData, Charge D
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Parameters
  (fun t => Oscillator t.1 × ℕ) (fun t => Oscillator t.1)
def actual : Realization signature := realize signature
  (fun _ t s => (affineP t.1 t.2 s.1).coeff s.2) (fun e => nomatch e)
def coefficientArena : Arena where
  signature := signature
  Law readout := ∀ t p R k, IsWeightedHomogeneous (sourceWeight t.1) p R →
    readout.readout () t (p, k) = (-1 : ℂ)^R •
      ((k.factorial : ℂ)⁻¹ • (((SourceMobius.sectorL1 t.1 t.2).toLinearMap^k) p))
theorem coefficient_source_bridge : (type_of% (@affineP_coeff)) ↔ coefficientArena.Law actual := by
  constructor
  · intro source t p R k hp
    exact source t.1 t.2 p R k hp
  · intro law D a p R k hp
    exact law ⟨D, a⟩ p R k hp
abbrev coefficientRealizationObligation := Registration coefficientArena (type_of% (@affineP_coeff))

def cutoffArena : Arena where
  signature := signature
  Law readout := ∀ t p R k, IsWeightedHomogeneous (sourceWeight t.1) p R → R < k →
    readout.readout () t (p, k) = 0
theorem cutoff_source_bridge : (type_of% (@affineP_above_weight)) ↔ cutoffArena.Law actual := by
  constructor
  · intro source t p R k hp hk
    exact source t.1 t.2 p R k hp hk
  · intro law D a p R k hp hk
    exact law ⟨D, a⟩ p R k hp hk
abbrev cutoffRealizationObligation := Registration cutoffArena (type_of% (@affineP_above_weight))

end Reg.D5.S3.VertexAlgebra.CorrectedInversion.SignedSource
