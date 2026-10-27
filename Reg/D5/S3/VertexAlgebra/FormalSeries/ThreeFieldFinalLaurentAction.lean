import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldFinalLaurentAction

/-! The dependent realization retains the complete algebra and index telescope.
The exact source bridge supplies no variation, sensitivity, observational
 dependence or typed source-selection evidence. -/
set_option autoImplicit false
namespace Reg.D5.S3.VertexAlgebra.FormalSeries.ThreeFieldFinalLaurentAction
open _root_.D5.S3.VertexAlgebra.UniformGradedLocalCorrelator
open _root_.D5.S3.VertexAlgebra.UngradedLocalWordSeries
open _root_.D5.S3.VertexAlgebra.SupportedThreeFieldCollision
open _root_.D5.S3.VertexAlgebra.ThreeFieldFinalLaurentFiber
open _root_.D5.S3.VertexAlgebra.ThreeFieldFinalCone
open _root_.D5.S3.VertexAlgebra.ThreeFieldFinalLaurentAction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
universe u
noncomputable section

structure Parameter where
  R : Type u
  ringR : CommRing R
  algebraR : @Algebra ℂ R _ ringR.toSemiring
  k : ℕ
  a : Fin 3 → ℕ
  e : Exponent 3

def signature : Signature where
  Params := Parameter.{u}
  State p := MvPowerSeries (Fin 3) p.R
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.R
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun role p P => by
    letI := p.ringR
    letI := p.algebraR
    exact Bool.rec (motive := fun _ => p.R)
      (polynomialAction (variablePolynomial 0 ^ p.k * variablePolynomial 1 ^ p.k * (variablePolynomial 0 + variablePolynomial 1) ^ p.k * (variablePolynomial 0 + variablePolynomial 1 + variablePolynomial 2) ^ p.a 0 * (variablePolynomial 1 + variablePolynomial 2) ^ p.a 1 * variablePolynomial 2 ^ p.a 2) (laurentCoefficient P p.k p.a) p.e) (signedExtend P p.e) role)
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law r := ∀ {R : Type u} [instR : CommRing R] [instA : Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3),
    r.readout false ⟨R, instR, instA, k, a, e⟩ P =
      r.readout true ⟨R, instR, instA, k, a, e⟩ P

theorem source_bridge :
    (type_of% (@raw_R_action_transport.{u})) ↔ arena.{u}.Law actual.{u} := Iff.rfl

abbrev RequiredEvidence := Registration arena.{u} (type_of% (@raw_R_action_transport.{u}))

end
end Reg.D5.S3.VertexAlgebra.FormalSeries.ThreeFieldFinalLaurentAction
