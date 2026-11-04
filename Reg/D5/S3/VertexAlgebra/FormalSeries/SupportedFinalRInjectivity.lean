import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.FormalSeries.SupportedFinalRInjectivity

/-! The dependent realization preserves the original algebra, exponents, two
distributions and support hypotheses. The bridge alone supplies no four-slot
registration: variation, sensitivity, observational dependence and the typed
source selection still require binding evidence. -/
set_option autoImplicit false
namespace Reg.D5.S3.VertexAlgebra.FormalSeries.SupportedFinalRInjectivity
open _root_.D5.S3.VertexAlgebra.SupportedFinalRInjectivity
open _root_.D5.S3.VertexAlgebra.UniformGradedLocalCorrelator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
universe u
noncomputable section

structure Parameter where
  R : Type u
  ringR : CommRing R
  algebraR : @Algebra ℂ R _ ringR.toSemiring
  k : ℕ
  A : ℕ
  C : ℕ
  D : ℕ

def signature : Signature where
  Params := Parameter.{u}
  State p := Distribution 3 p.R × Distribution 3 p.R
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Distribution 3 p.R
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun role p FG => Bool.rec (motive := fun _ => Distribution 3 p.R) FG.1 FG.2 role)
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law r := ∀ {R : Type u} [instR : CommRing R] [instA : Algebra ℂ R]
    (k A C D : ℕ) (F G : Distribution 3 R)
    (_hF : NestedSupport F) (_hG : NestedSupport G)
    (_same : polynomialAction
      (variablePolynomial 0 ^ k * variablePolynomial 1 ^ k *
        (variablePolynomial 0 + variablePolynomial 1) ^ k *
        (variablePolynomial 0 + variablePolynomial 1 + variablePolynomial 2) ^ A *
        (variablePolynomial 1 + variablePolynomial 2) ^ C * variablePolynomial 2 ^ D) F =
      polynomialAction
      (variablePolynomial 0 ^ k * variablePolynomial 1 ^ k *
        (variablePolynomial 0 + variablePolynomial 1) ^ k *
        (variablePolynomial 0 + variablePolynomial 1 + variablePolynomial 2) ^ A *
        (variablePolynomial 1 + variablePolynomial 2) ^ C * variablePolynomial 2 ^ D) G),
    r.readout false ⟨R, instR, instA, k, A, C, D⟩ (F, G) =
      r.readout true ⟨R, instR, instA, k, A, C, D⟩ (F, G)

theorem source_bridge :
    (type_of% (@finalR_injective.{u})) ↔ arena.{u}.Law actual.{u} := Iff.rfl

abbrev RequiredEvidence := Registration arena.{u} (type_of% (@finalR_injective.{u}))

end
end Reg.D5.S3.VertexAlgebra.FormalSeries.SupportedFinalRInjectivity
