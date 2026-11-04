import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldInnerInverseCoefficients

/-! The dependent readout retains the full complex-algebra, numerator and signed
index telescope. The exact source bridge supplies no variation, intervention,
observational-dependence or enrolled-template evidence. -/
set_option autoImplicit false
namespace Reg.D5.S3.VertexAlgebra.FormalSeries.ThreeFieldInnerInverseCoefficients
open _root_.D5.S3.VertexAlgebra.UniformGradedLocalCorrelator
open _root_.D5.S3.VertexAlgebra.ThreeFieldInnerNativeInverse
open _root_.D5.S3.VertexAlgebra.ThreeFieldInnerLaurentFiber
open _root_.D5.S3.VertexAlgebra.ThreeFieldInnerInverseCoefficients
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
      (rawInnerCoefficient P p.k p.a p.e)
      (innerCoefficient P p.k p.a (p.e 0) (p.e 1) (p.e 2)) role)
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law r := ∀ {R : Type u} [instR : CommRing R] [instA : Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3),
    r.readout false ⟨R, instR, instA, k, a, e⟩ P =
      r.readout true ⟨R, instR, instA, k, a, e⟩ P

theorem source_bridge :
    (type_of% (@raw_inner_coefficients.{u})) ↔ arena.{u}.Law actual.{u} := Iff.rfl

abbrev RequiredEvidence := Registration arena.{u} (type_of% (@raw_inner_coefficients.{u}))

#print source_bridge
#print axioms source_bridge
end
end Reg.D5.S3.VertexAlgebra.FormalSeries.ThreeFieldInnerInverseCoefficients
