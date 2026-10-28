import D5.S3.VertexAlgebra.CollisionAnalytic.AbsoluteEvaluation
import Reg.Support.DependentFamily

/- Faithful source-binding attempt. The complete source telescopes are retained
below, together with the actual dependent readouts. These are partial evidence,
not Contract.Registration values and not declared_validated registrations.
Whole-family variation/sensitivity, source-selection reconstruction and its
current inspector binding remain to be supplied. -/

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.CollisionAnalytic.AbsoluteEvaluation
universe u v
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open CollisionRationalExpansions.OrderedRationalExpansion
open SupportedFieldWords.OrderedWords
open SupportedFieldWords.FiniteConvolution
open UniformGradedLocalCorrelator
open CollisionAbsoluteEvaluation.Labelled

abbrev monomialSource := type_of%
  (@_root_.D5.S3.VertexAlgebra.CollisionAbsoluteEvaluation.monomial_family.{u,v})
abbrev collisionSource := type_of%
  (@_root_.D5.S3.VertexAlgebra.CollisionAbsoluteEvaluation.Labelled.collision_absolute_evaluation)

example : monomialSource.{u,v} :=
  @_root_.D5.S3.VertexAlgebra.CollisionAbsoluteEvaluation.monomial_family.{u,v}
example : collisionSource :=
  @_root_.D5.S3.VertexAlgebra.CollisionAbsoluteEvaluation.Labelled.collision_absolute_evaluation

-- Infinite state/output families are retained; neither is replaced by a finite sample.
def monomialSignature (Γ α : Type*) [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] : Signature where
  Params := Γ → ℂ
  State _ := HahnSeries.SummableFamily Γ ℂ α
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Γ → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def monomialActual (Γ α : Type*) [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] : Realization (monomialSignature Γ α) :=
  realize (monomialSignature Γ α)
    (fun _ w s g => s.hsum.coeff g * w g) (fun e => nomatch e)

structure CollisionParameters where
  n : ℕ
  sigma : Equiv.Perm (Fin n)
  orders : (Fin n × Fin n) → ℕ
  z : Fin n → ℂ

def collisionSignature : Signature where
  Params := CollisionParameters
  State p := LabelledPolynomial ℂ p.n
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (Fin p.n → ℤ) → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def collisionActual : Realization collisionSignature :=
  realize collisionSignature
    (fun _ p P e => (orderedRationalFor ℂ p.n p.sigma
      (algebraMap (LabelledPolynomial ℂ p.n) (CommonRational ℂ p.n) P /
       algebraMap (LabelledPolynomial ℂ p.n) (CommonRational ℂ p.n)
         (∏ q ∈ labelledPairs p.n, pairPolynomial q.1 q.2 ^ p.orders q))).coeff
          (orderExponents p.n p.sigma e) * monomial p.z e)
    (fun e => nomatch e)

#print axioms monomialActual
#print axioms collisionActual
end Reg.D5.S3.VertexAlgebra.CollisionAnalytic.AbsoluteEvaluation
