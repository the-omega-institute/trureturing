import D5.S3.VertexAlgebra.RationalCollision
import Reg.Support.DependentFamily

/-! Complete source telescope for weighted Laurent collision. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.RationalCollision
open _root_.D5.S3.VertexAlgebra
open SupportedFieldWords.OrderedWords
open CollisionRationalExpansions.OrderedRationalExpansion
open LabelledRationalClearing.GlobalRationalCurry
open LabelledRationalClearing.PairDifferenceLocalization
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility
open OrderedCollisionCoordinates.AdjacentFullOrders
open OrderedCollisionCoordinates.LocalResidueCurrying
open OrderedCollisionResidues.AdjacentLabelledCoordinates
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators
universe u

structure Parameters where
  scalar : Type u
  field : Field scalar
  pre : ℕ
  post : ℕ
  z : Fin ((pre + 2) + post)
  tau : Fin ((pre + 1) + post) ≃ Remaining z
  x : Remaining z
  adjacent : tau (boundarySlot pre post) = x

structure Input (p : Parameters.{u}) where
  P : letI := p.field; LabelledPolynomial p.scalar ((p.pre + 2) + p.post)
  orders : Fin ((p.pre + 2) + p.post) × Fin ((p.pre + 2) + p.post) → ℕ
  r : ℤ

def signature : Signature where
  Params := Parameters.{u}
  State := Input
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := letI := p.field; HahnSeries (Indices ((p.pre + 1) + p.post)) p.scalar
  Anchor := Empty
  finiteAnchor := inferInstance

def rational (p : Parameters.{u}) (v : Input p) :
    letI := p.field
    CommonRational p.scalar ((p.pre + 2) + p.post) :=
  letI := p.field
  LabelledRationalClearing.WeightedActualQ.globalDiagonal p.scalar p.z p.x ^ v.r *
    (algebraMap _ _ v.P /
      algebraMap _ _ (∏ q ∈ labelledPairs ((p.pre + 2) + p.post),
        pairPolynomial p.scalar q.1 q.2 ^ v.orders q))

def actual : Realization signature.{u} := realize signature.{u} (fun _ p v =>
  letI := p.field
  OrderedCollisionResidues.CollisionResidueMaps.jump p.scalar p.pre p.post p.z p.tau
    (rational p v)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ (p : Parameters.{u}) (v : Input p),
    letI := p.field
    (fusedLocalSeries p.scalar (p.pre + 1) p.post p.z p.x p.tau
      (rational p v)).coeff (-1) = R.readout () p v

theorem source_bridge :
    (type_of% (@_root_.D5.S3.VertexAlgebra.RationalCollision.LaurentNumerator.weighted_laurent_collision.{u})) ↔
      arena.{u}.Law actual.{u} := by
  constructor
  · intro h p v
    letI := p.field
    exact h p.scalar p.pre p.post p.z p.tau p.x p.adjacent v.P v.orders v.r
  · intro h K field pre post z tau x hx P orders r
    exact h ⟨K, field, pre, post, z, tau, x, hx⟩ ⟨P, orders, r⟩

theorem actual_law : arena.{u}.Law actual.{u} :=
  source_bridge.mp
    (@_root_.D5.S3.VertexAlgebra.RationalCollision.LaurentNumerator.weighted_laurent_collision.{u})

end Reg.D5.S3.VertexAlgebra.RationalCollision
