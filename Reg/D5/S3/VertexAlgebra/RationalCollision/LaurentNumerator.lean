import D5.S3.VertexAlgebra.RationalCollision.LaurentNumerator
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Algebra.Field.ULift

/-! Complete source telescope for weighted Laurent collision.

Source: lexa-ms, Reg/D5/S3/VertexAlgebra/RationalCollision.lean at
6c8682a64921b8f8d2f059c80e395b2af30c9a13.
This source-bound audit attempt leaves sourceSelection unfinished under
https://github.com/the-omega-institute/trureturing/issues/20163.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.RationalCollision.LaurentNumerator
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

abbrev signature : Signature where
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


/-- A whole-family intervention; the original parameter and state fibers remain intact. -/
def rejected : Realization signature.{u} := realize signature.{u} (fun _ p v =>
  letI := p.field
  actual.readout () p v + 1) actual.anchor

private def witnessOrder : Fin 1 ≃ Remaining (0 : Fin 2) where
  toFun _ := ⟨1, by decide⟩
  invFun _ := 0
  left_inv i := Subsingleton.elim _ _
  right_inv s := by
    apply Subtype.ext
    apply Fin.ext
    have hs : s.val.val ≠ 0 := by
      intro h
      exact s.property (Fin.ext h)
    change 1 = s.val.val
    omega

private def witnessParameters : Parameters.{u} where
  scalar := ULift.{u} ℚ
  field := inferInstance
  pre := 0
  post := 0
  z := 0
  tau := witnessOrder
  x := witnessOrder (boundarySlot 0 0)
  adjacent := rfl

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  let p := witnessParameters.{u}
  let v : Input p := ⟨0, fun _ => 0, 0⟩
  letI := p.field
  have good := actual_law p v
  have bad := h p v
  change _ = actual.readout () p v + 1 at bad
  have eq := good.symm.trans bad
  have impossible : (0 : HahnSeries (Indices ((p.pre + 1) + p.post)) p.scalar) = 1 :=
    add_left_cancel (show actual.readout () p v + 0 = actual.readout () p v + 1 by
      simpa only [add_zero] using eq)
  exact zero_ne_one impossible

theorem variation : Variation arena.{u} actual.{u} :=
  ⟨actual_law, rejected, rejected_law⟩

theorem sensitivity : Sensitivity arena.{u} actual.{u} := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hj
    exact (hj (Subsingleton.elim (α := Unit) j i)).elim
  · intro e
    cases e


theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro role
  let p := witnessParameters.{u}
  letI := p.field
  let v0 : Input p := ⟨0, fun _ => 0, -1⟩
  let v1 : Input p := ⟨1, fun _ => 0, -1⟩
  have hz : rational p v0 = 0 := by simp [rational, v0]
  have ho : rational p v1 =
      LabelledRationalClearing.WeightedActualQ.globalDiagonal p.scalar p.z p.x ^ (-1 : ℤ) := by
    simp [rational, v1]
  have hj : OrderedCollisionResidues.CollisionResidueMaps.jump p.scalar p.pre p.post p.z p.tau
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal p.scalar p.z p.x ^ (-1 : ℤ)) = 1 := by
    dsimp only [LabelledRationalClearing.WeightedActualQ.globalDiagonal]
    rw [← OrderedCollisionResidues.ActualDiagonalLocalResidue.diagonal_collision
      p.scalar p.pre p.post p.z p.tau p.x p.adjacent (-1)]
    change coefficientHahn p.scalar (p.pre + 1) p.post p.z p.tau
      (localResidue p.scalar p.z p.x
        ((algebraMap _ (CommonRational p.scalar ((p.pre + 2) + p.post))
          (pairPolynomial p.scalar p.z p.x.val)) ^ (-1 : ℤ))) = 1
    rw [OrderedCollisionResidues.ActualDiagonalLocalResidue.local_diagonal_power]
    simp
  refine ⟨p, v0, v1, ?_⟩
  change OrderedCollisionResidues.CollisionResidueMaps.jump p.scalar p.pre p.post p.z p.tau
      (rational p v0) ≠
    OrderedCollisionResidues.CollisionResidueMaps.jump p.scalar p.pre p.post p.z p.tau
      (rational p v1)
  rw [hz, ho, map_zero, hj]
  exact zero_ne_one

def familyRegistration : Registration arena.{u}
    (type_of% (@_root_.D5.S3.VertexAlgebra.RationalCollision.LaurentNumerator.weighted_laurent_collision.{u})) where
  actual := actual
  bridge := source_bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence


/-- The compiled mathematical family is supplied to the source implementation.
Source-coordinate binding is explicitly unfinished; this is not declared_validated. -/
def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.VertexAlgebra.RationalCollision.LaurentNumerator.weighted_laurent_collision.{u})
    (type_of% (realize signature.{u} actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.VertexAlgebra.RationalCollision.LaurentNumerator.weighted_laurent_collision.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.RationalCollision.LaurentNumerator.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Reg.D5.S3.VertexAlgebra.RationalCollision.LaurentNumerator
