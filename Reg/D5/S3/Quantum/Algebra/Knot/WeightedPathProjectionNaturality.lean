import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.Knot.WeightedPathProjectionNaturality
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb
open _root_.D5.S3.Quantum.Algebra.Knot.WeightedPathMarkovTrace
open _root_.D5.S3.Quantum.Algebra.Knot.WeightedPathProjectionNaturality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section
namespace Reg.D5.S3.Quantum.Algebra.Knot.WeightedPathProjectionNaturality
universe u
attribute [local instance] Classical.propDecidable
local instance {L : Type u} (R : L → L → Prop) (n : ℕ) (s t : L) :
    DecidableEq (LegalPath R n s t) := Classical.decEq _

structure NativeData where
  L : Type u
  finite : Fintype L
  eq : DecidableEq L
  R : L → L → Prop
  n : ℕ
  s : L

def data {L : Type u} [Fintype L] [DecidableEq L]
    (R : L → L → Prop) (n : ℕ) (s : L) : NativeData where
  L := L
  finite := inferInstance
  eq := inferInstance
  R := R
  n := n
  s := s

abbrev signature : Signature where
  Params := NativeData.{u}
  State p := C p.R p.n p.s
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := C p.R (p.n + 1) p.s
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p X => by
    letI := p.finite
    letI := p.eq
    exact iota p.R p.n p.s X) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {L : Type u} [Fintype L] [DecidableEq L]
    (R : L → L → Prop) (d : L → ℝ) (δ : ℝ),
    (∀ (n : ℕ) (s : L) (i : ℕ) (hi : 0 < i ∧ i < n),
      r.readout () (data R n s) (localProjection R d δ n s i hi) =
        localProjection R d δ (n + 1) s i ⟨hi.1, by omega⟩) ∧
    (∀ (n : ℕ) (s : L) (X Y : C R n s),
      tau R d δ n s (X * Y) = tau R d δ n s (Y * X))

def actual_law : arena.Law actual := by
  intro L _ _ R d δ
  exact weighted_path_projection_naturality R d δ

private def testRelation : ULift.{u} Unit → ULift.{u} Unit → Prop := fun _ _ => True
private def testStart : ULift.{u} Unit := ⟨()⟩
private def testPath (n : ℕ) : LegalPath testRelation n testStart testStart :=
  ⟨fun _ => testStart, rfl, rfl, fun _ => trivial⟩

def rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hh := (@h (ULift.{u} Unit) inferInstance inferInstance testRelation
    (fun _ => (1 : ℝ)) 1).1 2 testStart 1 (by omega)
  have he := congrArg (fun X : C testRelation 3 testStart =>
    X testStart (testPath 3) (testPath 3)) hh
  change (0 : ℂ) = pathProjection testRelation (fun _ => 1) 1 3
    testStart testStart 1 (by omega) (testPath 3) (testPath 3) at he
  norm_num [pathProjection, testPath] at he

private theorem unit_ne_zero (n : ℕ) : (0 : C testRelation n testStart) ≠ 1 := by
  intro h
  have hh := congrArg (fun X : C testRelation n testStart =>
    X testStart (testPath n) (testPath n)) h
  simpa using hh

def family : Registration arena (type_of% (@weighted_path_projection_naturality.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨data testRelation 0 testStart, 0, 1, ?_⟩
    change iota testRelation 0 testStart 0 ≠ iota testRelation 0 testStart 1
    rw [show iota testRelation 0 testStart 0 = 0 from (iotaHom _ _ _).map_zero,
      show iota testRelation 0 testStart 1 = 1 from (iotaHom _ _ _).map_one]
    exact unit_ne_zero 1

#print axioms family
end Reg.D5.S3.Quantum.Algebra.Knot.WeightedPathProjectionNaturality
