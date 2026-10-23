import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.Knot.WeightedPathReverseTemperleyLieb
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb
open _root_.D5.S3.Quantum.Algebra.Knot.WeightedPathReverseTemperleyLieb
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section
open scoped BigOperators
namespace Reg.D5.S3.Quantum.Algebra.Knot.WeightedPathReverseTemperleyLieb
universe u
attribute [local instance] Classical.propDecidable
local instance {L : Type u} (R : L → L → Prop) (n : ℕ) (s t : L) :
    DecidableEq (LegalPath R n s t) := Classical.decEq _

structure NativeData where
  L : Type u
  finite : Fintype L
  eq : DecidableEq L
  R : L → L → Prop
  d : L → ℝ
  delta : ℝ
  n : ℕ
  s : L
  t : L
  i : ℕ
  range : 0 < i ∧ i+1 < n

def data {L : Type u} [Fintype L] [DecidableEq L]
    (R : L → L → Prop) (d : L → ℝ) (delta : ℝ)
    (n : ℕ) (s t : L) (i : ℕ) (hi : 0 < i ∧ i+1 < n) : NativeData where
  L := L
  finite := inferInstance
  eq := inferInstance
  R := R
  d := d
  delta := delta
  n := n
  s := s
  t := t
  i := i
  range := hi

abbrev signature : Signature where
  Params := NativeData.{u}
  State p := Matrix (LegalPath p.R p.n p.s p.t) (LegalPath p.R p.n p.s p.t) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (LegalPath p.R p.n p.s p.t) (LegalPath p.R p.n p.s p.t) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p X => by
    letI := p.finite
    letI := p.eq
    exact X * pathProjection p.R p.d p.delta p.n p.s p.t (p.i+1)
      ⟨by have := p.range; omega, p.range.2⟩) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {L : Type u} [Fintype L] [DecidableEq L]
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a)
    (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (n : ℕ) (s t : L) (i : ℕ) (hi : 0 < i ∧ i+1 < n),
    r.readout () (data R d δ n s t i hi)
      (pathProjection R d δ n s t (i+1) ⟨by omega, hi.2⟩ *
        pathProjection R d δ n s t i ⟨hi.1, by omega⟩) =
      ((δ⁻¹ : ℂ)^2) • pathProjection R d δ n s t (i+1) ⟨by omega, hi.2⟩

def actual_law : arena.Law actual := by
  intro L _ _ R _ hR d hd δ hδ hPF n s t i hi
  exact weighted_path_reverse_temperley_lieb R hR d hd δ hδ hPF n s t i hi

private def testRelation : ULift.{u} Unit → ULift.{u} Unit → Prop := fun _ _ => True
private def testStart : ULift.{u} Unit := ⟨()⟩
private def testPath (n : ℕ) : LegalPath testRelation n testStart testStart :=
  ⟨fun _ => testStart, rfl, rfl, fun _ => trivial⟩

def rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hh := @h (ULift.{u} Unit) inferInstance inferInstance testRelation inferInstance
    ⟨fun _ _ _ => trivial⟩ (fun _ => 1) (by intro a; norm_num) 1 (by norm_num)
    (by intro a; simp [testRelation]) 3 testStart testStart 1 (by omega)
  have he := congrArg (fun X : Matrix (LegalPath testRelation 3 testStart testStart)
      (LegalPath testRelation 3 testStart testStart) ℂ => X (testPath 3) (testPath 3)) hh
  change (0 : ℂ) = ((1⁻¹ : ℂ)^2) * pathProjection testRelation (fun _ => 1) 1 3
    testStart testStart 2 (by omega) (testPath 3) (testPath 3) at he
  norm_num [pathProjection, testPath] at he

private theorem test_projection_nonzero :
    (0 : Matrix (LegalPath testRelation 3 testStart testStart)
      (LegalPath testRelation 3 testStart testStart) ℂ) ≠
      pathProjection testRelation (fun _ => 1) 1 3 testStart testStart 2 (by omega) := by
  intro h
  have hh := congrArg (fun X : Matrix (LegalPath testRelation 3 testStart testStart)
      (LegalPath testRelation 3 testStart testStart) ℂ => X (testPath 3) (testPath 3)) h
  norm_num [pathProjection, testPath] at hh

def family : Registration arena (type_of% (@weighted_path_reverse_temperley_lieb.{u})) where
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
    let p := data testRelation (fun _ => 1) 1 3 testStart testStart 1 (by omega)
    letI := p.finite
    letI := p.eq
    refine ⟨p, 0, 1, ?_⟩
    dsimp [actual, realize, p]
    intro h
    dsimp [data] at h
    exact test_projection_nonzero
      ((Matrix.zero_mul _).symm.trans (h.trans (Matrix.one_mul _)))

-- Typed Contract block is to be attempted after this native family compiles.
#print axioms family
end Reg.D5.S3.Quantum.Algebra.Knot.WeightedPathReverseTemperleyLieb
