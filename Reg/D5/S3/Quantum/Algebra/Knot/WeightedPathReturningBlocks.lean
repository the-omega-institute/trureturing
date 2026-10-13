import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.Knot.WeightedPathReturningBlocks
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb
open _root_.D5.S3.Quantum.Algebra.Knot.WeightedPathMarkovTrace
open _root_.D5.S3.Quantum.Algebra.Knot.WeightedPathReturningBlocks
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section
open scoped BigOperators Matrix
namespace Reg.D5.S3.Quantum.Algebra.Knot.WeightedPathReturningBlocks
universe u
attribute [local instance] Classical.propDecidable

structure FactorData where
  L : Type u
  finite : Fintype L
  eq : DecidableEq L
  R : L → L → Prop
  d : L → ℝ
  m : ℕ
  s : L
  v : L
  a : L
  c : L
  hva : R v a
  hvc : R v c
  hav : R a v
  hcv : R c v
  r : LegalPath R m s v
  x : LegalPath R (m + 1) s a
  y : LegalPath R (m + 1) s c

def data {L : Type u} [Fintype L] [DecidableEq L]
    (R : L → L → Prop) (d : L → ℝ) (m : ℕ) (s v a c : L)
    (hva : R v a) (hvc : R v c) (hav : R a v) (hcv : R c v)
    (r : LegalPath R m s v) (x : LegalPath R (m + 1) s a)
    (y : LegalPath R (m + 1) s c) : FactorData.{u} :=
  ⟨L, inferInstance, inferInstance, R, d, m, s, v, a, c, hva, hvc, hav, hcv, r, x, y⟩

abbrev signature : Signature where
  Params := FactorData.{u}
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := C p.R (p.m + 1 + 1) p.s
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p δ => by
    letI := p.finite
    letI := p.eq
    exact iota p.R (p.m + 1) p.s
        (blockUnit p.R (p.m + 1) p.s p.a p.x (append p.R p.m p.s p.v p.a p.hva p.r)) *
      lastProjection p.R p.d δ (p.m + 1) (by omega) p.s *
      iota p.R (p.m + 1) p.s
        (blockUnit p.R (p.m + 1) p.s p.c (append p.R p.m p.s p.v p.c p.hvc p.r) p.y))
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ p _ => by letI := p.finite; exact 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law z := ∀ {L : Type u} [Fintype L] [DecidableEq L]
    (R : L → L → Prop) (d : L → ℝ) (δ : ℝ) (m : ℕ) (s v a c : L)
    (hva : R v a) (hvc : R v c) (hav : R a v) (hcv : R c v)
    (r : LegalPath R m s v) (x : LegalPath R (m + 1) s a)
    (y : LegalPath R (m + 1) s c),
    z.readout () (data R d m s v a c hva hvc hav hcv r x y) δ =
      ((Real.sqrt (d a * d c) / (δ * d v) : ℝ) : ℂ) •
        blockUnit R (m + 1 + 1) s v
          (append R (m + 1) s a v hav x) (append R (m + 1) s c v hcv y)

theorem actual_law : arena.Law actual := by
  intro L _ _ R d δ m s v a c hva hvc hav hcv r x y
  exact returning_matrix_unit_factorization R d δ m s v a c hva hvc hav hcv r x y

private def testStart : ULift.{u} Unit := ⟨()⟩
private def testRelation : ULift.{u} Unit → ULift.{u} Unit → Prop := fun _ _ => True
private def testPath (n : ℕ) : LegalPath testRelation n testStart testStart :=
  ⟨fun _ => testStart, rfl, rfl, fun _ => trivial⟩
private def testData : FactorData.{u} := data testRelation (fun _ => 1) 0
  testStart testStart testStart testStart trivial trivial trivial trivial (testPath 0)
    (testPath 1) (testPath 1)
private def testFinal : LegalPath testRelation 2 testStart testStart :=
  append testRelation 1 testStart testStart testStart trivial (testPath 1)

private theorem actual_test_entry (δ : ℝ) :
    actual.{u}.readout () testData.{u} δ testStart testFinal testFinal =
      ((1 / δ : ℝ) : ℂ) := by
  have h := @actual_law (ULift.{u} Unit) inferInstance inferInstance
    testRelation (fun _ => 1) δ 0 testStart testStart testStart testStart
    trivial trivial trivial trivial (testPath 0) (testPath 1) (testPath 1)
  have he := congrArg (fun Z : C testRelation 2 testStart => Z testStart testFinal testFinal) h
  simpa [testData, testFinal, blockUnit] using he

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hh := @h (ULift.{u} Unit) inferInstance inferInstance
    testRelation (fun _ => 1) 1 0 testStart testStart testStart testStart
    trivial trivial trivial trivial (testPath 0) (testPath 1) (testPath 1)
  have he := congrArg (fun Z : C testRelation 2 testStart => Z testStart testFinal testFinal) hh
  norm_num [rejected, realize, testFinal, blockUnit] at he
  change (0 : ℂ) = 1 at he
  norm_num at he

def family : Registration arena (type_of% (@returning_matrix_unit_factorization.{u})) where
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
    refine ⟨testData, 1, 2, ?_⟩
    have hi : i = () := Subsingleton.elim _ _
    subst i
    intro heq
    have h := congrArg (fun Z : C testRelation 2 testStart => Z testStart testFinal testFinal) heq
    rw [actual_test_entry, actual_test_entry] at h
    norm_num at h

def registration_1.{u_1} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@returning_matrix_unit_factorization.{u_1}) (Realization signature.{u_1}) Unit Unit where
  unitName := `D5.S3.Quantum.Algebra.Knot.WeightedPathReturningBlocks.returning_matrix_unit_factorization.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.Knot.WeightedPathReturningBlocks.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_1}⟩
  objectArena := .source ⟨arena.{u_1}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_1} ⟨family.{u_1}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u_1}
    (fun _ p δ => by
      letI := p.finite
      letI := p.eq
      exact iota p.R (p.m + 1) p.s
          (blockUnit p.R (p.m + 1) p.s p.a p.x (append p.R p.m p.s p.v p.a p.hva p.r)) *
        lastProjection p.R p.d δ (p.m + 1) (by omega) p.s *
        iota p.R (p.m + 1) p.s
          (blockUnit p.R (p.m + 1) p.s p.c (append p.R p.m p.s p.v p.c p.hvc p.r) p.y))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.Knot.WeightedPathReturningBlocks
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration_1
end Reg.D5.S3.Quantum.Algebra.Knot.WeightedPathReturningBlocks
