import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.Knot.WeightedPathArtinRepresentation
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb
open _root_.D5.S3.Quantum.Algebra.Knot.WeightedPathMarkovTrace
open _root_.D5.S3.Quantum.Algebra.Knot.WeightedPathArtinRepresentation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section
open scoped BigOperators
namespace Reg.D5.S3.Quantum.Algebra.Knot.WeightedPathArtinRepresentation
universe u
attribute [local instance] Classical.propDecidable
local instance {L : Type u} (R : L → L → Prop) (n : ℕ) (s t : L) :
    DecidableEq (LegalPath R n s t) := Classical.decEq _

structure NativeData where
  L : Type u
  finite : Fintype L
  eq : DecidableEq L
  R : L → L → Prop
  dec : DecidableRel R
  symmetry : Std.Symm R
  d : L → ℝ
  positive : ∀ a, 0 < d a
  delta : ℝ
  deltaPositive : 0 < delta
  perron : ∀ a, (letI := finite; letI := dec; ∑ b : L with R a b, d b) = delta * d a
  A : ℂ
  nonzero : A ≠ 0
  parameter : (delta : ℂ) = -A ^ 2 - A⁻¹ ^ 2
  s : L

def data {L : Type u} [Fintype L] [DecidableEq L]
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (A : ℂ) (hA : A ≠ 0) (hparameter : (δ : ℂ) = -A ^ 2 - A⁻¹ ^ 2)
    (s : L) : NativeData where
  L := L
  finite := inferInstance
  eq := inferInstance
  R := R
  dec := inferInstance
  symmetry := hR
  d := d
  positive := hd
  delta := δ
  deltaPositive := hδ
  perron := hPF
  A := A
  nonzero := hA
  parameter := hparameter
  s := s

abbrev signature : Signature where
  Params := NativeData.{u}
  State _ := PositiveBraid
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p b => by
    letI := p.finite
    letI := p.eq
    letI := p.dec
    exact normalizedTrace p.R p.symmetry p.d p.positive p.delta p.deltaPositive
      p.perron p.A p.nonzero p.parameter p.s b) (fun e => nomatch e)

-- Strand count is deliberately incompatible with either stabilization move.
def rejected : Realization signature := realize signature
  (fun _ _ b => (b.1.val : ℂ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {L : Type u} [Fintype L] [DecidableEq L]
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (A : ℂ) (hA : A ≠ 0) (hparameter : (δ : ℂ) = -A ^ 2 - A⁻¹ ^ 2)
    (s : L) {b c : PositiveBraid} (_ : MarkovEquivalent b c),
    r.readout () (data R hR d hd δ hδ hPF A hA hparameter s) b =
      r.readout () (data R hR d hd δ hδ hPF A hA hparameter s) c

def actual_law : arena.Law actual := by
  intro L _ _ R _ hR d hd δ hδ hPF A hA hparameter s b c h
  exact weighted_path_artin_markov_invariant R hR d hd δ hδ hPF A hA hparameter s h

private def testRelation : ULift.{u} (Fin 2) → ULift.{u} (Fin 2) → Prop :=
  fun _ _ => True
private def testStart : ULift.{u} (Fin 2) := ⟨0⟩
private theorem testPF (a : ULift.{u} (Fin 2)) :
    (∑ b : ULift.{u} (Fin 2) with testRelation a b, (1 : ℝ)) = 2 * 1 := by
  rw [Finset.filter_eq_self.mpr (by intro b hb; trivial)]
  norm_num [Fintype.card_ulift]
private theorem testParameter : ((2 : ℝ) : ℂ) = -Complex.I ^ 2 - Complex.I⁻¹ ^ 2 := by
  norm_num [Complex.inv_I, Complex.I_sq]
private def testData : NativeData.{u} :=
  data testRelation ⟨fun _ _ _ => trivial⟩ (fun _ => 1) (by intro; norm_num)
    2 (by norm_num) testPF Complex.I Complex.I_ne_zero testParameter testStart

private def identityBraid (n : ℕ) (hn : 0 < n) : PositiveBraid := ⟨⟨n, hn⟩, 1⟩

def rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hh := @h (ULift.{u} (Fin 2)) inferInstance inferInstance testRelation inferInstance
    ⟨fun _ _ _ => trivial⟩ (fun _ => 1) (by intro; norm_num)
    2 (by norm_num) testPF Complex.I Complex.I_ne_zero testParameter testStart
    (identityBraid 1 (by omega))
    ⟨⟨2, by omega⟩, strandInclusion 1 1 * lastGenerator 1 (by omega)⟩
    (.rel _ _ (MarkovStep.positive 1 (by omega) 1))
  norm_num [rejected, realize, identityBraid] at hh

private theorem test_trace_one (n : ℕ) :
    tau testRelation (fun _ => 1) 2 n testStart 1 = 1 := by
  have h := weighted_path_markov_trace testRelation
    (⟨fun _ _ _ => trivial⟩ : Std.Symm testRelation) (fun _ => (1 : ℝ))
    (by intro; norm_num) 2 (by norm_num) testPF n testStart
  exact h.2.2.2.2.2.2.2.2.1

private theorem test_identity (n : ℕ) (hn : 0 < n) :
    actual.readout () testData (identityBraid n hn) = (2 : ℂ) ^ (n - 1) := by
  change normalizedTrace testRelation _ (fun _ => 1) _ 2 _ testPF Complex.I
    Complex.I_ne_zero testParameter testStart (identityBraid n hn) = _
  have hw : writhe n (1 : Artin n) = 0 := by
    change Multiplicative.toAdd (exponentHom n 1) = 0
    rw [(exponentHom n).map_one]
    rfl
  have hr : (representation testRelation ⟨fun _ _ _ => trivial⟩ (fun _ => 1)
      (by intro; norm_num) 2 (by norm_num) testPF Complex.I Complex.I_ne_zero
      testParameter n testStart (1 : Artin n) : C testRelation n testStart) = 1 := by
    rw [map_one]
    rfl
  change (2 : ℂ) ^ (n - 1) * (-Complex.I ^ 3) ^ writhe n 1 *
    tau testRelation (fun _ => 1) 2 n testStart
      (representation testRelation _ (fun _ => 1) _ 2 _ testPF Complex.I
        Complex.I_ne_zero testParameter n testStart 1 : C testRelation n testStart) = _
  rw [hw, hr, test_trace_one]
  simp

def family : Registration arena (type_of% (@weighted_path_artin_markov_invariant.{u})) where
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
    refine ⟨testData, identityBraid 1 (by omega), identityBraid 2 (by omega), ?_⟩
    have hi : i = () := Subsingleton.elim _ _
    subst i
    rw [test_identity, test_identity]
    norm_num

#print axioms family

def registration_1.{u_1} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_path_artin_markov_invariant.{u_1}) (Realization signature.{u_1}) Unit Unit where
  unitName := `D5.S3.Quantum.Algebra.Knot.WeightedPathArtinRepresentation.weighted_path_artin_markov_invariant.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.Knot.WeightedPathArtinRepresentation.family
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
    (fun _ p b => by
      letI := p.finite
      letI := p.eq
      letI := p.dec
      exact normalizedTrace p.R p.symmetry p.d p.positive p.delta p.deltaPositive
        p.perron p.A p.nonzero p.parameter p.s b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.Knot.WeightedPathArtinRepresentation
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 15
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 16
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration_1
end Reg.D5.S3.Quantum.Algebra.Knot.WeightedPathArtinRepresentation
