import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.Knot.TwoStrandTrace
import Reg.D5.S3.Quantum.Algebra.Knot.WeightedPathArtinRepresentation
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb
open _root_.D5.S3.Quantum.Algebra.Knot.WeightedPathArtinRepresentation
open _root_.D5.S3.Quantum.Algebra.Knot.TwoStrandTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.Algebra.Knot.WeightedPathArtinRepresentation (NativeData data)

noncomputable section
open scoped BigOperators
namespace Reg.D5.S3.Quantum.Algebra.Knot.TwoStrandTrace
universe u
attribute [local instance] Classical.propDecidable

abbrev signature : Signature where
  Params := NativeData.{u}
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p m => by
    letI := p.finite
    letI := p.eq
    letI := p.dec
    exact normalizedTrace p.R p.symmetry p.d p.positive p.delta p.deltaPositive
      p.perron p.A p.nonzero p.parameter p.s (twoStrand m)) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {L : Type u} [Fintype L] [DecidableEq L]
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (A : ℂ) (hA : A ≠ 0) (hparameter : (δ : ℂ) = -A ^ 2 - A⁻¹ ^ 2)
    (s : L) (m : ℤ),
    r.readout () (data R hR d hd δ hδ hPF A hA hparameter s) m =
      (δ : ℂ) * (-A ^ 3) ^ m *
        (A⁻¹ ^ m * (1 - (δ : ℂ)⁻¹ ^ 2) + (-A ^ 3) ^ m * (δ : ℂ)⁻¹ ^ 2)

def actual_law : arena.Law actual := by
  intro L _ _ R _ hR d hd δ hδ hPF A hA hparameter s m
  exact two_strand_trace R hR d hd δ hδ hPF A hA hparameter s m

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

def rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hh := @h (ULift.{u} (Fin 2)) inferInstance inferInstance testRelation inferInstance
    ⟨fun _ _ _ => trivial⟩ (fun _ => 1) (by intro; norm_num)
    2 (by norm_num) testPF Complex.I Complex.I_ne_zero testParameter testStart 0
  norm_num [rejected, realize] at hh

private theorem actual_zero : actual.{u}.readout () testData.{u} 0 = 2 := by
  have h := @actual_law (ULift.{u} (Fin 2)) inferInstance inferInstance testRelation
    inferInstance ⟨fun _ _ _ => trivial⟩ (fun _ => 1) (by intro; norm_num)
    2 (by norm_num) testPF Complex.I Complex.I_ne_zero testParameter testStart 0
  simpa [testData] using h

private theorem actual_one : actual.{u}.readout () testData.{u} 1 = 1 := by
  have h := @actual_law (ULift.{u} (Fin 2)) inferInstance inferInstance testRelation
    inferInstance ⟨fun _ _ _ => trivial⟩ (fun _ => 1) (by intro; norm_num)
    2 (by norm_num) testPF Complex.I Complex.I_ne_zero testParameter testStart 1
  have hh : (2 : ℂ) * (-Complex.I ^ 3) ^ (1 : ℤ) *
      (Complex.I⁻¹ ^ (1 : ℤ) * (1 - (2 : ℂ)⁻¹ ^ 2) +
        (-Complex.I ^ 3) ^ (1 : ℤ) * (2 : ℂ)⁻¹ ^ 2) = 1 := by
    norm_num [Complex.inv_I, Complex.I_sq, pow_succ, mul_assoc, mul_add, add_mul]
    ring_nf
    norm_num [Complex.I_sq]
  have h' : actual.{u}.readout () testData.{u} 1 =
      (2 : ℂ) * (-Complex.I ^ 3) ^ (1 : ℤ) *
        (Complex.I⁻¹ ^ (1 : ℤ) * (1 - (2 : ℂ)⁻¹ ^ 2) +
          (-Complex.I ^ 3) ^ (1 : ℤ) * (2 : ℂ)⁻¹ ^ 2) := by
    simpa only [testData, Complex.ofReal_ofNat] using h
  exact h'.trans hh

def family : Registration arena (type_of% (@two_strand_trace.{u})) where
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
    refine ⟨testData, 0, 1, ?_⟩
    have hi : i = () := Subsingleton.elim _ _
    subst i
    rw [actual_zero, actual_one]
    norm_num

def registration_1.{u_1} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@two_strand_trace.{u_1}) (Realization signature.{u_1}) Unit Unit where
  unitName := `D5.S3.Quantum.Algebra.Knot.TwoStrandTrace.two_strand_trace.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.Knot.TwoStrandTrace.family
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
    (fun _ p m => by
      letI := p.finite
      letI := p.eq
      letI := p.dec
      exact normalizedTrace p.R p.symmetry p.d p.positive p.delta p.deltaPositive
        p.perron p.A p.nonzero p.parameter p.s (twoStrand m)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.Knot.TwoStrandTrace
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 15
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
end Reg.D5.S3.Quantum.Algebra.Knot.TwoStrandTrace
