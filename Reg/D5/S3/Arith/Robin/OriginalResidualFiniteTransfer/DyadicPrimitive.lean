import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.DyadicPrimitive
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.DyadicPrimitive

open _root_.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
open _root_.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.DyadicPrimitive
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset

noncomputable section

namespace FoldedIdentity

abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℝ, ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p m => p.2.1*periodicPrimitive p.1 m-
    p.2.2*periodicPrimitive (2*p.1) m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1,1,1⟩, 0, 1, ?_⟩
  norm_num [actual, realize, periodicPrimitive]

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ}, 0 < d → ∀ (A B : ℝ) (m : ℕ),
    R.readout () ⟨d,A,B⟩ m =
      (2*A-B)*(min (m % (2*d)) (2*d-m % (2*d)) : ℕ)^2/(4*d)-
        (A-B)*(min (m % (2*d)) (2*d-m % (2*d)) : ℕ)/2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (d := 1) (by norm_num) 0 0 0
  norm_num [rejected, realize] at he

def registration : Registration arena (type_of% @folded_identity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨folded_identity, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@folded_identity) (Realization signature) Type Unit where
  unitName := `DyadicPrimitive.folded_identity.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.DyadicPrimitive.FoldedIdentity.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p m => p.2.1*periodicPrimitive p.1 m-
    p.2.2*periodicPrimitive (2*p.1) m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.DyadicPrimitive
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end FoldedIdentity

namespace PrimitiveRange

abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℝ, ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p m => p.2.1*periodicPrimitive p.1 m-
    p.2.2*periodicPrimitive (2*p.1) m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1,1,1⟩, 0, 1, ?_⟩
  norm_num [actual, realize, periodicPrimitive]

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ}, 0 < d → ∀ {A : ℝ}, 0 < A → ∀ (B : ℝ) (m : ℕ),
    |R.readout () ⟨d,A,B⟩ m-midpoint d A B| ≤ radius d A B

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (d := 1) (by norm_num) (A := 1) (by norm_num) 0 0
  norm_num [rejected, realize, midpoint, radius] at he

def registration : Registration arena (type_of% @primitive_range) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨primitive_range, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@primitive_range) (Realization signature) Type Unit where
  unitName := `DyadicPrimitive.primitive_range.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.DyadicPrimitive.PrimitiveRange.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p m => p.2.1*periodicPrimitive p.1 m-
    p.2.2*periodicPrimitive (2*p.1) m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.DyadicPrimitive
    definition := none
    coordinates := #[0, 2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end PrimitiveRange

namespace CenteredPairBound

abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℝ, ℝ
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p b => ∑ m ∈ Ico p.1 (2*p.1),
    b m*(p.2.2.1*centered p.2.1 m-p.2.2.2*centered (2*p.2.1) m))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N d : ℕ}, 0 < N → 0 < d → ∀ (b : ℕ → ℝ) {A : ℝ},
    0 < A → ∀ (B : ℝ), |R.readout () ⟨N,d,A,B⟩ b| ≤ radius d A B*variation N b

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (N := 1) (d := 1) (by norm_num) (by norm_num)
    (fun _ => 0) (A := 1) (by norm_num) 0
  norm_num [rejected, realize, variation] at he

def registration : Registration arena (type_of% @centered_pair_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨centered_pair_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1,2,1,0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    have hi : Ico 1 2 = {1} := by decide
    norm_num [actual, realize, hi, centered]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@centered_pair_bound) (Realization signature) Type Unit where
  unitName := `DyadicPrimitive.centered_pair_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.DyadicPrimitive.CenteredPairBound.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p b => ∑ m ∈ Ico p.1 (2*p.1),
    b m*(p.2.2.1*centered p.2.1 m-p.2.2.2*centered (2*p.2.1) m))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.DyadicPrimitive
    definition := none
    coordinates := #[0, 1, 5, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end CenteredPairBound

end
end Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.DyadicPrimitive
