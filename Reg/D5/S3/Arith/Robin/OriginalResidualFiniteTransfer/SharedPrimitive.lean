import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer

open _root_.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset

noncomputable section

namespace PrimitiveStep

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ d m => periodicPrimitive d (m+1)-periodicPrimitive d m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ}, 0 < d → ∀ (m : ℕ), R.readout () d m = centered d m

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (d := 1) (by norm_num) 0
  norm_num [rejected, realize, centered] at he

def registration : Registration arena (type_of% @primitive_step) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨primitive_step, rejected, rejected_law⟩
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
    refine ⟨2, 0, 1, ?_⟩
    norm_num [actual, realize, periodicPrimitive]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@primitive_step) (Realization signature) Type Unit where
  unitName := `OriginalResidualFiniteTransfer.primitive_step.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.PrimitiveStep.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ d m => periodicPrimitive d (m+1)-periodicPrimitive d m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end PrimitiveStep

namespace CenteredPairByParts

abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℕ → ℝ, Σ _ : ℕ → ℝ, ℝ
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p a => ∑ m ∈ Ico p.1 (2*p.1), a m*p.2.1 m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ}, 0 < N → ∀ (a f P : ℕ → ℝ),
    (∀ m, P (m+1)-P m = f m) → ∀ (s : ℝ),
    R.readout () ⟨N,f,P,s⟩ a = a (2*N-1)*(P (2*N)+s)-a N*(P N+s)-
      ∑ m ∈ Ico N (2*N-1), (a (m+1)-a m)*(P (m+1)+s)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (N := 1) (by norm_num) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (by intro m; simp) 0
  norm_num [rejected, realize] at he

def registration : Registration arena (type_of% @centered_pair_by_parts) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨centered_pair_by_parts, rejected, rejected_law⟩
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
    refine ⟨⟨1,(fun _ => 1),(fun m => (m : ℝ)),0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    have hi : Ico 1 2 = {1} := by decide
    norm_num [actual, realize, hi]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@centered_pair_by_parts) (Realization signature) Type Unit where
  unitName := `OriginalResidualFiniteTransfer.centered_pair_by_parts.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.CenteredPairByParts.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p a => ∑ m ∈ Ico p.1 (2*p.1), a m*p.2.1 m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
    definition := none
    coordinates := #[0, 3, 4, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end CenteredPairByParts

namespace CenteredPairOfPrimitiveRange

abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℕ → ℝ, Σ _ : ℕ → ℝ, Σ _ : ℝ, ℝ
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p a => ∑ m ∈ Ico p.1 (2*p.1), a m*p.2.1 m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ}, 0 < N → ∀ (a f P : ℕ → ℝ),
    (∀ m, P (m+1)-P m = f m) → ∀ (s C : ℝ),
    (∀ m, |P m+s| ≤ C) → |R.readout () ⟨N,f,P,s,C⟩ a| ≤ C*variation N a

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (N := 1) (by norm_num) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (by intro m; simp) 0 0 (by intro m; simp)
  norm_num [rejected, realize, variation] at he

def registration : Registration arena (type_of% @centered_pair_of_primitive_range) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨centered_pair_of_primitive_range, rejected, rejected_law⟩
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
    refine ⟨⟨1,centered 2,periodicPrimitive 2,0,1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    have hi : Ico 1 2 = {1} := by decide
    norm_num [actual, realize, hi, centered]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@centered_pair_of_primitive_range) (Realization signature) Type Unit where
  unitName := `OriginalResidualFiniteTransfer.centered_pair_of_primitive_range.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.CenteredPairOfPrimitiveRange.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p a => ∑ m ∈ Ico p.1 (2*p.1), a m*p.2.1 m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
    definition := none
    coordinates := #[0, 3, 4, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end CenteredPairOfPrimitiveRange

end
end Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
