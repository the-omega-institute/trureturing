import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Games.DivisorNimRevisedTargets
import Reg.Support.DependentFamily

/-! Faithful source registration for the native-game theorem. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S3.Combinatorics.Games.DivisorNimRevisedTargets
open _root_.D5.S3.Combinatorics.Games.DivisorNimGrundy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => Position
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ P => grundy P) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 3) (fun e => nomatch e)

private theorem sample_positive : Positive ({1} : Position) := by
  intro x hx
  have hx' : x = 1 := by simpa using hx
  omega
private theorem sample_depth : HasDepth ({1} : Position) 0 := by
  refine ⟨fun _ _ => Nat.zero_le _, 1, by simp, ?_⟩
  simpa using (padicValNat.prime_pow (p := 2) 0)

abbrev reference_arena : Arena where
  signature := signature
  Law R := ∀ {P : Position}, Positive P → ∀ {H k : ℕ}, HasDepth P k → H ∈ P → R.readout () () P ≤ revisedCeiling H k

private theorem reference_rejected : ¬ reference_arena.Law rejected := by
  intro h
  have hh := h sample_positive (H := 1) (k := 0) sample_depth (by simp)
  change 3 ≤ revisedCeiling 1 0 at hh
  norm_num [revisedCeiling] at hh

noncomputable def reference : Registration reference_arena (type_of% (@revised_bound_reference)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨revised_bound_reference, rejected, reference_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, reference_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, {1}, ?_⟩
    change grundy 0 ≠ grundy {1}
    rw [grundy_empty, singleton_grundy 1 (by decide)]
    decide

noncomputable def reference_contract :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@revised_bound_reference)
      (type_of% (realize signature (fun _ _ P => grundy P) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Games.DivisorNimRevisedTargets.referenceUnit
  realizationName := `Reg.D5.S3.Combinatorics.Games.DivisorNimRevisedTargets.reference
  realizationSource := none
  generated := false
  arena := .source ⟨reference_arena⟩
  objectArena := .source ⟨reference_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source reference_arena ⟨reference⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ P => grundy P) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Games.DivisorNimRevisedTargets
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

abbrev minimum_arena : Arena where
  signature := signature
  Law R := ∀ (P : Position) (H k : ℕ), Positive P → HasDepth P k → H ∈ P → (∀ h ∈ P, H ≤ h) → R.readout () () P ≤ revisedCeiling H k

private theorem minimum_rejected : ¬ minimum_arena.Law rejected := by
  intro h
  have hh := h ({1} : Position) 1 0 sample_positive sample_depth (by simp) (by
    intro x hx
    have hx' : x = 1 := by simpa using hx
    omega)
  change 3 ≤ revisedCeiling 1 0 at hh
  norm_num [revisedCeiling] at hh

noncomputable def minimum : Registration minimum_arena (type_of% (@revised_bound_statement)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨revised_bound_statement, rejected, minimum_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, minimum_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, {1}, ?_⟩
    change grundy 0 ≠ grundy {1}
    rw [grundy_empty, singleton_grundy 1 (by decide)]
    decide

noncomputable def minimum_contract :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@revised_bound_statement)
      (type_of% (realize signature (fun _ _ P => grundy P) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Games.DivisorNimRevisedTargets.minimumUnit
  realizationName := `Reg.D5.S3.Combinatorics.Games.DivisorNimRevisedTargets.minimum
  realizationSource := none
  generated := false
  arena := .source ⟨minimum_arena⟩
  objectArena := .source ⟨minimum_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source minimum_arena ⟨minimum⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ P => grundy P) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Games.DivisorNimRevisedTargets
    definition := some {
      owner := `D5.S3.Combinatorics.Games.DivisorNimRevisedTargets
      name := `D5.S3.Combinatorics.Games.DivisorNimGrundy.RevisedBoundStatement
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

abbrev chain_arena : Arena where
  signature := signature
  Law R := ∀ {P : Position}, Positive P → ∀ {H k : ℕ}, HasDepth P k → H ∈ P → R.readout () () P ≤ revisedCeiling H k ∧ revisedCeiling H k ≤ 2 * H

private theorem chain_rejected : ¬ chain_arena.Law rejected := by
  intro h
  have hh := h sample_positive (H := 1) (k := 0) sample_depth (by simp)
  have hb := hh.1
  change 3 ≤ revisedCeiling 1 0 at hb
  norm_num [revisedCeiling] at hb

noncomputable def chain : Registration chain_arena (type_of% (@revised_bound_chain)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨revised_bound_chain, rejected, chain_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, chain_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, {1}, ?_⟩
    change grundy 0 ≠ grundy {1}
    rw [grundy_empty, singleton_grundy 1 (by decide)]
    decide

noncomputable def chain_contract :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@revised_bound_chain)
      (type_of% (realize signature (fun _ _ P => grundy P) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Games.DivisorNimRevisedTargets.chainUnit
  realizationName := `Reg.D5.S3.Combinatorics.Games.DivisorNimRevisedTargets.chain
  realizationSource := none
  generated := false
  arena := .source ⟨chain_arena⟩
  objectArena := .source ⟨chain_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source chain_arena ⟨chain⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ P => grundy P) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Games.DivisorNimRevisedTargets
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Combinatorics.Games.DivisorNimRevisedTargets
