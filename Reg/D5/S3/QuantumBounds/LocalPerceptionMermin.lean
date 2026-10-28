import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumBounds.LocalPerceptionMermin
import Reg.Support.DependentFamily

/-! Faithful source-bound audit attempts for all four public source theorems.
The table theorems preserve the arbitrary finite outcome type and every hypothesis.
The exact elimination observes the four odd moment combinations; the classical
lemma observes its first monomial while fixing the other inputs. All bridges,
countermodels and sensitivity/dependence proofs are kernel checked below.
The standalone endpoint replay is kept outside D5 as verification evidence.
The polymorphic table and absolute-bound source_registration proofs compile,
but their outer Contract.Registration payloads are omitted: the reader rejects
their rigid universe parameters with contract.discovery:rigid_universes.
Their source-binding audit remains incomplete. No declared_validated claim is made.
Outstanding audit coordination: https://github.com/the-omega-institute/trureturing/issues/5214.
-/

namespace Reg.D5.S3.QuantumBounds.LocalPerceptionMermin
open _root_.D5.S3.QuantumBounds.LocalPerceptionMermin
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

abbrev signature : Signature where
  Params := Σ Ω : Type u, Σ _ : Fintype Ω,
    Σ _ : Fin 4 → Ω → ℝ, Fin 4 → Fin 3 → Ω → ℝ
  State _ := Fin 6 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ q m =>
    witness m (@triple q.1 q.2.1 q.2.2.1 q.2.2.2)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => 3) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (Ω : Type u) [inst : Fintype Ω]
    (p : Fin 4 → Ω → ℝ) (outputs : Fin 4 → Fin 3 → Ω → ℝ) (m : Fin 6 → ℝ),
    (∀ v i, 0 ≤ p v i) → (∀ v, ∑ i, p v i = 1) →
    (∀ v j i, -1 ≤ outputs v j i ∧ outputs v j i ≤ 1) →
    (∀ e, -1 ≤ m e ∧ m e ≤ 1) →
    (∀ v j, avg (p v) (outputs v j) = m (edge v j)) →
    R.readout () ⟨Ω, inst, p, outputs⟩ m ≤ 2

theorem actual_law : arena.{u}.Law actual := @table_bound

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have bad := h (ULift.{u} Unit) (fun _ _ => 1) (fun _ _ _ => 1) (fun _ => 1)
    (by intros; norm_num) (by intro v; simp)
    (by intros; norm_num) (by intros; norm_num)
    (by intros; simp [avg])
  change (3 : ℝ) ≤ 2 at bad
  norm_num at bad

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, inferInstance, (fun _ _ => 1), (fun _ _ _ => 1)⟩,
    (fun _ => 1), (fun _ => 0), ?_⟩
  change witness (fun _ => 1) (triple (fun _ (_ : ULift.{u} Unit) => 1)
    (fun _ _ _ => 1)) ≠ witness (fun _ => 0) (triple (fun _ (_ : ULift.{u} Unit) => 1)
    (fun _ _ _ => 1))
  norm_num [witness, triple, avg]

def source_registration : Registration arena.{u} (type_of% (@table_bound.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence


namespace Absolute

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (Ω : Type u) [inst : Fintype Ω]
    (p : Fin 4 → Ω → ℝ) (outputs : Fin 4 → Fin 3 → Ω → ℝ) (m : Fin 6 → ℝ),
    (∀ v i, 0 ≤ p v i) → (∀ v, ∑ i, p v i = 1) →
    (∀ v j i, -1 ≤ outputs v j i ∧ outputs v j i ≤ 1) →
    (∀ e, -1 ≤ m e ∧ m e ≤ 1) →
    (∀ v j, avg (p v) (outputs v j) = m (edge v j)) →
    |R.readout () ⟨Ω, inst, p, outputs⟩ m| ≤ 2

theorem actual_law : arena.{u}.Law actual := @table_abs_bound

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have bad := h (ULift.{u} Unit) (fun _ _ => 1) (fun _ _ _ => 1) (fun _ => 1)
    (by intros; norm_num) (by intro v; simp)
    (by intros; norm_num) (by intros; norm_num)
    (by intros; simp [avg])
  change |(3 : ℝ)| ≤ 2 at bad
  norm_num at bad

def source_registration : Registration arena.{u} (type_of% (@table_abs_bound.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence


end Absolute

namespace Projection

abbrev signature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 4 → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q a => odd a q.1 q.2.1 q.2.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c t : ℝ),
    (∃ d e f, positiveRows a b c t d e f) ↔
      ∑ i, |R.readout () ⟨b,c,t⟩ a i| ≤ 4

theorem actual_law : arena.Law actual := eliminate_pairs

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have rows := (h 2 0 0 0).mpr (by norm_num [rejected, realize])
  have bad := (eliminate_pairs 2 0 0 0).mp rows
  norm_num [odd, Fin.sum_univ_succ] at bad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0,0,0⟩, 0, 1, ?_⟩
  change odd 0 0 0 0 ≠ odd 1 0 0 0
  intro h
  have bad := congrFun h 0
  norm_num [odd] at bad

def source_registration : Registration arena (type_of% (@eliminate_pairs)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration
    (@_root_.D5.S3.QuantumBounds.LocalPerceptionMermin.eliminate_pairs)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumBounds.LocalPerceptionMermin.Projection.eliminate_pairs
  realizationName := `Reg.D5.S3.QuantumBounds.LocalPerceptionMermin.Projection.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q a => odd a q.1 q.2.1 q.2.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.LocalPerceptionMermin
    definition := none
    coordinates := #[1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "arg", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Projection

namespace ClassicalBound

abbrev signature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q a => a*q.2.1*q.2.2.2.1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 3) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a A b B c C : ℝ),
    (-1 ≤ a ∧ a ≤ 1) → (-1 ≤ A ∧ A ≤ 1) →
    (-1 ≤ b ∧ b ≤ 1) → (-1 ≤ B ∧ B ≤ 1) →
    (-1 ≤ c ∧ c ≤ 1) → (-1 ≤ C ∧ C ≤ 1) →
    R.readout () ⟨A,b,B,c,C⟩ a - a*B*C - A*b*C - A*B*c ≤ 2

theorem actual_law : arena.Law actual := classical_bound

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h 0 0 0 0 0 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  change (3 : ℝ) - 0*0*0 - 0*0*0 - 0*0*0 ≤ 2 at bad
  norm_num at bad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0,1,0,1,0⟩, 0, 1, ?_⟩
  change (0 : ℝ)*1*1 ≠ 1*1*1
  norm_num

def source_registration : Registration arena (type_of% (@classical_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration
    (@_root_.D5.S3.QuantumBounds.LocalPerceptionMermin.classical_bound)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumBounds.LocalPerceptionMermin.ClassicalBound.classical_bound
  realizationName := `Reg.D5.S3.QuantumBounds.LocalPerceptionMermin.ClassicalBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q a => a*q.2.1*q.2.2.2.1)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.LocalPerceptionMermin
    definition := none
    coordinates := #[1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end ClassicalBound

end
end Reg.D5.S3.QuantumBounds.LocalPerceptionMermin
