import D5.S3.Combinatorics.Graph.LinearForests.CycleLiftQuotient
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Reversal is observed on the actual directed lifts. -/

namespace Reg.D5.S3.Combinatorics.Graph.LinearForests.CycleLiftQuotient

open _root_.D5.S3.Combinatorics.Graph.LinearForests.UndirectedCycleCompletionLaw
open _root_.D5.S3.Combinatorics.Graph.LinearForests.CycleLiftQuotient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch (same_cycle_perm_congr)

universe u

private abbrev signature : Signature where
  Params := Σ V : Type u, SimpleGraph V
  State p := Lift p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Lift p.2
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u} :=
  realize signature (fun _ _ l => reverseLift l) (fun e => nomatch e)

private def identity : Realization signature.{u} :=
  realize signature (fun _ _ l => l) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Fintype V] (hn : 3 ≤ Fintype.card V) (F : SimpleGraph V),
    (∀ (a : Lift F) x y, (forget hn a).1.Adj x y ↔ a.σ x = y ∨ a.σ y = x) ∧
    (∀ (a : Lift F) x y, a.E x y ↔ F.Adj x y ∧ a.σ x = y) ∧
    Function.Surjective (forget hn (F := F)) ∧
    (∀ a b : Lift F, forget hn b = forget hn a ↔ b = a ∨ b = reverseLift a) ∧
    Function.Involutive (reverseLift (F := F)) ∧
    (∀ a : Lift F, a ≠ R.readout () ⟨V, F⟩ a) ∧
    (∃ e : Quotient (reversalSetoid hn F) ≃ CompletedGraph F,
      ∀ a : Lift F, e (Quotient.mk _ a) = forget hn a) ∧
    (∀ u v, u ≠ v →
      ∃ e : Lift (F ⊔ SimpleGraph.edge u v) ≃ {a : Lift F // (shadow a.σ).Adj u v},
        (∀ a, (e a).1.σ = a.σ ∧ (forget hn (e a).1).1 = (forget hn a).1) ∧
        (∀ a, (e (reverseLift a)).1 = reverseLift (e a).1))

private def sample : Lift (⊥ : SimpleGraph (ULift.{u} (Fin 3))) := by
  let e : Fin 3 ≃ ULift.{u} (Fin 3) := Equiv.ulift.symm
  let σ := e.permCongr (finRotate 3)
  have hRotate : (finRotate 3).IsCycleOn Set.univ := by
    have h := (isCycle_finRotate (n := 1)).isCycleOn
    convert h using 1
    ext x
    simp
  have hCycle : σ.IsCycleOn Set.univ := by
    refine ⟨by simp, ?_⟩
    intro a _ b _
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    exact (same_cycle_perm_congr e _ a b).mpr
      (hRotate.2 (Set.mem_univ a) (Set.mem_univ b))
  exact canonicalLift (by simp) ⊥ σ hCycle (fun _ _ h => False.elim h)

private theorem identity_invalid : ¬ arena.{u}.Law identity := by
  intro h
  have fixed := (h (V := ULift.{u} (Fin 3)) (by simp) ⊥).2.2.2.2.2.1 sample
  exact fixed rfl

def evidence : Registration arena.{u} (type_of% (@reversal_quotient_and_added_edges.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reversal_quotient_and_added_edges.{u}, identity, identity_invalid⟩
  sensitivity := ⟨fun i => ⟨identity, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, identity_invalid⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    refine ⟨⟨ULift.{u} (Fin 3), ⊥⟩, sample, reverseLift sample, ?_⟩
    change reverseLift sample ≠ reverseLift (reverseLift sample)
    have hn : 3 ≤ Fintype.card (ULift.{u} (Fin 3)) := by simp
    intro h
    let F : SimpleGraph (ULift.{u} (Fin 3)) := ⊥
    have inv := (reversal_quotient_and_added_edges hn F).2.2.2.2.1
    exact reverse_distinct hn sample (inv.injective h)

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@reversal_quotient_and_added_edges.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.Graph.LinearForests.CycleLiftQuotient.reversal_quotient_and_added_edges
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.LinearForests.CycleLiftQuotient.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ l => reverseLift l) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LinearForests.CycleLiftQuotient
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg",
        "fn", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.LinearForests.CycleLiftQuotient
