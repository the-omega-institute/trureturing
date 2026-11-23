import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9ParityOverlap
import Reg.Support.SingleDependentReadout

/-! The observed cardinality is the actual parity-restricted translated intersection. -/

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9ParityOverlap

open _root_.D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum (Q IsBalanced)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang (parity)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9ParityOverlap
  (parity_overlap_card_ne_one)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false

noncomputable section

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : Q 9, Σ _ : Bool, Finset (Q 9))
    (fun _ => Finset (Q 9)) (fun _ => ℕ)

open Classical in
private abbrev arena : Arena where
  signature := signature
  Law r := ∀ (a : Q 9) (b : Bool) (C D : Finset (Q 9)),
    IsBalanced C → IsBalanced D →
    ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3 →
    ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3 →
    r.readout () ⟨a, b, C⟩ D ≠ 1

private def actual : Realization signature :=
  realize signature
    (fun _ ⟨a, b, C⟩ D =>
      ((C ∩ D.image (fun x i => Bool.xor (a i) (x i))).filter (fun x => parity x = b)).card)
    Empty.elim

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) Empty.elim

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro law
  have hb : IsBalanced (∅ : Finset (Q 9)) := by
    refine ⟨fun _ => 1, ?_, ?_⟩ <;>
      intro x hx <;> exact (Finset.notMem_empty x hx).elim
  have hr : ((hypercube 9).induce ((∅ : Finset (Q 9)) : Set (Q 9))).IsRegularOfDegree 3 := by
    intro x
    exact (Finset.notMem_empty x.val (Finset.mem_coe.mp x.property)).elim
  exact law (fun _ => false) false ∅ ∅ hb hb hr hr rfl

def sourceEvidence : Registration arena (type_of% @parity_overlap_card_ne_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨parity_overlap_card_ne_one, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    let x : Q 9 := fun _ => false
    refine ⟨⟨x, parity x, {x}⟩, ∅, {x}, ?_⟩
    simp [actual, realize, x, Finset.filter_singleton]

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@parity_overlap_card_ne_one) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9ParityOverlap.parity_overlap_card_ne_one.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9ParityOverlap.sourceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ ⟨a, b, C⟩ D =>
      ((C ∩ D.image (fun x i => Bool.xor (a i) (x i))).filter (fun x => parity x = b)).card)
    Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9ParityOverlap
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms parity_overlap_card_ne_one
#print axioms registration

end
end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9ParityOverlap
