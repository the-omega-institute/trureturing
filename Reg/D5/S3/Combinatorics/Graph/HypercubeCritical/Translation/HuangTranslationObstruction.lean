import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.HuangTranslationObstruction
import Reg.Support.SingleDependentReadout

/-! Read out the number of pairs of TRUE coordinates of a translation mask. -/

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.HuangTranslationObstruction

open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.HuangTranslationObstruction (even_choose_two_of_reachable_translation)
open _root_.D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum (Q IsBalanced)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false

noncomputable section

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ Q (fun _ => ℕ)

private abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : ℕ} {C : Finset (Q n)} {a x : Q n}, IsBalanced C →
    ∀ hT : ∀ y ∈ C, (fun i => Bool.xor (a i) (y i)) ∈ C,
    ∀ hx : x ∈ C, ((hypercube n).induce (C : Set (Q n))).Reachable
      ⟨x, hx⟩ ⟨(fun i => Bool.xor (a i) (x i)), hT x hx⟩ →
    Even (r.readout () n a)

private def actual : Realization signature :=
  realize signature (fun _ _ a => (Finset.univ.filter fun i => a i = true).card.choose 2)
    (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let x : Q 0 := fun _ => false
  let C : Finset (Q 0) := {x}
  have hC : IsBalanced C := by
    refine ⟨fun _ => 1, fun _ _ => Or.inl rfl, ?_⟩
    intro u hu v hv h
    have huv : u = v := (Finset.mem_singleton.mp hu).trans (Finset.mem_singleton.mp hv).symm
    exact (h.ne huv).elim
  have hT : ∀ y ∈ C, (fun i => Bool.xor (x i) (y i)) ∈ C := by
    intro y hy
    simpa [x] using hy
  have hx : x ∈ C := Finset.mem_singleton_self x
  have h := law (C := C) (a := x) hC hT hx SimpleGraph.Reachable.rfl
  exact (by decide : ¬ Even (1 : ℕ)) h

def source_registration : Registration arena (type_of% @even_choose_two_of_reachable_translation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@even_choose_two_of_reachable_translation, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    refine ⟨2, fun _ => false, fun _ => true, ?_⟩
    decide

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@even_choose_two_of_reachable_translation) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.HuangTranslationObstruction.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.HuangTranslationObstruction.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ a => (Finset.univ.filter fun i => a i = true).card.choose 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.HuangTranslationObstruction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.HuangTranslationObstruction
