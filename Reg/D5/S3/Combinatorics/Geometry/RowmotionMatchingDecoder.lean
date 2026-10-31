import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.RowmotionMatchingDecoder
import Reg.Support.DependentFamily
import Mathlib.Tactic.FinCases

/-! The source-bound family observes the actual partner permutation. -/

namespace Reg.D5.S3.Combinatorics.Geometry.RowmotionMatchingDecoder

open _root_.D5.S3.Combinatorics.Geometry.RowmotionMatchingDecoder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open CupCapBridgeProposal LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State m := NCMatching m
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ m := Equiv.Perm (Fin m)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M => M.partner) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Equiv.refl _) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (M Q : NCMatching m),
    (∀ k, IsOpening M k ↔ IsOpening Q k) → R.readout () m M = Q.partner

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (patternMatching 4) (patternMatching 4) (fun _ => Iff.rfl)
  have hx := congrArg (fun e : Equiv.Perm (Fin 6) => e 0) he
  change (0 : Fin 6) = 1 at hx
  exact (by decide : (0 : Fin 6) ≠ 1) hx

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨6, patternMatching 4, patternMatching 0, ?_⟩
  intro h
  have hx := congrArg (fun e : Equiv.Perm (Fin 6) => e 0) h
  change (1 : Fin 6) = 5 at hx
  exact (by decide : (1 : Fin 6) ≠ 5) hx

def source_registration : Registration arena (type_of% @partner_eq_of_openings) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨partner_eq_of_openings, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@partner_eq_of_openings) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Geometry.RowmotionMatchingDecoder.unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.RowmotionMatchingDecoder.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.RowmotionMatchingDecoder
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

namespace ordinary

abbrev signature : Signature where
  Params := ℕ
  State n := OrdinaryMatching n
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Set (Fin 3 × Fin n)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M => decode M) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ},
    Function.Injective (R.readout () n) ∧
    (∀ M : OrdinaryMatching n, Separated (decode M) ∧ (decode M).OrdConnected) ∧
    (∀ I : Set (Fin 3 × Fin n), Separated I → ∃ M : OrdinaryMatching n, decode M = I)

private def spaced (P : NCMatching 6) : OrdinaryMatching 60 :=
  ⟨{ sites := OrderEmbedding.ofStrictMono
        (fun k : Fin 6 => (⟨8 * k.val, by have := k.isLt; omega⟩ : Fin 64))
        (by intro r s hrs; change 8 * r.val < 8 * s.val; omega)
     pairs := P
     separated := by
       intro r s hrs
       change 8 ≤ min (8 * s.val - 8 * r.val) (64 - (8 * s.val - 8 * r.val))
       have hr := r.isLt
       have hs := s.isLt
       apply le_min <;> omega },
   by intro k; change 8 * k.val < 62; have := k.isLt; omega⟩

private theorem spaced_ne : spaced (patternMatching 4) ≠ spaced (patternMatching 0) := by
  intro h
  have hh := congrArg (fun M : OrdinaryMatching 60 => M.val.pairs.partner 0) h
  change (1 : Fin 6) = 5 at hh
  exact (by decide : (1 : Fin 6) ≠ 5) hh

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact spaced_ne ((h (n := 60)).1 (show rejected.readout () 60 (spaced (patternMatching 4)) =
    rejected.readout () 60 (spaced (patternMatching 0)) from rfl))

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨60, spaced (patternMatching 4), spaced (patternMatching 0), ?_⟩
  intro he
  exact spaced_ne (ordinary_decoder.1 he)

def source_registration : Registration arena (type_of% @ordinary_decoder) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ordinary_decoder, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ordinary_decoder) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Geometry.RowmotionMatchingDecoder.ordinary.unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.RowmotionMatchingDecoder.ordinary.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.RowmotionMatchingDecoder
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end ordinary

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Combinatorics.Geometry.RowmotionMatchingDecoder
