import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.LeapGroups.LeapGroup
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.LeapGroups.LeapGroup

open _root_.D5.S3.Combinatorics.Graph.LeapGroups.LeapGroup
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Equiv Set MulAction Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

universe u

abbrev signature.{w} : Signature where
  Params := Type w
  State V := SimpleGraph V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := Subgroup (Perm V)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{w} : Realization signature.{w} :=
  realize signature (fun _ _ G => leapGroup G) (fun e => nomatch e)

def rejected.{w} : Realization signature.{w} :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

private def leftVertex : ULift.{u} Bool := ⟨false⟩
private def rightVertex : ULift.{u} Bool := ⟨true⟩
private def flip : Perm (ULift.{u} Bool) := swap leftVertex rightVertex

private theorem left_ne_right : leftVertex.{u} ≠ rightVertex.{u} := by
  intro h
  exact Bool.false_ne_true (congrArg ULift.down h)

private theorem flip_hop : IsHop (⊤ : SimpleGraph (ULift.{u} Bool)) flip := by
  intro ⟨b⟩
  cases b
  · change leftVertex ≠ swap leftVertex rightVertex leftVertex
    rw [swap_apply_left]
    exact left_ne_right
  · change rightVertex ≠ swap leftVertex rightVertex rightVertex
    rw [swap_apply_right]
    exact Ne.symm left_ne_right

private theorem flip_not_bot : flip.{u} ∉ (⊥ : Subgroup (Perm (ULift.{u} Bool))) := by
  intro h
  have he := congrArg (fun g : Perm (ULift.{u} Bool) => g leftVertex) (Subgroup.mem_bot.mp h)
  change swap leftVertex rightVertex leftVertex = leftVertex at he
  rw [swap_apply_left] at he
  exact left_ne_right he.symm

theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro _
  refine ⟨ULift.{u} Bool, ⊤, ⊥, ?_⟩
  intro he
  have hm : flip ∈ leapGroup (⊤ : SimpleGraph (ULift.{u} Bool)) :=
    Subgroup.subset_closure flip_hop
  change leapGroup (⊤ : SimpleGraph (ULift.{u} Bool)) = leapGroup ⊥ at he
  rw [he] at hm
  apply flip_not_bot
  have hempty : {p | IsHop (⊥ : SimpleGraph (ULift.{u} Bool)) p} = ∅ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hp => hp leftVertex
  simpa only [leapGroup, hempty, Subgroup.closure_empty] using hm

abbrev crossArena.{w} : Arena where
  signature := signature.{w}
  Law r := ∀ {V : Type w} (G : SimpleGraph V) [DecidableEq V] {h : Perm V},
    IsHop G h → ∀ (a c : V), G.Adj (h.symm a) c → G.Adj (h.symm c) a →
      swap a c ∈ r.readout () V G

private def color (b : ULift.{u} Bool) : ZMod 2 := if b.down then 1 else 0

theorem cross_rejected : ¬ crossArena.{u}.Law rejected.{u} := by
  classical
  intro bad
  let a : ULift.{u} (Bool × Bool) := ⟨(false, false)⟩
  let c : ULift.{u} (Bool × Bool) := ⟨(false, true)⟩
  let h : Perm (ULift.{u} (Bool × Bool)) :=
    { toFun := fun x => ⟨(!x.down.1, x.down.2)⟩
      invFun := fun x => ⟨(!x.down.1, x.down.2)⟩
      left_inv := by rintro ⟨⟨b, c⟩⟩; cases b <;> rfl
      right_inv := by rintro ⟨⟨b, c⟩⟩; cases b <;> rfl }
  have hh : IsHop (⊤ : SimpleGraph (ULift.{u} (Bool × Bool))) h := by
    rintro ⟨⟨b, d⟩⟩
    change (⟨(b, d)⟩ : ULift.{u} (Bool × Bool)) ≠ ⟨(!b, d)⟩
    intro he
    have he := congrArg (fun x : ULift.{u} (Bool × Bool) => x.down.1) he
    cases b <;> contradiction
  have ha : (⊤ : SimpleGraph (ULift.{u} (Bool × Bool))).Adj (h.symm a) c := by
    intro he
    have he := congrArg (fun x : ULift.{u} (Bool × Bool) => x.down.1) he
    exact (by decide : true ≠ false) he
  have hc : (⊤ : SimpleGraph (ULift.{u} (Bool × Bool))).Adj (h.symm c) a := by
    intro he
    have he := congrArg (fun x : ULift.{u} (Bool × Bool) => x.down.1) he
    exact (by decide : true ≠ false) he
  have hm := bad ⊤ hh a c ha hc
  change swap a c ∈ (⊥ : Subgroup (Perm (ULift.{u} (Bool × Bool)))) at hm
  have he := congrArg (fun g : Perm (ULift.{u} (Bool × Bool)) => g a) (Subgroup.mem_bot.mp hm)
  rw [swap_apply_left] at he
  exact (by decide : true ≠ false) (congrArg (fun x : ULift.{u} (Bool × Bool) => x.down.2) he)

def crossRecord.{w} : Registration crossArena.{w}
    (∀ {V : Type w} (G : SimpleGraph V) [DecidableEq V] {h : Perm V},
      IsHop G h → ∀ (a c : V), G.Adj (h.symm a) c → G.Adj (h.symm c) a →
        swap a c ∈ leapGroup G) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@swap_mem_of_cross_edges, rejected, cross_rejected⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, cross_rejected⟩, fun e => nomatch e⟩
  dependence := dependence

abbrev equalityArena.{w} : Arena where
  signature := signature.{w}
  Law r := ∀ {V : Type w} (G : SimpleGraph V) [Finite V] [DecidableEq V]
      (p : V → ZMod 2) (hflip : ∀ x y, G.Adj x y → p y = p x + 1)
      (hs : ∀ x y, p x = p y → swap x y ∈ leapGroup G)
      (h : Perm V) (hh : IsHop G h), r.readout () V G = parityStabilizer p

theorem equality_rejected : ¬ equalityArena.{u}.Law rejected.{u} := by
  classical
  intro bad
  let G : SimpleGraph (ULift.{u} Bool) := ⊤
  have hflip : ∀ x y, G.Adj x y → color y = color x + 1 := by
    rintro ⟨x⟩ ⟨y⟩ h
    change (⟨x⟩ : ULift.{u} Bool) ≠ ⟨y⟩ at h
    change (if y then 1 else 0 : ZMod 2) = (if x then 1 else 0) + 1
    cases x <;> cases y
    · exact (h rfl).elim
    · decide
    · decide
    · exact (h rfl).elim
  have hs : ∀ x y, color x = color y → swap x y ∈ leapGroup G := by
    rintro ⟨x⟩ ⟨y⟩ h
    change (if x then 1 else 0 : ZMod 2) = (if y then 1 else 0) at h
    cases x <;> cases y
    · rw [swap_self]; exact one_mem _
    · exact (zero_ne_one h).elim
    · exact (one_ne_zero h).elim
    · rw [swap_self]; exact one_mem _
  have hb := bad G color hflip hs flip flip_hop
  change (⊥ : Subgroup (Perm (ULift.{u} Bool))) = parityStabilizer color at hb
  have he := eq_parityStabilizer G color hflip hs flip flip_hop
  have hm : flip ∈ leapGroup G := Subgroup.subset_closure flip_hop
  rw [he, ← hb] at hm
  exact flip_not_bot hm

def equalityRecord.{w} : Registration equalityArena.{w}
    (∀ {V : Type w} (G : SimpleGraph V) [Finite V] [DecidableEq V]
      (p : V → ZMod 2) (hflip : ∀ x y, G.Adj x y → p y = p x + 1)
      (hs : ∀ x y, p x = p y → swap x y ∈ leapGroup G)
      (h : Perm V) (hh : IsHop G h), leapGroup G = parityStabilizer p) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eq_parityStabilizer, rejected, equality_rejected⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, equality_rejected⟩, fun e => nomatch e⟩
  dependence := dependence

def crossRegistration.{w} :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Combinatorics.Graph.LeapGroups.LeapGroup.swap_mem_of_cross_edges.{w})
      (Realization signature.{w}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.LeapGroups.LeapGroup.crossRegistrationUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LeapGroups.LeapGroup.crossRecord
  realizationSource := none
  generated := false
  arena := .source ⟨crossArena.{w}⟩
  objectArena := .source ⟨crossArena.{w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source crossArena.{w} ⟨crossRecord⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{w} (fun _ _ G => leapGroup G) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LeapGroups.LeapGroup
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def equalityRegistration.{w} :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Combinatorics.Graph.LeapGroups.LeapGroup.eq_parityStabilizer.{w})
      (Realization signature.{w}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.LeapGroups.LeapGroup.equalityRegistrationUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LeapGroups.LeapGroup.equalityRecord
  realizationSource := none
  generated := false
  arena := .source ⟨equalityArena.{w}⟩
  objectArena := .source ⟨equalityArena.{w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source equalityArena.{w} ⟨equalityRecord⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{w} (fun _ _ G => leapGroup G) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LeapGroups.LeapGroup
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.Graph.LeapGroups.LeapGroup
