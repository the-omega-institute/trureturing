import D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (SuccessfulWord)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Lean LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion

noncomputable section

abbrev signature : Signature where
  Params := Σ H : Nat, Σ _u : ZMod H, ZMod H
  State p := KnownRowFiber p.1 p.2.1 p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ZMod p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p source => (sourceNumber source.val : ZMod p.1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => (0 : ZMod p.1))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (H : Nat) (hH : 2 ≤ H) (u v : ZMod H)
    (hrow : ∃ source : ActualPrefix,
      ((nextRow source).1 : ZMod H) = u ∧
      ((nextRow source).2 : ZMod H) = v),
    ∃ j : Nat, ∀ r : ZMod H, ∃ source : KnownRowFiber H u v,
      source.val.past.length = j ∧
      R.readout () ⟨H, u, v⟩ source = r

theorem actual_law : arena.Law actual := by
  intro H hH u v hrow
  simpa only [actual, realize] using actual_common_depth_fullness H hH u v hrow

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let source : ActualPrefix := ⟨true, [], rfl⟩
  have hrow : ∃ source : ActualPrefix,
      ((nextRow source).1 : ZMod 2) = 0 ∧
      ((nextRow source).2 : ZMod 2) = 1 := by
    refine ⟨source, ?_⟩
    decide
  obtain ⟨j, hj⟩ := h 2 (by omega) 0 1 hrow
  obtain ⟨x, _, hx⟩ := hj 1
  have hfalse : (0 : ZMod 2) = 1 := by
    simpa only [rejected, realize] using hx
  exact (by decide : (0 : ZMod 2) ≠ 1) hfalse

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    let source : ActualPrefix := ⟨true, [], rfl⟩
    have hrow : ∃ source : ActualPrefix,
        ((nextRow source).1 : ZMod 2) = 0 ∧
        ((nextRow source).2 : ZMod 2) = 1 := by
      refine ⟨source, ?_⟩
      decide
    obtain ⟨j, hj⟩ := actual_common_depth_fullness 2 (by omega) 0 1 hrow
    obtain ⟨x, _, hx⟩ := hj 0
    obtain ⟨y, _, hy⟩ := hj 1
    refine ⟨⟨2, 0, 1⟩, x, y, ?_⟩
    change (sourceNumber x.val : ZMod 2) ≠ (sourceNumber y.val : ZMod 2)
    rw [hx,hy]
    decide

register_information_theorem actual_common_depth_fullness in arena
  readout via (realize signature
    (fun _ p source => (sourceNumber source.val : ZMod p.1))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion
    coordinates := #[0, 2, 3]
    readouts := #[{path := #["body", "body", "body", "body", "body", "arg",
      "body", "body", "arg", "body", "arg", "fn", "arg"], stateBinder := 7}] })
  escape continues (open)

#print axioms registration

abbrev nonconverseSignature : Signature where
  Params := Unit
  State _ := Finset (SuccessfulWord 2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Finset (ZMod 4)
  Anchor := Empty
  finiteAnchor := inferInstance

def nonconverseActual : Realization nonconverseSignature :=
  realize nonconverseSignature (fun _ _ available => centers 2 4 0 1 available)
    (fun e => nomatch e)

def nonconverseRejected : Realization nonconverseSignature :=
  realize nonconverseSignature (fun _ _ _ => ∅)
    (fun e => nomatch e)

abbrev nonconverseArena : Arena where
  signature := nonconverseSignature
  Law R := ∃ source : KnownRowFiber 4 0 1,
    sourceNumber source.val = 5 ∧
    ∃ available : Finset (SuccessfulWord 2),
      (R.readout () () available).card = 2 ∧
      ¬ BottomBlocks 2 4 0 1 available

theorem nonconverse_actual_law : nonconverseArena.Law nonconverseActual := by
  simpa only [nonconverseActual, realize] using actual_nonconverse

theorem nonconverse_rejected_law : ¬ nonconverseArena.Law nonconverseRejected := by
  rintro ⟨source, hs, available, hcard, _⟩
  simp [nonconverseRejected, realize] at hcard

def nonconverseRegistration :
    Registration nonconverseArena (nonconverseArena.Law nonconverseActual) where
  actual := nonconverseActual
  bridge := Iff.rfl
  variation := ⟨nonconverse_actual_law, nonconverseRejected,
    nonconverse_rejected_law⟩
  sensitivity := ⟨fun i => ⟨nonconverseRejected,
    fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, nonconverse_rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    obtain ⟨source, hs, available, hcard, _⟩ := actual_nonconverse
    refine ⟨(), ∅, available, ?_⟩
    change centers 2 4 0 1 ∅ ≠ centers 2 4 0 1 available
    intro heq
    have hz : (centers 2 4 0 1 (∅ : Finset (SuccessfulWord 2))).card = 0 := by
      simp [centers]
    have hc : (centers 2 4 0 1 available).card = 0 := by
      rw [← heq]
      exact hz
    omega

register_information_theorem actual_nonconverse in nonconverseArena
  readout via (realize nonconverseSignature
    (fun _ _ available => centers 2 4 0 1 available)
    (fun e => nomatch e))
  realizes nonconverseRegistration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion
    coordinates := #[]
    readouts := #[{path := #["arg", "body", "arg", "arg", "body", "fn",
      "arg", "fn", "arg", "arg"], stateBinder := 1}] })
  escape continues (open)

#print axioms nonconverseRegistration

abbrev futureSignature : Signature where
  Params := Σ H : Nat, Σ u : ZMod H, ZMod H
  State p := KnownRowFiber p.1 p.2.1 p.2.2
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ZMod p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def futureActual : Realization futureSignature :=
  realize futureSignature (fun _ p source => (sourceNumber source.val : ZMod p.1))
    (fun e => nomatch e)

def futureRejected : Realization futureSignature :=
  realize futureSignature (fun _ p _ => (0 : ZMod p.1))
    (fun e => nomatch e)

abbrev futureArena : Arena where
  signature := futureSignature
  Law R := ∀ (H : Nat) (hH : 2 ≤ H) (u v : ZMod H)
    (hrow : ∃ source : ActualPrefix,
      ((nextRow source).1 : ZMod H) = u ∧
      ((nextRow source).2 : ZMod H) = v)
    (x y : KnownRowFiber H u v),
    CompleteFuture H x.val y.val ↔
      R.readout false ⟨H,u,v⟩ x = R.readout true ⟨H,u,v⟩ y

theorem future_actual_law : futureArena.Law futureActual := by
  intro H hH u v hrow x y
  simpa only [futureActual, realize] using
    actual_future_residue_equivalence H hH u v hrow x y

theorem future_rejected_law : ¬ futureArena.Law futureRejected := by
  intro h
  let source : ActualPrefix := ⟨true, [], rfl⟩
  have hrow : ∃ source : ActualPrefix,
      ((nextRow source).1 : ZMod 2) = 0 ∧
      ((nextRow source).2 : ZMod 2) = 1 := by
    refine ⟨source, ?_⟩
    decide
  obtain ⟨j, hj⟩ := actual_common_depth_fullness 2 (by omega) 0 1 hrow
  obtain ⟨x, _, hx⟩ := hj 0
  obtain ⟨y, _, hy⟩ := hj 1
  have hfuture : CompleteFuture 2 x.val y.val :=
    (h 2 (by omega) 0 1 hrow x y).2 (by rfl)
  have heq := (actual_future_residue_equivalence 2 (by omega) 0 1 hrow x y).1 hfuture
  rw [hx,hy] at heq
  exact (by decide : (0 : ZMod 2) ≠ 1) heq

def futureIntervene (i : Bool) : Realization futureSignature :=
  realize futureSignature
    (fun role p source => if role = i then 0 else futureActual.readout role p source)
    (fun e => nomatch e)

theorem future_intervene_rejected (i : Bool) : ¬ futureArena.Law (futureIntervene i) := by
  intro h
  let source : ActualPrefix := ⟨true, [], rfl⟩
  have hrow : ∃ source : ActualPrefix,
      ((nextRow source).1 : ZMod 2) = 0 ∧
      ((nextRow source).2 : ZMod 2) = 1 := by
    refine ⟨source, ?_⟩
    decide
  obtain ⟨j, hj⟩ := actual_common_depth_fullness 2 (by omega) 0 1 hrow
  obtain ⟨x, _, hx⟩ := hj 1
  have heq := (h 2 (by omega) 0 1 hrow x x).1 (by intro suffix; rfl)
  cases i <;> simp [futureIntervene, futureActual, realize, hx] at heq

def futureRegistration : Registration futureArena (futureArena.Law futureActual) where
  actual := futureActual
  bridge := Iff.rfl
  variation := ⟨future_actual_law, futureRejected, future_rejected_law⟩
  sensitivity := ⟨fun i => ⟨futureIntervene i, by
      intro j hji
      funext p source
      simp [futureIntervene, realize, hji], rfl,
    future_intervene_rejected i⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    let source : ActualPrefix := ⟨true, [], rfl⟩
    have hrow : ∃ source : ActualPrefix,
        ((nextRow source).1 : ZMod 2) = 0 ∧
        ((nextRow source).2 : ZMod 2) = 1 := by
      refine ⟨source, ?_⟩
      decide
    obtain ⟨j, hj⟩ := actual_common_depth_fullness 2 (by omega) 0 1 hrow
    obtain ⟨x, _, hx⟩ := hj 0
    obtain ⟨y, _, hy⟩ := hj 1
    refine ⟨⟨2,0,1⟩, x, y, ?_⟩
    change (sourceNumber x.val : ZMod 2) ≠ (sourceNumber y.val : ZMod 2)
    rw [hx,hy]
    decide

register_information_theorem actual_future_residue_equivalence in futureArena
  readout via (realize futureSignature
    (fun _ p source => (sourceNumber source.val : ZMod p.1))
    (fun e => nomatch e))
  realizes futureRegistration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion
    coordinates := #[0, 2, 3]
    readouts := #[
      {path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg"], stateBinder := 5},
      {path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "arg"], stateBinder := 6}] })
  escape continues (open)

#print axioms futureRegistration

run_meta do
  let rows ← TemplateBinding.assessJoined
  for target in #[
      `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual_common_depth_fullness,
      `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual_nonconverse,
      `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual_future_residue_equivalence] do
    let some row := rows.find? (fun r => r.occurrence.key.theoremName == target &&
      r.occurrence.key.registrationModule ==
        `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion)
      | throwError "missing source registration for {target}"
    unless row.result matches .declaredValidated _ do
      throwError "source registration not declared_validated: {target}"
    logInfo m!"REGISTRATION {target}: declared_validated"

end

end Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion
