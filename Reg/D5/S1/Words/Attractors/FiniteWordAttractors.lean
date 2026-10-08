import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Attractors.FiniteWordAttractors
import Reg.Support.DependentFamily

open _root_.D5.S1.Words.Attractors
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u
namespace Reg.D5.S1.Words.Attractors.FiniteWordAttractors.HelperAudits
noncomputable section

theorem no_empty_attractor {α : Type u} (w : List α) (hw : 0 < w.length) :
    ¬ IsAttractor w ∅ := by
  intro h
  obtain ⟨b,p,hb,hp,rest⟩ := h.2 0 1 (by omega) (by omega)
  simpa using hp

theorem replicate_attractor {α : Type u} (a : α) (m : Nat) (hm : 0 < m) :
    IsAttractor (List.replicate m a) {0} := by
  refine ⟨by simpa using hm, ?_⟩
  intro s l hl hsl
  simp only [List.length_replicate] at hsl
  refine ⟨0,0,by simp; omega,by simp,le_rfl,by simpa using hl,?_⟩
  simp only [List.drop_replicate, List.drop_zero, List.take_replicate]
  congr 1
  omega

theorem gamma_nil {α : Type u} : gamma ([] : List α) = 0 := by
  classical
  have h := (attractor_minimum ([] : List α)).2.1 ∅
    (by refine ⟨by simp, ?_⟩; intro a l hl ha; simp at ha; omega)
  simpa using h

theorem gamma_singleton {α : Type u} [DecidableEq α] (a : α) : gamma [a] = 1 := by
  have lo := (attractor_minimum [a]).2.2
  have hi := (attractor_minimum [a]).2.1 {0}
    (replicate_attractor a 1 (by omega))
  simp at lo hi
  omega

namespace Minimum
abbrev signature : Signature where
  Params := Type u
  State := fun α => List α
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ w => gamma w) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : Type u} [DecidableEq α] (w : List α),
(∃ S : Finset Nat, IsAttractor w S ∧ S.card = R.readout () α w) ∧
      (∀ S : Finset Nat, IsAttractor w S → gamma w ≤ S.card) ∧
      w.toFinset.card ≤ gamma w

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨S,hS,hcard⟩ := (h ([⟨0⟩] : List (ULift.{u} Nat))).1
  have hzero : S = ∅ := Finset.card_eq_zero.mp hcard
  rw [hzero] at hS
  exact no_empty_attractor _ (by simp) hS

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@attractor_minimum, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    exact ⟨ULift.{u} Nat, [], [⟨0⟩], by simp [actual, realize, gamma_nil, gamma_singleton]⟩

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Attractors.attractor_minimum.{u_1}) (type_of% (realize.{u_1 + 1, u_1, 0, 0, 0} signature.{u_1} (fun _ _ w => gamma.{u_1} w) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Attractors") "attractor_minimum") "Reg.D5.S1.Words.Attractors.FiniteWordAttractors/Reg.D5.S1.Words.Attractors.FiniteWordAttractors.HelperAudits.Minimum.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Attractors.FiniteWordAttractors.HelperAudits.Minimum.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, 0, 0} signature.{u_1} (fun _ _ w => gamma.{u_1} w) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Attractors.FiniteWordAttractors, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "fn", "arg", "arg", "body", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }



end Minimum

namespace Window
abbrev signature : Signature where
  Params := Nat
  State := fun _ => Finset Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Finset Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p S => insert (p-1) S) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => ∅) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : Type u} (w : List α)
    (N q p B : Nat) (S : Finset Nat)
    (hN : 0 < N) (hNw : N ≤ w.length)
    (hq : 0 < q) (hqp : q ≤ p) (hpN : p ≤ N)
    (hqB : q ≤ B) (hBN : B ≤ N - 1)
    (hwindow : (w.drop (p - q)).take B = w.take B)
    (hwindow_bound : p - q + B ≤ w.length)
    (hold : IsAttractor (w.take (N - 1)) S)
    (hqS : q - 1 ∈ S)
    (hcut : B = N - 1 ∨ B ∈ S.erase (q - 1))
    (hreduce : (p = N ∧ List.HasPeriod w N) ∨ w.drop p <+: w.take B),
IsAttractor w (R.readout () p (S.erase (q - 1))) ∧
      (insert (p - 1) (S.erase (q - 1))).card ≤ S.card

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h ([⟨0⟩,⟨0⟩] : List (ULift.{u} Nat)) 2 1 2 1 {0}
    (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rfl) (by decide) (replicate_attractor (ULift.up 0) 1 (by omega))
    (by simp) (Or.inl rfl) (Or.inl ⟨rfl, by exact List.hasPeriod_of_length_le _ _ (by decide)⟩)
  exact no_empty_attractor _ (by simp) hh.1

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@attractor_window_transfer, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    exact ⟨1, ∅, {1}, by cases i; decide⟩

noncomputable def registration_2.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Attractors.attractor_window_transfer.{u_1}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ p S => insert.{0, 0} (p-1) S) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Attractors") "attractor_window_transfer") "Reg.D5.S1.Words.Attractors.FiniteWordAttractors/Reg.D5.S1.Words.Attractors.FiniteWordAttractors.HelperAudits.Window.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Attractors.FiniteWordAttractors.HelperAudits.Window.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ p S => insert.{0, 0} (p-1) S) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Attractors.FiniteWordAttractors, definition := none, coordinates := #[4], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }



end Window

namespace Extension
abbrev signature : Signature where
  Params := Nat
  State := fun _ => Finset Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Finset Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ N S => insert (N-1) S) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => ∅) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : Type u} (w : List α) (N : Nat) (S : Finset Nat)
    (hN : 0 < N) (hNw : N ≤ w.length) (hper : List.HasPeriod w N)
    (hold : IsAttractor (w.take (N - 1)) S),
IsAttractor w (R.readout () N S)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h ([⟨0⟩] : List (ULift.{u} Nat)) 1 ∅ (by omega) (by decide)
    (List.hasPeriod_of_length_le _ _ (by decide)) (by
      refine ⟨by simp, ?_⟩
      intro a l hl ha
      simp at ha
      omega)
  exact no_empty_attractor _ (by simp) hh

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@periodic_attractor_extension, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    exact ⟨1, ∅, {1}, by cases i; decide⟩

noncomputable def registration_3.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Attractors.periodic_attractor_extension.{u_1}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ N S => insert.{0, 0} (N-1) S) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Attractors") "periodic_attractor_extension") "Reg.D5.S1.Words.Attractors.FiniteWordAttractors/Reg.D5.S1.Words.Attractors.FiniteWordAttractors.HelperAudits.Extension.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Attractors.FiniteWordAttractors.HelperAudits.Extension.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ N S => insert.{0, 0} (N-1) S) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Attractors.FiniteWordAttractors, definition := none, coordinates := #[2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }



end Extension

end
end Reg.D5.S1.Words.Attractors.FiniteWordAttractors.HelperAudits
