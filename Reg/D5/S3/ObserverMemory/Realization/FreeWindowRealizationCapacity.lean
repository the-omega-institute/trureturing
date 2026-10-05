import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity
import Reg.Support.DependentFamily

open _root_.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity
open _root_.D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity

universe u v z

@[reducible] def signature : Signature where
  Params := Σ S : Type u, Σ A : Type v, Σ _ : S → S, Σ _ : S → A, ℕ
  State p := WindowState p.2.2.1 p.2.2.2.1 p.2.2.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ w => firstLetter w) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ p w => w.1 ⟨p.2.2.2.2, by omega⟩) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {S : Type u} {A : Type v} [Finite S] (D : S → S) (q : S → A) (n : ℕ),
    (∀ (M : Type z) [Finite M] (I : S → M) (F : M → M) (g : M → A),
      WindowCorrect D q n I F g → Nat.card (WindowState D q n) ≤ Nat.card M) ∧
    (Finite (WindowState D q n) ∧ Function.Surjective (prepare D q n)) ∧
    (∃ r : WindowState D q n → S, Function.RightInverse r (prepare D q n)) ∧
    (∀ r : WindowState D q n → S, Function.RightInverse r (prepare D q n) →
      WindowCorrect D q n (prepare D q n) (representativeUpdate D q n r)
          (R.readout () ⟨S, A, D, q, n⟩) ∧
      ∀ (w : WindowState D q n) (t : ℕ),
        futureReadoutWord (representativeUpdate D q n r) firstLetter n
            ((representativeUpdate D q n r)^[t] w) =
          ((representativeUpdate D q n r)^[t] w).1) ∧
    (∃ (D₀ : Bool × Bool → Bool × Bool) (q₀ : Bool × Bool → Bool)
        (r₀ : WindowState D₀ q₀ 0 → Bool × Bool),
      Function.RightInverse r₀ (prepare D₀ q₀ 0) ∧
      prepare D₀ q₀ 0 ∘ D₀ ≠ representativeUpdate D₀ q₀ 0 r₀ ∘ prepare D₀ q₀ 0)

theorem actual_law : arena.{u,v,z}.Law actual := by
  exact free_window_realization_capacity

theorem rejected_law : ¬ arena.{u,v,z}.Law rejected := by
  intro h
  let D : ULift.{u} Bool → ULift.{u} Bool := fun s => ⟨!s.down⟩
  let q : ULift.{u} Bool → ULift.{v} Bool := fun s => ⟨s.down⟩
  have hs := h D q 1
  obtain ⟨r, hr⟩ := hs.2.2.1
  have hx := (hs.2.2.2.1 r hr).1 (ULift.up false) (0 : Fin 2)
  have impossible : (true : Bool) = false := congrArg ULift.down hx
  exact Bool.noConfusion impossible

def registration : Registration arena.{u,v,z} (arena.{u,v,z}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    let D : ULift.{u} Bool → ULift.{u} Bool := id
    let q : ULift.{u} Bool → ULift.{v} Bool := fun s => ⟨s.down⟩
    refine ⟨⟨ULift.{u} Bool, ULift.{v} Bool, D, q, 0⟩,
      prepare D q 0 (ULift.up false), prepare D q 0 (ULift.up true), ?_⟩
    intro h
    exact Bool.noConfusion (congrArg ULift.down h)

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.free_window_realization_capacity.{u, v, z}) (type_of% (realize.{max (u + 1) (v + 1), v, 0, v, 0} signature.{u, v}
    (fun _ p w => @firstLetter.{u, v} p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 w)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ObserverMemory") "Realization") "FreeWindowRealizationCapacity") "free_window_realization_capacity") "Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity/Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u, v, z})⟩,
  objectArena := .source ⟨(arena.{u, v, z})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u, v, z}) ⟨(registration.{u, v, z})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{max (u + 1) (v + 1), v, 0, v, 0} signature.{u, v}
    (fun _ p w => @firstLetter.{u, v} p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 w)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, definition := none, coordinates := #[0, 1, 3, 4, 5], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg", "body", "body", "fn", "arg", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

namespace Overlap

@[reducible] def signature : Signature where
  Params := Σ X : Type u, Σ A : Type v, Σ n : ℕ, Σ _ : X → X, X → Fin (n + 1) → A
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p x => p.2.2.2.2 x 0) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ p x => p.2.2.2.2 x ⟨p.2.2.1, by omega⟩) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {X : Type u} {A : Type v} (n : ℕ) (U : X → X)
    (L : X → Fin (n + 1) → A),
    (∀ x k (hk : k < n), L (U x) ⟨k, by omega⟩ = L x ⟨k + 1, by omega⟩) →
    ∀ x (j : Fin (n + 1)), R.readout () ⟨X, A, n, U, L⟩ (U^[j.val] x) = L x j

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let U : ULift.{u} Bool → ULift.{u} Bool := fun x => ⟨!x.down⟩
  let L : ULift.{u} Bool → Fin 2 → ULift.{v} Bool :=
    fun x k => ⟨if k.val = 0 then x.down else !x.down⟩
  have hoverlap : ∀ x k (hk : k < 1),
      L (U x) ⟨k, by omega⟩ = L x ⟨k + 1, by omega⟩ := by
    intro x k hk
    have hk0 : k = 0 := by omega
    subst k
    rfl
  have hx := h 1 U L hoverlap (ULift.up false) 0
  have impossible : (true : Bool) = false := congrArg ULift.down hx
  exact Bool.noConfusion impossible

def registration : Registration arena.{u,v} (arena.{u,v}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨overlap_output_window, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, ULift.{v} Bool, 0, id, fun x _ => ⟨x.down⟩⟩,
      ULift.up false, ULift.up true, ?_⟩
    intro h
    exact Bool.noConfusion (congrArg ULift.down h)

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.overlap_output_window.{u, v}) (type_of% (realize.{max (u + 1) (v + 1), u, 0, v, 0} signature.{u, v}
    (fun _ p x => p.2.2.2.2 x 0) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ObserverMemory") "Realization") "FreeWindowRealizationCapacity") "overlap_output_window") "Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity/Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u, v})⟩,
  objectArena := .source ⟨(arena.{u, v})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u, v}) ⟨(registration.{u, v})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{max (u + 1) (v + 1), u, 0, v, 0} signature.{u, v}
    (fun _ p x => p.2.2.2.2 x 0) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, definition := none, coordinates := #[0, 1, 2, 3, 4], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end Overlap

end Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity
