import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
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
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.free_window_realization_capacity, part := .type, path := [], levels := [.param `u, .param `v, .param `z] },
    { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v, .param `z] },
    { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v, .param `z] },
    { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v, .param `z] },
    { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u, .param `v, .param `z] }], facts := [`Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.canonicalArenaFact, `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.sourceBridgeFact, `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.observationFact0, `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.anchorEnumeration }


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
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.overlap_output_window, part := .type, path := [], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u, .param `v] }], facts := [`Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.canonicalArenaFact, `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.sourceBridgeFact, `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.observationFact0, `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.anchorEnumeration }


#print axioms registration

end Overlap

end Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity


noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.canonicalArenaOperand.{u, v} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u + 1) (v + 1), u, 0, v, 0} :=
  Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.arena.{u, v}
noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.canonicalArenaFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"Overlap\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"Overlap\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  .evidence
noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.canonicalObjectArenaOperand.{u, v} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u + 1) (v + 1), u, 0, v, 0} :=
  Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.arena.{u, v}
noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.canonicalObjectArenaFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"Overlap\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"Overlap\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  .evidence

noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.canonicalArenaOperand.{u, v, z} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u + 1) (v + 1), v, 0, v, 0} :=
  Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.arena.{u, v, z}
noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.canonicalArenaFact.{u, v, z} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"z\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"z\"]]]}"))
  { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u), (.param `v), (.param `z)] }
  { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u), (.param `v), (.param `z)] }
  .evidence
noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.canonicalObjectArenaOperand.{u, v, z} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u + 1) (v + 1), v, 0, v, 0} :=
  Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.arena.{u, v, z}
noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.canonicalObjectArenaFact.{u, v, z} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"z\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"z\"]]]}"))
  { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u), (.param `v), (.param `z)] }
  { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u), (.param `v), (.param `z)] }
  .evidence


noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.sourceLaw.{u, v} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u + 1) (v + 1), u, 0, v, 0} (Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.arena.) (Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration.{u, v}).actual

noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.sourceBridgeFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"overlap_output_window\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"Overlap\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.overlap_output_window, part := .type, path := [], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.sourceLaw, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  (Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration.{u, v}).bridge

noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.observation0.{u, v} : {X : Type u} →
  {A : Type v} →
    (n : Nat) →
      (U : X → X) →
        (L :
            X →
              Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                A) →
          (hoverlap :
              ∀ (x : X) (k : Nat) (hk : @LT.lt.{0} Nat instLTNat k n),
                @Eq.{v + 1} A
                  (L (U x)
                    (@Fin.mk
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      k
                      (@Decidable.byContradiction
                        (@LT.lt.{0} Nat instLTNat k
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (Nat.decLt k
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        fun
                          (a :
                            Not
                              (@LT.lt.{0} Nat instLTNat k
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) =>
                        D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.overlap_output_window._proof_1 n
                          k hk a)))
                  (L x
                    (@Fin.mk
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@Decidable.byContradiction
                        (@LT.lt.{0} Nat instLTNat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (Nat.decLt
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        fun
                          (a :
                            Not
                              (@LT.lt.{0} Nat instLTNat
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) =>
                        D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.overlap_output_window._proof_2 n
                          k hk a)))) →
            (x : X) →
              (j :
                  Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{max (u + 1) (v + 1), u, 0, v,
                    0}
                  Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.signature.{u, v}
                  PUnit.unit.{1}
                  (@Sigma.mk.{u + 1, max (max u v) (v + 1)} (Type u)
                    (fun (X : Type u) =>
                      @Sigma.{v + 1, max u v} (Type v) fun (A : Type v) =>
                        @Sigma.{0, max u v} Nat fun (n : Nat) =>
                          @Sigma.{u, max u v} (X → X) fun (x : X → X) =>
                            X →
                              Fin
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                A)
                    X
                    (@Sigma.mk.{v + 1, max u v} (Type v)
                      (fun (A : Type v) =>
                        @Sigma.{0, max u v} Nat fun (n : Nat) =>
                          @Sigma.{u, max u v} (X → X) fun (x : X → X) =>
                            X →
                              Fin
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                A)
                      A
                      (@Sigma.mk.{0, max u v} Nat
                        (fun (n : Nat) =>
                          @Sigma.{u, max u v} (X → X) fun (x : X → X) =>
                            X →
                              Fin
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                A)
                        n
                        (@Sigma.mk.{u, max u v} (X → X)
                          (fun (x : X → X) =>
                            X →
                              Fin
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                A)
                          U L)))) :=
  fun {X : Type u} {A : Type v} (n : Nat) (U : X → X)
    (L :
      X →
        Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          A)
    (hoverlap :
      ∀ (x : X) (k : Nat) (hk : @LT.lt.{0} Nat instLTNat k n),
        @Eq.{v + 1} A
          (L (U x)
            (@Fin.mk
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k
              (@Decidable.byContradiction
                (@LT.lt.{0} Nat instLTNat k
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (Nat.decLt k
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                fun
                  (a :
                    Not
                      (@LT.lt.{0} Nat instLTNat k
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) =>
                D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.overlap_output_window._proof_1 n k hk
                  a)))
          (L x
            (@Fin.mk
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Decidable.byContradiction
                (@LT.lt.{0} Nat instLTNat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (Nat.decLt
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                fun
                  (a :
                    Not
                      (@LT.lt.{0} Nat instLTNat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) =>
                D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.overlap_output_window._proof_2 n k hk
                  a))))
    (x : X)
    (j :
      Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{max (u + 1) (v + 1), u, 0, v, 0}
    Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.signature.{u, v}
    Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.actual.{u, v} PUnit.unit.{1}
    (@Sigma.mk.{u + 1, max (max u v) (v + 1)} (Type u)
      (fun (X : Type u) =>
        @Sigma.{v + 1, max u v} (Type v) fun (A : Type v) =>
          @Sigma.{0, max u v} Nat fun (n : Nat) =>
            @Sigma.{u, max u v} (X → X) fun (x : X → X) =>
              X →
                Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                  A)
      X
      (@Sigma.mk.{v + 1, max u v} (Type v)
        (fun (A : Type v) =>
          @Sigma.{0, max u v} Nat fun (n : Nat) =>
            @Sigma.{u, max u v} (X → X) fun (x : X → X) =>
              X →
                Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                  A)
        A
        (@Sigma.mk.{0, max u v} Nat
          (fun (n : Nat) =>
            @Sigma.{u, max u v} (X → X) fun (x : X → X) =>
              X →
                Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                  A)
          n
          (@Sigma.mk.{u, max u v} (X → X)
            (fun (x : X → X) =>
              X →
                Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                  A)
            U L))))
    (@Nat.iterate.{u + 1} X U
      (@Fin.val
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        j)
      x)

noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.observationFact0.{u, v} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"overlap_output_window\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"Overlap\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.overlap_output_window, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .function, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.observation0, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.varyingLawInput.{u, v} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.canonicalArenaOperand.{u, v})
noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.varyingLaw.{u, v}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"Overlap\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"

noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.statementExclusion.{u, v} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"Overlap\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"overlap_output_window\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.varyingLaw, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  statementLocation := { owner := `D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.overlap_output_window, part := .type, path := [], levels := [(.param `u), (.param `v)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration.{u, v}).actual (Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration.{u, v}).variation.2.choose (Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration.{u, v}).variation.1 (Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration.{u, v}).variation.2.choose_spec

noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2.descriptorFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"Overlap\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"Overlap\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.Overlap.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u), (.param `v)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.sourceLaw.{u, v, z} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u + 1) (v + 1), v, 0, v, 0} (Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.arena.) (Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration.{u, v, z}).actual

noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.sourceBridgeFact.{u, v, z} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"free_window_realization_capacity\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"z\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"z\"]]]}"))
  { owner := `D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.free_window_realization_capacity, part := .type, path := [], levels := [(.param `u), (.param `v), (.param `z)] }
  { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u), (.param `v), (.param `z)] }
  (Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration.{u, v, z}).bridge

noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.observation0.{u, v} : {S : Type u} →
  {A : Type v} →
    [Finite.{u + 1} S] →
      (D : S → S) →
        (q : S → A) →
          (n : Nat) →
            (r :
                @Set.Elem.{v}
                    (Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                      A)
                    (@D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.WindowState.{u, v} S A D q n) →
                  S) →
              @Function.RightInverse.{u + 1, v + 1} S
                  (@Set.Elem.{v}
                    (Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                      A)
                    (@D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.WindowState.{u, v} S A D q n))
                  r (@D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.prepare.{u, v} S A D q n) →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{max (u + 1) (v + 1), v, 0, v,
                      0}
                    Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.signature.{u, v}
                    (@Sigma.mk.{u + 1, max (max u v) (v + 1)} (Type u)
                      (fun (S : Type u) =>
                        @Sigma.{v + 1, max u v} (Type v) fun (A : Type v) =>
                          @Sigma.{u, max u v} (S → S) fun (x : S → S) =>
                            @Sigma.{max u v, 0} (S → A) fun (x : S → A) => Nat)
                      S
                      (@Sigma.mk.{v + 1, max u v} (Type v)
                        (fun (A : Type v) =>
                          @Sigma.{u, max u v} (S → S) fun (x : S → S) =>
                            @Sigma.{max u v, 0} (S → A) fun (x : S → A) => Nat)
                        A
                        (@Sigma.mk.{u, max u v} (S → S)
                          (fun (x : S → S) => @Sigma.{max u v, 0} (S → A) fun (x : S → A) => Nat) D
                          (@Sigma.mk.{max u v, 0} (S → A) (fun (x : S → A) => Nat) q n)))) →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{max (u + 1) (v + 1), v, 0,
                      v, 0}
                    Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.signature.{u, v} PUnit.unit.{1}
                    (@Sigma.mk.{u + 1, max (max u v) (v + 1)} (Type u)
                      (fun (S : Type u) =>
                        @Sigma.{v + 1, max u v} (Type v) fun (A : Type v) =>
                          @Sigma.{u, max u v} (S → S) fun (x : S → S) =>
                            @Sigma.{max u v, 0} (S → A) fun (x : S → A) => Nat)
                      S
                      (@Sigma.mk.{v + 1, max u v} (Type v)
                        (fun (A : Type v) =>
                          @Sigma.{u, max u v} (S → S) fun (x : S → S) =>
                            @Sigma.{max u v, 0} (S → A) fun (x : S → A) => Nat)
                        A
                        (@Sigma.mk.{u, max u v} (S → S)
                          (fun (x : S → S) => @Sigma.{max u v, 0} (S → A) fun (x : S → A) => Nat) D
                          (@Sigma.mk.{max u v, 0} (S → A) (fun (x : S → A) => Nat) q n)))) :=
  fun {S : Type u} {A : Type v} [Finite.{u + 1} S] (D : S → S) (q : S → A) (n : Nat)
    (r :
      @Set.Elem.{v}
          (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            A)
          (@D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.WindowState.{u, v} S A D q n) →
        S)
    (a :
      @Function.RightInverse.{u + 1, v + 1} S
        (@Set.Elem.{v}
          (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            A)
          (@D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.WindowState.{u, v} S A D q n))
        r (@D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.prepare.{u, v} S A D q n)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{max (u + 1) (v + 1), v, 0, v, 0}
    Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.signature.{u, v}
    Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.actual.{u, v} PUnit.unit.{1}
    (@Sigma.mk.{u + 1, max (max u v) (v + 1)} (Type u)
      (fun (S : Type u) =>
        @Sigma.{v + 1, max u v} (Type v) fun (A : Type v) =>
          @Sigma.{u, max u v} (S → S) fun (x : S → S) => @Sigma.{max u v, 0} (S → A) fun (x : S → A) => Nat)
      S
      (@Sigma.mk.{v + 1, max u v} (Type v)
        (fun (A : Type v) =>
          @Sigma.{u, max u v} (S → S) fun (x : S → S) => @Sigma.{max u v, 0} (S → A) fun (x : S → A) => Nat)
        A
        (@Sigma.mk.{u, max u v} (S → S) (fun (x : S → S) => @Sigma.{max u v, 0} (S → A) fun (x : S → A) => Nat) D
          (@Sigma.mk.{max u v, 0} (S → A) (fun (x : S → A) => Nat) q n))))

noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.observationFact0.{u, v} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"free_window_realization_capacity\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"body\",\"body\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"z\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.free_window_realization_capacity, part := .type, path := [.body, .body, .body, .body, .body, .body, .argument, .argument, .argument, .function, .argument, .body, .body, .function, .argument, .argument], levels := [(.param `u), (.param `v), (.param `z)] }
  { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.observation0, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.varyingLawInput.{u, v, z} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.canonicalArenaOperand.{u, v, z})
noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.varyingLaw.{u, v, z}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"z\"]]]}"

noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.statementExclusion.{u, v, z} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"z\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"free_window_realization_capacity\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"z\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u), (.param `v), (.param `z)] }
  statementLocation := { owner := `D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.free_window_realization_capacity, part := .type, path := [], levels := [(.param `u), (.param `v), (.param `z)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration.{u, v, z}).actual (Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration.{u, v, z}).variation.2.choose (Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration.{u, v, z}).variation.1 (Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration.{u, v, z}).variation.2.choose_spec

noncomputable def Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1.descriptorFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"z\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Realization\",\"FreeWindowRealizationCapacity\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"z\"]]]}"))
  { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u), (.param `v), (.param `z)] }
  { owner := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity, declaration := `Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u), (.param `v), (.param `z)] }
  (by first | rfl | (ext <;> rfl))
