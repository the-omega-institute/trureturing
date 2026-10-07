import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.PrimePowers.AffineGcdBehavior
import Reg.Support.DependentFamily

open _root_.D5.S3.Factorization.PrimePowers.AffineGcdBehavior
open _root_.D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution (depth)
open _root_.D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality (runWord)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior

namespace Word

abbrev signature : Signature where
  Params := Σ H : Nat, Σ A : List ℕ+, List (Operation A)
  State _ := ℕ+
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => (runWord (update p.2.1) p.2.2 x).val)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (H : Nat) (A : List ℕ+) (w : List (Operation A)),
    ∃ a t : Nat, 0 < a ∧ libraryGcd H A ∣ t ∧
      ∀ x : ℕ+, R.readout () ⟨H, A, w⟩ x = a * (x : ℕ) + t

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨a, t, ha, _, hrun⟩ := h 2 [] []
  have h1 : 0 = a + t := by
    simpa [rejected, realize] using hrun (1 : ℕ+)
  omega

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro H A w
    exact affine_word_translation H A w,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨⟨2, [], []⟩, (1 : ℕ+), (2 : ℕ+), ?_⟩
    change (1 : Nat) ≠ 2
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.affine_word_translation) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ p x => (runWord (update p.2.1) p.2.2 x).val)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Factorization") "PrimePowers") "AffineGcdBehavior") "affine_word_translation") "Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior/Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ p x => (runWord (update p.2.1) p.2.2 x).val)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior, definition := none, coordinates := #[0, 1, 2], readouts := #[{ path := #["body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "body", "fn", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior.affine_word_translation, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.canonicalArenaFact, `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.sourceBridgeFact, `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.observationFact0, `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.anchorEnumeration }


end Word

namespace Action

abbrev signature : Signature where
  Params := Σ H : Nat, Σ A : List ℕ+, Σ a : ℕ+, List (Fin A.length)
  State _ := ℕ+
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x =>
    (runWord (update p.2.1) (Sum.inl p.2.2.1 :: p.2.2.2.map Sum.inr) x).val)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (H : Nat) (hH : 2 ≤ H) (A : List ℕ+)
      (a : ℕ+) (t : Nat) (ht : libraryGcd H A ∣ t),
    ∃ ws : List (Fin A.length), ∀ x : ℕ+,
      ((R.readout () ⟨H, A, a, ws⟩ x : Nat) : ZMod H) =
        (((a : Nat) * (x : Nat) + t : Nat) : ZMod H)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ws, hw⟩ := h 2 (by omega) [] 1 0 (by simp [libraryGcd])
  have hc := hw 1
  norm_num [rejected, realize] at hc

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro H hH A a t ht
    exact affine_action_realization H hH A a t ht,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨⟨2, [], 1, []⟩, (1 : ℕ+), (2 : ℕ+), ?_⟩
    change (1 : Nat) ≠ 2
    decide

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.affine_action_realization) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ p x =>
    (runWord (update p.2.1) (Sum.inl.{0, 0} p.2.2.1 :: p.2.2.2.map Sum.inr.{0, 0}) x).val)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Factorization") "PrimePowers") "AffineGcdBehavior") "affine_action_realization") "Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior/Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ p x =>
    (runWord (update p.2.1) (Sum.inl.{0, 0} p.2.2.1 :: p.2.2.2.map Sum.inr.{0, 0}) x).val)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior, definition := none, coordinates := #[0, 2, 3, 6], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg", "body", "body", "fn", "arg", "arg"], stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior.affine_action_realization, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.canonicalArenaFact, `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.sourceBridgeFact, `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.observationFact0, `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.anchorEnumeration }


end Action

namespace Local

abbrev signature : Signature where
  Params := Σ _ : Nat, Nat
  State q := ZMod (q.1 ^ q.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q z => depth q.1 q.2 0 z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨2, 1⟩, (0 : ZMod 2), (1 : ZMod 2), ?_⟩
  have hzero : depth 2 1 0 (0 : ZMod 2) = 1 :=
    ((D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result
      2 1 (by decide)).2.1 0 0).2 rfl
  have hone : depth 2 1 0 (1 : ZMod 2) ≠ 1 := by
    intro h
    have hz := ((D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result
      2 1 (by decide)).2.1 0 1).1 h
    exact (by decide : (1 : ZMod 2) ≠ 0) hz
  change depth 2 1 0 (0 : ZMod 2) ≠ depth 2 1 0 (1 : ZMod 2)
  rw [hzero]
  exact Ne.symm hone


namespace Complete

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (p h e : Nat) (hp : p.Prime) (hh : 1 ≤ h) (heh : e ≤ h),
    (∀ X Y : Int,
      localEncoding p h e hp hh heh (X : ZMod (p ^ h)) =
        localEncoding p h e hp hh heh (Y : ZMod (p ^ h)) ↔
      ∀ (a : ℕ+) (b : Int),
        R.readout () ⟨p, h⟩
            ((((a : Nat) : Int) * X + (p : Int) ^ e * b : Int) : ZMod (p ^ h)) =
          depth p h 0 ((((a : Nat) : Int) * Y + (p : Int) ^ e * b : Int) : ZMod (p ^ h))) ∧
    (∀ c : LocalCode p h e, ∃ X : Int,
      localEncoding p h e hp hh heh (X : ZMod (p ^ h)) = c)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := ((law 2 1 0 (by decide) (by decide) (by decide)).1 0 0).1 rfl
    (1 : ℕ+) 0
  have htop : depth 2 1 0 (0 : ZMod 2) = 1 :=
    ((D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result
      2 1 (by decide)).2.1 0 0).2 rfl
  have h' : (0 : Nat) = depth 2 1 0 (0 : ZMod 2) := by
    simpa [rejected, realize] using h
  omega

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro p h e hp hh heh
    exact local_encoding_complete p h e hp hh heh,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := Local.dependence

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.local_encoding_complete) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ q z => depth q.1 q.2 0 z)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Factorization") "PrimePowers") "AffineGcdBehavior") "local_encoding_complete") "Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior/Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ q z => depth q.1 q.2 0 z)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "arg", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior.local_encoding_complete, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.canonicalArenaFact, `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.canonicalObjectArenaFact, `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.sourceBridgeFact, `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.observationFact0, `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.descriptorFact] },
  exclusion := some `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.anchorEnumeration }


end Complete

end Local

end Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior


noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.arena
noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Word\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Word\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.arena
noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Word\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Word\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.arena
noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Action\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Action\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.arena
noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Action\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Action\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.arena
noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Local\",\"Complete\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Local\",\"Complete\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.arena
noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Local\",\"Complete\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Local\",\"Complete\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.arena
      Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.actual)
    Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration)

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"affine_word_translation\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Word\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior.affine_word_translation, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.arena
    Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.actual)
  Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration)

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.observation0 : (H : Nat) →
  (A : List.{0} PNat) →
    (w : List.{0} (D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Operation A)) →
      (a t : Nat) →
        (x : PNat) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.signature PUnit.unit.{1}
            (@Sigma.mk.{0, 0} Nat
              (fun (H : Nat) =>
                @Sigma.{0, 0} (List.{0} PNat) fun (A : List.{0} PNat) =>
                  List.{0} (D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Operation A))
              H
              (@Sigma.mk.{0, 0} (List.{0} PNat)
                (fun (A : List.{0} PNat) => List.{0} (D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Operation A)) A
                w)) :=
  fun (H : Nat) (A : List.{0} PNat) (w : List.{0} (D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Operation A))
    (a t : Nat) (x : PNat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.signature
    Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (H : Nat) =>
        @Sigma.{0, 0} (List.{0} PNat) fun (A : List.{0} PNat) =>
          List.{0} (D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Operation A))
      H
      (@Sigma.mk.{0, 0} (List.{0} PNat)
        (fun (A : List.{0} PNat) => List.{0} (D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Operation A)) A w))
    x

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"affine_word_translation\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Word\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior.affine_word_translation, part := .type, path := [.body, .body, .body, .argument, .body, .argument, .body, .argument, .argument, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Word\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Word\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"affine_word_translation\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior.affine_word_translation, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration).actual (Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration).variation.2.choose (Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration).variation.1 (Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Word\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Word\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Word.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.arena
      Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.actual)
    Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration)

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"affine_action_realization\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Action\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior.affine_action_realization, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.arena
    Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.actual)
  Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration)

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.observation0 : (H : Nat) →
  (hH : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H) →
    (A : List.{0} PNat) →
      (a : PNat) →
        (t : Nat) →
          (ht : @Dvd.dvd.{0} Nat Nat.instDvd (D5.S3.Factorization.PrimePowers.AffineGcdBehavior.libraryGcd H A) t) →
            (ws : List.{0} (Fin (@List.length.{0} PNat A))) →
              (x : PNat) →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                  Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.signature PUnit.unit.{1}
                  (@Sigma.mk.{0, 0} Nat
                    (fun (H : Nat) =>
                      @Sigma.{0, 0} (List.{0} PNat) fun (A : List.{0} PNat) =>
                        @Sigma.{0, 0} PNat fun (a : PNat) => List.{0} (Fin (@List.length.{0} PNat A)))
                    H
                    (@Sigma.mk.{0, 0} (List.{0} PNat)
                      (fun (A : List.{0} PNat) =>
                        @Sigma.{0, 0} PNat fun (a : PNat) => List.{0} (Fin (@List.length.{0} PNat A)))
                      A (@Sigma.mk.{0, 0} PNat (fun (a : PNat) => List.{0} (Fin (@List.length.{0} PNat A))) a ws))) :=
  fun (H : Nat) (hH : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H)
    (A : List.{0} PNat) (a : PNat) (t : Nat)
    (ht : @Dvd.dvd.{0} Nat Nat.instDvd (D5.S3.Factorization.PrimePowers.AffineGcdBehavior.libraryGcd H A) t)
    (ws : List.{0} (Fin (@List.length.{0} PNat A))) (x : PNat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.signature
    Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (H : Nat) =>
        @Sigma.{0, 0} (List.{0} PNat) fun (A : List.{0} PNat) =>
          @Sigma.{0, 0} PNat fun (a : PNat) => List.{0} (Fin (@List.length.{0} PNat A)))
      H
      (@Sigma.mk.{0, 0} (List.{0} PNat)
        (fun (A : List.{0} PNat) => @Sigma.{0, 0} PNat fun (a : PNat) => List.{0} (Fin (@List.length.{0} PNat A))) A
        (@Sigma.mk.{0, 0} PNat (fun (a : PNat) => List.{0} (Fin (@List.length.{0} PNat A))) a ws)))
    x

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"affine_action_realization\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"body\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Action\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior.affine_action_realization, part := .type, path := [.body, .body, .body, .body, .body, .body, .argument, .body, .body, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Action\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Action\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"affine_action_realization\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior.affine_action_realization, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration).actual (Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration).variation.2.choose (Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration).variation.1 (Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Action\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Action\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Action.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.arena
      Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.actual)
    Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration)

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"local_encoding_complete\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Local\",\"Complete\",\"registration_3\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior.local_encoding_complete, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.arena
    Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.actual)
  Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration)

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.observation0 : (p h e : Nat) →
  (hp : Nat.Prime p) →
    (hh : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) h) →
      (heh : @LE.le.{0} Nat instLENat e h) →
        (X Y : Int) →
          (a : PNat) →
            (b : Int) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.signature PUnit.unit.{1}
                (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => Nat) p h) :=
  fun (p h e : Nat) (hp : Nat.Prime p)
    (hh : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) h)
    (heh : @LE.le.{0} Nat instLENat e h) (X Y : Int) (a : PNat) (b : Int) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.signature
    Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => Nat) p h)
    (@Int.cast.{0}
      (ZMod
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p h))
      (@AddGroupWithOne.toIntCast.{0}
        (ZMod
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p h))
        (@Ring.toAddGroupWithOne.{0}
          (ZMod
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p h))
          (@CommRing.toRing.{0}
            (ZMod
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p h))
            (ZMod.commRing
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p h)))))
      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@Nat.cast.{0} Int instNatCastInt (PNat.val a)) X)
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@HPow.hPow.{0, 0, 0} Int Nat Int
            (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
            (@Nat.cast.{0} Int instNatCastInt p) e)
          b)))

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"local_encoding_complete\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"body\",\"argument\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Local\",\"Complete\",\"registration_3\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior.local_encoding_complete, part := .type, path := [.body, .body, .body, .body, .body, .body, .function, .argument, .body, .body, .argument, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Local\",\"Complete\",\"registration_3\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Local\",\"Complete\",\"registration_3\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"local_encoding_complete\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior.local_encoding_complete, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration).actual (Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration).variation.2.choose (Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration).variation.1 (Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Local\",\"Complete\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"PrimePowers\",\"AffineGcdBehavior\",\"Local\",\"Complete\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior, declaration := `Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior.Local.Complete.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
