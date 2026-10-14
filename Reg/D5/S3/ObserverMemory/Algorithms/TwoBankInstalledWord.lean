import D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord
open D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

private def readTable : Table 0 := ⟨fun _ => .read [], fun _ _ => ∅⟩
private def haltTable : Table 0 := ⟨fun _ => .halt false, fun _ _ => ∅⟩
private def obs : Nat → Address → RawReply := fun _ _ => 0

private theorem routing_zero {k : Nat} {T : Table k} {w v : Word k}
    (h : Routing T w v 0) : w = v := by
  cases h
  rfl

private theorem execution_nil {k : Nat} {T : Table k}
    {o : Nat → Address → RawReply} {w v : Word k} {a b : Nat}
    (h : Execution T o w a v b []) : w = v := by
  cases h
  rfl

private theorem execution_from_halt {k : Nat} {T : Table k}
    {o : Nat → Address → RawReply} {w v : Word k} {a b : Nat}
    {es : List Event} {bit : Bool}
    (halt : (installed T w).instruction = .halt bit)
    (h : Execution T o w a v b es) : es = [] := by
  cases h with
  | refl => rfl
  | read hi _ _ => rw [halt] at hi; contradiction
  | update hi _ _ => rw [halt] at hi; contradiction

private theorem change_irrefl {k : Nat} (w : Word k) : ¬ Change w w := by
  have different : ∀ {v : Word k}, Change w v → w ≠ v := by
    intro v h
    cases h with
    | a j =>
      intro same
      have bit := congrArg (fun u => j ∈ u.a) same
      by_cases hj : j ∈ w.a <;> simp [Finset.mem_symmDiff, hj] at bit
    | b j =>
      intro same
      have bit := congrArg (fun u => j ∈ u.b) same
      by_cases hj : j ∈ w.b <;> simp [Finset.mem_symmDiff, hj] at bit
    | flag r =>
      intro same
      have bit := congrArg (fun u => r ∈ u.flags) same
      by_cases hr : r ∈ w.flags <;> simp [Finset.mem_symmDiff, hr] at bit
    | phase =>
      intro same
      have index := congrArg (fun u => u.phase.val) same
      change w.phase.val = (w.phase.val + 1) % 8 at index
      have bound := w.phase.isLt
      omega
  exact fun h => different h rfl

namespace TypedTransfer

@[reducible] def signature : Signature where
  Params := Σ k : Nat, Σ _ : Table k, Σ _ : Bool, Σ _ : Bank k, Flag
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ ⟨_k, T, right, z, r⟩ n => decide
      (Routing T ((installed T (ready right z)).next r)
        (ready (!right) (T.delta z r)) n)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {k : Nat} (T : Table k) (right : Bool) (z : Bank k) (r : Flag)
    (_typed : Typed (T.instruction z) r),
    (installed T (ready right z)).instruction = T.instruction z ∧
    F.readout () ⟨k, T, right, z, r⟩
      (z.card + (T.delta z r).card + if right then 6 else 4) = true

private theorem positive : arena.Law actual := by
  classical
  intro k T right z r typed
  simpa [actual, realize] using (typed_transfer T right z r typed)

private theorem negative : ¬ arena.Law rejected := by
  intro h
  have bad := (h readTable false ∅ 0 (by decide)).2
  cases bad

def evidence : Registration arena (type_of% (@typed_transfer)) where
  actual := actual
  bridge := by
    classical
    simp [actual, realize]
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    refine ⟨⟨0, readTable, false, ∅, 0⟩, 4, 0, ?_⟩
    have good := (typed_transfer readTable false ∅ 0 (by decide)).2
    have bad : ¬ Routing readTable ((installed readTable (ready false ∅)).next 0)
        (ready true ∅) 0 := by
      intro h
      have same := congrArg Word.flags (routing_zero h)
      simp [installed, ready] at same
    change decide (Routing readTable ((installed readTable (ready false ∅)).next 0)
      (ready true ∅) 4) ≠ decide (Routing readTable
        ((installed readTable (ready false ∅)).next 0) (ready true ∅) 0)
    rw [decide_eq_true (by simpa [readTable] using good), decide_eq_false bad]
    decide

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@typed_transfer)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.typed_transfer,
  realizationName :=
    `Reg.D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.TypedTransfer.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord,
    definition := none, coordinates := #[0, 1, 2, 3, 4],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := true }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end TypedTransfer

namespace LocalRows

@[reducible] def signature : Signature where
  Params := Σ k : Nat, Word k
  State p := Word p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ ⟨_k, w⟩ v => decide (Change w v)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {k : Nat} (T : Table k) (w : Word k) (r : Flag),
    (installed T w).next r = w ∨ F.readout () ⟨k, w⟩ ((installed T w).next r) = true

private theorem positive : arena.Law actual := by
  classical
  intro k T w r
  simpa [actual, realize] using (installed_local T w r)

private theorem negative : ¬ arena.Law rejected := by
  intro h
  have bad := h readTable (ready false ∅) 0
  rcases bad with same | impossible
  · have flags := congrArg Word.flags same
    simp [installed, ready] at flags
  · cases impossible

def evidence : Registration arena (type_of% (@installed_local)) where
  actual := actual
  bridge := by
    classical
    simp [actual, realize]
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    let w : Word 0 := ready false ∅
    let v : Word 0 := { w with flags := {0} }
    have good : Change w v := by
      simpa [w, v, ready, Finset.symmDiff_def] using Change.flag w 0
    have bad : ¬ Change w w := change_irrefl w
    refine ⟨⟨0, w⟩, v, w, ?_⟩
    change decide (Change w v) ≠ decide (Change w w)
    rw [decide_eq_true good, decide_eq_false bad]
    decide

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@installed_local)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.installed_local,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.LocalRows.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord,
    definition := none, coordinates := #[0, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := true }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end LocalRows

namespace PhysicalRows

@[reducible] def signature : Signature where
  Params := Nat
  State k := Word k
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ k := Fin (2 * (k + (k + (5 + 3))) - 1) → Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ _ w => physical w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => true) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {k : Nat} (T : Table k) (w : Word k) (r : Flag),
    (∀ i j, i.val + 1 = j.val → F.readout () k w i = false ∨ physical w j = false) ∧
    (∀ i j, i.val + 1 = j.val →
      physical ((installed T w).next r) i = false ∨
      physical ((installed T w).next r) j = false) ∧
    ((installed T w).next r = w ∨
      OneBit (physical w) (physical ((installed T w).next r)))

private theorem positive : arena.Law actual := by
  classical
  intro k T w r
  simpa [actual, realize] using (physical_rows T w r)

private theorem negative : ¬ arena.Law rejected := by
  intro h
  let T : Table 1 := ⟨fun _ => .halt false, fun _ _ => ∅⟩
  let w : Word 1 := ⟨∅, {0}, ∅, 0⟩
  have bad := (h T w 0).1 (1 : Fin 19) (2 : Fin 19) rfl
  change true = false ∨ true = false at bad
  rcases bad with bad | bad <;> cases bad

def evidence : Registration arena (type_of% (@physical_rows)) where
  actual := actual
  bridge := by
    classical
    simp [actual, realize]
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨1, ⟨∅, ∅, ∅, 0⟩, ⟨{0}, ∅, ∅, 0⟩, ?_⟩
    intro same
    have bit := congrFun same (0 : Fin 19)
    change false = true at bit
    cases bit

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@physical_rows)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.physical_rows,
  realizationName :=
    `Reg.D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.PhysicalRows.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "fn", "arg", "body",
        "body", "body", "fn", "arg", "fn", "arg", "fn"],
      stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end PhysicalRows

namespace NativeTransfer

@[reducible] def signature : Signature where
  Params := Σ k : Nat, Σ _ : Table k, Σ _ : Nat → Address → RawReply,
    Σ _ : Bool, Σ _ : Bank k, Σ _ : Nat, Address
  State _ := List Event
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ ⟨_k, T, o, right, z, a, p⟩ es => decide
      (Execution T o (ready right z) a
        (ready (!right) (T.delta z (replyFlag (o a p)))) a es)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {k : Nat} (T : Table k) (obs : Nat → Address → RawReply)
    (right : Bool) (z : Bank k) (a : Nat),
    (∀ p, T.instruction z = .read p →
      F.readout () ⟨k, T, obs, right, z, a, p⟩
        (.read p (obs a p) :: List.replicate
          (z.card + (T.delta z (replyFlag (obs a p))).card + if right then 6 else 4)
          (.read [] (obs a []))) = true) ∧
    (T.instruction z = .update →
      Execution T obs (ready right z) a (ready (!right) (T.delta z 4)) (a + 1)
        (.update :: List.replicate
          (z.card + (T.delta z 4).card + if right then 6 else 4)
          (.read [] (obs (a + 1) []))))

private theorem positive : arena.Law actual := by
  classical
  intro k T obs right z a
  simpa [actual, realize] using (native_transfer T obs right z a)

private theorem negative : ¬ arena.Law rejected := by
  intro h
  have bad := (h readTable obs false ∅ 0).1 [] rfl
  cases bad

def evidence : Registration arena (type_of% (@native_transfer)) where
  actual := actual
  bridge := by
    classical
    simp [actual, realize]
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    let es : List Event := .read [] 0 :: List.replicate 4 (.read [] 0)
    have good : Execution readTable obs (ready false ∅) 0 (ready true ∅) 0 es := by
      simpa [readTable, obs, es] using (native_transfer readTable obs false ∅ 0).1 [] rfl
    have bad : ¬ Execution readTable obs (ready false ∅) 0 (ready true ∅) 0 [] := by
      intro h
      have same := congrArg Word.phase (execution_nil h)
      cases same
    refine ⟨⟨0, readTable, obs, false, ∅, 0, []⟩, es, [], ?_⟩
    change decide (Execution readTable obs (ready false ∅) 0 (ready true ∅) 0 es) ≠
      decide (Execution readTable obs (ready false ∅) 0 (ready true ∅) 0 [])
    rw [decide_eq_true good, decide_eq_false bad]
    decide

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_transfer)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.native_transfer,
  realizationName :=
    `Reg.D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.NativeTransfer.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord,
    definition := none, coordinates := #[0, 1, 2, 3, 4, 5, 6],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := true }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end NativeTransfer

namespace Simulation

@[reducible] def signature : Signature where
  Params := Σ k : Nat, Σ _ : Table k, Σ _ : Nat → Address → RawReply,
    Σ _ : Bank k, Σ _ : Bank k, Σ _ : Nat, Σ _ : Nat, Σ _ : Bool, Bool
  State _ := List Event
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ ⟨_k, T, o, z, t, a, b, right, last⟩ es => decide
      (Execution T o (ready right z) a (ready last t) b es)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {k : Nat} {T : Table k} {obs : Nat → Address → RawReply}
    {z t : Bank k} {a b : Nat} (_path : Run (sourceProgram T) obs z a t b)
    (right : Bool),
    ∃ last events, F.readout () ⟨k, T, obs, z, t, a, b, right, last⟩ events = true

private theorem positive : arena.Law actual := by
  classical
  intro k T obs z t a b path right
  simpa [actual, realize] using (simulate_run path right)

private theorem negative : ¬ arena.Law rejected := by
  intro h
  obtain ⟨last, events, bad⟩ := @h 0 haltTable obs ∅ ∅ 0 0 (.refl _ _) false
  cases bad

def evidence : Registration arena (type_of% (@simulate_run)) where
  actual := actual
  bridge := by
    classical
    simp [actual, realize]
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    have good : Execution haltTable obs (ready false ∅) 0 (ready false ∅) 0 [] := .refl _ _
    have bad : ¬ Execution haltTable obs (ready false ∅) 0 (ready false ∅) 0 [.update] := by
      intro h
      have impossible := execution_from_halt (bit := false) (by rfl) h
      cases impossible
    refine ⟨⟨0, haltTable, obs, ∅, ∅, 0, 0, false, false⟩, [], [.update], ?_⟩
    change decide (Execution haltTable obs (ready false ∅) 0 (ready false ∅) 0 []) ≠
      decide (Execution haltTable obs (ready false ∅) 0 (ready false ∅) 0 [.update])
    rw [decide_eq_true good, decide_eq_false bad]
    decide

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@simulate_run)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.simulate_run,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.Simulation.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord,
    definition := none, coordinates := #[0, 1, 2, 3, 4, 5, 6, 8, 9],
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "arg", "body"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := true }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end Simulation

namespace Halt

open Simulation (signature actual rejected)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {k : Nat} {T : Table k} {obs : Nat → Address → RawReply}
    {z t : Bank k} {a b : Nat} {bit : Bool}
    (_path : Run (sourceProgram T) obs z a t b) (_halt : T.instruction t = .halt bit)
    (right : Bool),
    (installedWords k).card = 2 ^ (2 * k + 8) ∧
    2 * (k + (k + (5 + 3))) - 1 = 4 * k + 15 ∧
    (∀ s : Bool, ∀ u : Bank k, ∀ r : Flag,
      u.card + (T.delta u r).card + (if s then 7 else 5) ≤ 2 * k + 7) ∧
    (∀ w : Word k, ∀ r : Flag,
      (∀ i j, i.val + 1 = j.val → physical w i = false ∨ physical w j = false) ∧
      ((installed T w).next r = w ∨
        OneBit (physical w) (physical ((installed T w).next r)))) ∧
    ∃ last events, F.readout () ⟨k, T, obs, z, t, a, b, right, last⟩ events = true ∧
      (installed T (ready last t)).instruction = .halt bit ∧
      (∀ w c, Run (wordProgram T) obs (ready right z) a w c →
        wordProgram T w = .halt → w = ready last t ∧ c = b) ∧
      physicalInstruction T (physicalEquiv (ready last t)) = .halt bit ∧
      Run (physicalProgram T) obs (physicalEquiv (ready right z)) a
        (physicalEquiv (ready last t)) b ∧
      (∀ w c, Run (physicalProgram T) obs (physicalEquiv (ready right z)) a w c →
        physicalProgram T w = .halt → w = physicalEquiv (ready last t) ∧ c = b) ∧
      remaining T obs (ready right z) a = events.length ∧
      remaining T obs (ready last t) b = 0 ∧
      (∀ w c, Run (wordProgram T) obs (ready right z) a w c →
        ∃ suffix, Execution T obs w c (ready last t) b suffix ∧
          remaining T obs w c = suffix.length) ∧
      (∀ w v u : Word k, ∀ a' b' c' : Nat, ∀ e es bit',
        Execution T obs w a' v b' [e] → Execution T obs v b' u c' es →
        (installed T u).instruction = .halt bit' →
        remaining T obs w a' = remaining T obs v b' + 1) ∧ SourceRankInvariant T

private theorem positive : arena.Law actual := by
  classical
  intro k T obs z t a b bit path halt right
  simpa [actual, realize] using (installed_halt path halt right)

private theorem negative : ¬ arena.Law rejected := by
  intro h
  have bad := @h 0 haltTable obs ∅ ∅ 0 0 false (.refl _ _) rfl false
  obtain ⟨last, events, impossible, _⟩ := bad.2.2.2.2
  cases impossible

def evidence : Registration arena (type_of% (@installed_halt)) where
  actual := actual
  bridge := by
    classical
    simp [actual, realize]
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    exact Simulation.evidence.dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@installed_halt)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.installed_halt,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.Halt.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord,
    definition := none, coordinates := #[0, 1, 2, 3, 4, 5, 6, 10, 11],
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "arg", "arg",
        "arg", "arg", "body", "arg", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := true }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end Halt

end
end Reg.D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord
