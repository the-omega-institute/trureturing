/- GID: D5/S3/ConceptDynamics/InformationEscape/PhysicalParser/CellRegistrations
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/PhysicalParser/CellRegistrations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native parser registrations observe the specified physical output cells. -/

import D5.S0.Computability.Coding.PhysicalParserExecution
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import LeanInformationAudit.Syntax

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.PhysicalParser.CellRegistrations

open D5.S0.Computability.Coding PhysicalSixParser
open RegistrationTemplates LeanInformationAudit

/- The finite states are the Boolean cell values in each original statement.
Each native Law retains the complete source statement and observes its specified
output cells. At the identity readout the Law is definitionally the exact source
statement. Constant false contradicts a true cell and the retained frame.
The varying observation leaves control states and head coordinates unchanged.
The further residual beyond these cell observations remains open. -/

register_information_template cutRealization

/-- Observe the specified output memory, retaining control and head coordinates. -/
def observeCells (r : PrimitiveRealization (cutSignature Bool Bool))
    (c : Configuration) : Configuration :=
  { c with cell := fun t z => r.readout () (c.cell t z) }

/-- A competing observation which loses every true cell. -/
def erased : PrimitiveRealization (cutSignature Bool Bool) :=
  @cutRealization Bool Bool instDecidableEqBool (fun _ : Bool => false)

namespace Rewind

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ (m : Track → ℤ → Bool) (h : Track → ℤ) (W B k : ℕ)
    (hhome : m (7, false) 0 = false ∧ m (7, true) 0 = true)
    (hmarks : ∀ j : ℕ, 0 < j → j ≤ W → m (7, false) j = true ∧ m (7, true) j = true)
    (hk : k ≤ W) (hB : k ≤ B),
    run ⟨.sourceRewind 0, rewindHeads h k k k, m⟩ (5 * k + 2) =
        observeCells r ⟨.pad 0 0, rewindHeads h 0 0 0, m⟩ ∧
      ∀ n ≤ 5 * k + 2, RewindFrame m h B
        (run ⟨.sourceRewind 0, rewindHeads h k k k, m⟩ n)

def realization : PrimitiveRealization (cutSignature Bool Bool) :=
  @cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)

def unit : TheoremUnit arena.toArena where
  primitives := realization.toPrimitiveBundle
  Statement := arena.Law realization
  proof := coupled_source_rewind

def variation : FiniteLawVariation arena := by
  refine ⟨realization, erased, coupled_source_rewind, ?_⟩
  intro bad
  obtain ⟨result, frame⟩ := bad (fun t _ => t.2) (fun _ => 0) 0 0 0
    ⟨rfl, rfl⟩ (by intro j hj hj0; omega) (by omega) (by omega)
  obtain ⟨a, b, c, _, _, _, _, _, _, cells⟩ := frame 2 (by omega)
  have contradiction := congrFun (congrFun cells (0, true)) 0
  rw [result] at contradiction
  exact Bool.false_ne_true contradiction

def sensitivity : FiniteSlotSensitivity arena := by
  constructor
  · intro i
    obtain ⟨r, r', hr, hr'⟩ := variation
    refine ⟨r, r', ?_, ?_, ⟨fun _ => hr', fun _ => hr⟩⟩
    · intro j hj; cases i; cases j; exact (hj rfl).elim
    · intro j; exact Fin.elim0 j
  · intro i; exact Fin.elim0 i

run_cmd registrationTransaction do
  let (descriptor, diagnostic) ← elaborateReadoutDescriptor
    (← `(term| @cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)))
  let canonicalArena ← Lean.Elab.Command.liftTermElabM <| resolveCanonicalArenaName ``arena
  TemplateBinding.withDeclaration {
    theoremName := ``coupled_source_rewind
    arena := canonicalArena
    descriptor, diagnostic
    escapeInput := { fromObject := some (Lean.mkConst ``Bool), openContinuation := true } } do
    registerValidatedEntry {
      theoremName := ``coupled_source_rewind
      unitName := ``unit
      arenaName := ``arena
      realizationName := ``realization
      variationWitness := ``variation
      sensitivityWitness := ``sensitivity }

end Rewind

namespace Tally
open PhysicalParserTally

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ (m : Track → ℤ → Bool) (h : Track → ℤ) (u n : ℕ) (c : Continuation),
    ∃ T : ℕ, T ≤ 8 * n.bits.length + 14 ∧
      run (configuration m h u n.bits 0 (.count c 0)) T =
        observeCells r (configuration m h (u + 1) (n + 1).bits 0 (resume c)) ∧
      ∀ t ≤ T, Frame m h u n.bits.length
        (run (configuration m h u n.bits 0 (.count c 0)) t)

def realization : PrimitiveRealization (cutSignature Bool Bool) :=
  @cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)

def unit : TheoremUnit arena.toArena where
  primitives := realization.toPrimitiveBundle
  Statement := arena.Law realization
  proof := count_one

def variation : FiniteLawVariation arena := by
  refine ⟨realization, erased, count_one, ?_⟩
  intro bad
  obtain ⟨T, _, result, frame⟩ := bad (fun _ _ => true) (fun _ => 0) 0 0 .finish
  have cells := ((frame T (by omega)).1 (0, true) (by decide) (by decide)).2
  have contradiction := congrFun cells 0
  rw [result] at contradiction
  exact Bool.false_ne_true contradiction

def sensitivity : FiniteSlotSensitivity arena := by
  constructor
  · intro i
    obtain ⟨r, r', hr, hr'⟩ := variation
    refine ⟨r, r', ?_, ?_, ⟨fun _ => hr', fun _ => hr⟩⟩
    · intro j hj; cases i; cases j; exact (hj rfl).elim
    · intro j; exact Fin.elim0 j
  · intro i; exact Fin.elim0 i

run_cmd registrationTransaction do
  let (descriptor, diagnostic) ← elaborateReadoutDescriptor
    (← `(term| @cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)))
  let canonicalArena ← Lean.Elab.Command.liftTermElabM <| resolveCanonicalArenaName ``arena
  TemplateBinding.withDeclaration {
    theoremName := ``count_one
    arena := canonicalArena
    descriptor, diagnostic
    escapeInput := { fromObject := some (Lean.mkConst ``Bool), openContinuation := true } } do
    registerValidatedEntry {
      theoremName := ``count_one
      unitName := ``unit
      arenaName := ``arena
      realizationName := ``realization
      variationWitness := ``variation
      sensitivityWitness := ``sensitivity }

end Tally

namespace Padding
open PhysicalParserPadding

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ (m : Track → ℤ → Bool) (h : Track → ℤ) (i : Fin 6) (W : ℕ)
    (bs : List Bool) (hlen : bs.length ≤ W),
    ∃ T : ℕ, T ≤ 14 * W + 11 ∧
      run (configuration m h i W bs 0 (.pad i 0)) T =
        observeCells r
          (configuration m h i W (bs ++ List.replicate (W - bs.length) false) 0 (next i)) ∧
      ∀ t ≤ T, Frame m h i W (run (configuration m h i W bs 0 (.pad i 0)) t)

def realization : PrimitiveRealization (cutSignature Bool Bool) :=
  @cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)

def unit : TheoremUnit arena.toArena where
  primitives := realization.toPrimitiveBundle
  Statement := arena.Law realization
  proof := pad_one

def variation : FiniteLawVariation arena := by
  refine ⟨realization, erased, pad_one, ?_⟩
  intro bad
  obtain ⟨T, _, result, frame⟩ := bad (fun _ _ => true) (fun _ => 0) 0 0 [] (by simp)
  have cells := ((frame T (by omega)).1 (0, true) (by decide) (by decide)).2
  have contradiction := congrFun cells 0
  rw [result] at contradiction
  exact Bool.false_ne_true contradiction

def sensitivity : FiniteSlotSensitivity arena := by
  constructor
  · intro i
    obtain ⟨r, r', hr, hr'⟩ := variation
    refine ⟨r, r', ?_, ?_, ⟨fun _ => hr', fun _ => hr⟩⟩
    · intro j hj; cases i; cases j; exact (hj rfl).elim
    · intro j; exact Fin.elim0 j
  · intro i; exact Fin.elim0 i

run_cmd registrationTransaction do
  let (descriptor, diagnostic) ← elaborateReadoutDescriptor
    (← `(term| @cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)))
  let canonicalArena ← Lean.Elab.Command.liftTermElabM <| resolveCanonicalArenaName ``arena
  TemplateBinding.withDeclaration {
    theoremName := ``pad_one
    arena := canonicalArena
    descriptor, diagnostic
    escapeInput := { fromObject := some (Lean.mkConst ``Bool), openContinuation := true } } do
    registerValidatedEntry {
      theoremName := ``pad_one
      unitName := ``unit
      arenaName := ``arena
      realizationName := ``realization
      variationWitness := ``variation
      sensitivityWitness := ``sensitivity }

end Padding

namespace Field
open PhysicalParserField

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ (m : Track → ℤ → Bool) (h : Track → ℤ) (i : Fin 6)
    (n N : ℕ) (payload : List Bool) (hN : n + 2 * payload.length + 1 ≤ N)
    (hraw : ∀ k < 2 * payload.length + 1, m (0,false) (n + k + 1) =
      (List.replicate payload.length true ++ false :: payload)[k]?.getD false),
    ∃ T : ℕ, T ≤ (2 * payload.length + 1) * (8 * N + 20) + 2 ∧
      run (configuration m h i n [] 0 (.header i 0)) T =
        observeCells r
          (configuration m h i (n + 2 * payload.length + 1) payload.reverse 0 (next i)) ∧
      ∀ t ≤ T, Frame m h i N (run (configuration m h i n [] 0 (.header i 0)) t)

def realization : PrimitiveRealization (cutSignature Bool Bool) :=
  @cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)

def unit : TheoremUnit arena.toArena where
  primitives := realization.toPrimitiveBundle
  Statement := arena.Law realization
  proof := parse_field

def variation : FiniteLawVariation arena := by
  refine ⟨realization, erased, parse_field, ?_⟩
  intro bad
  obtain ⟨T, _, result, frame⟩ := bad (fun t _ => t.2) (fun _ => 0) 0 0 1 [] (by simp)
    (by
      intro k hk
      have hk0 : k = 0 := by simpa using hk
      subst k
      rfl)
  have cells := (frame T (by omega)).1 (0, true) (by decide) (by decide) (by decide)
  have contradiction := congrFun cells 0
  rw [result] at contradiction
  exact Bool.false_ne_true contradiction

def sensitivity : FiniteSlotSensitivity arena := by
  constructor
  · intro i
    obtain ⟨r, r', hr, hr'⟩ := variation
    refine ⟨r, r', ?_, ?_, ⟨fun _ => hr', fun _ => hr⟩⟩
    · intro j hj; cases i; cases j; exact (hj rfl).elim
    · intro j; exact Fin.elim0 j
  · intro i; exact Fin.elim0 i

run_cmd registrationTransaction do
  let (descriptor, diagnostic) ← elaborateReadoutDescriptor
    (← `(term| @cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)))
  let canonicalArena ← Lean.Elab.Command.liftTermElabM <| resolveCanonicalArenaName ``arena
  TemplateBinding.withDeclaration {
    theoremName := ``parse_field
    arena := canonicalArena
    descriptor, diagnostic
    escapeInput := { fromObject := some (Lean.mkConst ``Bool), openContinuation := true } } do
    registerValidatedEntry {
      theoremName := ``parse_field
      unitName := ``unit
      arenaName := ``arena
      realizationName := ``realization
      variationWitness := ``variation
      sensitivityWitness := ``sensitivity }

end Field

namespace Execution
open PhysicalParserExecution

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := Contract ∧ (∀ x y : ℤ, headDescription x <+: headDescription y → x = y) ∧
    (∀ q : List Bool, ∀ n : ℕ,
      (run (initial q) n).head (0,true) = 0 ∧
      (run (initial q) n).cell (0,false) = fun z => r.readout () (rawCell q z))

def realization : PrimitiveRealization (cutSignature Bool Bool) :=
  @cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)

def unit : TheoremUnit arena.toArena where
  primitives := realization.toPrimitiveBundle
  Statement := arena.Law realization
  proof := parser_frame_resources

def variation : FiniteLawVariation arena := by
  refine ⟨realization, erased, parser_frame_resources, ?_⟩
  intro bad
  have contradiction := congrFun (bad.2.2 [true] 0).2 1
  exact Bool.false_ne_true contradiction.symm

def sensitivity : FiniteSlotSensitivity arena := by
  constructor
  · intro i
    obtain ⟨r, r', hr, hr'⟩ := variation
    refine ⟨r, r', ?_, ?_, ⟨fun _ => hr', fun _ => hr⟩⟩
    · intro j hj; cases i; cases j; exact (hj rfl).elim
    · intro j; exact Fin.elim0 j
  · intro i; exact Fin.elim0 i

run_cmd registrationTransaction do
  let (descriptor, diagnostic) ← elaborateReadoutDescriptor
    (← `(term| @cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)))
  let canonicalArena ← Lean.Elab.Command.liftTermElabM <| resolveCanonicalArenaName ``arena
  TemplateBinding.withDeclaration {
    theoremName := ``parser_frame_resources
    arena := canonicalArena
    descriptor, diagnostic
    escapeInput := { fromObject := some (Lean.mkConst ``Bool), openContinuation := true } } do
    registerValidatedEntry {
      theoremName := ``parser_frame_resources
      unitName := ``unit
      arenaName := ``arena
      realizationName := ``realization
      variationWitness := ``variation
      sensitivityWitness := ``sensitivity }

end Execution

end D5.S3.ConceptDynamics.InformationEscape.PhysicalParser.CellRegistrations
