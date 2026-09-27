/- GID: D5/S0/Computability/PhysicalDivider/OperandProduction
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Separately counted sequential writes replace same-capacity operand buffers. -/

import D5.S0.Computability.PhysicalDivider.Framing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S0.Computability.PhysicalDivider
open Turing Lax51Proofs.RamToTM

/-- Actions of the surrounding operand producer, separately counted from division. -/
inductive BufferAction
  | write (bit : Bool)
  | move (direction : Dir)

def bufferStep (t : Tape Bool) : BufferAction → Tape Bool
  | .write b => t.write b
  | .move dir => t.move dir

/-- Observer only: the tape operation does not inspect these coordinates. -/
def observeBuffer (c : Tape Bool × Extent) (action : BufferAction) : Tape Bool × Extent :=
  let head := match action with
    | .write _ => c.2.head
    | .move .left => c.2.head - 1
    | .move .right => c.2.head + 1
  (bufferStep c.1 action, ⟨head, min c.2.low head, max c.2.high head⟩)

/-- Write one cell, advance one cell, write the suffix, then return one cell.
This is an explicit trace of elementary actions, not an atomic tape replacement. -/
def overwriteActions : List Bool → List BufferAction
  | [] => []
  | b :: bs => .write b :: .move .right :: (overwriteActions bs ++ [.move .left])

/-- A same-size replacement returns the physical head and all charged extents
unchanged. Every intermediate head stays within the already allocated buffer. -/
theorem overwrite_execution (bits old left right : List Bool)
    (hlen : old.length = bits.length) (e : Extent)
    (hl : e.low ≤ e.head) (hh : e.head + bits.length ≤ e.high) :
    (overwriteActions bits).length = 3 * bits.length ∧
    (overwriteActions bits).foldl observeBuffer (Tape.mk₂ left (old ++ right), e) =
      (Tape.mk₂ left (bits ++ right), e) ∧
    (∀ i ≤ (overwriteActions bits).length,
      let c := ((overwriteActions bits).take i).foldl observeBuffer
        (Tape.mk₂ left (old ++ right), e)
      c.2.low = e.low ∧ c.2.high = e.high ∧
      e.head ≤ c.2.head ∧ c.2.head ≤ e.head + bits.length) ∧
    (∀ i, (((overwriteActions bits).take i).foldl observeBuffer
      (Tape.mk₂ left (old ++ right), e)).1 =
      ((overwriteActions bits).take i).foldl bufferStep (Tape.mk₂ left (old ++ right))) := by
  have projection (actions : List BufferAction) (t : Tape Bool) (f : Extent) :
      (actions.foldl observeBuffer (t, f)).1 = actions.foldl bufferStep t := by
    exact (List.foldl_hom Prod.fst (g₁ := observeBuffer) (g₂ := bufferStep)
      (l := actions) (init := (t, f)) (by intro c action; rfl)).symm
  have main : ∀ (bits old left right : List Bool), old.length = bits.length →
      ∀ e : Extent, e.low ≤ e.head → e.head + bits.length ≤ e.high →
      (overwriteActions bits).length = 3 * bits.length ∧
      (overwriteActions bits).foldl observeBuffer (Tape.mk₂ left (old ++ right), e) =
        (Tape.mk₂ left (bits ++ right), e) ∧
      ∀ i ≤ (overwriteActions bits).length,
        let c := ((overwriteActions bits).take i).foldl observeBuffer
          (Tape.mk₂ left (old ++ right), e)
        c.2.low = e.low ∧ c.2.high = e.high ∧
        e.head ≤ c.2.head ∧ c.2.head ≤ e.head + bits.length := by
    intro bits
    induction bits with
    | nil =>
      intro old left right hlen e hl hh
      have ho : old = [] := List.eq_nil_of_length_eq_zero hlen
      subst old
      refine ⟨rfl, rfl, ?_⟩
      intro i hi
      have : i = 0 := by simpa [overwriteActions] using hi
      subst i
      exact ⟨rfl, rfl, le_rfl, by simp⟩
    | cons b bits ih =>
      intro old left right hlen e hl hh
      cases old with
      | nil => simp at hlen
      | cons o old =>
        have ho : old.length = bits.length := by simpa using hlen
        let e' : Extent := ⟨e.head + 1, e.low, e.high⟩
        have hl' : e'.low ≤ e'.head := by dsimp [e']; omega
        have hh' : e'.head + bits.length ≤ e'.high := by
          dsimp [e']; simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hh
          omega
        obtain ⟨hiLen, hiRun, hiBounds⟩ := ih old (b :: left) right ho e' hl' hh'
        have first : observeBuffer
            (observeBuffer (Tape.mk₂ left ((o :: old) ++ right), e) (.write b))
            (.move .right) = (Tape.mk₂ (b :: left) (old ++ right), e') := by
          simp [observeBuffer, bufferStep, Tape.mk₂, Tape.mk', Tape.write, Tape.move,
            min_eq_left hl, max_eq_left (show e.head ≤ e.high by omega), e',
            min_eq_left (show e.low ≤ e.head + 1 by omega),
            max_eq_left (show e.head + 1 ≤ e.high by
              simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hh; omega)]
        have last : observeBuffer (Tape.mk₂ (b :: left) (bits ++ right), e') (.move .left) =
            (Tape.mk₂ left ((b :: bits) ++ right), e) := by
          simp [observeBuffer, bufferStep, Tape.mk₂, Tape.mk', Tape.move, e',
            min_eq_left hl, max_eq_left (show e.head ≤ e.high by omega)]
          change (ListBlank.mk (bits ++ right)).tail.cons
            (ListBlank.mk (bits ++ right)).head = ListBlank.mk (bits ++ right)
          exact ListBlank.cons_head_tail _
        have full : (overwriteActions (b :: bits)).foldl observeBuffer
            (Tape.mk₂ left ((o :: old) ++ right), e) =
            (Tape.mk₂ left ((b :: bits) ++ right), e) := by
          simp only [overwriteActions, List.foldl_cons, List.foldl_append, List.foldl_nil]
          rw [first, hiRun, last]
        refine ⟨by simp [overwriteActions, hiLen]; omega, full, ?_⟩
        intro i hi
        by_cases hiz : i = 0
        · subst i
          simp <;> omega
        by_cases hio : i = 1
        · subst i
          simp only [overwriteActions, List.take_succ_cons, List.take_zero,
            List.foldl_cons, List.foldl_nil]
          simp [observeBuffer, min_eq_left hl,
            max_eq_left (show e.head ≤ e.high by omega)]
          omega
        by_cases him : i ≤ 2 + (overwriteActions bits).length
        · have heq : i = (i-2)+2 := by omega
          have hj : i-2 ≤ (overwriteActions bits).length := by omega
          have h := hiBounds (i-2) hj
          rw [heq]
          simp only [overwriteActions, show i - 2 + 2 = (i - 2 + 1) + 1 by omega,
            List.take_succ_cons, List.foldl_cons]
          rw [List.take_append_of_le_length hj, first]
          dsimp [e'] at h ⊢
          refine ⟨h.1, h.2.1, ?_, ?_⟩
          · omega
          · omega
        · have heq : i = (overwriteActions (b :: bits)).length := by
            simp only [overwriteActions, List.length_cons, List.length_append,
              List.length_nil] at hi ⊢
            omega
          rw [heq, List.take_length, full]
          refine ⟨rfl, rfl, le_rfl, ?_⟩
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          omega
  obtain ⟨hsize, hrun, hbound⟩ := main bits old left right hlen e hl hh
  exact ⟨hsize, hrun, hbound, fun i => projection _ _ _⟩

def operandTape (divisor : Bool) : ActiveTape :=
  .inr (if divisor then .operandD else .operandA)

/-- The producer uses the existing primitive executor and leaves its control unchanged. -/
def producerStep (divisor : Bool) (c : FramedCfg) (action : BufferAction) : FramedCfg :=
  framedExecute c (match action with
    | .write b => .write (operandTape divisor) b c.active.control
    | .move dir => .move (operandTape divisor) dir c.active.control)

/-- The producer's charge observer follows exactly those physical actions. -/
def observeProducer (divisor : Bool) (c : FramedCfg × (ActiveTape → Extent))
    (action : BufferAction) : FramedCfg × (ActiveTape → Extent) :=
  (producerStep divisor c.1 action,
    Function.update c.2 (operandTape divisor)
      (observeBuffer (c.1.active.tapes (operandTape divisor), c.2 (operandTape divisor)) action).2)

def operandCells (bits : List Bool) : List Bool :=
  [false, true] ++ bits.reverse.flatMap (fun b => [true, b])

/-- A description of the endpoint, never an instruction of the divider or producer. -/
def replacedOperand (divisor : Bool) (c : FramedCfg) (bits : List Bool) : FramedCfg :=
  ⟨⟨c.active.control, Function.update c.active.tapes (operandTape divisor)
    (stackAtOrigin bits)⟩, c.caller⟩

/-- Supplying an operand is a paid sequence of writes and unit moves. Its cost
is separate from the division call. It preserves all other tapes, every retained
interval, and the parked boundary; even temporary head excursions stay allocated. -/
theorem produce_operand_buffer (divisor : Bool) (c : FramedCfg)
    (charged : ActiveTape → Extent) (old bits : List Bool)
    (htape : c.active.tapes (operandTape divisor) = stackAtOrigin old)
    (hlen : old.length = bits.length)
    (hh : (charged (operandTape divisor)).head = 0)
    (hl : (charged (operandTape divisor)).low ≤ 0)
    (hu : 2 * bits.length + 2 ≤ (charged (operandTape divisor)).high) :
    let actions := overwriteActions (operandCells bits)
    actions.length = 6 * bits.length + 6 ∧
    actions.foldl (observeProducer divisor) (c, charged) =
      (replacedOperand divisor c bits, charged) ∧
    actions.foldl (producerStep divisor) c = replacedOperand divisor c bits ∧
    (∀ i ≤ actions.length,
      let s := (actions.take i).foldl (observeProducer divisor) (c, charged)
      s.1 = (actions.take i).foldl (producerStep divisor) c ∧
      s.1.caller = c.caller ∧ s.1.active.control = c.active.control ∧
      (∀ k, (s.2 k).low = (charged k).low ∧ (s.2 k).high = (charged k).high) ∧
      (∀ k, k ≠ operandTape divisor → s.1.active.tapes k = c.active.tapes k ∧
        s.2 k = charged k) ∧
      0 ≤ (s.2 (operandTape divisor)).head ∧
      (s.2 (operandTape divisor)).head ≤ 2 * bits.length + 2) ∧
    (∀ i, (∀ k, Within (c.active.tapes k) (charged k)) →
      let s := (actions.take i).foldl (observeProducer divisor) (c, charged)
      ∀ k, Within (s.1.active.tapes k) (s.2 k)) := by
  let k := operandTape divisor
  let embed (s : Tape Bool × Extent) : FramedCfg × (ActiveTape → Extent) :=
    (⟨⟨c.active.control, Function.update c.active.tapes k s.1⟩, c.caller⟩,
      Function.update charged k s.2)
  have commute (s : Tape Bool × Extent) (a : BufferAction) :
      observeProducer divisor (embed s) a = embed (observeBuffer s a) := by
    cases a <;>
      simp [observeProducer, producerStep, framedExecute, executeInstruction, embed,
        k, bufferStep, observeBuffer, Function.update_idem]
  have start : embed (Tape.mk₂ [] (operandCells old ++ []), charged k) = (c, charged) := by
    simp only [List.append_nil]
    change (FramedCfg.mk
      ⟨c.active.control, Function.update c.active.tapes k (stackAtOrigin old)⟩ c.caller,
        Function.update charged k (charged k)) = _
    rw [← htape, Function.update_eq_self, Function.update_eq_self]
  have transfer (actions : List BufferAction) :
      actions.foldl (observeProducer divisor) (c, charged) =
        embed (actions.foldl observeBuffer (Tape.mk₂ [] (operandCells old ++ []), charged k)) := by
    rw [← start]
    exact List.foldl_hom embed commute
  have project (actions : List BufferAction) :
      (actions.foldl (observeProducer divisor) (c, charged)).1 =
        actions.foldl (producerStep divisor) c := by
    exact (List.foldl_hom Prod.fst (g₁ := observeProducer divisor)
      (g₂ := producerStep divisor) (l := actions) (init := (c, charged))
      (by intro s a; rfl)).symm
  have cellLen (bs : List Bool) : (operandCells bs).length = 2 * bs.length + 2 := by
    simp [operandCells, List.length_flatMap]; omega
  obtain ⟨hsize, hrun, hbound, _⟩ := overwrite_execution (operandCells bits)
    (operandCells old) [] [] (by rw [cellLen, cellLen, hlen]) (charged k)
    (by simpa only [k, hh] using hl)
    (by simpa only [cellLen, k, hh, Int.zero_add, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat] using hu)
  have finish : (overwriteActions (operandCells bits)).foldl (observeProducer divisor)
      (c, charged) = (replacedOperand divisor c bits, charged) := by
    rw [transfer, hrun]
    dsimp only [embed]
    rw [Function.update_eq_self]
    simp only [List.append_nil]
    rfl
  refine ⟨by rw [hsize, cellLen]; omega, finish, ?_, ?_, ?_⟩
  · have h := project (overwriteActions (operandCells bits))
    rw [finish] at h
    exact h.symm
  · intro i hi
    have hb := hbound i hi
    dsimp only at hb
    rw [cellLen] at hb
    rw [hh] at hb
    dsimp only
    refine ⟨project _, ?_⟩
    rw [transfer]
    dsimp only [embed]
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro j
      by_cases hj : j = k
      · subst j; simpa only [Function.update_self] using ⟨hb.1, hb.2.1⟩
      · simp [Function.update_of_ne hj]
    · intro j hj
      simp only [k] at hj ⊢
      rw [Function.update_of_ne hj, Function.update_of_ne hj]
      exact ⟨rfl, rfl⟩
    · simpa only [k, Function.update_self] using hb.2.2.1
    · simpa only [k, Function.update_self, Int.zero_add, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat] using hb.2.2.2
  · have scalar (s : Tape Bool × Extent) (a : BufferAction) (h : Within s.1 s.2) :
        Within (observeBuffer s a).1 (observeBuffer s a).2 := by
      rcases h with ⟨hl, hh, hs⟩
      cases a with
      | write b =>
        dsimp only [observeBuffer, bufferStep, Within]
        refine ⟨by omega, by omega, ?_⟩
        intro p hp
        by_cases hz : p = 0
        · subst p; constructor <;> omega
        · rw [Tape.write_nth, if_neg hz] at hp
          have := hs p hp
          constructor <;> omega
      | move dir =>
        cases dir <;> dsimp only [observeBuffer, bufferStep, Within]
        all_goals
          refine ⟨by omega, by omega, ?_⟩
          intro p hp
          first
          | rw [Tape.move_left_nth] at hp
            have := hs (p-1) hp
            constructor <;> omega
          | rw [Tape.move_right_nth] at hp
            have := hs (p+1) hp
            constructor <;> omega
    have one (s : FramedCfg × (ActiveTape → Extent)) (a : BufferAction)
        (h : ∀ j, Within (s.1.active.tapes j) (s.2 j)) :
        ∀ j, Within ((observeProducer divisor s a).1.active.tapes j)
          ((observeProducer divisor s a).2 j) := by
      intro j
      have hb := scalar (s.1.active.tapes k, s.2 k) a (h k)
      by_cases hj : j = k
      · subst j
        cases a <;>
          simpa [observeProducer, producerStep, framedExecute, executeInstruction,
            k, observeBuffer, bufferStep] using hb
      · cases a <;>
          simpa [observeProducer, producerStep, framedExecute, executeInstruction,
            show j ≠ operandTape divisor from hj] using h j
    have all (actions : List BufferAction) (s : FramedCfg × (ActiveTape → Extent))
        (h : ∀ j, Within (s.1.active.tapes j) (s.2 j)) :
        ∀ j, Within ((actions.foldl (observeProducer divisor) s).1.active.tapes j)
          ((actions.foldl (observeProducer divisor) s).2 j) := by
      induction actions generalizing s with
      | nil => exact h
      | cons a actions ih => exact ih _ (one s a h)
    intro i h
    exact all _ _ h

end D5.S0.Computability.PhysicalDivider
