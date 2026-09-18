/- GID: D5/S0/Computability/PhysicalDivider/Parking
   generality: G
   mirror-B: D5/B/S0/Computability/PhysicalDivider/Parking
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every-prefix support and visited-extent control for the physical parking loop. -/

import D5.S0.Computability.PhysicalDivider.BlockExecution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S0.Computability.PhysicalDivider
open Turing

/-- The actual parking loop takes three actions per data block and one final read.
Every prefix preserves the charged interval and keeps the head between its initial
position and the fixed origin; support cannot escape that interval. -/
theorem park_preserves_extent (k : ActiveTape) (next : Continuation)
    (tapes : ActiveTape → Tape Bool) (below above : List Bool) (H : ℤ)
    (hH : 2 * (below.length : ℤ) ≤ H)
    (hwithin : Within (stackWithAbove below above) ⟨2 * (below.length : ℤ), 0, H⟩) :
    let step := fun o : Option (BlockCfg × Extent) => o.bind accountedBlockStep
    let initial : BlockCfg × Extent :=
      (⟨.parkMarker, stackWithAbove below above⟩, ⟨2 * (below.length : ℤ), 0, H⟩)
    (step^[3 * below.length + 1]) (some initial) =
      some (⟨.finished none,
        Tape.mk₂ [] ([false, true] ++
          below.reverse.flatMap (fun b => [true, b]) ++ above)⟩, ⟨0, 0, H⟩) ∧
    ((fun o : Option PhysicalCfg => o.bind physicalStep)^[3 * below.length + 2])
        (some (liftBlockCfg k next tapes initial.1)) =
      some ⟨continueBlock next none,
        Function.update tapes k (Tape.mk₂ [] ([false, true] ++
          below.reverse.flatMap (fun b => [true, b]) ++ above))⟩ ∧
    ∀ n ≤ 3 * below.length + 1, ∃ c,
      (step^[n]) (some initial) = some c ∧
      ((fun o : Option PhysicalCfg => o.bind physicalStep)^[n])
        (some (liftBlockCfg k next tapes initial.1)) =
        some (liftBlockCfg k next tapes c.1) ∧
      c.2.low = 0 ∧ c.2.high = H ∧
      0 ≤ c.2.head ∧ c.2.head ≤ 2 * (below.length : ℤ) ∧ Within c.1.tape c.2 := by
  have bounded (below above : List Bool) (H : ℤ)
      (hH : 2 * (below.length : ℤ) ≤ H) :
      let step := fun o : Option (BlockCfg × Extent) => o.bind accountedBlockStep
      let initial : BlockCfg × Extent :=
        (⟨.parkMarker, stackWithAbove below above⟩, ⟨2 * (below.length : ℤ), 0, H⟩)
      (step^[3 * below.length + 1]) (some initial) =
        some (⟨.finished none,
          Tape.mk₂ [] ([false, true] ++
            below.reverse.flatMap (fun b => [true, b]) ++ above)⟩, ⟨0, 0, H⟩) ∧
      ∀ n ≤ 3 * below.length + 1, ∃ c,
        (step^[n]) (some initial) = some c ∧
        c.2.low = 0 ∧ c.2.high = H ∧
        0 ≤ c.2.head ∧ c.2.head ≤ 2 * (below.length : ℤ) := by
    dsimp only
    let step := fun o : Option (BlockCfg × Extent) => o.bind accountedBlockStep
    induction below generalizing above with
    | nil =>
        simp only [List.length_nil, Nat.cast_zero, mul_zero] at hH
        constructor
        · simp [step, accountedBlockStep, blockStep, blockAction, stackWithAbove,
            Tape.mk₂, Tape.mk', accountAction, min_eq_left, max_eq_left, hH]
        · intro n hn
          have hn' : n = 0 ∨ n = 1 := by simp only [List.length_nil] at hn; omega
          rcases hn' with rfl | rfl <;>
            simp [step, accountedBlockStep, blockStep, blockAction, stackWithAbove,
              Tape.mk₂, Tape.mk', accountAction, min_eq_left, max_eq_left, hH]
    | cons b bs ih =>
        have hbs : 0 ≤ (bs.length : ℤ) := by omega
        have hH' : 2 * (bs.length : ℤ) ≤ H := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hH; omega
        let c₀ : BlockCfg × Extent :=
          (⟨.parkMarker, stackWithAbove (b :: bs) above⟩, ⟨2 * ((b :: bs).length : ℤ), 0, H⟩)
        let c₃ : BlockCfg × Extent :=
          (⟨.parkMarker, stackWithAbove bs ([true, b] ++ above)⟩, ⟨2 * (bs.length : ℤ), 0, H⟩)
        have hthree : (step^[3]) (some c₀) = some c₃ := by
          cases bs <;>
            simp only [List.length_cons, List.length_nil, Nat.cast_add, Nat.cast_one, Nat.cast_zero] at hH hH' <;>
            simp [step, c₀, c₃, stackWithAbove, accountedBlockStep, blockStep, blockAction,
              Tape.mk₂, Tape.mk', Tape.move, cellsBelow, accountAction,
              Function.iterate_succ_apply, min_eq_left, max_eq_left] <;> omega
        obtain ⟨hend, hprefix⟩ := ih ([true,b] ++ above) hH'
        constructor
        · rw [show 3 * (b :: bs).length + 1 = (3 * bs.length + 1) + 3 by simp; omega,
            Function.iterate_add_apply]
          change (step^[3 * bs.length + 1]) ((step^[3]) (some c₀)) = _
          rw [hthree]
          dsimp only [c₃, step]
          rw [hend]
          simp [List.reverse_cons, List.flatMap_append, List.append_assoc]
        · intro n hn
          by_cases hn3 : n < 3
          · have hn' : n = 0 ∨ n = 1 ∨ n = 2 := by omega
            rcases hn' with rfl | rfl | rfl <;>
              cases bs <;>
              simp only [List.length_cons, List.length_nil, Nat.cast_add, Nat.cast_one, Nat.cast_zero] at hH hH' <;>
              simp [step, c₀, stackWithAbove, accountedBlockStep, blockStep, blockAction,
                Tape.mk₂, Tape.mk', Tape.move, cellsBelow, accountAction,
                Function.iterate_succ_apply, min_eq_left, max_eq_left] <;> omega
          · have hn' : n - 3 ≤ 3 * bs.length + 1 := by simp only [List.length_cons] at hn; omega
            obtain ⟨c, hc, hl, hh, hzero, hhead⟩ := hprefix (n - 3) hn'
            refine ⟨c, ?_, hl, hh, hzero, ?_⟩
            · rw [show n = (n - 3) + 3 by omega, Function.iterate_add_apply]
              change (step^[n - 3]) ((step^[3]) (some c₀)) = _
              rw [hthree]
              exact hc
            · simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
              omega
  have preserve (c c' : BlockCfg × Extent) (hs : accountedBlockStep c = some c')
      (hc : Within c.1.tape c.2) : Within c'.1.tape c'.2 := by
    rcases hc with ⟨hl, hh, ht⟩
    cases ha : blockAction c.1.control with
    | none => simp [accountedBlockStep, ha] at hs
    | some action =>
      cases action with
      | read next =>
        simp [accountedBlockStep, blockStep, ha] at hs
        subst c'
        dsimp [Within, accountAction]
        refine ⟨by omega, by omega, ?_⟩
        intro i hi
        have := ht i hi
        constructor <;> omega
      | write bit next =>
        simp [accountedBlockStep, blockStep, ha] at hs
        subst c'
        dsimp [Within, accountAction]
        refine ⟨by omega, by omega, ?_⟩
        intro i hi
        by_cases hz : i = 0
        · subst i; constructor <;> omega
        · rw [Tape.write_nth, if_neg hz] at hi
          have := ht i hi
          constructor <;> omega
      | move dir next =>
        simp [accountedBlockStep, blockStep, ha] at hs
        subst c'
        cases dir <;>
          dsimp [Within, accountAction] <;>
          refine ⟨by omega, by omega, ?_⟩
        · intro i hi
          rw [Tape.move_left_nth] at hi
          have := ht (i - 1) hi
          constructor <;> omega
        · intro i hi
          rw [Tape.move_right_nth] at hi
          have := ht (i + 1) hi
          constructor <;> omega
  let step := fun o : Option (BlockCfg × Extent) => o.bind accountedBlockStep
  let initial : BlockCfg × Extent :=
    (⟨.parkMarker, stackWithAbove below above⟩, ⟨2 * (below.length : ℤ), 0, H⟩)
  have allWithin : ∀ n c, (step^[n]) (some initial) = some c → Within c.1.tape c.2 := by
    intro n
    induction n with
    | zero =>
        intro c hc
        simp only [Function.iterate_zero, id_eq, Option.some.injEq] at hc
        subst c
        exact hwithin
    | succ n ih =>
        intro c hc
        rw [Function.iterate_succ_apply'] at hc
        cases he : (step^[n]) (some initial) with
        | none => simp [he, step] at hc
        | some previous =>
            rw [he] at hc
            exact preserve previous c hc (ih previous he)
  have project : ∀ n c, (step^[n]) (some initial) = some c →
      ((fun o : Option BlockCfg => o.bind blockStep)^[n]) (some initial.1) = some c.1 := by
    intro n
    induction n with
    | zero =>
        intro c hc
        simp only [Function.iterate_zero, id_eq, Option.some.injEq] at hc
        subst c
        rfl
    | succ n ih =>
        intro c hc
        rw [Function.iterate_succ_apply'] at hc ⊢
        cases he : (step^[n]) (some initial) with
        | none => simp [he, step] at hc
        | some previous =>
            rw [he] at hc
            rw [ih previous he]
            change accountedBlockStep previous = some c at hc
            unfold accountedBlockStep at hc
            cases ha : blockAction previous.1.control with
            | none => simp [ha] at hc
            | some action =>
                rw [ha] at hc
                cases hb : blockStep previous.1 with
                | none => simp [hb] at hc
                | some result =>
                    simp [hb] at hc
                    subst c
                    exact hb
  obtain ⟨hend, hp⟩ := bounded below above H hH
  refine ⟨hend, ?_, ?_⟩
  · have hr := block_lift_run k next tapes (3 * below.length + 1) _ _
      (project (3 * below.length + 1) _ hend)
    rw [show 3 * below.length + 2 = (3 * below.length + 1) + 1 by omega,
      Function.iterate_succ_apply', hr]
    simp [physicalStep, liftBlockCfg, instruction, controlRead, executeInstruction]
  · intro n hn
    obtain ⟨c, hc, hl, hh, hz, hb⟩ := hp n hn
    exact ⟨c, hc, block_lift_run k next tapes n _ _ (project n c hc),
      hl, hh, hz, hb, allWithin n c hc⟩

end D5.S0.Computability.PhysicalDivider
