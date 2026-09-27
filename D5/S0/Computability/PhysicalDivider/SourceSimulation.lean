/- GID: D5/S0/Computability/PhysicalDivider/SourceSimulation
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Structural execution of the fixed divider statements on sequential bit tapes. -/

import D5.S0.Computability.PhysicalDivider.CallProgram

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S0.Computability.PhysicalDivider
open Turing Lax51Proofs.RamToTM

/-- The frame tapes are arbitrary and stay physically unchanged during source execution. -/
def logicalTapes (words : DivStack → List Bool) (frame : FrameTape → Tape Bool) :
    ActiveTape → Tape Bool
  | .inl k => stackAtTop (words k)
  | .inr k => frame k

/-- The source halt boundary starts the executed copy-out phase. -/
def sourceCfg (c : divMachine.Cfg) (frame : FrameTape → Tape Bool) : PhysicalCfg :=
  ⟨match c.l with
    | some label => .sourceLabel label c.var
    | none => .frame .copyQ none,
   logicalTapes c.stk frame⟩

/-- Ghost head coordinates accompany an execution but are never machine inputs. -/
abbrev LocatedCfg := PhysicalCfg × (ActiveTape → ℤ)

def advanceHeads (heads : ActiveTape → ℤ) : Instruction → ActiveTape → ℤ
  | .move k .left _ => Function.update heads k (heads k - 1)
  | .move k .right _ => Function.update heads k (heads k + 1)
  | _ => heads

def locatedStep (c : LocatedCfg) : Option LocatedCfg :=
  (instruction c.1.control).map (fun action =>
    (executeInstruction c.1.tapes action, advanceHeads c.2 action))

def logicalHeads (words : DivStack → List Bool) (frameHeads : FrameTape → ℤ) :
    ActiveTape → ℤ
  | .inl k => 2 * (words k).length
  | .inr k => frameHeads k

def locatedStmtCfg (node : SourceNode) (state : DivControl)
    (words : DivStack → List Bool) (frame : FrameTape → Tape Bool)
    (frameHeads : FrameTape → ℤ) : LocatedCfg :=
  (⟨.sourceStmt node state, logicalTapes words frame⟩, logicalHeads words frameHeads)

def locatedSourceCfg (c : divMachine.Cfg) (frame : FrameTape → Tape Bool)
    (frameHeads : FrameTape → ℤ) : LocatedCfg :=
  (sourceCfg c frame, logicalHeads c.stk frameHeads)

/-- A code-only bound, independent of every operand and width. -/
def statementBudget : TM2.Stmt (fun _ : DivStack => Bool) DivLabel DivControl → ℕ
  | .push _ _ q => 7 + statementBudget q
  | .pop _ _ q => 9 + statementBudget q
  | .peek _ _ q => 5 + statementBudget q
  | .load _ q => 1 + statementBudget q
  | .branch _ a b => 1 + max (statementBudget a) (statementBudget b)
  | .goto _ | .halt => 1

/-- Each actual source substatement executes to its exact stack semantics, with a
uniform code-only bound and with the arbitrary caller frame unchanged. -/
theorem source_statement_execution (node : SourceNode) (state : DivControl)
    (words : DivStack → List Bool) (frame : FrameTape → Tape Bool) (frameHeads : FrameTape → ℤ) :
    ∃ n ≤ statementBudget node.val,
      ((fun o : Option LocatedCfg => o.bind locatedStep)^[n])
        (some (locatedStmtCfg node state words frame frameHeads)) =
      some (locatedSourceCfg (TM2.stepAux node.val state words) frame frameHeads) := by
  classical
  let run := fun o : Option LocatedCfg => o.bind locatedStep
  have push (parent : SourceNode) (k : DivStack) (f : DivControl → Bool)
      (q : TM2.Stmt (fun _ : DivStack => Bool) DivLabel DivControl)
      (hp : parent.val = .push k f q) (state : DivControl)
      (words : DivStack → List Bool) :
      (run^[7]) (some (locatedStmtCfg parent state words frame frameHeads)) =
        some (locatedStmtCfg (sourceChild parent q (by
          rw [hp]; exact Finset.mem_insert_of_mem TM2.stmts₁_self)) state
          (Function.update words k (f state :: words k)) frame frameHeads) := by
    rcases parent with ⟨p, hmem⟩
    dsimp only at hp
    subst p
    try dsimp only
    cases hs : words k <;>
      simp [run, locatedStmtCfg, locatedStep, advanceHeads, logicalHeads, Function.iterate_succ_apply, physicalStep, instruction, sourceInstruction,
        startBlock, liftBlockAction, blockAction, executeInstruction, logicalTapes,
        continueBlock, controlRead, stackAtTop, hs, cellsBelow, Tape.mk₂, Tape.mk', Tape.move,
        Tape.write, Function.update_idem] <;>
      (try constructor) <;> funext j <;> cases j with
      | inl l =>
        by_cases hl : l = k
        · subst l; simp [logicalHeads, logicalTapes, stackAtTop, hs, Tape.mk₂, Tape.mk', cellsBelow] <;> omega
        · simp [logicalHeads, logicalTapes, Function.update, hl]
      | inr l => simp [logicalHeads, logicalTapes]
  have pop (parent : SourceNode) (k : DivStack) (f : DivControl → Option Bool → DivControl)
      (q : TM2.Stmt (fun _ : DivStack => Bool) DivLabel DivControl)
      (hp : parent.val = .pop k f q) (state : DivControl)
      (words : DivStack → List Bool) :
      ∃ n ≤ 9, (run^[n]) (some (locatedStmtCfg parent state words frame frameHeads)) =
        some (locatedStmtCfg (sourceChild parent q (by
          rw [hp]; exact Finset.mem_insert_of_mem TM2.stmts₁_self)) (f state (words k).head?)
          (Function.update words k (words k).tail) frame frameHeads) := by
    rcases parent with ⟨p, hmem⟩
    dsimp only at hp
    subst p
    try dsimp only
    cases hs : words k with
    | nil =>
      refine ⟨2, by omega, ?_⟩
      simp [run, locatedStmtCfg, locatedStep, advanceHeads, logicalHeads, Function.iterate_succ_apply, physicalStep, instruction, sourceInstruction,
        startBlock, liftBlockAction, blockAction, executeInstruction, logicalTapes,
        continueBlock, controlRead, stackAtTop, hs, cellsBelow, Tape.mk₂, Tape.mk', Tape.move,
        Tape.write, Function.update_idem]
      (try constructor) <;> funext j <;> cases j with
      | inl l => by_cases hl : l = k <;> simp [logicalHeads, logicalTapes, Function.update, hl, hs]
      | inr l => rfl
    | cons b bs =>
      refine ⟨9, le_rfl, ?_⟩
      cases bs <;>
        simp [run, locatedStmtCfg, locatedStep, advanceHeads, logicalHeads, Function.iterate_succ_apply, physicalStep, instruction, sourceInstruction,
          startBlock, liftBlockAction, blockAction, executeInstruction, logicalTapes,
          continueBlock, controlRead, stackAtTop, hs, cellsBelow, Tape.mk₂, Tape.mk', Tape.move,
          Tape.write, Function.update_idem] <;>
        (try constructor) <;> funext j <;> cases j with
        | inl l =>
          by_cases hl : l = k
          · subst l
            simp [logicalHeads, logicalTapes, stackAtTop, hs, Tape.mk₂, Tape.mk', cellsBelow] <;>
              first | omega | (apply Quotient.sound; exact Or.inr ⟨2, rfl⟩)
          · simp [logicalHeads, logicalTapes, Function.update, hl]
        | inr l => simp [logicalHeads, logicalTapes]
  have peek (parent : SourceNode) (k : DivStack) (f : DivControl → Option Bool → DivControl)
      (q : TM2.Stmt (fun _ : DivStack => Bool) DivLabel DivControl)
      (hp : parent.val = .peek k f q) (state : DivControl)
      (words : DivStack → List Bool) :
      ∃ n ≤ 5, (run^[n]) (some (locatedStmtCfg parent state words frame frameHeads)) =
        some (locatedStmtCfg (sourceChild parent q (by
          rw [hp]; exact Finset.mem_insert_of_mem TM2.stmts₁_self)) (f state (words k).head?)
          words frame frameHeads) := by
    rcases parent with ⟨p, hmem⟩
    dsimp only at hp
    subst p
    try dsimp only
    cases hs : words k with
    | nil =>
      refine ⟨2, by omega, ?_⟩
      simp [run, locatedStmtCfg, locatedStep, advanceHeads, logicalHeads, Function.iterate_succ_apply, physicalStep, instruction, sourceInstruction,
        startBlock, liftBlockAction, blockAction, executeInstruction, logicalTapes,
        continueBlock, controlRead, stackAtTop, hs, cellsBelow, Tape.mk₂, Tape.mk', Tape.move,
        Tape.write, Function.update_idem]
    | cons b bs =>
      refine ⟨5, le_rfl, ?_⟩
      cases bs <;>
        simp [run, locatedStmtCfg, locatedStep, advanceHeads, logicalHeads, Function.iterate_succ_apply, physicalStep, instruction, sourceInstruction,
          startBlock, liftBlockAction, blockAction, executeInstruction, logicalTapes,
          continueBlock, controlRead, stackAtTop, hs, cellsBelow, Tape.mk₂, Tape.mk', Tape.move,
          Tape.write, Function.update_idem] <;>
        (try constructor) <;> funext j <;> cases j with
        | inl l => by_cases hl : l = k <;> simp [logicalHeads, logicalTapes, Function.update, hl, hs,
            stackAtTop, Tape.mk₂, Tape.mk', cellsBelow]
        | inr l => simp [logicalHeads, logicalTapes]
  rcases node with ⟨q, hq⟩
  induction q generalizing state words with
  | push k f q ih =>
    let child := sourceChild ⟨.push k f q, hq⟩ q
      (Finset.mem_insert_of_mem TM2.stmts₁_self)
    obtain ⟨n, hn, hr⟩ := ih state (Function.update words k (f state :: words k)) child.property
    refine ⟨n + 7, by dsimp [statementBudget]; dsimp [child] at hn; omega, ?_⟩
    rw [Function.iterate_add_apply]
    change (run^[n]) ((run^[7]) _) = _
    rw [push ⟨.push k f q, hq⟩ k f q rfl state words]
    exact hr
  | pop k f q ih =>
    let child := sourceChild ⟨.pop k f q, hq⟩ q
      (Finset.mem_insert_of_mem TM2.stmts₁_self)
    obtain ⟨m, hm, hop⟩ := pop ⟨.pop k f q, hq⟩ k f q rfl state words
    obtain ⟨n, hn, hr⟩ := ih (f state (words k).head?)
      (Function.update words k (words k).tail) child.property
    refine ⟨n + m, by dsimp [statementBudget]; dsimp [child] at hn; omega, ?_⟩
    rw [Function.iterate_add_apply]
    change (run^[n]) ((run^[m]) _) = _
    rw [hop]
    exact hr
  | peek k f q ih =>
    let child := sourceChild ⟨.peek k f q, hq⟩ q
      (Finset.mem_insert_of_mem TM2.stmts₁_self)
    obtain ⟨m, hm, hop⟩ := peek ⟨.peek k f q, hq⟩ k f q rfl state words
    obtain ⟨n, hn, hr⟩ := ih (f state (words k).head?) words child.property
    refine ⟨n + m, by dsimp [statementBudget]; dsimp [child] at hn; omega, ?_⟩
    rw [Function.iterate_add_apply]
    change (run^[n]) ((run^[m]) _) = _
    rw [hop]
    exact hr
  | load f q ih =>
    let child := sourceChild ⟨.load f q, hq⟩ q
      (Finset.mem_insert_of_mem TM2.stmts₁_self)
    obtain ⟨n, hn, hr⟩ := ih (f state) words child.property
    refine ⟨n + 1, by dsimp [statementBudget]; dsimp [child] at hn; omega, ?_⟩
    rw [Function.iterate_succ_apply]
    simpa [locatedStmtCfg, locatedSourceCfg, sourceCfg, locatedStep, advanceHeads, physicalStep, instruction, sourceInstruction, controlRead, executeInstruction,
      child, sourceChild] using hr
  | branch f a b iha ihb =>
    cases hf : f state with
    | false =>
      let child := sourceChild ⟨.branch f a b, hq⟩ b
        (Finset.mem_insert_of_mem (Finset.mem_union_right _ TM2.stmts₁_self))
      obtain ⟨n, hn, hr⟩ := ihb state words child.property
      refine ⟨n + 1, by dsimp [statementBudget]; dsimp [child] at hn; omega, ?_⟩
      rw [Function.iterate_succ_apply]
      simpa [locatedStmtCfg, locatedSourceCfg, sourceCfg, locatedStep, advanceHeads, physicalStep, instruction, sourceInstruction, controlRead, executeInstruction,
        child, sourceChild, TM2.stepAux, hf] using hr
    | true =>
      let child := sourceChild ⟨.branch f a b, hq⟩ a
        (Finset.mem_insert_of_mem (Finset.mem_union_left _ TM2.stmts₁_self))
      obtain ⟨n, hn, hr⟩ := iha state words child.property
      refine ⟨n + 1, by dsimp [statementBudget]; dsimp [child] at hn; omega, ?_⟩
      rw [Function.iterate_succ_apply]
      simpa [locatedStmtCfg, locatedSourceCfg, sourceCfg, locatedStep, advanceHeads, physicalStep, instruction, sourceInstruction, controlRead, executeInstruction,
        child, sourceChild, TM2.stepAux, hf] using hr
  | goto f =>
    exact ⟨1, le_rfl, rfl⟩
  | halt =>
    exact ⟨1, le_rfl, rfl⟩

end D5.S0.Computability.PhysicalDivider
