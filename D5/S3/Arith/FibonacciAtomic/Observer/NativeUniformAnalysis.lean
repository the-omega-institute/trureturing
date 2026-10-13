/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact complete native cell and whole-row analysis serialization. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformSyntax

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformAnalysis

open D5.S0.Computability.PreorderTreeEvaluation
open ActualTreeReadoutAcquisition (Address)
open ActualCutPartitionRecovery (LiteralRow CutSet)
open NativeDepthPatterns (Pattern Frontier frontierAddress History)
open NativeHistoryCells (Patterns Variables oldTerm wholeTerm patternTerm)
open NativeUniformPatterns NativeUniformInput NativeUniformVariables
open NativeWholeRowService (PairKind PairPlan planPair presentation variableList)
open NativeGroundSolutionSpace
open NativeTermUnification (Term Presentation finPresentation encode nativeDecode)
open Lambda Strata.Util
open Lambda.UniformNativeUnification (TermN F liftTerm liftEquations project)

abbrev SummaryCode := Nat × Nat × Bool × Nat
abbrev ExteriorCode := Word ((Bool ⊕ Nat) ⊕ Address)
abbrev CompleteCellCode := List PatternWord × List VariableKey × Bool ×
  ExteriorCode × List Address × List PairCode × Bool × Nat
abbrev AnalysisCode := Nat × List Nat × List CompleteCellCode × SummaryCode × Nat

/-- Templates are finite Boolean trees; their native budget counts leaves. -/
def templateLeaves (w : TemplateWord) : Nat := (w.filterMap id).length

def codedCellBudget (ps : List PairCode) : Nat :=
  (ps.map (fun p => (p.2.2.2.map (fun b => templateLeaves b.2)).sum)).sum

def exteriorHasVariable : NativeSymbolicRecutting.SymbolicExterior Nat → Bool
  | .of (.inl (.inr _)) => true
  | .of _ => false
  | .mul l r => exteriorHasVariable l || exteriorHasVariable r

/-- Every raw cell is retained; feasibility is a field rather than an input premise. -/
def materializeCell (C : LiteralRow) (Q : CutSet) (H : History)
    (names : List Nat) (cell : List PatternWord × List VariableKey) :
    Option CompleteCellCode := do
  let a : SyntaxInput := (names,cell.1,cell.2)
  let t ← wholeCode a C
  let Δ ← deltaCode a
  let js := NativeSymbolicRecutting.symbolicOrdered Q t
  let ext := NativeSymbolicRecutting.symbolicExterior Q [] t
  let ps ← traverseCodes (fun p => codedPlan (cell.2.length,Δ,p.1,p.2,
      (NativeSymbolicRecutting.termAt p.1 t).getD (.of (.inl true)),
      (NativeSymbolicRecutting.termAt p.2 t).getD (.of (.inl true))))
    (js.flatMap (fun q => (js.filter (fun r => q < r)).map (fun r => (q,r))))
  let history := decide (NativeDepthPatterns.Consistent H
    (NativeTermUnification.evaluate (fun _ => .of true) t))
  let legal := Δ.all (fun e => e.1 != e.2)
  let passes := !exteriorHasVariable ext && ps.all (fun p => p.2.2.1 != 3)
  some (cell.1,cell.2,history && legal,word ext,js,ps,passes,codedCellBudget ps)

/-- This is the complete native cell serialization, including infeasible cells. -/
def nativeCellCode {C : LiteralRow} {d : Nat} (Q : CutSet) (H : History)
    (η : Patterns C d) : CompleteCellCode :=
  let j := fun x : Variables η => ((variableList η).map variableKey).idxOf (variableKey x)
  let ext := FreeMagma.map (Sum.map (Sum.map id j) id)
    (NativeSymbolicRecutting.symbolicExterior Q [] (wholeTerm η))
  (familyWord η,(variableList η).map variableKey,NativeHistoryCells.feasible η H,
    word ext,NativeSymbolicRecutting.symbolicOrdered Q (wholeTerm η),
    (NativeWholeRowService.pairPlans Q η).map (nativePairCode η),
    NativeWholeRowService.cellPass Q η,NativeWholeRowService.cellBudget Q η)

/-- The reference bundle retains the existing native summary and all ordered data. -/
def nativeAnalysisCode (C : LiteralRow) (Q : CutSet) (H : History) : AnalysisCode :=
  let d := NativeHistoryCells.requiredDepth Q H
  let analysis := NativeWholeRowService.analyze C Q H
  (d,(NativeWholeRowService.classList C).map Subtype.val,
    (NativeWholeRowService.allPatterns C d).map (nativeCellCode Q H),
    (analysis.rawCells,analysis.feasibleCells,analysis.passes,analysis.templateMaximum),
    NativeWholeRowService.K0 C Q H)

/-- Malformed row/history words and malformed generated components return none.
Contradictory histories remain inputs and may yield no feasible cells. -/
def materializeAnalysis (w : CommonCode) : Option AnalysisCode := do
  let input ← parseCommon w
  let raw ← materializeVariableCells w
  let cells ← traverseCodes (materializeCell input.1 input.2.1.toFinset
    input.2.2.1 raw.2.1) raw.2.2
  let feasible := cells.filter (fun cell => cell.2.2.1)
  let summary : SummaryCode := (cells.length,feasible.length,
    feasible.all (fun cell => cell.2.2.2.2.2.2.1),
    (feasible.map (fun cell => cell.2.2.2.2.2.2.2)).foldr max 0)
  let budget := 2 * raw.2.1.length * (2 ^ raw.1 - 1) + summary.2.2.2
  some (raw.1,raw.2.1,cells,summary,budget)

private theorem term_at_rename {X Y : Type} (f : X → Y) (q : Address) (t : Term X) :
    NativeSymbolicRecutting.termAt q (renameTerm f t) =
      (NativeSymbolicRecutting.termAt q t).map (renameTerm f) := by
  induction q generalizing t with
  | nil => rfl
  | cons b q ih =>
      cases t with
      | of a => rfl
      | mul l r => cases b <;> exact ih _

private theorem symbolic_order_rename {X Y : Type} (f : X → Y)
    (Q : CutSet) (t : Term X) :
    NativeSymbolicRecutting.symbolicOrdered Q (renameTerm f t) =
      NativeSymbolicRecutting.symbolicOrdered Q t := by
  unfold NativeSymbolicRecutting.symbolicOrdered
  congr 1
  apply Finset.filter_congr
  intro q _
  rw [term_at_rename,Option.isSome_map]

private theorem symbolic_exterior_rename {X Y : Type} (f : X → Y)
    (Q : CutSet) (a : Address) (t : Term X) :
    NativeSymbolicRecutting.symbolicExterior Q a (renameTerm f t) =
      FreeMagma.map (Sum.map (Sum.map id f) id)
        (NativeSymbolicRecutting.symbolicExterior Q a t) := by
  induction t using FreeMagma.recOn generalizing a with
  | of b =>
      by_cases h : a ∈ Q <;>
        simp only [renameTerm,FreeMagma.map_of,NativeSymbolicRecutting.symbolicExterior,h,if_pos,if_neg]
      all_goals rfl
  | mul l r hl hr =>
      change NativeSymbolicRecutting.symbolicExterior Q a
        ((renameTerm f l).mul (renameTerm f r)) = _
      by_cases h : a ∈ Q
      · simp only [NativeSymbolicRecutting.symbolicExterior,h,if_pos]
        rfl
      · simp only [NativeSymbolicRecutting.symbolicExterior,h,if_neg]
        exact congrArg₂ FreeMagma.mul (hl _) (hr _)

private theorem exterior_variables_code {X : Type} (f : X → Nat)
    (t : NativeSymbolicRecutting.SymbolicExterior X) :
    (!exteriorHasVariable (FreeMagma.map (Sum.map (Sum.map id f) id) t)) =
      (NativeWholeRowService.exteriorVariables t).isEmpty := by
  induction t using FreeMagma.recOn with
  | of a => cases a with
    | inl a => cases a <;> rfl
    | inr q => rfl
  | mul l r hl hr =>
      change (!(exteriorHasVariable (FreeMagma.map (Sum.map (Sum.map id f) id) l) ||
        exteriorHasVariable (FreeMagma.map (Sum.map (Sum.map id f) id) r))) = _
      rw [Bool.not_or,hl,hr]
      change _ = (NativeWholeRowService.exteriorVariables l ++ NativeWholeRowService.exteriorVariables r).isEmpty
      cases NativeWholeRowService.exteriorVariables l <;>
        cases NativeWholeRowService.exteriorVariables r <;> rfl

private theorem evaluate_rename {X Y : Type} (f : X → Y) (t : Term X) :
    NativeTermUnification.evaluate (fun _ => .of true) (renameTerm f t) =
      NativeTermUnification.evaluate (fun _ => .of true) t := by
  induction t using FreeMagma.recOn with
  | of a => cases a <;> rfl
  | mul l r hl hr => exact congrArg₂ FreeMagma.mul hl hr

private theorem template_leaves_exact (t : NativeGroundSolutionSpace.Source) :
    templateLeaves (word t) = t.length := by
  induction t using FreeMagma.recOn with
  | of b => rfl
  | mul l r hl hr =>
      change (List.filterMap id (none :: (word l ++ word r))).length = l.length + r.length
      simp only [templateLeaves,List.filterMap_cons,id_eq,List.filterMap_append,List.length_append] at *
      omega

private theorem coded_budget_exact {C : LiteralRow} {d : Nat} (η : Patterns C d)
    (ps : List (PairPlan (Variables η))) :
    codedCellBudget (ps.map (nativePairCode η)) =
      (ps.map (fun p => (p.bindings.map (fun b => b.2.length)).sum)).sum := by
  simp only [codedCellBudget,List.map_map,Function.comp_def,nativePairCode,
    template_leaves_exact]

private theorem materialize_cell_exact (C : LiteralRow) (Q : CutSet) (H : History)
    (η : Patterns C (NativeHistoryCells.requiredDepth Q H)) :
    materializeCell C Q H ((NativeWholeRowService.classList C).map Subtype.val)
      (familyWord η,(variableList η).map variableKey) = some (nativeCellCode Q H η) := by
  let j := fun x : Variables η => ((variableList η).map variableKey).idxOf (variableKey x)
  have ht : wholeCode (cellSyntax η) C = some (cellTerm η (wholeTerm η)) :=
    whole_code_exact η
  have hd := delta_code_exact η
  have ho := symbolic_order_rename j Q (wholeTerm η)
  have he := symbolic_exterior_rename j Q [] (wholeTerm η)
  have hh := evaluate_rename j (wholeTerm η)
  have hp : traverseCodes (fun p => codedPlan ((variableList η).length,
      (NativeWholeRowService.delta η).map (fun e => (cellTerm η e.1,cellTerm η e.2)),
      p.1,p.2,(NativeSymbolicRecutting.termAt p.1 (cellTerm η (wholeTerm η))).getD (.of (.inl true)),
      (NativeSymbolicRecutting.termAt p.2 (cellTerm η (wholeTerm η))).getD (.of (.inl true))))
      ((NativeSymbolicRecutting.symbolicOrdered Q (wholeTerm η)).flatMap
        (fun q => ((NativeSymbolicRecutting.symbolicOrdered Q (wholeTerm η)).filter
          (fun r => q < r)).map (fun r => (q,r)))) =
      some ((NativeWholeRowService.pairPlans Q η).map (nativePairCode η)) := by
    unfold NativeWholeRowService.pairPlans
    rw [List.map_flatMap]
    have hpoint (q r : Address) :
        (NativeSymbolicRecutting.termAt q (cellTerm η (wholeTerm η))).getD (.of (.inl true)) =
          cellTerm η ((NativeSymbolicRecutting.termAt q (wholeTerm η)).getD (.of (.inl true))) := by
      rw [cell_term_rename,term_at_rename]
      cases NativeSymbolicRecutting.termAt q (wholeTerm η) <;> simp [cell_term_rename,j,renameTerm]
    simpa only [List.map_id,List.map_flatMap,List.map_map,Function.comp_def,id_eq] using
      traverse_map_exact
        (fun p : Address × Address => codedPlan ((variableList η).length,
          (NativeWholeRowService.delta η).map (fun e => (cellTerm η e.1,cellTerm η e.2)),
          p.1,p.2,(NativeSymbolicRecutting.termAt p.1 (cellTerm η (wholeTerm η))).getD (.of (.inl true)),
          (NativeSymbolicRecutting.termAt p.2 (cellTerm η (wholeTerm η))).getD (.of (.inl true))))
        id (fun p => nativePairCode η (planPair (presentation η) (NativeWholeRowService.delta η)
          p.1 p.2 ((NativeSymbolicRecutting.termAt p.1 (wholeTerm η)).getD (.of (.inl true)))
          ((NativeSymbolicRecutting.termAt p.2 (wholeTerm η)).getD (.of (.inl true)))))
        ((NativeSymbolicRecutting.symbolicOrdered Q (wholeTerm η)).flatMap
          (fun q => ((NativeSymbolicRecutting.symbolicOrdered Q (wholeTerm η)).filter
            (fun r => q < r)).map (fun r => (q,r))))
        (by intro p _; dsimp only [id]; rw [hpoint p.1 p.2,hpoint p.2 p.1]; exact native_pair_exact C Q H η _ _ _ _ _)
  have legal := syntax_legal_code_exact C Q H η
  rw [delta_code_exact,Option.map_some] at legal
  have legal' := Option.some.inj legal
  unfold materializeCell
  change (wholeCode (cellSyntax η) C).bind _ = _
  rw [ht]
  simp only [Bind.bind,Option.bind]
  change (deltaCode (cellSyntax η)).bind _ = _
  rw [hd]
  simp only [Bind.bind,Option.bind,List.length_map]
  rw [cell_term_rename η (wholeTerm η)]
  rw [ho,he]
  rw [← cell_term_rename η (wholeTerm η),hp]
  dsimp only [Bind.bind,Option.bind]
  rw [cell_term_rename η (wholeTerm η),hh,legal',coded_budget_exact]
  change some (_,_,_,_,_,_,_,_) = some (nativeCellCode Q H η)
  have pass : ((NativeWholeRowService.pairPlans Q η).map (nativePairCode η)).all
      (fun p => p.2.2.1 != 3) =
      (NativeWholeRowService.pairPlans Q η).all (fun p => p.kind != .feasibleNonground) := by
    rw [List.all_map]
    congr 1
    funext p
    change (kindCode p.kind != 3) = (p.kind != .feasibleNonground)
    cases p.kind <;> rfl
  rw [exterior_variables_code,pass]
  rfl

theorem materialize_analysis_exact (C : LiteralRow) (Q : CutSet) (H : History) (N : Nat) :
    materializeAnalysis (codeCommon C Q H N) = some (nativeAnalysisCode C Q H) := by
  rw [materializeAnalysis,uniform_common_codec.2 C Q H N]
  simp only [Bind.bind,Option.bind]
  rw [(uniform_variable_materializer.2 C Q H N).1]
  dsimp only [Bind.bind,Option.bind]
  try rw [Finset.sort_toFinset]
  rw [traverse_map_exact _ _ (nativeCellCode Q H)
    (NativeWholeRowService.allPatterns C (NativeHistoryCells.requiredDepth Q H))
    (by intro η _; exact materialize_cell_exact C Q H η)]
  simp only [Bind.bind,Option.bind,List.filter_map,List.length_map,List.all_map,List.map_map,
    Function.comp_def,nativeCellCode]
  congr 1
  simp only [nativeAnalysisCode,NativeWholeRowService.analyze,NativeWholeRowService.feasibleList,
    NativeWholeRowService.K0,NativeWholeRowService.classList,List.length_map,
    List.length_attach,Finset.length_sort]

end D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformAnalysis
