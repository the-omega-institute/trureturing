/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformMaterializer
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Uniform computable complete native analysis and exact K0 materialization. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformAnalysis
import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformAnalysis

open D5.S0.Computability.PreorderTreeEvaluation
open ActualTreeReadoutAcquisition (Address)
open ActualCutPartitionRecovery (LiteralRow CutSet)
open NativeDepthPatterns (History)
open NativeUniformPatterns NativeUniformInput NativeUniformVariables
open Lambda.UniformNativeUnification (TermN)

private theorem list_all_prim {A X : Type} [Primcodable A] [Primcodable X]
    (f : X → A → Bool) (hf : Primrec₂ f) :
    Primrec₂ (fun (x : X) (xs : List A) => xs.all (f x)) := by
  have h := Primrec.list_foldr (Primrec.snd : Primrec (Prod.snd : X × List A → List A))
    (Primrec.const true)
    (Primrec.and.comp (hf.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact h.of_eq (fun p => by induction p.2 <;> simp_all)

private theorem list_sum_prim : Primrec (List.sum : List Nat → Nat) := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
      (fun xs => by induction xs <;> simp_all)

private theorem coded_budget_prim : Primrec codedCellBudget := by
  have ht : Primrec templateLeaves :=
    Primrec.list_length.comp (Primrec.listFilterMap Primrec.id Primrec.snd.to₂)
  have hp : Primrec (fun p : PairCode => (p.2.2.2.map (fun b => templateLeaves b.2)).sum) :=
    list_sum_prim.comp (Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      (ht.comp (Primrec.snd.comp Primrec.snd)).to₂)
  exact list_sum_prim.comp (Primrec.list_map Primrec.id (hp.comp Primrec.snd).to₂)

private theorem exterior_variable_prim : Primrec exteriorHasVariable := by
  let leaf (a : (Bool ⊕ Nat) ⊕ Address) : Bool :=
    Sum.elim (Sum.elim (fun _ => false) (fun _ => true)) (fun _ => false) a
  have hl : Primrec leaf := by
    refine Primrec.sumCasesOn Primrec.id ?_ (Primrec.const false).to₂
    exact (Primrec.sumCasesOn Primrec.snd (Primrec.const false).to₂ (Primrec.const true).to₂)
  have h := uniform_tree_fold (fun _ : Unit => leaf)
    (fun _ : Unit => fun p : Bool × Bool => p.1 || p.2)
    (hl.comp Primrec.snd).to₂
    (Primrec.or.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact (h.comp (Primrec.const ()) Primrec.id).of_eq (fun t => by
    induction t using FreeMagma.recOn with
    | of a => cases a with
      | inl a => cases a <;> rfl
      | inr q => rfl
    | mul l r hl hr => exact congrArg₂ Bool.or hl hr)

private theorem address_pairs_prim : Primrec (fun js : List Address =>
    js.flatMap (fun q => (js.filter (fun r => q < r)).map (fun r => (q,r)))) := by
  have hr : PrimrecRel (fun (r : Address) (q : Address) => q < r) :=
    PrimrecPred.comp address_lt_prim (Primrec.snd.pair Primrec.fst)
  have hf : Primrec₂ (fun (js : List Address) (q : Address) => js.filter (fun r => q < r)) :=
    PrimrecRel.listFilter hr
  refine Primrec.list_flatMap Primrec.id ?_
  exact Primrec.list_map hf
    ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂

private abbrev PairInput := Nat × List (TermN × TermN) × TermN × List Address

private theorem pair_list_computable : Computable (fun a : PairInput =>
    traverseCodes (fun (p : Address × Address) => codedPlan (a.1,a.2.1,p.1,p.2,
      (NativeSymbolicRecutting.termAt p.1 a.2.2.1).getD (.of (.inl true)),
      (NativeSymbolicRecutting.termAt p.2 a.2.2.1).getD (.of (.inl true))))
    (a.2.2.2.flatMap (fun q => (a.2.2.2.filter (fun r => q < r)).map (fun r => (q,r))))) := by
  have hf : Computable₂ (fun (a : PairInput) (p : Address × Address) =>
      codedPlan (a.1,a.2.1,p.1,p.2,
        (NativeSymbolicRecutting.termAt p.1 a.2.2.1).getD (.of (.inl true)),
        (NativeSymbolicRecutting.termAt p.2 a.2.2.1).getD (.of (.inl true)))) := by
    have ht : Computable (fun p : PairInput × (Address × Address) => p.1.2.2.1) :=
      Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
    have hq : Computable (fun p : PairInput × (Address × Address) => p.2.1) :=
      Computable.fst.comp Computable.snd
    have hr : Computable (fun p : PairInput × (Address × Address) => p.2.2) :=
      Computable.snd.comp Computable.snd
    exact coded_plan_computable.comp
      ((Computable.fst.comp Computable.fst).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
          (hq.pair (hr.pair
            ((Primrec.option_getD.to_comp.comp (term_at_prim.to_comp.comp hq ht)
              (Computable.const (FreeMagma.of (Sum.inl true) : TermN))).pair
             (Primrec.option_getD.to_comp.comp (term_at_prim.to_comp.comp hr ht)
              (Computable.const (FreeMagma.of (Sum.inl true) : TermN))))))))
  exact (traverse_computable _ hf).comp Computable.id
    (address_pairs_prim.to_comp.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))

private abbrev RawCell := List PatternWord × List VariableKey
private abbrev ReadyCell := List Address × History × RawCell × TermN × List (TermN × TermN)

set_option maxHeartbeats 2000000 in
-- Nested finite-code instances are elaborated across the complete product domain.
private theorem ready_cell_computable : Computable (fun a : ReadyCell => do
    let js := NativeSymbolicRecutting.symbolicOrdered a.1.toFinset a.2.2.2.1
    let ext := NativeSymbolicRecutting.symbolicExterior a.1.toFinset [] a.2.2.2.1
    let ps ← traverseCodes (fun (p : Address × Address) => codedPlan (a.2.2.1.2.length,a.2.2.2.2,p.1,p.2,
      (NativeSymbolicRecutting.termAt p.1 a.2.2.2.1).getD (.of (.inl true)),
      (NativeSymbolicRecutting.termAt p.2 a.2.2.2.1).getD (.of (.inl true))))
      (js.flatMap (fun q => (js.filter (fun r => q < r)).map (fun r => (q,r))))
    some (a.2.2.1.1,a.2.2.1.2,
      decide (NativeDepthPatterns.Consistent a.2.1
        (NativeTermUnification.evaluate (fun _ => .of true) a.2.2.2.1)) &&
        a.2.2.2.2.all (fun e => e.1 != e.2),
      word ext,js,ps,!exteriorHasVariable ext && ps.all (fun p => p.2.2.1 != 3),
      codedCellBudget ps)) := by
  have hq : Primrec (fun a : ReadyCell => a.1) := Primrec.fst
  have hh : Primrec (fun a : ReadyCell => a.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun a : ReadyCell => a.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ht : Primrec (fun a : ReadyCell => a.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hd : Primrec (fun a : ReadyCell => a.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hj := symbolic_ordered_prim.comp hq ht
  have he := symbolic_exterior_prim.comp hq ((Primrec.const []).pair ht)
  have hp := pair_list_computable.comp
    ((Primrec.list_length.comp (Primrec.snd.comp hc)).pair
      (hd.pair (ht.pair hj))).to_comp
  refine Computable.option_bind hp ?_
  apply Computable₂.mk
  have hall : Primrec (fun es : List (TermN × TermN) =>
      es.all (fun e => e.1 != e.2)) :=
    (list_all_prim (fun _ : Unit => fun e : TermN × TermN => e.1 != e.2)
      (Primrec.not.comp (Primrec.beq.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))).to₂).comp (Primrec.const ()) Primrec.id
  have hpass : Primrec (fun ps : List PairCode => ps.all (fun p => p.2.2.1 != 3)) :=
    (list_all_prim (fun _ : Unit => fun p : PairCode => p.2.2.1 != 3)
      (Primrec.not.comp (Primrec.beq.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.const 3))).to₂).comp (Primrec.const ()) Primrec.id
  exact (Primrec.option_some.comp
    ((Primrec.fst.comp (hc.comp Primrec.fst)).pair
      ((Primrec.snd.comp (hc.comp Primrec.fst)).pair
        ((Primrec.and.comp ((history_consistent_prim.comp hh ht).comp Primrec.fst)
          ((hall.comp hd).comp Primrec.fst)).pair
          ((tree_word_prim.comp (he.comp Primrec.fst)).pair
            ((hj.comp Primrec.fst).pair (Primrec.snd.pair
              ((Primrec.and.comp
                (Primrec.not.comp (exterior_variable_prim.comp (he.comp Primrec.fst)))
                (hpass.comp Primrec.snd)).pair (coded_budget_prim.comp Primrec.snd))))))))).to_comp

private abbrev CellInput := LiteralRow × List Address × History × List Nat × RawCell

set_option maxHeartbeats 1000000 in
-- Nested finite-code instances are elaborated across the complete product domain.
private theorem materialize_cell_computable : Computable (fun a : CellInput =>
    materializeCell a.1 a.2.1.toFinset a.2.2.1 a.2.2.2.1 a.2.2.2.2) := by
  have hc : Primrec (fun a : CellInput => a.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have ha : Primrec (fun a : CellInput => (a.2.2.2.1,a.2.2.2.2.1,a.2.2.2.2.2)) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).pair
      ((Primrec.fst.comp hc).pair (Primrec.snd.comp hc))
  have harg : Computable (fun p : (CellInput × TermN) × List (TermN × TermN) =>
      (p.1.1.2.1,p.1.1.2.2.1,p.1.1.2.2.2.2,p.1.2,p.2)) :=
    (Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))).pair
      ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
        (Computable.fst.comp Computable.fst)))).pair
        ((hc.to_comp.comp (Computable.fst.comp Computable.fst)).pair
          ((Computable.snd.comp Computable.fst).pair Computable.snd)))
  have hready := ready_cell_computable.comp harg
  have hdelta : Computable (fun p : CellInput × TermN =>
      deltaCode (p.1.2.2.2.1,p.1.2.2.2.2.1,p.1.2.2.2.2.2)) := by
    exact delta_code_computable.comp (ha.to_comp.comp Computable.fst)
  have hwhole := whole_code_prim.to_comp.comp ha.to_comp (Computable.fst :
    Computable (Prod.fst : CellInput → LiteralRow))
  have h := Computable.option_bind hwhole
    (Computable.option_bind hdelta hready.to₂).to₂
  exact h.of_eq (fun a => rfl)


private def cellSummary (cells : List CompleteCellCode) : SummaryCode :=
  let feasible := cells.filter (fun cell => cell.2.2.1)
  (cells.length,feasible.length,feasible.all (fun cell => cell.2.2.2.2.2.2.1),
    (feasible.map (fun cell => cell.2.2.2.2.2.2.2)).foldr max 0)

private theorem cell_summary_prim : Primrec cellSummary := by
  have hf : Primrec (fun cells : List CompleteCellCode => cells.filter (fun cell => cell.2.2.1)) :=
    (Primrec.listFilter (Primrec.eq.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const true))).of_eq
      (fun xs => by simp)
  have hp : Primrec (fun cell : CompleteCellCode => cell.2.2.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  have hb : Primrec (fun cell : CompleteCellCode => cell.2.2.2.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  have hall : Primrec (fun cells : List CompleteCellCode => cells.all (fun cell => cell.2.2.2.2.2.2.1)) :=
    (list_all_prim (fun _ : Unit => fun cell : CompleteCellCode => cell.2.2.2.2.2.2.1)
      (hp.comp Primrec.snd).to₂).comp (Primrec.const ()) Primrec.id
  have hm : Primrec (fun xs : List Nat => xs.foldr max 0) :=
    Primrec.list_foldr Primrec.id (Primrec.const 0)
      (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_length.pair ((Primrec.list_length.comp hf).pair
    ((hall.comp hf).pair (hm.comp (Primrec.list_map hf (hb.comp Primrec.snd).to₂))))

private def finishAnalysis (a : Nat × List Nat × List CompleteCellCode) : AnalysisCode :=
  let summary := cellSummary a.2.2
  (a.1,a.2.1,a.2.2,summary,2 * a.2.1.length * (2 ^ a.1 - 1) + summary.2.2.2)

private theorem finish_analysis_prim : Primrec finishAnalysis := by
  have hd : Primrec (fun a : Nat × List Nat × List CompleteCellCode => a.1) := Primrec.fst
  have hn : Primrec (fun a : Nat × List Nat × List CompleteCellCode => a.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun a : Nat × List Nat × List CompleteCellCode => a.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hs := cell_summary_prim.comp hc
  have hpow : Primrec₂ ((· ^ ·) : Nat → Nat → Nat) := Primrec₂.unpaired'.mp Nat.Primrec.pow
  exact hd.pair (hn.pair (hc.pair (hs.pair
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.list_length.comp hn))
        (Primrec.nat_sub.comp (hpow.comp (Primrec.const 2) hd) (Primrec.const 1)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hs)))))))

set_option maxHeartbeats 2000000 in
-- Nested finite-code instances are elaborated across the complete product domain.
private theorem materialize_analysis_computable : Computable materializeAnalysis := by
  have harg : Computable (fun p : (CommonData × VariableCellCode) × RawCell =>
      (p.1.1.1,p.1.1.2.1,p.1.1.2.2.1,p.1.2.2.1,p.2)) :=
    (Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
      ((Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))).pair
        ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
          (Computable.fst.comp Computable.fst)))).pair
          ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair
            Computable.snd)))
  have hc := (materialize_cell_computable.comp harg).to₂
  have hall : Computable (fun p : CommonData × VariableCellCode =>
      traverseCodes (materializeCell p.1.1 p.1.2.1.toFinset p.1.2.2.1 p.2.2.1) p.2.2.2) :=
    (traverse_computable _ hc).comp Computable.id
      (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hfarg : Computable (fun p : ((CommonCode × CommonData) × VariableCellCode) ×
      List CompleteCellCode => (p.1.2.1,p.1.2.2.1,p.2)) :=
    (Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
      ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair
        Computable.snd)
  have hf := Computable.option_some.comp (finish_analysis_prim.to_comp.comp hfarg)
  have htarg : Computable (fun p : (CommonCode × CommonData) × VariableCellCode =>
      (p.1.2,p.2)) := (Computable.snd.comp Computable.fst).pair Computable.snd
  have ht := hall.comp htarg
  have hv : Computable (fun p : CommonCode × CommonData => materializeVariableCells p.1) :=
    uniform_variable_materializer.1.to_comp.comp Computable.fst
  have h := Computable.option_bind uniform_common_codec.1.to_comp
    (Computable.option_bind hv (Computable.option_bind ht hf.to₂).to₂).to₂
  exact h.of_eq (fun w => rfl)

/-- One computable map realizes the complete native analysis and K0 before all input quantifiers.
The native analysis retains every raw cell and tests every old disequality after composition. -/
theorem uniform_native_materializer :
    Computable materializeAnalysis ∧ ∀ (C : LiteralRow) (Q : CutSet) (H : History) (N : Nat),
      materializeAnalysis (codeCommon C Q H N) = some (nativeAnalysisCode C Q H) :=
  ⟨materialize_analysis_computable,materialize_analysis_exact⟩

end D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformAnalysis
