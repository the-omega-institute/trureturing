/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Primitive recursive native tree navigation and exact finite history evaluation. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformSyntax

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformAnalysis

open D5.S0.Computability.PreorderTreeEvaluation
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualCutPartitionRecovery (LiteralRow CutSet)
open NativeDepthPatterns (History)
open NativeTermUnification (Term)
open Lambda.UniformNativeUnification (TermN)

private def treeView {A : Type} : FreeMagma A → A ⊕ (FreeMagma A × FreeMagma A)
  | .of a => .inl a
  | .mul l r => .inr (l,r)

private theorem tree_view_prim {A : Type} [Primcodable A] : Primrec (@treeView A) := by
  let leaf (a : A) : FreeMagma A × (A ⊕ (FreeMagma A × FreeMagma A)) :=
    (.of a,.inl a)
  let node (p : (FreeMagma A × (A ⊕ (FreeMagma A × FreeMagma A))) ×
      (FreeMagma A × (A ⊕ (FreeMagma A × FreeMagma A)))) :=
    (p.1.1.mul p.2.1,(Sum.inr (p.1.1,p.2.1) : A ⊕ (FreeMagma A × FreeMagma A)))
  have hl : Primrec leaf := tree_of_prim.pair Primrec.sumInl
  have hn : Primrec node :=
    (tree_mul_prim.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.sumInr.comp ((Primrec.fst.comp Primrec.fst).pair
        (Primrec.fst.comp Primrec.snd)))
  have hf := uniform_tree_fold (fun _ : Unit => leaf) (fun _ : Unit => node)
    (hl.comp Primrec.snd).to₂ (hn.comp Primrec.snd).to₂
  have he (t : FreeMagma A) :
      (@FreeMagma.lift A _ ⟨fun l r => node (l,r)⟩ leaf) t = (t,treeView t) := by
    induction t using FreeMagma.recOn with
    | of a => rfl
    | mul l r hl hr =>
        change node ((@FreeMagma.lift A _ ⟨fun l r => node (l,r)⟩ leaf) l,
          (@FreeMagma.lift A _ ⟨fun l r => node (l,r)⟩ leaf) r) = _
        rw [hl,hr]
        rfl
  exact (Primrec.snd.comp (hf.comp (Primrec.const ()) Primrec.id)).of_eq
    (fun t => congrArg Prod.snd (he t))

private def child {A : Type} (b : Bool) (t : FreeMagma A) : Option (FreeMagma A) :=
  Sum.casesOn (treeView t) (fun _ => none) (fun p => some (bif b then p.2 else p.1))

private theorem child_prim {A : Type} [Primcodable A] : Primrec₂ (@child A) := by
  unfold child
  refine Primrec.sumCasesOn (tree_view_prim.comp Primrec.snd) (Primrec.const none).to₂ ?_
  exact (Primrec.option_some.comp (Primrec.cond (Primrec.fst.comp Primrec.fst)
    (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))).to₂

private def walkStep {A : Type} (s : Option (FreeMagma A)) (b : Bool) :=
  s.bind (child b)

private theorem walk_step_prim {A : Type} [Primcodable A] : Primrec₂ (@walkStep A) := by
  unfold walkStep
  refine Primrec.option_bind Primrec.fst ?_
  exact (child_prim.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

private theorem walk_exact {X : Type} (q : Address) (s : Option (Term X)) :
    q.foldl walkStep s = s.bind (NativeSymbolicRecutting.termAt q) := by
  induction q generalizing s with
  | nil => cases s <;> rfl
  | cons b q ih =>
      rw [List.foldl_cons,ih]
      cases s with
      | none => rfl
      | some t => cases t with
        | of a => rfl
        | mul l r => cases b <;> rfl

/-- The same original address navigation is primitive recursive on fixed tree codes. -/
theorem term_at_prim {X : Type} [Primcodable X] :
    Primrec₂ (NativeSymbolicRecutting.termAt : Address → Term X → Option (Term X)) := by
  have h := Primrec.list_foldl (Primrec.fst : Primrec (Prod.fst : Address × Term X → Address))
    (Primrec.option_some.comp Primrec.snd)
    (walk_step_prim.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact h.of_eq (fun p => by simpa only [Option.bind_some] using walk_exact p.1 (some p.2))

private theorem test_filling_prim :
    Primrec (NativeTermUnification.evaluate (fun _ : Nat => FreeMagma.of true)) := by
  have hl : Primrec (fun a : Bool ⊕ Nat =>
      Sum.elim FreeMagma.of (fun _ => FreeMagma.of true) a) := by
    exact Primrec.sumCasesOn Primrec.id (tree_of_prim.comp Primrec.snd).to₂
      (Primrec.const (FreeMagma.of true)).to₂
  exact (uniform_tree_fold (fun _ : Unit => Sum.elim FreeMagma.of (fun _ : Nat => .of true))
    (fun _ : Unit => fun p : FreeMagma Bool × FreeMagma Bool => p.1.mul p.2)
    (hl.comp Primrec.snd).to₂ (tree_mul_prim.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).comp
      (Primrec.const ()) Primrec.id


theorem tree_word_prim {A : Type} [Primcodable A] :
    Primrec (word : FreeMagma A → Word A) :=
  Primrec.encode_iff.mp (show Primrec (fun t : FreeMagma A =>
    Encodable.encode (word t)) from Primrec.encode)

private def exteriorChildren (p : Address × TermN) : List (Address × TermN) :=
  Sum.casesOn (treeView p.2) (fun _ => []) (fun z =>
    [(p.1 ++ [false],z.1),(p.1 ++ [true],z.2)])

private theorem exterior_children_prim : Primrec exteriorChildren := by
  unfold exteriorChildren
  refine Primrec.sumCasesOn (tree_view_prim.comp Primrec.snd) (Primrec.const []).to₂ ?_
  exact (Primrec.list_cons.comp
    ((Primrec.list_append.comp (Primrec.fst.comp Primrec.fst) (Primrec.const [false])).pair
      (Primrec.fst.comp Primrec.snd))
    (Primrec.list_cons.comp
      ((Primrec.list_append.comp (Primrec.fst.comp Primrec.fst) (Primrec.const [true])).pair
        (Primrec.snd.comp Primrec.snd)) (Primrec.const []))).to₂

private def exteriorStep (qs : List Address)
    (p : (Address × TermN) × List (NativeSymbolicRecutting.SymbolicExterior Nat)) :
    Option (NativeSymbolicRecutting.SymbolicExterior Nat) :=
  if p.1.1 ∈ qs then some (.of (.inr p.1.1)) else
  Sum.casesOn (treeView p.1.2) (fun a => some (.of (.inl a))) (fun _ => do
    let l ← p.2.head?
    let r ← p.2.tail.head?
    some (l.mul r))

private theorem exterior_step_prim : Primrec₂ exteriorStep := by
  have mem : PrimrecRel (fun (xs : List Address) (a : Address) => a ∈ xs) :=
    (PrimrecRel.exists_mem_list (Primrec.eq : PrimrecRel ((· = ·) : Address → Address → Prop))).of_eq
      (fun xs a => by simp)
  unfold exteriorStep
  refine Primrec.ite (mem.comp Primrec.fst (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
    (Primrec.option_some.comp (tree_of_prim.comp (Primrec.sumInr.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))))) ?_
  refine Primrec.sumCasesOn
    (tree_view_prim.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
    (Primrec.option_some.comp (tree_of_prim.comp (Primrec.sumInl.comp Primrec.snd))).to₂ ?_
  have takeTwo : Primrec (fun xs : List (NativeSymbolicRecutting.SymbolicExterior Nat) => do
      let l ← xs.head?; let r ← xs.tail.head?; some (l.mul r)) := by
    refine Primrec.option_bind Primrec.list_head? ?_
    apply Primrec₂.mk
    change Primrec (fun p : List (NativeSymbolicRecutting.SymbolicExterior Nat) ×
      NativeSymbolicRecutting.SymbolicExterior Nat => do
        let r ← p.1.tail.head?; some (p.2.mul r))
    refine Primrec.option_bind (Primrec.list_head?.comp (Primrec.list_tail.comp Primrec.fst)) ?_
    exact (Primrec.option_some.comp (tree_mul_prim.comp (Primrec.snd.comp Primrec.fst)
      Primrec.snd)).to₂
  exact (takeTwo.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to₂

/-- Symbolic cutting keeps the original inherited addresses and every residual variable. -/
theorem symbolic_exterior_prim : Primrec₂ (fun (qs : List Address) (p : Address × TermN) =>
    NativeSymbolicRecutting.symbolicExterior qs.toFinset p.1 p.2) := by
  apply Primrec.nat_omega_rec
    (m := fun _ p => (word p.2).length) (l := fun _ p => exteriorChildren p)
    (g := exteriorStep)
  · exact (Primrec.list_length.comp (tree_word_prim.comp (Primrec.snd.comp Primrec.snd))).to₂
  · exact (exterior_children_prim.comp Primrec.snd).to₂
  · exact exterior_step_prim
  · intro qs p z hz
    rcases p with ⟨a,t⟩
    cases t with
    | of b => simp [exteriorChildren,treeView] at hz
    | mul l r =>
        simp only [exteriorChildren,treeView,List.mem_cons,List.not_mem_nil,or_false] at hz
        rcases hz with rfl | rfl <;> simp only [word,List.length_cons,List.length_append] <;> omega
  · intro qs p
    rcases p with ⟨a,t⟩
    cases t <;> by_cases h : a ∈ qs <;>
      simp [exteriorStep,exteriorChildren,treeView,NativeSymbolicRecutting.symbolicExterior,h]

private def rootReply (t : FreeMagma Bool) : Reply :=
  Sum.casesOn (treeView t) (fun b => bif b then .alpha else .beta) (fun _ => .branch)

private theorem root_reply_prim : Primrec rootReply := by
  unfold rootReply
  exact Primrec.sumCasesOn tree_view_prim
    ((Primrec.dom_finite (fun b : Bool => bif b then Reply.alpha else Reply.beta)).comp Primrec.snd).to₂
    (Primrec.const Reply.branch).to₂

private theorem readout_walk (q : Address) (s : Option (FreeMagma Bool)) :
    ((q.foldl walkStep s).map rootReply).getD .absent =
      (s.map (readout q)).getD .absent := by
  induction q generalizing s with
  | nil =>
      cases s with
      | none => rfl
      | some t => cases t with
        | of b => cases b <;> rfl
        | mul l r => rfl
  | cons b q ih =>
      rw [List.foldl_cons,ih]
      cases s with
      | none => rfl
      | some t => cases t with
        | of a => rfl
        | mul l r => cases b <;> rfl

theorem readout_prim : Primrec₂ readout := by
  have h : Primrec (fun p : Address × FreeMagma Bool => p.1.foldl walkStep (some p.2)) :=
    Primrec.list_foldl Primrec.fst (Primrec.option_some.comp Primrec.snd)
      (walk_step_prim.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  have hm := Primrec.option_map h (root_reply_prim.comp Primrec.snd).to₂
  exact (Primrec.option_getD.comp hm (Primrec.const Reply.absent)).of_eq
    (fun p => readout_walk p.1 (some p.2))

theorem substitution_prim : Primrec GenealogicalFiberTransport.substitution := by
  exact (uniform_tree_fold
    (fun _ : Unit => fun b : Bool => if b then FreeMagma.of false else .mul (.of false) (.of true))
    (fun _ : Unit => fun p : FreeMagma Bool × FreeMagma Bool => p.1.mul p.2)
    ((Primrec.dom_finite (fun b : Bool => if b then FreeMagma.of false else
      (FreeMagma.of false).mul (.of true))).comp Primrec.snd).to₂
    (tree_mul_prim.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).comp
      (Primrec.const ()) Primrec.id

/-- Arbitrary finite histories retain their epochs, repetitions and absent replies. -/
theorem history_consistent_prim : Primrec₂ (fun (H : History) (t : TermN) =>
    decide (NativeDepthPatterns.Consistent H
      (NativeTermUnification.evaluate (fun _ : Nat => FreeMagma.of true) t))) := by
  have hi : Primrec₂ (fun (n : Nat) (t : FreeMagma Bool) =>
      GenealogicalFiberTransport.substitution^[n] t) :=
    Primrec.nat_iterate Primrec.fst Primrec.snd (substitution_prim.comp Primrec.snd).to₂
  have hr : PrimrecRel (fun (e : Nat × Address × Reply) (t : FreeMagma Bool) =>
      readout e.2.1 (GenealogicalFiberTransport.substitution^[e.1] t) = e.2.2) :=
    Primrec.eq.comp
      (readout_prim.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (hi.comp (Primrec.fst.comp Primrec.fst) Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  exact (hr.forall_mem_list.decide.comp Primrec.fst (test_filling_prim.comp Primrec.snd))

end D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformAnalysis
