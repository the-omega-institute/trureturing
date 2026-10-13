/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Uniform old-class syntax and exact original-presentation pair-plan transport. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformPlan

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

theorem tree_of_prim {A : Type} [Primcodable A] :
    Primrec (FreeMagma.of : A → FreeMagma A) := by
  apply Primrec.encode_iff.mp
  change Primrec (fun a : A => Encodable.encode ([some a] : Word A))
  exact Primrec.encode.comp (Primrec.list_cons.comp
    (Primrec.option_some.comp Primrec.id) (Primrec.const []))

theorem tree_mul_prim {A : Type} [Primcodable A] :
    Primrec₂ (FreeMagma.mul : FreeMagma A → FreeMagma A → FreeMagma A) := by
  have hw : Primrec (word : FreeMagma A → Word A) := Primrec.encode_iff.mp Primrec.encode
  apply Primrec₂.uncurry.mp
  apply Primrec.encode_iff.mp
  change Primrec (fun p : FreeMagma A × FreeMagma A =>
    Encodable.encode (none :: (word p.1 ++ word p.2)))
  exact Primrec.encode.comp (Primrec.list_cons.comp (Primrec.const none)
    (Primrec.list_append.comp (hw.comp Primrec.fst) (hw.comp Primrec.snd)))

private theorem parse_prim {A : Type} [Primcodable A] :
    Primrec (parse : Word A → Option (FreeMagma A)) := by
  exact (Primrec.decode.comp Primrec.encode).of_eq (fun w => by
    change ((Encodable.decode (α := Word A) (Encodable.encode w)).bind parse) = parse w
    rw [Encodable.encodek]
    rfl)

/-- Prefixing a key changes only its relative address. -/
def prefixKeys (b : Bool) : Term VariableKey → Term VariableKey :=
  FreeMagma.map (Sum.map id (fun x => (x.1,b :: x.2)))

private theorem prefix_keys_prim : Primrec₂ prefixKeys := by
  have hl : Primrec₂ (fun (b : Bool) (a : Bool ⊕ VariableKey) =>
      Sum.map id (fun x => (x.1,b :: x.2)) a) := by
    refine Primrec.sumCasesOn Primrec.snd (Primrec.sumInl.comp Primrec.snd).to₂ ?_
    exact (Primrec.sumInr.comp
      ((Primrec.fst.comp Primrec.snd).pair
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)))).to₂
  exact uniform_tree_fold
    (fun (_b : Bool) (a : Bool ⊕ VariableKey) =>
      FreeMagma.of (Sum.map id (fun x : VariableKey => (x.1,_b :: x.2)) a))
    (fun (_ : Bool) (p : Term VariableKey × Term VariableKey) => p.1.mul p.2)
    ((tree_of_prim (A := Bool ⊕ VariableKey)).comp₂ hl)
    (tree_mul_prim.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

/-- Class names and reached addresses replace frontier placeholders. -/
private def keyedFold (n : Nat) (t : TermN) : Term VariableKey :=
  (@FreeMagma.lift (Bool ⊕ Nat) (Term VariableKey)
    ⟨fun l r => .mul (prefixKeys false l) (prefixKeys true r)⟩
    (fun a => match a with
      | .inl b => .of (.inl b)
      | .inr _ => .of (.inr (n,[])))) t

private theorem keyed_fold_prim : Primrec₂ keyedFold := by
  have hl : Primrec₂ (fun (n : Nat) (a : Bool ⊕ Nat) =>
      Sum.elim (fun b => (FreeMagma.of (Sum.inl b) : Term VariableKey))
        (fun _ => .of (.inr (n,[]))) a) := by
    refine Primrec.sumCasesOn Primrec.snd (tree_of_prim.comp (Primrec.sumInl.comp Primrec.snd)).to₂ ?_
    exact (tree_of_prim.comp (Primrec.sumInr.comp
      ((Primrec.fst.comp Primrec.fst).pair (Primrec.const ([] : Address))))).to₂
  have h := uniform_tree_fold
    (fun n a => Sum.elim (fun b => (FreeMagma.of (Sum.inl b) : Term VariableKey))
      (fun _ => .of (.inr (n,[]))) a)
    (fun (_ : Nat) (p : Term VariableKey × Term VariableKey) =>
      .mul (prefixKeys false p.1) (prefixKeys true p.2)) hl
    (tree_mul_prim.comp
      (prefix_keys_prim.comp (Primrec.const false) (Primrec.fst.comp Primrec.snd))
      (prefix_keys_prim.comp (Primrec.const true) (Primrec.snd.comp Primrec.snd)))
  exact h.of_eq (fun n t => by
    induction t using FreeMagma.recOn with
    | of a => cases a <;> rfl
    | mul l r hl hr =>
        have hleaf :
            (fun a : Bool ⊕ Nat =>
              Sum.elim (fun b => (FreeMagma.of (Sum.inl b) : Term VariableKey))
                (fun _ => .of (.inr (n,[]))) a) =
            (fun a => match a with
              | .inl b => .of (.inl b)
              | .inr _ => .of (.inr (n,[]))) := by
          funext a
          cases a <;> rfl
        simp only [keyedFold, hleaf, hl, hr])

private theorem map_pattern {X Y : Type} (f : X → Y) (d : Nat) (p : Pattern d)
    (name : Frontier p → X) :
    FreeMagma.map (Sum.map id f) (patternTerm p name) = patternTerm p (f ∘ name) := by
  induction d with
  | zero => rfl
  | succ d ih => cases p with
    | inl b => rfl
    | inr p => exact congrArg₂ FreeMagma.mul (ih p.1 _) (ih p.2 _)

private theorem pattern_word (d : Nat) (p : Pattern d) :
    patternWord p = word (patternTerm p (fun _ => (0 : Nat))) := by
  induction d with
  | zero => rfl
  | succ d ih => cases p with
    | inl b => rfl
    | inr p => exact congrArg (none :: ·) (congrArg₂ List.append (ih p.1) (ih p.2))

private theorem keyed_fold_exact (n d : Nat) (p : Pattern d) :
    keyedFold n (patternTerm p (fun _ => (0 : Nat))) =
      patternTerm p (fun x => (n,frontierAddress p x)) := by
  induction d with
  | zero => rfl
  | succ d ih => cases p with
    | inl b => rfl
    | inr p =>
        change (prefixKeys false (keyedFold n (patternTerm p.1 (fun _ => 0)))).mul
          (prefixKeys true (keyedFold n (patternTerm p.2 (fun _ => 0)))) = _
        rw [ih p.1,ih p.2]
        simp only [prefixKeys,map_pattern]
        rfl

/-- Original variable keys are translated by their exact table ordinal. -/
def ordinalTerm (keys : List VariableKey) : Term VariableKey → TermN :=
  FreeMagma.map (Sum.map id (fun x => @List.idxOf VariableKey instBEqOfDecidableEq x keys))

private theorem ordinal_term_prim : Primrec₂ ordinalTerm := by
  have hl : Primrec₂ (fun (keys : List VariableKey) (a : Bool ⊕ VariableKey) =>
      Sum.map id (fun x => @List.idxOf VariableKey instBEqOfDecidableEq x keys) a) := by
    refine Primrec.sumCasesOn Primrec.snd (Primrec.sumInl.comp Primrec.snd).to₂ ?_
    have hfst : Primrec (fun p :
        (List VariableKey × (Bool ⊕ VariableKey)) × VariableKey => p.1.1) :=
      Primrec.fst.comp Primrec.fst
    have hsnd : Primrec (fun p :
        (List VariableKey × (Bool ⊕ VariableKey)) × VariableKey => p.2) :=
      Primrec.snd
    show Primrec (fun p : (List VariableKey × (Bool ⊕ VariableKey)) × VariableKey =>
      (Sum.inr (@List.idxOf VariableKey instBEqOfDecidableEq p.2 p.1.1) : Bool ⊕ Nat))
    exact ((Primrec.sumInr (α := Bool) (β := Nat)).comp
      ((Primrec.list_idxOf (α := VariableKey)).comp hsnd hfst))
  have htree : Primrec₂ (fun (keys : List VariableKey) (a : Bool ⊕ VariableKey) =>
      FreeMagma.of (Sum.map id (fun x : VariableKey => @List.idxOf VariableKey instBEqOfDecidableEq x keys) a)) :=
    (tree_of_prim (A := Bool ⊕ Nat)).comp₂ hl
  exact uniform_tree_fold
    (fun (keys : List VariableKey) (a : Bool ⊕ VariableKey) =>
      FreeMagma.of (Sum.map id (fun x : VariableKey => @List.idxOf VariableKey instBEqOfDecidableEq x keys) a))
    (fun (_ : List VariableKey) (p : TermN × TermN) => p.1.mul p.2)
    htree
    (tree_mul_prim.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

abbrev SyntaxInput := List Nat × List PatternWord × List VariableKey

/-- Missing class words and malformed pattern constructor words are rejected. -/
def oldCode (a : SyntaxInput) (n : Nat) : Option TermN := do
  let w ← a.2.1[a.1.idxOf n]?
  let t ← parse w
  some (ordinalTerm a.2.2 (keyedFold n t))

private theorem old_code_prim : Primrec₂ oldCode := by
  apply Primrec₂.mk
  change Primrec (fun p : SyntaxInput × Nat => do
    let w ← p.1.2.1[p.1.1.idxOf p.2]?
    let t ← parse w
    some (ordinalTerm p.1.2.2 (keyedFold p.2 t)))
  have hidx : Primrec (fun p : SyntaxInput × Nat => p.1.1.idxOf p.2) :=
    by
      have hfst : Primrec (fun p : SyntaxInput × Nat => p.1.1) :=
        Primrec.fst.comp Primrec.fst
      have hsnd : Primrec (fun p : SyntaxInput × Nat => p.2) := Primrec.snd
      exact (Primrec.list_idxOf (α := Nat)).comp hsnd hfst
  have hget : Primrec (fun p : SyntaxInput × Nat => p.1.2.1[p.1.1.idxOf p.2]?) :=
    Primrec.list_getElem?.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) hidx
  refine Primrec.option_bind hget ?_
  refine Primrec.option_bind (parse_prim.comp Primrec.snd) ?_
  let Final := ((SyntaxInput × Nat) × PatternWord) × TermN
  have h1 : Primrec (fun p : Final => p.1) := Primrec.fst
  have h2 : Primrec (fun p : Final => p.1.1) := Primrec.fst.comp h1
  have h3 : Primrec (fun p : Final => p.1.1.1) := Primrec.fst.comp h2
  have h4 : Primrec (fun p : Final => p.1.1.1.2) := Primrec.snd.comp h3
  have hkeys : Primrec (fun p : Final => p.1.1.1.2.2) := Primrec.snd.comp h4
  have hn : Primrec (fun p : Final => p.1.1.2) := Primrec.snd.comp h2
  have ht : Primrec (fun p : Final => p.2) := Primrec.snd
  have hkeyed : Primrec (fun p : Final => keyedFold p.1.1.2 p.2) :=
    keyed_fold_prim.comp hn ht
  have hterm : Primrec (fun p : Final => ordinalTerm p.1.1.1.2.2
      (keyedFold p.1.1.2 p.2)) := ordinal_term_prim.comp hkeys hkeyed
  exact Primrec.option_some.comp hterm


/-- A finite cell keeps the native class order and original structural keys. -/
def cellSyntax {C : LiteralRow} {d : Nat} (η : Patterns C d) : SyntaxInput :=
  ((NativeWholeRowService.classList C).map Subtype.val, familyWord η,
    (variableList η).map variableKey)

def cellTerm {C : LiteralRow} {d : Nat} (η : Patterns C d)
    (t : Term (Variables η)) : TermN :=
  ordinalTerm ((variableList η).map variableKey)
    (FreeMagma.map (Sum.map id variableKey) t)

private theorem class_index (C : LiteralRow) (b : NativeCutFibers.Classes C) :
    ((NativeWholeRowService.classList C).map Subtype.val).idxOf b.val =
      (NativeWholeRowService.classList C).idxOf b := by
  unfold List.idxOf
  rw [List.findIdx_map]
  congr 1

private theorem old_code_exact {C : LiteralRow} {d : Nat} (η : Patterns C d)
    (b : NativeCutFibers.Classes C) :
    oldCode (cellSyntax η) b.val = some (cellTerm η (oldTerm η b)) := by
  unfold oldCode cellSyntax familyWord
  rw [class_index, List.getElem?_map, List.getElem?_idxOf (NativeWholeRowService.class_complete C b)]
  change (parse (patternWord (η b)) >>= fun t =>
    some (ordinalTerm ((variableList η).map variableKey) (keyedFold b.val t))) = _
  rw [pattern_word, (preorder_codec _ _).mpr rfl]
  change some (ordinalTerm _ (keyedFold b.val (patternTerm (η b) (fun _ => 0)))) = _
  rw [keyed_fold_exact]
  simp only [cellTerm, oldTerm, map_pattern]
  rfl

/-- Expansion uses the same old-class term at every retained occurrence. -/
def wholeCode (a : SyntaxInput) (C : LiteralRow) : Option TermN :=
  (@FreeMagma.lift (Bool ⊕ Nat) (Option TermN)
    ⟨fun l r => do
      let l ← l
      let r ← r
      some (l.mul r)⟩
    (fun b => match b with
      | .inl b => some (.of (.inl b))
      | .inr n => oldCode a n)) C

theorem whole_code_prim : Primrec₂ wholeCode := by
  have leaf : Primrec₂ (fun (a : SyntaxInput) (b : Bool ⊕ Nat) =>
      Sum.elim (fun b => (some (.of (.inl b)) : Option TermN)) (oldCode a) b) := by
    refine Primrec.sumCasesOn Primrec.snd ?_ ?_
    · exact (Primrec.option_some.comp
        (tree_of_prim.comp (Primrec.sumInl.comp Primrec.snd))).to₂
    · exact (old_code_prim.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  have node : Primrec₂ (fun (_ : SyntaxInput) (p : Option TermN × Option TermN) => do
      let l ← p.1
      let r ← p.2
      some (l.mul r)) := by
    apply Primrec₂.mk
    refine Primrec.option_bind (Primrec.fst.comp Primrec.snd) ?_
    refine Primrec.option_bind (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) ?_
    exact (Primrec.option_some.comp
      (tree_mul_prim.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
  have h := uniform_tree_fold _ _ leaf node
  exact h.of_eq (fun a C => by
    have hleaf :
        (fun b : Bool ⊕ Nat =>
          Sum.elim (fun b => (some (.of (.inl b)) : Option TermN)) (oldCode a) b) =
        (fun b => match b with
          | .inl b => some (.of (.inl b))
          | .inr n => oldCode a n) := by
      funext b
      cases b <;> rfl
    simp only [wholeCode, hleaf])

theorem whole_code_exact {C : LiteralRow} {d : Nat} (η : Patterns C d) :
    wholeCode (cellSyntax η) C = some (cellTerm η (wholeTerm η)) := by
  have general (t : LiteralRow) (ht : NativeCutFibers.labels t ⊆ NativeCutFibers.labels C) :
      wholeCode (cellSyntax η) t = some (cellTerm η
        (FreeMagma.lift (fun b => match b with
          | .inl b => .of (.inl b)
          | .inr n => if h : n ∈ NativeCutFibers.labels C then
              oldTerm η ⟨n,h⟩ else .of (.inl true)) t)) := by
    induction t with
    | of b => cases b with
      | inl b => rfl
      | inr n =>
          have hn : n ∈ NativeCutFibers.labels C := ht (by simp [NativeCutFibers.labels])
          simpa only [wholeCode, FreeMagma.lift_of, dif_pos hn] using
            old_code_exact η ⟨n,hn⟩
    | mul l r hl hr =>
        have hl' := hl (fun n hn => ht (Finset.mem_union_left _ hn))
        have hr' := hr (fun n hn => ht (Finset.mem_union_right _ hn))
        change (do
          let l' ← wholeCode (cellSyntax η) l
          let r' ← wholeCode (cellSyntax η) r
          some (l'.mul r')) = _
        rw [hl', hr']
        rfl
  exact general C (Finset.Subset.refl _)

/-- Each ordered pair represents an old disequality, never a solver equation. -/
def namePairs (names : List Nat) : List (Nat × Nat) :=
  names.flatMap (fun b => (names.filter (fun c => b < c)).map (fun c => (b,c)))

/-- Finite traversal retains order and rejects a malformed component. -/
def traverseCodes {A B : Type} (f : A → Option B) : List A → Option (List B)
  | [] => some []
  | a :: xs => do
      let b ← f a
      let bs ← traverseCodes f xs
      some (b :: bs)

private def traversalStep {A B : Type} (f : A → Option B)
    (s : List A × Option (List B)) : List A × Option (List B) :=
  (s.1.tail, do
    let a ← s.1.head?
    let b ← f a
    let bs ← s.2
    some (b :: bs))

private theorem traversal_cursor {A B : Type} (f : A → Option B)
    (xs : List A) (acc : Option (List B)) :
    (traversalStep f)^[xs.length] (xs,acc) =
      ([],xs.foldl (fun bs a => do
        let b ← f a
        let bs ← bs
        some (b :: bs)) acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.length_cons, Function.iterate_succ_apply]
      change (traversalStep f)^[xs.length] (xs,_) = _
      exact ih _

theorem traverse_computable {A B X : Type} [Primcodable A]
    [Primcodable B] [Primcodable X] (f : X → A → Option B)
    (hf : Computable₂ f) : Computable₂ (fun x xs => traverseCodes (f x) xs) := by
  have step : Computable₂ (fun (x : X) (s : List A × Option (List B)) =>
      traversalStep (f x) s) := by
    unfold traversalStep
    refine ((Primrec.list_tail.to_comp).comp (Computable.fst.comp Computable.snd)).pair ?_
    refine Computable.option_bind
      ((Primrec.list_head?.to_comp).comp (Computable.fst.comp Computable.snd)) ?_
    change Computable (fun p : (X × (List A × Option (List B))) × A => do
      let b ← f p.1.1 p.2
      let bs ← p.1.2.2
      some (b :: bs))
    refine Computable.option_bind (hf.comp (Computable.fst.comp Computable.fst) Computable.snd) ?_
    have hmap : Computable (fun p : ((X × (List A × Option (List B))) × A) × B =>
        p.1.1.2.2.map (fun bs => p.2 :: bs)) := by
      refine Computable.option_map
        (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))) ?_
      change Computable (fun p :
        (((X × (List A × Option (List B))) × A) × B) × List B => p.1.2 :: p.2)
      exact Computable.list_cons.comp (Computable.snd.comp Computable.fst) Computable.snd
    apply Computable₂.mk
    exact hmap.of_eq (fun p => by cases p.1.1.2.2 <;> rfl)
  have hrec : Computable (fun p : X × List A =>
      Nat.rec (motive := fun _ => List A × Option (List B))
        (p.2.reverse,some []) (fun _ s => traversalStep (f p.1) s) p.2.length) :=
    Computable.nat_rec (Computable.list_length.comp Computable.snd)
    ((Computable.list_reverse.comp Computable.snd).pair (Computable.const (some ([] : List B))))
    ((step.comp (Computable.fst.comp Computable.fst)
      (Computable.snd.comp Computable.snd)).to₂)
  apply Computable₂.mk
  refine (Computable.snd.comp hrec).of_eq ?_
  intro p
  have iter (n : Nat) :
      Nat.rec (motive := fun _ => List A × Option (List B))
        (p.2.reverse,some []) (fun _ s => traversalStep (f p.1) s) n =
      (traversalStep (f p.1))^[n] (p.2.reverse,some []) := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Nat.rec_add_one, ih, Function.iterate_succ_apply']
  rw [iter]
  rw [← List.length_reverse (as := p.2), traversal_cursor]
  simp only [List.foldl_reverse]
  have fold (xs : List A) :
      xs.foldr (fun a bs => do
        let b ← f p.1 a
        let bs ← bs
        some (b :: bs)) (some []) = traverseCodes (f p.1) xs := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [List.foldr_cons, traverseCodes, ih]
  exact fold _

theorem traverse_map_exact {A B D : Type} (f : B → Option D)
    (g : A → B) (h : A → D) (xs : List A) (exact : ∀ x ∈ xs, f (g x) = some (h x)) :
    traverseCodes f (xs.map g) = some (xs.map h) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, traverseCodes, exact x (List.mem_cons_self)]
      rw [ih (fun y hy => exact y (List.mem_cons_of_mem x hy))]
      rfl

/-- Delta uses all class pairs in the original numeric class order. -/
def deltaCode (a : SyntaxInput) : Option (Equations Nat) :=
  traverseCodes (fun p => do
    let l ← oldCode a p.1
    let r ← oldCode a p.2
    some (l,r)) (namePairs a.1)

private theorem name_pairs_exact (C : LiteralRow) :
    namePairs ((NativeWholeRowService.classList C).map Subtype.val) =
      ((NativeWholeRowService.classList C).flatMap (fun b =>
        ((NativeWholeRowService.classList C).filter (fun c => b.val < c.val)).map
          (fun c => (b,c)))).map (fun p => (p.1.val,p.2.val)) := by
  simp only [namePairs, List.flatMap_map, List.filter_map, List.map_map,
    List.map_flatMap, Function.comp_def]

theorem delta_code_exact {C : LiteralRow} {d : Nat} (η : Patterns C d) :
    deltaCode (cellSyntax η) = some ((NativeWholeRowService.delta η).map
      (fun e => (cellTerm η e.1,cellTerm η e.2))) := by
  unfold deltaCode
  rw [show (cellSyntax η).1 =
    (NativeWholeRowService.classList C).map Subtype.val from rfl, name_pairs_exact]
  rw [traverse_map_exact _ _
    (fun p => (cellTerm η (oldTerm η p.1),cellTerm η (oldTerm η p.2)))]
  · simp only [NativeWholeRowService.delta, List.map_flatMap, List.map_map,
      Function.comp_def]
  · intro p hp
    rw [old_code_exact, old_code_exact]
    rfl

private theorem key_index (keys : List VariableKey) (x : VariableKey) :
    @List.idxOf VariableKey instBEqOfDecidableEq x keys = keys.idxOf x := by
  unfold List.idxOf
  congr 1
  funext y
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]

private theorem cell_term_native (C : LiteralRow) (Q : CutSet) (H : History)
    (η : Patterns C (NativeHistoryCells.requiredDepth Q H)) (t : Term (Variables η)) :
    UniformNativeUnification.Code.nativeTerm (cellTerm η t) = encode (presentation η) t := by
  induction t using FreeMagma.recOn with
  | of a => cases a with
    | inl b => rfl
    | inr x =>
        change LMonoTy.ftvar (NativeTermUnification.finName
          (@List.idxOf VariableKey instBEqOfDecidableEq (variableKey x)
            ((variableList η).map variableKey))) =
            LMonoTy.ftvar ((presentation η).code x)
        rw [key_index]
        exact congrArg LMonoTy.ftvar ((uniform_variable_materializer.2 C Q H 0).2 η x).symm
  | mul l r hl hr =>
      change NativeTermUnification.pair
        (UniformNativeUnification.Code.nativeTerm (cellTerm η l))
        (UniformNativeUnification.Code.nativeTerm (cellTerm η r)) =
          NativeTermUnification.pair (encode (presentation η) l) (encode (presentation η) r)
      rw [hl,hr]

private theorem cell_term_injective (C : LiteralRow) (Q : CutSet) (H : History)
    (η : Patterns C (NativeHistoryCells.requiredDepth Q H)) :
    Function.Injective (cellTerm η) := by
  intro s t h
  apply NativeTermUnification.encode_injective (presentation η)
  rw [← cell_term_native C Q H η s, ← cell_term_native C Q H η t, h]

private theorem name_pairs_prim : Primrec namePairs := by
  have filt : Primrec₂ (fun (names : List Nat) (b : Nat) =>
      names.filter (fun c => b < c)) :=
    PrimrecRel.listFilter (Primrec.nat_lt.comp₂ Primrec₂.right Primrec₂.left)
  unfold namePairs
  refine Primrec.list_flatMap Primrec.id ?_
  exact (Primrec.list_map filt
    ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂).to₂

theorem delta_code_computable : Computable deltaCode := by
  have hp : Computable₂ (fun (a : SyntaxInput) (p : Nat × Nat) => do
      let l ← oldCode a p.1
      let r ← oldCode a p.2
      some (l,r)) := by
    apply Computable₂.mk
    refine Computable.option_bind
      (old_code_prim.to_comp.comp Computable.fst (Computable.fst.comp Computable.snd)) ?_
    refine Computable.option_bind
      (old_code_prim.to_comp.comp (Computable.fst.comp Computable.fst)
        (Computable.snd.comp (Computable.snd.comp Computable.fst))) ?_
    exact (Computable.option_some.comp
      ((Computable.snd.comp Computable.fst).pair Computable.snd)).to₂
  exact (traverse_computable _ hp).comp Computable.id
    (name_pairs_prim.to_comp.comp Computable.fst)

theorem syntax_legal_code_exact (C : LiteralRow) (Q : CutSet) (H : History)
    (η : Patterns C (NativeHistoryCells.requiredDepth Q H)) :
    (deltaCode (cellSyntax η)).map (fun Δ => Δ.all (fun e => e.1 != e.2)) =
      some (decide (NativeHistoryCells.syntaxLegal η)) := by
  rw [delta_code_exact, Option.map_some]
  apply congrArg some
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_map, List.all_eq_true, Function.comp_def, bne_iff_ne, decide_eq_true_eq]
  have member (b c : NativeCutFibers.Classes C) (lt : b.val < c.val) :
      (oldTerm η b,oldTerm η c) ∈ NativeWholeRowService.delta η := by
    exact List.mem_flatMap.mpr ⟨b,NativeWholeRowService.class_complete C b,List.mem_map.mpr
      ⟨c,List.mem_filter.mpr ⟨NativeWholeRowService.class_complete C c,by simpa using lt⟩,rfl⟩⟩
  constructor
  · intro pass b c ne eq
    have vn : b.val ≠ c.val := fun h => ne (Subtype.ext h)
    rcases lt_or_gt_of_ne vn with lt | lt
    · exact pass _ (member b c lt) (congrArg (cellTerm η) eq)
    · exact pass _ (member c b lt) (congrArg (cellTerm η) eq.symm)
  · intro legal p hp eq
    obtain ⟨b,hb,hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
    have lt : b.val < c.val := by simpa using (List.mem_filter.mp hc).2
    have ne : b ≠ c := fun h => (Nat.ne_of_lt lt) (congrArg Subtype.val h)
    exact legal b c ne (cell_term_injective C Q H η eq)

/-- Original variable ordinals label the native ordered ground bindings. -/
def nativePairCode {C : LiteralRow} {d : Nat} (η : Patterns C d)
    (p : PairPlan (Variables η)) : PairCode :=
  (p.first,p.second,kindCode p.kind,p.bindings.map (fun b =>
    (((variableList η).map variableKey).idxOf (variableKey b.1),word b.2)))

private def cellEquiv {C : LiteralRow} {d : Nat} (η : Patterns C d) :
    Variables η ≃ Fin (variableList η).length :=
  (List.Nodup.getEquivOfForallMemList (variableList η)
    (by unfold variableList; exact List.nodup_dedup _)
    (NativeWholeRowService.variable_complete η)).symm

private theorem cell_equiv_index (C : LiteralRow) (Q : CutSet) (H : History)
    (η : Patterns C (NativeHistoryCells.requiredDepth Q H)) (x : Variables η) :
    (cellEquiv η x).val = ((variableList η).map variableKey).idxOf (variableKey x) := by
  have h := (uniform_variable_materializer.2 C Q H 0).2 η x
  change NativeTermUnification.finName (cellEquiv η x).val = _ at h
  have hl := congrArg (fun s : String => s.toList.length) h
  simpa only [NativeTermUnification.finName,String.toList_ofList,List.length_replicate] using hl

private theorem cell_term_lift (C : LiteralRow) (Q : CutSet) (H : History)
    (η : Patterns C (NativeHistoryCells.requiredDepth Q H)) (t : Term (Variables η)) :
    cellTerm η t = liftTerm (renameTerm (cellEquiv η) t) := by
  induction t using FreeMagma.recOn with
  | of a => cases a with
    | inl b => rfl
    | inr x =>
        change FreeMagma.of (Sum.inr (@List.idxOf VariableKey instBEqOfDecidableEq
          (variableKey x) ((variableList η).map variableKey)) : Bool ⊕ Nat) =
          FreeMagma.of (Sum.inr (cellEquiv η x).val : Bool ⊕ Nat)
        rw [key_index,cell_equiv_index C Q H η x]
  | mul l r hl hr => exact congrArg₂ FreeMagma.mul hl hr

theorem native_pair_exact (C : LiteralRow) (Q : CutSet) (H : History)
    (η : Patterns C (NativeHistoryCells.requiredDepth Q H))
    (Δ : Equations (Variables η)) (q r : Address) (s t : Term (Variables η)) :
    codedPlan ((variableList η).length,
      Δ.map (fun z => (cellTerm η z.1,cellTerm η z.2)),q,r,cellTerm η s,cellTerm η t) =
      some (nativePairCode η (planPair (presentation η) Δ q r s t)) := by
  have hc := coded_plan_exact (variableList η).length
    (Δ.map (fun z => (renameTerm (cellEquiv η) z.1,renameTerm (cellEquiv η) z.2)))
    q r (renameTerm (cellEquiv η) s) (renameTerm (cellEquiv η) t)
  simp only [liftEquations,List.map_map,Function.comp_def] at hc
  simp only [cell_term_lift C Q H η]
  rw [hc,plan_transport]
  apply congrArg some
  change ordinalPlan (fun x => (cellEquiv η x).val)
    (planPair (presentation η) Δ q r s t) = _
  simp only [ordinalPlan,nativePairCode,cell_equiv_index C Q H η]

theorem cell_term_rename {C : LiteralRow} {d : Nat} (η : Patterns C d)
    (t : Term (Variables η)) :
    cellTerm η t = renameTerm
      (fun x => ((variableList η).map variableKey).idxOf (variableKey x)) t := by
  induction t using FreeMagma.recOn with
  | of a => cases a with
    | inl b => rfl
    | inr x =>
        change FreeMagma.of (Sum.inr (@List.idxOf VariableKey instBEqOfDecidableEq
          (variableKey x) ((variableList η).map variableKey)) : Bool ⊕ Nat) = _
        rw [key_index]
        rfl
  | mul l r hl hr => exact congrArg₂ FreeMagma.mul hl hr


end D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformAnalysis
