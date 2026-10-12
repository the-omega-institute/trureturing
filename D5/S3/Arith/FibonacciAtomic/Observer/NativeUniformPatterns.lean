/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPatterns
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Fixed structural constructor words for uniform native pattern materialization. -/

import D5.S0.Computability.PreorderTreeEvaluation
import D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowPlan
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformPatterns

open D5.S0.Computability.PreorderTreeEvaluation
open NativeDepthPatterns (Pattern Frontier frontierAddress History)
open NativeWholeRowService (patternList frontierList classList)
open ActualTreeReadoutAcquisition (Address Reply)
open ActualCutPartitionRecovery (LiteralRow)
open NativeSerialDepth (RowWord rowWord)

abbrev Token := Option (Bool ⊕ Nat)
abbrev PatternWord := List Token

def branchWord (l r : PatternWord) : PatternWord := none :: (l ++ r)

/-- A frontier token contains its syntactic ordinal placeholder, never a tree value. -/
def patternWord : {d : Nat} → Pattern d → PatternWord
  | 0, _ => [some (.inr 0)]
  | _+1, .inl b => [some (.inl b)]
  | _+1, .inr p => branchWord (patternWord p.1) (patternWord p.2)

/-- The factory has one fixed first-order domain, with unbounded depth. -/
def pairWords (ws : List PatternWord) : List PatternWord :=
  ws.flatMap (fun l => ws.map (branchWord l))

def patternWords : Nat → List PatternWord
  | 0 => [[some (.inr 0)]]
  | d+1 => [[some (.inl false)], [some (.inl true)]] ++ pairWords (patternWords d)

private theorem branch_primrec : Primrec₂ branchWord :=
  Primrec.list_cons.comp (Primrec.const none) (Primrec.list_append.comp Primrec.fst Primrec.snd)

private theorem pair_words_primrec : Primrec pairWords := by
  unfold pairWords
  refine Primrec.list_flatMap (g := fun ws l => ws.map (branchWord l)) Primrec.id ?_
  exact Primrec.list_map Primrec.fst
    (branch_primrec.comp₂ (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right)

private theorem pattern_words_primrec : Primrec patternWords := by
  have next : Primrec₂ (fun (_ : Nat) (ws : List PatternWord) =>
      [[some (.inl false)], [some (.inl true)]] ++ pairWords ws) :=
    Primrec.list_append.comp (Primrec.const _) (pair_words_primrec.comp Primrec.snd)
  have hrec : Primrec (Nat.rec [[some (.inr 0)]] (fun (_ : Nat) ws =>
      [[some (.inl false)], [some (.inl true)]] ++ pairWords ws)) :=
    Primrec.nat_rec₁ [[some (.inr 0)]] next
  have heq (d : Nat) :
      Nat.rec [[some (.inr 0)]] (fun (_ : Nat) ws =>
        [[some (.inl false)], [some (.inl true)]] ++ pairWords ws) d = patternWords d := by
    induction d with
    | zero => rfl
    | succ d ih =>
        simpa only [Nat.rec_add_one, patternWords] using
          (congrArg (fun ws => [[some (.inl false)], [some (.inl true)]] ++ pairWords ws) ih)
  exact hrec.of_eq heq

private theorem pattern_words_exact (d : Nat) :
    patternWords d = (patternList d).map patternWord := by
  induction d with
  | zero => rfl
  | succ d ih =>
      have leaf (b : Bool) : patternWord (d := d+1) (Sum.inl b) = [some (.inl b)] := rfl
      have pair (l r : Pattern d) : patternWord (d := d+1) (Sum.inr (l,r)) =
          branchWord (patternWord l) (patternWord r) := rfl
      simp only [Pattern] at *
      simp only [patternWords, patternList, List.map_append, pairWords, ih,
        List.flatMap_map, List.map_flatMap, List.map_map, List.map_cons, List.map_nil,
        Function.comp_def, leaf, pair]

/-- The primitive recursive factory returns the exact native enumeration in its
existing order. The computability assertion precedes the depth quantifier. -/
theorem uniform_pattern_words :
    Primrec patternWords ∧ ∀ d, patternWords d = (patternList d).map patternWord :=
  ⟨pattern_words_primrec, pattern_words_exact⟩

/-- Leaves end a branch; only reached frontier placeholders contribute addresses. -/
def frontierLeaf : Bool ⊕ Nat → List Address
  | .inl _ => []
  | .inr _ => [[]]

def frontierNode (p : List Address × List Address) : List Address :=
  p.1.map (false :: ·) ++ p.2.map (true :: ·)

def frontierWords (w : PatternWord) : Option (List Address) :=
  evaluate frontierLeaf (fun l r => frontierNode (l,r)) w

private theorem frontier_leaf_primrec : Primrec frontierLeaf := by
  unfold frontierLeaf
  exact (Primrec.sumCasesOn (Primrec.id : Primrec (id : Bool ⊕ Nat → Bool ⊕ Nat))
    (Primrec.const ([] : List Address)).to₂ (Primrec.const ([[]] : List Address)).to₂).of_eq
      (fun x => by cases x <;> rfl)

private theorem frontier_node_primrec : Primrec frontierNode := by
  unfold frontierNode
  exact Primrec.list_append.comp
    (Primrec.list_map Primrec.fst (Primrec.list_cons.comp (Primrec.const false) Primrec.snd))
    (Primrec.list_map Primrec.snd (Primrec.list_cons.comp (Primrec.const true) Primrec.snd))

private def patternTree : {d : Nat} → Pattern d → FreeMagma (Bool ⊕ Nat)
  | 0, _ => .of (.inr 0)
  | _+1, .inl b => .of (.inl b)
  | _+1, .inr p => .mul (patternTree p.1) (patternTree p.2)

private theorem pattern_tree_word {d : Nat} (p : Pattern d) :
    word (patternTree p) = patternWord p := by
  induction d with
  | zero => rfl
  | succ d ih => cases p with
    | inl b => rfl
    | inr p => simp only [patternTree, word, patternWord, branchWord, ih]

private theorem pattern_tree_frontier {d : Nat} (p : Pattern d) :
    (@FreeMagma.lift (Bool ⊕ Nat) (List Address)
      ⟨fun l r => frontierNode (l,r)⟩ frontierLeaf) (patternTree p) =
    (frontierList p).map (frontierAddress p) := by
  induction d with
  | zero => rfl
  | succ d ih => cases p with
    | inl b => rfl
    | inr p =>
        change frontierNode ((@FreeMagma.lift (Bool ⊕ Nat) (List Address)
          ⟨fun l r => frontierNode (l,r)⟩ frontierLeaf) (patternTree p.1),
          (@FreeMagma.lift (Bool ⊕ Nat) (List Address)
          ⟨fun l r => frontierNode (l,r)⟩ frontierLeaf) (patternTree p.2)) = _
        rw [ih p.1, ih p.2]
        simp only [Frontier] at *
        simp only [frontierNode, frontierList, List.map_append, List.map_map,
          Function.comp_def, frontierAddress]

/-- The same fixed parser recovers every actual reached frontier in left-to-right
order, including the depth-zero hole and early leaves with empty frontiers. -/
theorem uniform_frontier_words :
    Primrec frontierWords ∧ ∀ d (p : Pattern d),
      frontierWords (patternWord p) = some ((frontierList p).map (frontierAddress p)) := by
  obtain ⟨effective, exactFold⟩ := uniform_preorder_evaluation
    (fun (_ : Nat) a => frontierLeaf a) (fun (_ : Nat) p => frontierNode p)
    (frontier_leaf_primrec.comp Primrec.snd) (frontier_node_primrec.comp Primrec.snd)
  constructor
  · exact effective.comp (Primrec.const 0) Primrec.id
  · intro d p
    rw [← pattern_tree_word p]
    exact (exactFold 0 (patternTree p)).trans (congrArg some (pattern_tree_frontier p))

/-- Cartesian vectors preserve the exact left-to-right native enumeration. -/
def vectors (ws : List PatternWord) : Nat → List (List PatternWord)
  | 0 => [[]]
  | n+1 => ws.flatMap (fun w => (vectors ws n).map (w :: ·))

private theorem vectors_primrec : Primrec₂ vectors := by
  have next : Primrec₂ (fun (ws : List PatternWord)
      (p : Nat × List (List PatternWord)) =>
      ws.flatMap (fun w => p.2.map (w :: ·))) := by
    refine Primrec.list_flatMap
      (g := fun (p : List PatternWord × (Nat × List (List PatternWord))) (w : PatternWord) =>
        p.2.2.map (w :: ·)) Primrec.fst ?_
    exact Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have hrec : Primrec₂ (fun (ws : List PatternWord) (n : Nat) =>
      Nat.rec (motive := fun _ => List (List PatternWord)) [[]] (fun _ vs => ws.flatMap (fun w => vs.map (w :: ·))) n) :=
    Primrec.nat_rec (Primrec.const [[]]) next
  have heq (ws : List PatternWord) (n : Nat) :
      Nat.rec (motive := fun _ => List (List PatternWord)) [[]] (fun _ vs => ws.flatMap (fun w => vs.map (w :: ·))) n = vectors ws n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Nat.rec_add_one, vectors, ih]
  exact hrec.of_eq heq

private theorem pi_vectors {I A : Type} [DecidableEq I] (xs : List I)
    (nd : xs.Nodup) (ys : List A) (code : A → PatternWord) :
    (xs.pi (fun _ => ys)).map (fun f =>
      xs.attach.map (fun x => code (f x.val x.property))) =
      vectors (ys.map code) xs.length := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      have ni : i ∉ xs := (List.nodup_cons.mp nd).1
      have nx : xs.Nodup := (List.nodup_cons.mp nd).2
      have projection (y : A) (f : ∀ j ∈ xs, A) :
          (i :: xs).attach.map (fun x => code (List.Pi.cons i xs y f x.val x.property)) =
          code y :: xs.attach.map (fun x => code (f x.val x.property)) := by
        simp only [List.attach_cons, List.map_cons, List.map_map]
        congr 1
        · simp [List.Pi.cons_def]
        · apply List.map_congr_left
          intro x hx
          have ne : x.val ≠ i := fun h => ni (h ▸ x.property)
          simp [List.Pi.cons_def, ne]
      calc
        _ = ys.flatMap (fun y => (xs.pi (fun _ => ys)).map (fun f =>
              code y :: xs.attach.map (fun x => code (f x.val x.property)))) := by
          simp only [List.pi_cons, List.map_flatMap, List.map_map, Function.comp_def,
            projection]
        _ = (ys.map code).flatMap (fun w =>
              (vectors (ys.map code) xs.length).map (w :: ·)) := by
          rw [← ih nx]
          simp only [List.flatMap_map, List.map_map, Function.comp_def]
        _ = vectors (ys.map code) (i :: xs).length := rfl

/-- A pattern family is encoded as a vector in the unchanged class order. -/
def familyWord {C : LiteralRow} {d : Nat} (η : NativeHistoryCells.Patterns C d) :
    List PatternWord := (classList C).map (fun b => patternWord (η b))

private theorem class_list_nodup (C : LiteralRow) : (classList C).Nodup := by
  unfold classList
  apply List.Nodup.map
  · intro x y h
    apply Subtype.ext
    exact congrArg (fun z : NativeCutFibers.Classes C => z.val) h
  · exact ((NativeCutFibers.labels C).sort_nodup (· ≤ ·)).attach

/-- The one vector factory is primitive recursive for all finite class counts
and depths. Its output is exactly the changing native allPatterns family. -/
theorem uniform_pattern_families :
    Primrec₂ (fun (n d : Nat) => vectors (patternWords d) n) ∧
    ∀ C d, vectors (patternWords d) (classList C).length =
      (NativeWholeRowService.allPatterns C d).map familyWord := by
  constructor
  · exact vectors_primrec.comp₂ (uniform_pattern_words.1.comp Primrec.snd).to₂ Primrec₂.left
  · intro C d
    rw [uniform_pattern_words.2 d]
    rw [← pi_vectors (classList C) (class_list_nodup C) (patternList d) patternWord]
    unfold NativeWholeRowService.allPatterns familyWord
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro f hf
    conv_rhs => rw [← List.attach_map_val]

end D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformPatterns
