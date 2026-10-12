/- GID: D5/S0/Computability/PreorderTreeEvaluation
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Uniform first-order evaluation of finite ordered tree constructor words. -/

import Mathlib.Algebra.Free
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Computability.PreorderTreeEvaluation

abbrev Word (A : Type) := List (Option A)

def word {A : Type} : FreeMagma A → Word A
  | .of a => [some a]
  | .mul l r => none :: (word l ++ word r)

/-- A branch requires two complete children. -/
def pop {B : Type} (node : B → B → B) (s : List B) : Option (List B) :=
  List.casesOn s none fun l rest =>
    List.casesOn rest none fun r tail => some (node l r :: tail)

/-- Right-to-left evaluation rejects an incomplete constructor word. -/
def step {A B : Type} (leaf : A → B) (node : B → B → B)
    (token : Option A) (s : Option (List B)) : Option (List B) :=
  s.bind fun s => Option.casesOn token (pop node s) (fun a => some (leaf a :: s))

def stack {A B : Type} (leaf : A → B) (node : B → B → B)
    (w : Word A) (s : List B) : Option (List B) :=
  w.foldr (step leaf node) (some s)

def finish {B : Type} (s : List B) : Option B :=
  List.casesOn s none fun b tail => List.casesOn tail (some b) (fun _ _ => none)

def evaluate {A B : Type} (leaf : A → B) (node : B → B → B)
    (w : Word A) : Option B :=
  (stack leaf node w []).bind finish

private theorem pop_primrec {B X : Type} [Primcodable B] [Primcodable X]
    {node : X → B × B → B} (hn : Primrec₂ node) :
    Primrec₂ (fun x s => pop (fun l r => node x (l,r)) s) := by
  change Primrec (fun p : X × List B => pop (fun l r => node p.1 (l,r)) p.2)
  unfold pop
  refine Primrec.list_casesOn (h := fun p q =>
    List.casesOn q.2 none (fun r tail => some (node p.1 (q.1,r) :: tail)))
    Primrec.snd (Primrec.const none) ?_
  change Primrec (fun p : (X × List B) × (B × List B) =>
    (List.casesOn p.2.2 none (fun r tail => some (node p.1.1 (p.2.1,r) :: tail)) : Option (List B)))
  refine Primrec.list_casesOn (h := fun (p : (X × List B) × (B × List B)) (q : B × List B) =>
    some (node p.1.1 (p.2.1,q.1) :: q.2))
    (Primrec.snd.comp Primrec.snd) (Primrec.const none) ?_
  change Primrec (fun p : ((X × List B) × (B × List B)) × (B × List B) =>
    some (node p.1.1.1 (p.1.2.1,p.2.1) :: p.2.2))
  exact Primrec.option_some.comp (Primrec.list_cons.comp
    (hn.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair (Primrec.fst.comp Primrec.snd)))
    (Primrec.snd.comp Primrec.snd))

private theorem step_primrec {A B X : Type} [Primcodable A] [Primcodable B]
    [Primcodable X] {leaf : X → A → B} {node : X → B × B → B}
    (hl : Primrec₂ leaf) (hn : Primrec₂ node) :
    Primrec₂ (fun x (p : Option A × Option (List B)) =>
      step (leaf x) (fun l r => node x (l,r)) p.1 p.2) := by
  change Primrec (fun p : X × (Option A × Option (List B)) =>
    step (leaf p.1) (fun l r => node p.1 (l,r)) p.2.1 p.2.2)
  unfold step
  refine Primrec.option_bind (g := fun p s =>
    Option.casesOn p.2.1 (pop (fun l r => node p.1 (l,r)) s)
      (fun a => some (leaf p.1 a :: s))) (Primrec.snd.comp Primrec.snd) ?_
  change Primrec (fun p : (X × (Option A × Option (List B))) × List B =>
    (Option.casesOn p.1.2.1 (pop (fun l r => node p.1.1 (l,r)) p.2)
      (fun a => some (leaf p.1.1 a :: p.2)) : Option (List B)))
  refine Primrec.option_casesOn (g := fun (p : (X × (Option A × Option (List B))) × List B) (a : A) =>
    some (leaf p.1.1 a :: p.2))
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    ((pop_primrec hn).comp (Primrec.fst.comp Primrec.fst) Primrec.snd) ?_
  change Primrec (fun p : ((X × (Option A × Option (List B))) × List B) × A =>
    some (leaf p.1.1.1 p.2 :: p.1.2))
  exact Primrec.option_some.comp (Primrec.list_cons.comp
    (hl.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
    (Primrec.snd.comp Primrec.fst))

private theorem finish_primrec {B : Type} [Primcodable B] :
    Primrec (finish : List B → Option B) := by
  unfold finish
  refine Primrec.list_casesOn (h := fun (_ : List B) q =>
    List.casesOn q.2 (some q.1) (fun _ _ => none)) Primrec.id (Primrec.const none) ?_
  change Primrec (fun p : List B × (B × List B) =>
    (List.casesOn p.2.2 (some p.2.1) (fun _ _ => none) : Option B))
  exact Primrec.list_casesOn (Primrec.snd.comp Primrec.snd)
    (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const none).to₂

private theorem stack_exact {A B : Type} (leaf : A → B) (node : B → B → B)
    (t : FreeMagma A) (s : List B) :
    stack leaf node (word t) s =
      some ((@FreeMagma.lift A B ⟨node⟩ leaf) t :: s) := by
  induction t using FreeMagma.recOn generalizing s with
  | of a => rfl
  | mul l r ihl ihr =>
      simp only [word, stack, List.foldr_cons, List.foldr_append]
      change step leaf node none ((word l).foldr (step leaf node)
        (stack leaf node (word r) s)) = _
      rw [ihr]
      change step leaf node none (stack leaf node (word l)
        ((@FreeMagma.lift A B ⟨node⟩ leaf) r :: s)) = _
      rw [ihl]
      rfl

/-- One primitive recursive evaluator works for every constructor word and every
parameter. On a tree word it gives precisely its free-magma fold. -/
theorem uniform_preorder_evaluation {A B X : Type} [Primcodable A] [Primcodable B]
    [Primcodable X] (leaf : X → A → B) (node : X → B × B → B)
    (hl : Primrec₂ leaf) (hn : Primrec₂ node) :
    Primrec₂ (fun x w => evaluate (leaf x) (fun l r => node x (l,r)) w) ∧
    ∀ (x : X) (t : FreeMagma A),
      evaluate (leaf x) (fun l r => node x (l,r)) (word t) =
        some ((@FreeMagma.lift A B ⟨fun l r => node x (l,r)⟩ (leaf x)) t) := by
  constructor
  · have hs : Primrec₂ (fun (x : X) (w : Word A) =>
        stack (leaf x) (fun l r => node x (l,r)) w []) := by
      exact Primrec.list_foldr Primrec.snd (Primrec.const (some []))
        ((step_primrec hl hn).comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)
    exact Primrec.option_bind hs (finish_primrec.comp Primrec.snd).to₂
  · intro x t
    rw [evaluate, stack_exact]
    rfl

/-- Structural decoding has no search or choice of a source tree. -/
def parse {A : Type} (w : Word A) : Option (FreeMagma A) :=
  evaluate FreeMagma.of FreeMagma.mul w

private theorem parse_stack_sound {A : Type} (w : Word A) (s t : List (FreeMagma A))
    (h : stack FreeMagma.of FreeMagma.mul w s = some t) :
    w ++ s.flatMap word = t.flatMap word := by
  induction w generalizing t with
  | nil =>
      have he : s = t := by simpa [stack] using h
      subst t
      rfl
  | cons token w ih =>
      change step FreeMagma.of FreeMagma.mul token (stack FreeMagma.of FreeMagma.mul w s) = some t at h
      cases hs : stack FreeMagma.of FreeMagma.mul w s with
      | none => simp only [hs, step, Option.bind_none, reduceCtorEq] at h
      | some ts =>
          have ht := ih ts hs
          rw [hs] at h
          cases token with
          | some a =>
              have he : FreeMagma.of a :: ts = t := by simpa [step] using h
              subst t
              simpa [word, List.flatMap_cons, List.cons_append] using congrArg (some a :: ·) ht
          | none =>
              cases ts with
              | nil => simp [step, pop] at h
              | cons l ts => cases ts with
                | nil => simp [step, pop] at h
                | cons r ts =>
                    have he : FreeMagma.mul l r :: ts = t := by simpa [step, pop] using h
                    subst t
                    simpa [word, List.flatMap_cons, List.append_assoc, List.cons_append]
                      using congrArg (none :: ·) ht

/-- Decoding accepts precisely complete constructor words. Extra tokens,
incomplete branches and the empty word are rejected. -/
theorem preorder_codec {A : Type} (w : Word A) (t : FreeMagma A) :
    parse w = some t ↔ w = word t := by
  constructor
  · intro h
    cases hs : stack FreeMagma.of FreeMagma.mul w [] with
    | none => simp [parse, evaluate, hs] at h
    | some ts =>
        cases ts with
        | nil => simp [parse, evaluate, hs, finish] at h
        | cons a ts => cases ts with
          | nil =>
              have he : a = t := by simpa [parse, evaluate, hs, finish] using h
              subst a
              simpa using parse_stack_sound w [] [t] hs
          | cons b ts => simp [parse, evaluate, hs, finish] at h
  · intro h
    subst w
    rw [parse, evaluate, stack_exact]
    change some ((FreeMagma.lift FreeMagma.of) t) = some t
    exact congrArg some (show (FreeMagma.lift FreeMagma.of) t = t from bind_pure t)

/-- Normalization produces an ordinary constructor word, suitable for the fixed
list encoding; it never introduces an extensional tree identity. -/
def normalize {A : Type} (w : Word A) : Option (Word A) :=
  evaluate (fun a => [some a]) (fun l r => none :: (l ++ r)) w

private theorem normalize_stack {A : Type} (w : Word A) :
    w.foldr (step (fun a => [some a]) (fun l r => none :: (l ++ r))) (some []) =
      (w.foldr (step FreeMagma.of FreeMagma.mul) (some [])).map (List.map word) := by
  induction w with
  | nil => rfl
  | cons token w ih =>
      simp only [List.foldr_cons, ih]
      cases hs : w.foldr (step FreeMagma.of FreeMagma.mul) (some []) with
      | none => simp [step]
      | some s => cases token with
        | some a => simp [step, word]
        | none => cases s with
          | nil => rfl
          | cons a s => cases s with
            | nil => rfl
            | cons b s => simp [step, pop, word]

private theorem normalize_parse {A : Type} (w : Word A) :
    normalize w = (parse w).map word := by
  unfold normalize parse evaluate stack
  rw [normalize_stack]
  cases hs : w.foldr (step FreeMagma.of FreeMagma.mul) (some []) with
  | none => rfl
  | some s => cases s with
    | nil => rfl
    | cons a s => cases s with
      | nil => rfl
      | cons b s => rfl

private theorem normalize_primrec {A : Type} [Primcodable A] :
    Primrec (normalize : Word A → Option (Word A)) := by
  have leaf : Primrec₂ (fun (_ : Nat) (a : A) => [some a]) :=
    Primrec.list_cons.comp (Primrec.option_some.comp Primrec.snd) (Primrec.const [])
  have node : Primrec₂ (fun (_ : Nat) (p : Word A × Word A) => none :: (p.1 ++ p.2)) :=
    Primrec.list_cons.comp (Primrec.const none)
      (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact (uniform_preorder_evaluation (fun (_ : Nat) a => [some a])
    (fun (_ : Nat) p => none :: (p.1 ++ p.2)) leaf node).1.comp (Primrec.const 0) Primrec.id

/-- The numerical encoding is exactly the existing list encoding of the
preorder word. Its image recognizer is primitive recursive. -/
instance treePrimcodable {A : Type} [Primcodable A] : Primcodable (FreeMagma A) where
  encode t := Encodable.encode (word t)
  decode n := (Encodable.decode (α := Word A) n).bind parse
  encodek t := by
    simp only [Encodable.encodek, Option.bind_some]
    exact (preorder_codec (word t) t).mpr rfl
  prim := by
    have hn : Primrec (fun n : Nat =>
        (Encodable.decode (α := Word A) n).bind normalize) :=
      Primrec.option_bind Primrec.decode (normalize_primrec.comp Primrec.snd).to₂
    apply (Primrec.nat_iff.mp (Primrec.encode.comp hn)).of_eq
    intro n
    cases hd : Encodable.decode (α := Word A) n with
    | none => rfl
    | some w =>
        simp only [Option.bind_some, normalize_parse]
        cases hp : parse w <;> rfl

/-- A constructor fold is primitive recursive under the fixed preorder coding
when its parameterized leaf and branch operations are primitive recursive. -/
theorem uniform_tree_fold {A B X : Type} [Primcodable A] [Primcodable B]
    [Primcodable X] (leaf : X → A → B) (node : X → B × B → B)
    (hl : Primrec₂ leaf) (hn : Primrec₂ node) :
    Primrec₂ (fun x t => (@FreeMagma.lift A B
      ⟨fun l r => node x (l,r)⟩ (leaf x)) t) := by
  have hw : Primrec (word : FreeMagma A → Word A) :=
    Primrec.encode_iff.mp (show Primrec (fun t : FreeMagma A =>
      Encodable.encode (word t)) from Primrec.encode)
  obtain ⟨he, hs⟩ := uniform_preorder_evaluation leaf node hl hn
  exact Primrec₂.option_some_iff.mp ((he.comp₂ Primrec₂.left
    (hw.comp Primrec.snd).to₂).of_eq (fun x t => hs x t))

set_option backward.isDefEq.respectTransparency false

private theorem dedup_primrec {A : Type} [Primcodable A] [DecidableEq A] :
    Primrec (@List.dedup A _) := by
  have mem : PrimrecRel (fun (xs : List A) (a : A) => a ∈ xs) :=
    (PrimrecRel.exists_mem_list (Primrec.eq : PrimrecRel ((· = ·) : A → A → Prop))).of_eq
      (fun xs a => by simp)
  have hf : Primrec (fun xs : List A => xs.foldr
      (fun a ys => if a ∈ ys then ys else a :: ys) []) :=
    Primrec.list_foldr Primrec.id (Primrec.const [])
      (Primrec.ite (mem.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd))).to₂
  exact hf.of_eq (fun xs => by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [List.foldr_cons, ih, List.dedup_cons, List.mem_dedup])

private theorem ordered_insert_primrec {A : Type} [Primcodable A]
    (r : A → A → Prop) [DecidableRel r] (hr : PrimrecRel r) :
    Primrec₂ (fun a xs => List.orderedInsert r a xs) := by
  have hs : Primrec₂ (fun (p : A × List A) (q : A × List A × List A) =>
      if r p.1 q.1 then p.1 :: q.1 :: q.2.1 else q.1 :: q.2.2) :=
    Primrec.ite (hr.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hf := Primrec.list_rec (α := A × List A) Primrec.snd
    (Primrec.list_cons.comp Primrec.fst (Primrec.const [])) hs
  exact hf.of_eq (fun p => by
    rcases p with ⟨a,xs⟩
    induction xs with
    | nil => rfl
    | cons b xs ih => simp only [List.rec, List.orderedInsert, ih])

/-- Duplicate elimination preserves the pinned rightmost-occurrence convention,
and sorting uses the supplied relation rather than numeric encoding order. -/
theorem primitive_list_algorithms {A : Type} [Primcodable A] [DecidableEq A]
    (r : A → A → Prop) [DecidableRel r] (hr : PrimrecRel r) :
    Primrec (@List.dedup A _) ∧ Primrec (List.insertionSort r) := by
  refine ⟨dedup_primrec, ?_⟩
  exact Primrec.list_foldr Primrec.id (Primrec.const [])
    (Primrec.comp (ordered_insert_primrec r hr) Primrec.snd).to₂


end D5.S0.Computability.PreorderTreeEvaluation
