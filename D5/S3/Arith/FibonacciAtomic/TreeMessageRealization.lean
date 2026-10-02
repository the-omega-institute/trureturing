/- GID: D5/S3/Arith/FibonacciAtomic/TreeMessageRealization
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/TreeMessageRealization
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Tree.Basic]
   utility: none
   digest: Complete messages on labelled binary trees separate every subtree completion response. -/

import D5.S3.Observer.Separation.SurjectiveColumnSharpWidth
import Mathlib.Data.Tree.Basic
import Mathlib.Data.Set.Piecewise

set_option autoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.TreeMessageRealization

open D5.S3.Observer.Separation.SurjectiveColumnSharpWidth (response capacity)

/-- Terminal nodes carry coordinates; binary forks carry no coordinate. -/
abbrev Tree (I : Type) := BinaryTree (Option I)

abbrev leaf {I : Type} (i : I) : Tree I := .node (some i) .nil .nil
abbrev fork {I : Type} (l r : Tree I) : Tree I := .node none l r

noncomputable def leaves {I : Type} (t : Tree I) : Finset I := by
  classical
  exact match t with
  | .nil => ∅
  | .node (some i) _ _ => {i}
  | .node none l r => leaves l ∪ leaves r

/-- Every coordinate occurs once. The empty storage tree is not a task tree. -/
def Full {I : Type} (t : Tree I) : Prop := match t with
  | .nil => False
  | .node (some _) l r => l = .nil ∧ r = .nil
  | .node none l r => Full l ∧ Full r ∧ Disjoint (leaves l) (leaves r)

noncomputable def subtrees {I : Type} (t : Tree I) : Finset (Tree I) := by
  classical
  exact match t with
  | .nil => ∅
  | .node (some _) _ _ => {t}
  | .node none l r => insert t (subtrees l ∪ subtrees r)

/-- Height counts task-tree edges, so a labelled terminal has height zero. -/
def height {I : Type} (t : Tree I) : ℕ := t.height - 1

/-- Arbitrary heterogeneous complete messages, one-coordinate leaf encoders,
and atomic binary mergers. The value on the empty storage tree is unused by Full trees. -/
structure Implementation {I : Type} (X : I → Type) where
  Message : Tree I → Type
  empty : Message .nil
  encode : ∀ (i : I) (l r : Tree I), X i → Message (.node (some i) l r)
  combine : ∀ (l r : Tree I), Message l → Message r → Message (fork l r)

def evaluate {I : Type} {X : I → Type} (m : Implementation X) :
    (t : Tree I) → (∀ i, X i) → m.Message t
  | .nil, _ => m.empty
  | .node (some i) l r, x => m.encode i l r (x i)
  | .node none l r, x => m.combine l r (evaluate m l x) (evaluate m r x)

def Correct {I O : Type} {X : I → Type} (F : (∀ i, X i) → O)
    (t : Tree I) (m : Implementation X) (read : m.Message t → O) : Prop :=
  ∀ x, read (evaluate m t x) = F x

noncomputable def reachable {I : Type} {X : I → Type} (m : Implementation X)
    (t : Tree I) : ℕ := Nat.card (Set.range (evaluate m t))

noncomputable def peak {I : Type} {X : I → Type} (m : Implementation X)
    (t : Tree I) : ℕ := (subtrees t).sup (reachable m)

/-- The optimum is taken over accurate implementations, not over cut capacities. -/
noncomputable def optimum {I O : Type} {X : I → Type} (F : (∀ i, X i) → O)
    (t : Tree I) : ℕ := sInf {p | ∃ (m : Implementation X) (read : m.Message t → O),
      Correct F t m read ∧ peak m t = p}

/-- Every actual subtree of a fully labelled task tree is fully labelled,
and all its coordinates belong to its ancestor's coordinate block. -/
theorem subtree_structure {I : Type} (t : Tree I) (ht : Full t) :
    ∀ s ∈ subtrees t, Full s ∧ leaves s ⊆ leaves t := by
  classical
  intro s hs
  induction t with
  | nil => simp [Full] at ht
  | node a l r hl hr =>
    cases a with
    | some i =>
      have he : s = .node (some i) l r := by simpa [subtrees] using hs
      subst s
      exact ⟨ht, Finset.Subset.refl _⟩
    | none =>
      simp only [subtrees, Finset.mem_insert, Finset.mem_union] at hs
      rcases hs with he | hs | hs
      · subst s; exact ⟨ht, Finset.Subset.refl _⟩
      · exact ⟨(hl ht.1 hs).1, (hl ht.1 hs).2.trans
          (by intro i hi; simp [leaves, hi])⟩
      · exact ⟨(hr ht.2.1 hs).1, (hr ht.2.1 hs).2.trans
          (by intro i hi; simp [leaves, hi])⟩

/-- Every accurate implementation separates the full completion responses at
every actual subtree. No restriction is placed on the leaf-label order or input words. -/
theorem implementation_lower_bound {I O : Type} [Finite I] {X : I → Type}
    [∀ i, Finite (X i)] [∀ i, Nonempty (X i)]
    (F : (∀ i, X i) → O) (t : Tree I) (ht : Full t)
    (m : Implementation X) (read : m.Message t → O) (hm : Correct F t m read) :
    ∀ s ∈ subtrees t, capacity X F (fun i => i ∈ leaves s) ≤ reachable m s := by
  classical
  have locality (s : Tree I) (x y : ∀ i, X i)
      (h : ∀ i ∈ leaves s, x i = y i) : evaluate m s x = evaluate m s y := by
    induction s with
    | nil => rfl
    | node a l r hl hr =>
      cases a with
      | some i => exact congrArg (m.encode i l r) (h i (by simp [leaves]))
      | none =>
        exact congrArg₂ (m.combine l r)
          (hl (fun i hi => h i (by simp [leaves, hi])))
          (hr (fun i hi => h i (by simp [leaves, hi])))
  have context (u : Tree I) (hu : Full u) (s : Tree I) (hs : s ∈ subtrees u)
      (x y : ∀ i, X i) (hout : ∀ i ∉ leaves s, x i = y i)
      (heq : evaluate m s x = evaluate m s y) : evaluate m u x = evaluate m u y := by
    induction u generalizing s x y with
    | nil => simp [Full] at hu
    | node a l r hl hr =>
      cases a with
      | some i =>
        have he : s = .node (some i) l r := by simpa [subtrees] using hs
        subst s
        exact heq
      | none =>
        simp only [subtrees, Finset.mem_insert, Finset.mem_union] at hs
        rcases hs with hs | hs | hs
        · subst s
          exact heq
        · apply congrArg₂ (m.combine l r)
          · exact hl hu.1 s hs x y hout heq
          · apply locality r x y
            intro i hi
            apply hout i
            intro his
            exact Finset.disjoint_left.mp hu.2.2 ((subtree_structure l hu.1 s hs).2 his) hi
        · apply congrArg₂ (m.combine l r)
          · apply locality l x y
            intro i hi
            apply hout i
            intro his
            exact Finset.disjoint_left.mp hu.2.2 hi ((subtree_structure r hu.2.1 s hs).2 his)
          · exact hr hu.2.1 s hs x y hout heq
  intro s hs
  let A := leaves s
  let x₀ : ∀ i, X i := fun _ => Classical.choice inferInstance
  let glue := (Equiv.piEquivPiSubtypeProd (fun i => i ∈ A) X).symm
  let send := fun a : (∀ i : {i // i ∈ A}, X i.val) =>
    evaluate m s (glue (a, fun i => x₀ i.val))
  have distinguish (a a' : ∀ i : {i // i ∈ A}, X i.val) (he : send a = send a') :
      response X F (fun i => i ∈ A) a = response X F (fun i => i ∈ A) a' := by
    funext b
    have view (a : ∀ i : {i // i ∈ A}, X i.val)
        (b : ∀ i : {i // i ∉ A}, X i.val) :
        response X F (fun i => i ∈ A) a b = F (glue (a,b)) := by
      unfold response
      congr 1
      funext i
      by_cases hi : i ∈ A <;>
        simp [glue, Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk, hi]
    rw [view, view]
    rw [← hm (glue (a,b)), ← hm (glue (a',b))]
    apply congrArg read
    apply context t ht s hs
    · intro i hi
      simp [glue, Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk, A, hi]
    · calc
        evaluate m s (glue (a,b)) = send a := locality s _ _ (by
          intro i hi
          simp [glue, Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk, A, hi])
        _ = send a' := he
        _ = evaluate m s (glue (a',b)) := (locality s _ _ (by
          intro i hi
          simp [glue, Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk, A, hi])).symm
  let select : Set.range (response X F (fun i => i ∈ A)) → Set.range (evaluate m s) :=
    fun q => ⟨send q.property.choose, ⟨glue (q.property.choose, fun i => x₀ i.val), rfl⟩⟩
  apply Nat.card_le_card_of_injective select
  intro q q' he
  apply Subtype.ext
  have he' : send q.property.choose = send q'.property.choose := congrArg Subtype.val he
  exact q.property.choose_spec.symm.trans ((distinguish _ _ he').trans q'.property.choose_spec)

/-- A node's actual complete response, viewed in the existing response range. -/
noncomputable def responseMessage {I O : Type} {X : I → Type}
    (F : (∀ i, X i) → O) (t : Tree I) (x : ∀ i, X i) :
    Set.range (response X F (fun i => i ∈ leaves t)) :=
  ⟨response X F (fun i => i ∈ leaves t) (fun i => x i.val),
    ⟨(fun i => x i.val), rfl⟩⟩

/-- Choose a nominal input realizing a response, with the supplied background
outside its coordinate block. -/
noncomputable def nominal {I O : Type} {X : I → Type}
    (F : (∀ i, X i) → O) (x₀ : ∀ i, X i) (t : Tree I)
    (q : Set.range (response X F (fun i => i ∈ leaves t))) : ∀ i, X i := by
  classical
  exact (Equiv.piEquivPiSubtypeProd (fun i => i ∈ leaves t) X).symm
    (q.property.choose, fun i => x₀ i.val)

/-- Leaf encoding and binary response-class merging use no input beyond their
arguments. The nominal representatives are fixed functions of the messages. -/
noncomputable def responseImplementation {I O : Type} {X : I → Type}
    (F : (∀ i, X i) → O) (x₀ : ∀ i, X i) : Implementation X := by
  classical
  exact {
    Message := fun t => Set.range (response X F (fun i => i ∈ leaves t))
    empty := responseMessage F .nil x₀
    encode := fun i l r a => responseMessage F (.node (some i) l r) (Function.update x₀ i a)
    combine := fun l r a b => responseMessage F (fork l r)
      ((leaves l : Set I).piecewise (nominal F x₀ l a) (nominal F x₀ r b)) }

/-- One accurate response-class implementation simultaneously attains the
completion-response capacity at every node of every fully labelled binary tree. -/
theorem simultaneous_realization {I O : Type} [Fintype I] {X : I → Type}
    [∀ i, Finite (X i)] [∀ i, Nonempty (X i)]
    (F : (∀ i, X i) → O) (t : Tree I) (ht : Full t)
    (hall : leaves t = Finset.univ) :
    ∃ (m : Implementation X) (read : m.Message t → O), Correct F t m read ∧
      (∀ s ∈ subtrees t, reachable m s = capacity X F (fun i => i ∈ leaves s)) ∧
      peak m t = optimum F t ∧
      optimum F t = (subtrees t).sup (fun s => capacity X F (fun i => i ∈ leaves s)) := by
  classical
  let x₀ : ∀ i, X i := fun _ => Classical.choice inferInstance
  let m := responseImplementation F x₀
  have nominal_response (s : Tree I) (q : Set.range (response X F (fun i => i ∈ leaves s))) :
      responseMessage F s (nominal F x₀ s q) = q := by
    apply Subtype.ext
    change response X F (fun i => i ∈ leaves s) _ = q.val
    rw [← q.property.choose_spec]
    congr 1
    funext i
    simp [nominal, Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk, i.property]
  have response_on (A : Finset I) (x y : ∀ i, X i)
      (h : ∀ i ∈ A, x i = y i) :
      response X F (fun i => i ∈ A) (fun i => x i.val) =
        response X F (fun i => i ∈ A) (fun i => y i.val) := by
    congr 1
    funext i
    exact h i.val i.property
  have view (A : Finset I) (x : ∀ i, X i)
      (b : ∀ i : {i // i ∉ A}, X i.val) :
      response X F (fun i => i ∈ A) (fun i => x i.val) b =
        F (fun i => if h : i ∈ A then x i else b ⟨i,h⟩) := by
    unfold response
    congr 1
    funext i
    by_cases hi : i ∈ A <;>
      simp [Equiv.piEquivPiSubtypeProd, hi]
  have substitute (A : Finset I) (x y : ∀ i, X i)
      (h : response X F (fun i => i ∈ A) (fun i => x i.val) =
        response X F (fun i => i ∈ A) (fun i => y i.val)) (z : ∀ i, X i) :
      F ((A : Set I).piecewise x z) = F ((A : Set I).piecewise y z) := by
    calc
      F ((A : Set I).piecewise x z) =
          response X F (fun i => i ∈ A) (fun i => x i.val) (fun i => z i.val) := by
        unfold response
        congr 1
        funext i
        by_cases hi : i ∈ A <;>
        simp [Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk, Set.piecewise, hi]
      _ = response X F (fun i => i ∈ A) (fun i => y i.val) (fun i => z i.val) :=
        congrFun h _
      _ = F ((A : Set I).piecewise y z) := by
        unfold response
        congr 1
        funext i
        by_cases hi : i ∈ A <;>
        simp [Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk, Set.piecewise, hi]
  have evaluates (u : Tree I) (hu : Full u) (x : ∀ i, X i) :
      evaluate m u x = responseMessage F u x := by
    induction u with
    | nil => simp [Full] at hu
    | node a l r hl hr =>
      cases a with
      | some i =>
        apply Subtype.ext
        apply response_on
        intro j hj
        have : j = i := by simpa [leaves] using hj
        subst j
        simp [Function.update]
      | none =>
        rw [evaluate, hl hu.1, hr hu.2.1]
        apply Subtype.ext
        change response X F (fun i => i ∈ leaves (fork l r)) _ =
          response X F (fun i => i ∈ leaves (fork l r)) _
        funext b
        let xl := nominal F x₀ l (responseMessage F l x)
        let xr := nominal F x₀ r (responseMessage F r x)
        let z : ∀ i, X i := fun i => if h : i ∈ leaves (fork l r) then x i else b ⟨i,h⟩
        have el : response X F (fun i => i ∈ leaves l) (fun i => xl i.val) =
            response X F (fun i => i ∈ leaves l) (fun i => x i.val) :=
          congrArg Subtype.val (nominal_response l (responseMessage F l x))
        have er : response X F (fun i => i ∈ leaves r) (fun i => xr i.val) =
            response X F (fun i => i ∈ leaves r) (fun i => x i.val) :=
          congrArg Subtype.val (nominal_response r (responseMessage F r x))
        have elz : response X F (fun i => i ∈ leaves l) (fun i => x i.val) =
            response X F (fun i => i ∈ leaves l) (fun i => z i.val) := by
          apply response_on
          intro i hi
          simp [z, fork, leaves, hi]
        have erz : response X F (fun i => i ∈ leaves r) (fun i => x i.val) =
            response X F (fun i => i ∈ leaves r) (fun i => z i.val) := by
          apply response_on
          intro i hi
          simp [z, fork, leaves, hi]
        have first := substitute (leaves l) xl z (el.trans elz)
          ((leaves r : Set I).piecewise xr z)
        have second := substitute (leaves r) xr z (er.trans erz) z
        have first_right : (leaves l : Set I).piecewise z ((leaves r : Set I).piecewise xr z) =
            (leaves r : Set I).piecewise xr z := by
          funext i
          by_cases hil : i ∈ leaves l
          · have hir : i ∉ leaves r := fun hir => Finset.disjoint_left.mp hu.2.2 hil hir
            simp [Set.piecewise, hil, hir]
          · simp [Set.piecewise, hil]
        rw [first_right] at first
        rw [Set.piecewise_same] at second
        have assembled :
            F ((leaves l : Set I).piecewise xl ((leaves r : Set I).piecewise xr z)) = F z :=
          first.trans second
        rw [view, view]
        convert assembled using 1
        congr 1
        funext i
        · by_cases hil : i ∈ leaves l <;> by_cases hir : i ∈ leaves r <;>
            simp [responseMessage, Set.piecewise,
              fork, leaves, xl, xr, z, hil, hir]
  let read : m.Message t → O := fun q => q.val (fun i => x₀ i.val)
  have correct : Correct F t m read := by
    intro x
    rw [evaluates t ht x]
    change response X F (fun i => i ∈ leaves t) (fun i => x i.val) _ = F x
    unfold response
    congr 1
    funext i
    simp [Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk, hall]
  have sharp : ∀ s ∈ subtrees t,
      reachable m s = capacity X F (fun i => i ∈ leaves s) := by
    intro s hs
    have surj : Function.Surjective (evaluate m s) := by
      intro q
      refine ⟨nominal F x₀ s q, ?_⟩
      exact (evaluates s (subtree_structure t ht s hs).1 _).trans (nominal_response s q)
    rw [reachable, surj.range_eq]
    simp only [Nat.card_univ]
    rfl
  have peak_eq : peak m t =
      (subtrees t).sup (fun s => capacity X F (fun i => i ∈ leaves s)) := by
    exact Finset.sup_congr rfl sharp
  have opt_le : optimum F t ≤ peak m t := Nat.sInf_le ⟨m,read,correct,rfl⟩
  have attained : ∃ (m' : Implementation X) (read' : m'.Message t → O),
      Correct F t m' read' ∧ peak m' t = optimum F t := by
    let peaks : Set ℕ := {p | ∃ (a : Implementation X) (g : a.Message t → O),
      Correct F t a g ∧ peak a t = p}
    have inhabited : peaks.Nonempty := ⟨peak m t,m,read,correct,rfl⟩
    exact Nat.sInf_mem inhabited
  obtain ⟨m',read',correct',attained'⟩ := attained
  have opt_ge : (subtrees t).sup (fun s => capacity X F (fun i => i ∈ leaves s)) ≤
      optimum F t := by
    rw [← attained']
    apply Finset.sup_le
    intro s hs
    exact (implementation_lower_bound F t ht m' read' correct' s hs).trans
      (Finset.le_sup hs)
  have opt_eq : optimum F t =
      (subtrees t).sup (fun s => capacity X F (fun i => i ∈ leaves s)) :=
    le_antisymm (opt_le.trans_eq peak_eq) opt_ge
  exact ⟨m,read,correct,sharp,peak_eq.trans opt_eq.symm,opt_eq⟩

end D5.S3.Arith.FibonacciAtomic.TreeMessageRealization
