/- GID: D5/S3/Observer/Separation/FixedTreeCommonExtension
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/FixedTreeCommonExtension
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Reachable-message retractions on finite trees yield a common total extension. -/

import D5.S3.Observer.Separation.SurjectiveColumnSharpWidth
import Mathlib.Data.Set.Piecewise

set_option autoImplicit false

namespace D5.S3.Observer.Separation.FixedTreeCommonExtension

open D5.S3.Observer.Separation.SurjectiveColumnSharpWidth (response capacity)

/-- Vertex labels distinguish original nodes, including unary nodes. A zero-child
node is an input-free constant node. -/
inductive Tree (I V : Type) : Type
  | leaf : V → I → Tree I V
  | node : V → (n : ℕ) → (Fin n → Tree I V) → Tree I V

noncomputable def leaves {I V : Type} (t : Tree I V) : Finset I := by
  classical
  exact match t with
  | .leaf _ i => {i}
  | .node _ _ c => Finset.univ.biUnion (fun j => leaves (c j))

noncomputable def subtrees {I V : Type} (t : Tree I V) : Finset (Tree I V) := by
  classical
  exact match t with
  | .leaf _ _ => {t}
  | .node _ _ c => insert t (Finset.univ.biUnion (fun j => subtrees (c j)))

/-- Sibling subtrees have disjoint actual descendant-leaf coordinate sets. -/
def Full {I V : Type} : Tree I V → Prop
  | .leaf _ _ => True
  | .node _ _ c => (∀ j, Full (c j)) ∧
      (∀ j k, j ≠ k → Disjoint (leaves (c j)) (leaves (c k)))

/-- Complete messages and local tables; no alphabet finiteness is required. -/
structure Implementation {I V : Type} (X : I → Type) where
  Message : Tree I V → Type
  encode : ∀ v i, X i → Message (.leaf v i)
  combine : ∀ v n (c : Fin n → Tree I V), (∀ j, Message (c j)) → Message (.node v n c)

def evaluate {I V : Type} {X : I → Type} (m : Implementation (V := V) X) :
    (t : Tree I V) → (∀ i, X i) → m.Message t
  | .leaf v i, x => m.encode v i (x i)
  | .node v n c, x => m.combine v n c (fun j => evaluate m (c j) x)

noncomputable def reachable {I V : Type} {X : I → Type}
    (m : Implementation (V := V) X) (D : Set (∀ i, X i)) (s : Tree I V) : ℕ :=
  Nat.card (Set.range (fun x : D => evaluate m s x.val))

private theorem subtree_structure {I V : Type} (t : Tree I V) (ht : Full t) :
    ∀ s ∈ subtrees t, Full s ∧ leaves s ⊆ leaves t := by
  classical
  induction t with
  | leaf v i =>
    intro s hs
    have : s = Tree.leaf v i := by simpa [subtrees] using hs
    subst s
    exact ⟨ht, Finset.Subset.refl _⟩
  | node v n c ih =>
    intro s hs
    simp only [subtrees, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ,
      true_and] at hs
    rcases hs with rfl | ⟨j, hj⟩
    · exact ⟨ht, Finset.Subset.refl _⟩
    · obtain ⟨hf, hsub⟩ := ih j (ht.1 j) s hj
      refine ⟨hf, fun i hi => ?_⟩
      simp only [leaves, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨j, hsub hi⟩

private theorem locality {I V : Type} {X : I → Type}
    (m : Implementation (V := V) X) (s : Tree I V) (x y : ∀ i, X i)
    (h : ∀ i ∈ leaves s, x i = y i) : evaluate m s x = evaluate m s y := by
  classical
  induction s with
  | leaf v i => exact congrArg (m.encode v i) (h i (by simp [leaves]))
  | node v n c ih =>
    apply congrArg (m.combine v n c)
    funext j
    apply ih j
    intro i hi
    apply h i
    simp only [leaves, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨j, hi⟩

private theorem context {I V : Type} {X : I → Type}
    (m : Implementation (V := V) X) (t : Tree I V) (ht : Full t)
    (s : Tree I V) (hs : s ∈ subtrees t) (x y : ∀ i, X i)
    (hout : ∀ i ∉ leaves s, x i = y i)
    (heq : evaluate m s x = evaluate m s y) : evaluate m t x = evaluate m t y := by
  classical
  induction t with
  | leaf v i =>
    have : s = Tree.leaf v i := by simpa [subtrees] using hs
    subst s
    exact heq
  | node v n c ih =>
    simp only [subtrees, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ,
      true_and] at hs
    rcases hs with rfl | ⟨j, hj⟩
    · exact heq
    · apply congrArg (m.combine v n c)
      funext k
      by_cases hkj : k = j
      · subst k
        exact ih j (ht.1 j) hj
      · apply locality
        intro i hi
        apply hout i
        intro his
        exact Finset.disjoint_left.mp (ht.2 j k (Ne.symm hkj))
          ((subtree_structure (c j) (ht.1 j) s hj).2 his) hi

/-- Every ambient label is sent into the actual promised image, fixing that image. -/
noncomputable def retract {A B : Type} (g : A → B) (a₀ : A) (b : B) : B := by
  classical
  exact if b ∈ Set.range g then b else g a₀

private theorem retract_mem {A B : Type} (g : A → B) (a₀ : A) (b : B) :
    retract g a₀ b ∈ Set.range g := by
  classical
  unfold retract
  split_ifs with h
  · exact h
  · exact ⟨a₀, rfl⟩

private theorem retract_fix {A B : Type} (g : A → B) (a₀ a : A) :
    retract g a₀ (g a) = g a := by
  classical
  simp [retract]

/-- Local retractions are performed after each original local table. -/
noncomputable def restricted {I V : Type} {X : I → Type}
    (m : Implementation (V := V) X) (D : Set (∀ i, X i)) (x₀ : D) :
    Implementation (V := V) X where
  Message := m.Message
  encode := fun v i a => retract (fun x : D => evaluate m (.leaf v i) x.val) x₀
    (m.encode v i a)
  combine := fun v n c a => retract (fun x : D => evaluate m (.node v n c) x.val) x₀
    (m.combine v n c a)

private theorem restricted_agrees {I V : Type} {X : I → Type}
    (m : Implementation (V := V) X) (D : Set (∀ i, X i)) (x₀ x : D) (s : Tree I V) :
    evaluate (restricted m D x₀) s x.val = evaluate m s x.val := by
  induction s with
  | leaf v i => exact retract_fix (fun z : D => evaluate m (.leaf v i) z.val) x₀ x
  | node v n c ih =>
    change retract _ x₀ (m.combine v n c (fun j => _)) = _
    have e : (fun j => evaluate (restricted m D x₀) (c j) x.val) =
        (fun j => evaluate m (c j) x.val) := funext ih
    rw [e]
    exact retract_fix _ x₀ x

private theorem restricted_mem {I V : Type} {X : I → Type}
    (m : Implementation (V := V) X) (D : Set (∀ i, X i)) (x₀ : D)
    (s : Tree I V) (x : ∀ i, X i) :
    evaluate (restricted m D x₀) s x ∈ Set.range (fun z : D => evaluate m s z.val) := by
  cases s with
  | leaf v i => exact retract_mem _ x₀ (m.encode v i (x i))
  | node v n c => exact retract_mem _ x₀ _

/-- One total extension simultaneously respects all original-node promised
reachable bounds, even for infinite heterogeneous alphabets and arbitrary outputs. -/
private theorem common_extension {I V O : Type} [Finite I] {X : I → Type}
    [∀ i, Finite (X i)] [∀ i, Nonempty (X i)]
    (t : Tree I V) (ht : Full t) (D : Set (∀ i, X i)) (hD : D.Nonempty)
    (f : D → O) (m : Implementation (V := V) X) (read : m.Message t → O)
    (correct : ∀ x : D, read (evaluate m t x.val) = f x) :
    ∃ H : (∀ i, X i) → O, (∀ x : D, H x.val = f x) ∧
      ∀ s ∈ subtrees t, capacity X H (fun i => i ∈ leaves s) ≤ reachable m D s := by
  classical
  let x₀ : D := ⟨hD.choose, hD.choose_spec⟩
  let m' := restricted m D x₀
  let H : (∀ i, X i) → O := fun x => read (evaluate m' t x)
  refine ⟨H, ?_, ?_⟩
  · intro x
    exact (congrArg read (restricted_agrees m D x₀ x t)).trans (correct x)
  · intro s hs
    let A := leaves s
    let glue := (Equiv.piEquivPiSubtypeProd (fun i => i ∈ A) X).symm
    let send := fun a : (∀ i : {i // i ∈ A}, X i.val) =>
      evaluate m' s (glue (a, fun i => x₀.val i.val))
    have ker (a a' : ∀ i : {i // i ∈ A}, X i.val) (he : send a = send a') :
        response X H (fun i => i ∈ A) a = response X H (fun i => i ∈ A) a' := by
      funext b
      have view (a : ∀ i : {i // i ∈ A}, X i.val) :
          response X H (fun i => i ∈ A) a b = H (glue (a,b)) := by
        unfold response
        congr 1
        funext i
        by_cases hi : i ∈ A <;>
          simp [glue, Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk, hi]
      rw [view, view]
      apply congrArg read
      apply context m' t ht s hs
      · intro i hi
        simp [glue, Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk, A, hi]
      · change evaluate m' s (glue (a,b)) = evaluate m' s (glue (a',b))
        calc
          evaluate m' s (glue (a,b)) = send a := locality m' s _ _ (by
            intro i hi
            simp [glue, Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk, A, hi])
          _ = send a' := he
          _ = evaluate m' s (glue (a',b)) := (locality m' s _ _ (by
            intro i hi
            simp [glue, Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk, A, hi])).symm
    let chooseMessage : Set.range (response X H (fun i => i ∈ A)) →
        Set.range (fun x : D => evaluate m s x.val) :=
      fun q => ⟨send q.property.choose,
        restricted_mem m D x₀ s (glue (q.property.choose, fun i => x₀.val i.val))⟩
    apply Nat.card_le_card_of_injective chooseMessage
    intro q q' he
    apply Subtype.ext
    exact q.property.choose_spec.symm.trans
      ((ker _ _ (congrArg Subtype.val he)).trans q'.property.choose_spec)

noncomputable def responseMessage {I V O : Type} {X : I → Type}
    (H : (∀ i, X i) → O) (s : Tree I V) (x : ∀ i, X i) :
    Set.range (response X H (fun i => i ∈ leaves s)) :=
  Set.rangeFactorization (response X H (fun i => i ∈ leaves s)) (fun i => x i.val)

private theorem response_on {I O : Type} {X : I → Type}
    (H : (∀ i, X i) → O) (A : Finset I) (x y : ∀ i, X i)
    (h : ∀ i ∈ A, x i = y i) :
    response X H (fun i => i ∈ A) (fun i => x i.val) =
      response X H (fun i => i ∈ A) (fun i => y i.val) := by
  congr 1
  funext i
  exact h i.val i.property

private theorem response_substitute {I O : Type} [DecidableEq I] {X : I → Type}
    (H : (∀ i, X i) → O) (A : Finset I) (x y z : ∀ i, X i)
    (h : response X H (fun i => i ∈ A) (fun i => x i.val) =
      response X H (fun i => i ∈ A) (fun i => y i.val)) :
    H ((A : Set I).piecewise x z) = H ((A : Set I).piecewise y z) := by
  classical
  have e := congrFun h (fun i => z i.val)
  convert e using 1 <;> congr 1 <;> funext i <;>
    by_cases hi : i ∈ A <;>
    simp [Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk, Set.piecewise, hi]

/-- Finite sibling replacement uses their actual disjoint coordinate blocks. -/
private theorem sibling_kernel {I V O : Type} {X : I → Type}
    (H : (∀ i, X i) → O) (v : V) (n : ℕ) (c : Fin n → Tree I V)
    (hd : ∀ j k, j ≠ k → Disjoint (leaves (c j)) (leaves (c k)))
    (x y : ∀ i, X i)
    (h : ∀ j, responseMessage H (c j) x = responseMessage H (c j) y) :
    responseMessage H (.node v n c) x = responseMessage H (.node v n c) y := by
  classical
  apply Subtype.ext
  funext b
  let A := leaves (Tree.node v n c)
  let z : ∀ i, X i := fun i => if hi : i ∈ A then x i else b ⟨i,hi⟩
  let mixed (K : Finset (Fin n)) : ∀ i, X i :=
    fun i => if ∃ j ∈ K, i ∈ leaves (c j) then y i else z i
  have chain (K : Finset (Fin n)) : H z = H (mixed K) := by
    induction K using Finset.induction_on with
    | empty => simp [mixed]
    | @insert j K hj ih =>
      have same : response X H (fun i => i ∈ leaves (c j))
          (fun i => mixed K i.val) =
          response X H (fun i => i ∈ leaves (c j)) (fun i => x i.val) := by
        apply response_on
        intro i hi
        have no : ¬ ∃ k ∈ K, i ∈ leaves (c k) := by
          rintro ⟨k,hk,hik⟩
          have hjk : j ≠ k := fun e => hj (e ▸ hk)
          exact Finset.disjoint_left.mp (hd j k hjk) hi hik
        have hiA : i ∈ A := by
          simp only [A, leaves, Finset.mem_biUnion, Finset.mem_univ, true_and]
          exact ⟨j,hi⟩
        simp [mixed, no, z, hiA]
      have eq := response_substitute H (leaves (c j)) (mixed K) y (mixed K)
        (same.trans (congrArg Subtype.val (h j)))
      rw [Set.piecewise_same] at eq
      have em : (leaves (c j) : Set I).piecewise y (mixed K) = mixed (insert j K) := by
        funext i
        by_cases hi : i ∈ leaves (c j)
        · simp [Set.piecewise, mixed, hi]
        · simp [Set.piecewise, mixed, hi]
      rw [em] at eq
      exact ih.trans eq
  have all := chain Finset.univ
  change response X H (fun i => i ∈ leaves (Tree.node v n c)) (fun i => x i.val) b =
    response X H (fun i => i ∈ leaves (Tree.node v n c)) (fun i => y i.val) b
  unfold response
  convert all using 1
  · congr 1
    funext i
    by_cases hi : i ∈ A <;>
      dsimp only [A] at hi <;>
      simp [Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk, z, A, hi]
  · congr 1
    funext i
    by_cases hi : i ∈ A
    · have hex : ∃ j ∈ (Finset.univ : Finset (Fin n)), i ∈ leaves (c j) := by
        simpa [A, leaves] using hi
      simp only [mixed, if_pos hex]
      dsimp only [A] at hi
      simp [Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk, hi]
    · have hno : ¬ ∃ j ∈ (Finset.univ : Finset (Fin n)), i ∈ leaves (c j) := by
        simpa [A, leaves] using hi
      simp only [mixed, if_neg hno]
      dsimp only [A] at hi
      simp [Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk, hi, z, A]

/-- The local merger chooses a representative of the complete child profile.
Its output is always a response class, including on unreached tuples. -/
noncomputable def canonical {I V O : Type} {X : I → Type}
    [∀ i, Nonempty (X i)] (H : (∀ i, X i) → O) : Implementation (V := V) X := by
  classical
  let x₀ : ∀ i, X i := fun i => Classical.choice inferInstance
  exact {
    Message := fun s => Set.range (response X H (fun i => i ∈ leaves s))
    encode := fun v i a => responseMessage H (.leaf v i) (Function.update x₀ i a)
    combine := fun v n c a => responseMessage H (.node v n c)
      (Function.invFun (fun x : ∀ i, X i => fun j => responseMessage H (c j) x) a) }

private theorem canonical_evaluates {I V O : Type} {X : I → Type}
    [∀ i, Nonempty (X i)] (H : (∀ i, X i) → O)
    (s : Tree I V) (hs : Full s) (x : ∀ i, X i) :
    evaluate (canonical H) s x = responseMessage H s x := by
  classical
  induction s with
  | leaf v i =>
    apply Subtype.ext
    apply response_on
    intro j hj
    have : j = i := by simpa [leaves] using hj
    subst j
    simp [Function.update]
  | node v n c ih =>
    change responseMessage H (.node v n c)
      (Function.invFun (fun z : ∀ i, X i => fun j => responseMessage H (c j) z)
        (fun j => evaluate (canonical H) (c j) x)) = _
    have ev : (fun j => evaluate (canonical H) (c j) x) =
        (fun j => responseMessage H (c j) x) := funext (fun j => ih j (hs.1 j))
    rw [ev]
    apply sibling_kernel H v n c hs.2
    intro j
    exact congrFun (Function.apply_invFun_apply
      (f := fun z : ∀ i, X i => fun j => responseMessage H (c j) z) (a := x)) j

/-- Execution of the response protocol has exactly the promised response image. -/
private theorem canonical_realization {I V O : Type} [Fintype I] {X : I → Type}
    [∀ i, Finite (X i)] [∀ i, Nonempty (X i)]
    (t : Tree I V) (ht : Full t) (hall : leaves t = Finset.univ)
    (H : (∀ i, X i) → O) (D : Set (∀ i, X i)) :
    ∃ read : (canonical H (V := V)).Message t → O,
      (∀ x, read (evaluate (canonical H) t x) = H x) ∧
      (∀ s ∈ subtrees t,
        Set.range (fun x : D => evaluate (canonical H) s x.val) =
          Set.range (fun x : D => responseMessage H s x.val)) ∧
      (∀ s ∈ subtrees t, reachable (canonical H) D s ≤
        capacity X H (fun i => i ∈ leaves s)) := by
  classical
  let x₀ : ∀ i, X i := fun i => Classical.choice inferInstance
  refine ⟨fun q => q.val (fun i => x₀ i.val), ?_, ?_, ?_⟩
  · intro x
    rw [canonical_evaluates H t ht x]
    change response X H (fun i => i ∈ leaves t) (fun i => x i.val) _ = H x
    unfold response
    congr 1
    funext i
    simp [Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk, hall]
  · intro s hs
    congr 1
    funext x
    exact canonical_evaluates H s (subtree_structure t ht s hs).1 x.val
  · intro s hs
    unfold reachable capacity
    letI : Finite ((canonical H (V := V)).Message s) :=
      inferInstanceAs (Finite (Set.range (response X H (fun i => i ∈ leaves s))))
    apply Nat.card_le_card_of_injective
      (fun q : Set.range (fun x : D => evaluate (canonical H) s x.val) => q.val)
    exact fun _ _ h => Subtype.ext h

/-- Vectors retain every original node, including the root. -/
abbrev Nodes {I V : Type} (t : Tree I V) := {s // s ∈ subtrees t}

noncomputable def protocolVector {I V : Type} {X : I → Type} (t : Tree I V)
    (D : Set (∀ i, X i)) (m : Implementation (V := V) X) : Nodes t → ℕ :=
  fun s => reachable m D s.val

noncomputable def capacityVector {I V O : Type} {X : I → Type} (t : Tree I V)
    (H : (∀ i, X i) → O) : Nodes t → ℕ :=
  fun s => capacity X H (fun i => i ∈ leaves s.val)

private theorem capacity_bound {I V O : Type} [Finite I] {X : I → Type}
    [∀ i, Finite (X i)] [∀ i, Nonempty (X i)]
    (H : (∀ i, X i) → O) (s : Tree I V) :
    capacity X H (fun i => i ∈ leaves s) ≤ Nat.card (∀ i, X i) := by
  classical
  let x₀ : ∀ i, X i := fun i => Classical.choice inferInstance
  apply Nat.card_le_card_of_surjective (responseMessage H s)
  intro q
  let x := (Equiv.piEquivPiSubtypeProd (fun i => i ∈ leaves s) X).symm
    (q.property.choose, fun i => x₀ i.val)
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change response X H (fun i => i ∈ leaves s) _ = q.val
  rw [← q.property.choose_spec]
  congr 1
  funext i
  simp [x, Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk, i.property]

/-- The full vector upward closures coincide. Every monotone cost into an
arbitrary linear order has attained equal minima on protocols and extensions. -/
private theorem vector_and_cost {I V O : Type} [Fintype I] {X : I → Type}
    [∀ i, Finite (X i)] [∀ i, Nonempty (X i)]
    (t : Tree I V) (ht : Full t) (hall : leaves t = Finset.univ)
    (D : Set (∀ i, X i)) (hD : D.Nonempty) (f : D → O) :
    (∀ b : Nodes t → ℕ,
      (∃ (m : Implementation (V := V) X) (read : m.Message t → O),
        (∀ x : D, read (evaluate m t x.val) = f x) ∧ protocolVector t D m ≤ b) ↔
      (∃ H : (∀ i, X i) → O, (∀ x : D, H x.val = f x) ∧ capacityVector t H ≤ b)) ∧
    (∀ (L : Type) [LinearOrder L] (C : (Nodes t → ℕ) → L), Monotone C →
      ∃ (H : (∀ i, X i) → O) (m : Implementation (V := V) X)
        (read : m.Message t → O),
        (∀ x : D, H x.val = f x) ∧
        (∀ x : D, read (evaluate m t x.val) = f x) ∧
        C (protocolVector t D m) = C (capacityVector t H) ∧
        (∀ (m' : Implementation (V := V) X) (read' : m'.Message t → O),
          (∀ x : D, read' (evaluate m' t x.val) = f x) →
          C (protocolVector t D m) ≤ C (protocolVector t D m')) ∧
        (∀ H' : (∀ i, X i) → O, (∀ x : D, H' x.val = f x) →
          C (capacityVector t H) ≤ C (capacityVector t H'))) := by
  classical
  have forward (m : Implementation (V := V) X) (read : m.Message t → O)
      (hc : ∀ x : D, read (evaluate m t x.val) = f x) :
      ∃ H : (∀ i, X i) → O, (∀ x : D, H x.val = f x) ∧
        capacityVector t H ≤ protocolVector t D m := by
    obtain ⟨H,hH,hb⟩ := common_extension t ht D hD f m read hc
    exact ⟨H,hH,fun s => hb s.val s.property⟩
  have reverse (H : (∀ i, X i) → O) (hH : ∀ x : D, H x.val = f x) :
      ∃ read : (canonical H (V := V)).Message t → O,
        (∀ x : D, read (evaluate (canonical H) t x.val) = f x) ∧
        protocolVector t D (canonical H) ≤ capacityVector t H := by
    obtain ⟨read,hc,_,hb⟩ := canonical_realization t ht hall H D
    exact ⟨read,fun x => (hc x.val).trans (hH x),fun s => hb s.val s.property⟩
  constructor
  · intro b
    constructor
    · rintro ⟨m,read,hc,hb⟩
      obtain ⟨H,hH,hh⟩ := forward m read hc
      exact ⟨H,hH,le_trans hh hb⟩
    · rintro ⟨H,hH,hb⟩
      obtain ⟨read,hc,hh⟩ := reverse H hH
      exact ⟨canonical H,read,hc,le_trans hh hb⟩
  · intro L _ C hC
    let K : Set (Nodes t → ℕ) := {k | ∃ H : (∀ i, X i) → O,
      (∀ x : D, H x.val = f x) ∧ k = capacityVector t H}
    let N := Nat.card (∀ i, X i)
    have finiteK : K.Finite := by
      apply (Set.finite_range (fun a : Nodes t → Fin (N+1) => fun s => (a s).val)).subset
      rintro k ⟨H,hH,rfl⟩
      exact ⟨fun s => ⟨capacityVector t H s,
        Nat.lt_succ_of_le (capacity_bound H s.val)⟩, rfl⟩
    let x₀ : D := ⟨hD.choose,hD.choose_spec⟩
    let H₀ := Function.extend Subtype.val f (fun _ => f x₀)
    have correct₀ : ∀ x : D, H₀ x.val = f x :=
      fun x => Function.Injective.extend_apply Subtype.val_injective f (fun _ => f x₀) x
    obtain ⟨k,⟨H,hH,hk⟩,hmin⟩ := Set.exists_min_image K C finiteK
      ⟨capacityVector t H₀,H₀,correct₀,rfl⟩
    subst k
    obtain ⟨read,hc,hb⟩ := reverse H hH
    have minP (m' : Implementation (V := V) X) (read' : m'.Message t → O)
        (hc' : ∀ x : D, read' (evaluate m' t x.val) = f x) :
        C (capacityVector t H) ≤ C (protocolVector t D m') := by
      obtain ⟨H',hH',hb'⟩ := forward m' read' hc'
      exact (hmin _ ⟨H',hH',rfl⟩).trans (hC hb')
    refine ⟨H,canonical H,read,hH,hc,le_antisymm (hC hb) (minP _ read hc),?_,?_⟩
    · intro m' read' hc'
      exact (hC hb).trans (minP m' read' hc')
    · intro H' hH'
      exact hmin _ ⟨H',hH',rfl⟩

/-- Both minima are witnessed by an actual protocol and one total extension. -/
def OptimalPair {I V O L : Type} [LE L] {X : I → Type}
    (t : Tree I V) (D : Set (∀ i, X i)) (f : D → O)
    (C : (Nodes t → ℕ) → L) : Prop :=
  ∃ (H : (∀ i, X i) → O) (m : Implementation (V := V) X)
    (read : m.Message t → O),
    (∀ x : D, H x.val = f x) ∧
    (∀ x : D, read (evaluate m t x.val) = f x) ∧
    C (protocolVector t D m) = C (capacityVector t H) ∧
    (∀ (m' : Implementation (V := V) X) (read' : m'.Message t → O),
      (∀ x : D, read' (evaluate m' t x.val) = f x) →
      C (protocolVector t D m) ≤ C (protocolVector t D m')) ∧
    (∀ H' : (∀ i, X i) → O, (∀ x : D, H' x.val = f x) →
      C (capacityVector t H) ≤ C (capacityVector t H'))

private theorem empty_node_laws {I V O : Type} {X : I → Type}
    [∀ i, Nonempty (X i)] (D : Set (∀ i, X i)) (hD : D.Nonempty)
    (v : V) (c : Fin 0 → Tree I V) (m : Implementation (V := V) X)
    (H : (∀ i, X i) → O) :
    reachable m D (.node v 0 c) = 1 ∧
    capacity X H (fun i => i ∈ leaves (.node v 0 c)) = 1 ∧
    Finset.univ.sup (protocolVector (.node v 0 c) D m) = 1 ∧
    Finset.univ.sup (capacityVector (.node v 0 c) H) = 1 := by
  classical
  let t : Tree I V := .node v 0 c
  let x₀ : D := ⟨hD.choose, hD.choose_spec⟩
  letI : Nonempty D := ⟨x₀⟩
  have hr : reachable m D t = 1 := by
    have e : (fun x : D => evaluate m t x.val) =
        (fun _ : D => evaluate m t x₀.val) := by
      funext x
      apply congrArg (m.combine v 0 c)
      funext j
      exact Fin.elim0 j
    unfold reachable
    rw [e]
    simp
  have hk : capacity X H (fun i => i ∈ leaves t) = 1 := by
    let a₀ : ∀ i : {i // i ∈ leaves t}, X i.val :=
      fun i => Classical.choice inferInstance
    have unique (a : ∀ i : {i // i ∈ leaves t}, X i.val) : a = a₀ := by
      funext i
      have no : False := by simpa [t, leaves] using i.property
      exact no.elim
    have e : response X H (fun i => i ∈ leaves t) =
        fun _ => response X H (fun i => i ∈ leaves t) a₀ :=
      funext (fun a => congrArg _ (unique a))
    unfold capacity
    rw [e]
    simp
  have only (s : Nodes t) : s.val = t := by simpa [t, subtrees] using s.property
  have hN : (Finset.univ : Finset (Nodes t)).Nonempty :=
    ⟨⟨t, by simp [t, subtrees]⟩, Finset.mem_univ _⟩
  refine ⟨hr, hk, ?_, ?_⟩
  · have e : protocolVector t D m = fun _ => 1 := by
      funext s
      simpa [protocolVector, only s] using hr
    rw [e]
    exact Finset.sup_const hN 1
  · have e : capacityVector t H = fun _ => 1 := by
      funext s
      simpa [capacityVector, only s] using hk
    rw [e]
    exact Finset.sup_const hN 1

/-- Native common extension, native response realization, the whole vector
upward closure, all attained monotone costs, and the original-node peak. -/
theorem result {I V O : Type} [Fintype I] {X : I → Type}
    [∀ i, Finite (X i)] [∀ i, Nonempty (X i)]
    (t : Tree I V) (ht : Full t) (hall : leaves t = Finset.univ)
    (D : Set (∀ i, X i)) (hD : D.Nonempty) (f : D → O) :
    (∀ (m : Implementation (V := V) X) (read : m.Message t → O),
      (∀ x : D, read (evaluate m t x.val) = f x) →
      ∃ H : (∀ i, X i) → O, (∀ x : D, H x.val = f x) ∧
        capacityVector t H ≤ protocolVector t D m) ∧
    (∀ H : (∀ i, X i) → O, (∀ x : D, H x.val = f x) →
      ∃ read : (canonical H (V := V)).Message t → O,
        (∀ x : D, read (evaluate (canonical H) t x.val) = f x) ∧
        protocolVector t D (canonical H) ≤ capacityVector t H ∧
        ∀ s ∈ subtrees t,
          Set.range (fun x : D => evaluate (canonical H) s x.val) =
          Set.range (fun x : D => responseMessage H s x.val)) ∧
    (∀ b : Nodes t → ℕ,
      (∃ (m : Implementation (V := V) X) (read : m.Message t → O),
        (∀ x : D, read (evaluate m t x.val) = f x) ∧ protocolVector t D m ≤ b) ↔
      (∃ H : (∀ i, X i) → O, (∀ x : D, H x.val = f x) ∧ capacityVector t H ≤ b)) ∧
    (∀ (L : Type) [LinearOrder L] (C : (Nodes t → ℕ) → L),
      Monotone C → OptimalPair t D f C) ∧
    OptimalPair t D f (fun k => Finset.univ.sup k) ∧
    (∀ (v : V) (c : Fin 0 → Tree I V) (m : Implementation (V := V) X),
      ∀ H : (∀ i, X i) → O,
        reachable m D (.node v 0 c) = 1 ∧
        capacity X H (fun i => i ∈ leaves (.node v 0 c)) = 1 ∧
        Finset.univ.sup (protocolVector (.node v 0 c) D m) = 1 ∧
        Finset.univ.sup (capacityVector (.node v 0 c) H) = 1) := by
  classical
  obtain ⟨hup,hcost⟩ := vector_and_cost t ht hall D hD f
  refine ⟨?_, ?_, hup, hcost, hcost ℕ (fun k => Finset.univ.sup k) ?_, ?_⟩
  · intro m read hc
    obtain ⟨H,hH,hb⟩ := common_extension t ht D hD f m read hc
    exact ⟨H,hH,fun s => hb s.val s.property⟩
  · intro H hH
    obtain ⟨read,hc,hr,hb⟩ := canonical_realization t ht hall H D
    exact ⟨read,fun x => (hc x.val).trans (hH x),fun s => hb s.val s.property,hr⟩
  · intro a b hab
    apply Finset.sup_le
    intro s hs
    exact (hab s).trans (Finset.le_sup hs)
  · intro v c m H
    exact empty_node_laws D hD v c m H

#print axioms result

end D5.S3.Observer.Separation.FixedTreeCommonExtension
