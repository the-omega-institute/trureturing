/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalObstruction
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Native finite-cycle descent and whole-system extension of closed boundaries. -/

import D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion

/-! Raw functional systems use the existing unrestricted native completion.
Finite dependency descent uses a positive additive weight on actual leaves.
Closed boundary assignments extend through native leaf limits to joint solutions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeFunctionalObstruction

open GenealogicalFiberTransport (Source substitution)
open NativeCompletionPrefixLifting
open CompletionHomogeneousFixedPoints
open ActualTreeReadoutAcquisition (Address)

abbrev Expr (m : Nat) := CompletionPositiveDriftRegion.Expr 0 m

def value {m : Nat} (v : Fin m → CompletionTree) (E : Expr m) : CompletionTree :=
  CompletionPositiveDriftRegion.value Fin.elim0 Fin.elim0 v E

/-- One optional original equation for each state. Undefined states have no
constraint; the values of every defined state and all auxiliaries are joint. -/
abbrev System (m : Nat) := Fin m → Option (Expr m)

def Satisfies {m : Nat} (S : System m) (v : Fin m → CompletionTree) : Prop :=
  ∀ i E, S i = some E → v i = value v E

/-- Each component carries its actual original designated coordinate. -/
structure Component where
  states : Nat
  equations : System states
  designated : Fin states

def projected (S : Component) : Set CompletionTree :=
  {X | ∃ v, Satisfies S.equations v ∧ v S.designated = X}

def represented (family : List Component) : Set CompletionTree :=
  {X | ∃ S ∈ family, X ∈ projected S}

/-- The full original statement, on the unrestricted completed native domain. -/
def Obstruction : Prop :=
  ∀ (a : Nat) (H : Homogeneous), PairRoot H →
    eval H (leaf true) = atomic a → ∀ family : List Component,
      {X : CompletionTree | rho^[a] X = eval H X} ≠ represented family

/-- A finite native tree has positive leaf weight, including both leaf labels. -/
def leafWeight : Source → Nat
  | .of b => if b then 1 else 2
  | .mul s t => leafWeight s + leafWeight t

private theorem leafWeight_pos (t : Source) : 0 < leafWeight t := by
  induction t with
  | of b => cases b <;> decide
  | mul s t ihs iht => change 0 < leafWeight s + leafWeight t; omega

private theorem leafWeight_substitution (t : Source) :
    leafWeight t < leafWeight (substitution t) := by
  induction t with
  | of b => cases b <;> decide
  | mul s t ihs iht =>
    change leafWeight s + leafWeight t <
      leafWeight (substitution s) + leafWeight (substitution t)
    omega

private theorem leafWeight_iterate (a : Nat) (t : Source) :
    leafWeight t ≤ leafWeight (substitution^[a] t) ∧
      (0 < a → leafWeight t < leafWeight (substitution^[a] t)) := by
  induction a with
  | zero => exact ⟨le_rfl, by omega⟩
  | succ a ih =>
    rw [Function.iterate_succ_apply']
    have inc := leafWeight_substitution (substitution^[a] t)
    exact ⟨by omega, by omega⟩

private theorem leafWeight_subtree (p : Address) (s t : Source)
    (present : subtree p (embed s) = some (embed t)) :
    leafWeight t ≤ leafWeight s ∧ (p ≠ [] → leafWeight t < leafWeight s) := by
  induction p generalizing s with
  | nil =>
    have eq := NativeCompletionSupportClosure.embed_injective (Option.some.inj present)
    subst s
    exact ⟨le_rfl, fun h => (h rfl).elim⟩
  | cons b p ih =>
    cases s with
    | of c => simp [subtree, embed, leaf] at present
    | mul s u =>
      have ps := leafWeight_pos s
      have pu := leafWeight_pos u
      cases b
      · have h := (ih s present).1
        change leafWeight t ≤ leafWeight s + leafWeight u ∧ _
        exact ⟨by omega, by intro _; change leafWeight t < leafWeight s + leafWeight u; omega⟩
      · have h := (ih u present).1
        change leafWeight t ≤ leafWeight s + leafWeight u ∧ _
        exact ⟨by omega, by intro _; change leafWeight t < leafWeight s + leafWeight u; omega⟩

/-- Every occurrence belongs to the supplied right side of an original equation. -/
structure Dependency {m : Nat} (S : System m) (i j : Fin m) where
  expression : Expr m
  equation : S i = some expression
  address : Address
  power : Nat
  occurrence : CompletionPositiveDriftRegion.Occurs expression address power j

private theorem dependency_present {m : Nat} {S : System m}
    {v : Fin m → CompletionTree} (sat : Satisfies S v) {i j : Fin m}
    (e : Dependency S i j) :
    subtree e.address (v i) = some (rho^[e.power] (v j)) := by
  rw [sat i e.expression e.equation]
  exact CompletionPositiveDriftRegion.occurrence_value Fin.elim0 Fin.elim0 v e.occurrence

/-- A finite designated value constrains its own dependencies; no finiteness
condition is imposed on disconnected or unused auxiliary states. -/
private theorem finite_dependency_descent {m : Nat} {S : System m}
    {v : Fin m → CompletionTree} (sat : Satisfies S v) {i j : Fin m}
    (e : Dependency S i j) (s : Source) (hs : embed s = v i) :
    ∃ t : Source, embed t = v j ∧ leafWeight t ≤ leafWeight s ∧
      (e.address ≠ [] ∨ 0 < e.power → leafWeight t < leafWeight s) := by
  have present := dependency_present sat e
  have fj : IsFinite (v j) :=
    (finite_iterate_iff e.power _).mp
      (finite_subtree e.address ⟨s, hs⟩ present)
  obtain ⟨t, ht⟩ := fj
  rw [← hs, ← ht, iterate_embed] at present
  have below := leafWeight_subtree e.address s (substitution^[e.power] t) present
  have shifted := leafWeight_iterate e.power t
  refine ⟨t, ht, ?_, ?_⟩
  · omega
  · rintro (guarded | positive)
    · have strict := below.2 guarded
      omega
    · have strict := shifted.2 positive
      omega

inductive Walk {m : Nat} (S : System m) : Fin m → Fin m → Type where
  | nil (i : Fin m) : Walk S i i
  | cons {i j k : Fin m} : Dependency S i j → Walk S j k → Walk S i k

/-- An occurrence beneath a pair or with a positive shift is a strict edge. -/
def Walk.Strict {m : Nat} {S : System m} {i j : Fin m} : Walk S i j → Prop
  | .nil _ => False
  | .cons e tail => e.address ≠ [] ∨ 0 < e.power ∨ tail.Strict

private theorem finite_walk_descent {m : Nat} {S : System m}
    {v : Fin m → CompletionTree} (sat : Satisfies S v) {i j : Fin m}
    (walk : Walk S i j) (s : Source) (hs : embed s = v i) :
    ∃ t : Source, embed t = v j ∧ leafWeight t ≤ leafWeight s ∧
      (walk.Strict → leafWeight t < leafWeight s) := by
  induction walk generalizing s with
  | nil i => exact ⟨s, hs, le_rfl, False.elim⟩
  | cons edge tail ih =>
    obtain ⟨u, hu, leu, ltu⟩ := finite_dependency_descent sat edge s hs
    obtain ⟨t, ht, let_, ltt⟩ := ih u hu
    refine ⟨t, ht, let_.trans leu, ?_⟩
    rintro (guarded | positive | strict)
    · exact let_.trans_lt (ltu (Or.inl guarded))
    · exact let_.trans_lt (ltu (Or.inr positive))
    · exact (ltt strict).trans_le leu

/-- Every dependency cycle at a finite native value consists solely of
zero-power root links. Infinite values at other states remain unrestricted. -/
theorem finite_cycle_is_silent {m : Nat} {S : System m}
    {v : Fin m → CompletionTree} (sat : Satisfies S v) {i : Fin m}
    (cycle : Walk S i i) (finite : IsFinite (v i)) : ¬ cycle.Strict := by
  obtain ⟨s, hs⟩ := finite
  obtain ⟨t, ht, _, strict⟩ := finite_walk_descent sat cycle s hs
  have eq := NativeCompletionSupportClosure.embed_injective (ht.trans hs.symm)
  subst t
  intro live
  exact (Nat.lt_irrefl _) (strict live)

private def LeafAt (X : CompletionTree) (p : Address) (b : Bool) : Prop :=
  completionReadout p X = if b then Reply.alpha else Reply.beta

private theorem leafAt_leaf (c : Bool) (p : Address) (b : Bool) :
    LeafAt (leaf c) p b ↔ p = [] ∧ c = b := by
  cases p <;> cases c <;> cases b <;> simp [LeafAt, completionReadout, leaf]

private theorem leafAt_node_nil (l r : CompletionTree) (b : Bool) :
    ¬ LeafAt (node l r) [] b := by
  cases b <;> simp [LeafAt, completionReadout, node]

private theorem leafAt_node_cons (l r : CompletionTree) (c : Bool) (p : Address) (b : Bool) :
    LeafAt (node l r) (c :: p) b ↔ LeafAt (if c then r else l) p b := by
  cases c <;> rfl

private theorem leafAt_root (X : CompletionTree) (b : Bool) :
    LeafAt X [] b ↔ X = leaf b := by
  induction X using tree_cases with
  | leaf_case c =>
    rw [leafAt_leaf]
    constructor
    · rintro ⟨_, rfl⟩; rfl
    · intro h
      have tag := congrArg (fun T => (PFunctor.M.dest T).1) h
      have ht : (Sum.inl c : Bool ⊕ Unit) = Sum.inl b := by
        simpa only [leaf, PFunctor.M.dest_mk] using tag
      exact ⟨rfl, Sum.inl.inj ht⟩
  | node_case l r =>
    constructor
    · exact fun h => (leafAt_node_nil l r b h).elim
    · intro h
      have tag := congrArg (fun T => (PFunctor.M.dest T).1) h
      simp [leaf, node] at tag

private def LeafBelow (X Y : CompletionTree) : Prop :=
  ∀ p b, LeafAt X p b → LeafAt Y p b

private theorem leafBelow_refl (X : CompletionTree) : LeafBelow X X := fun _ _ h => h

private theorem leafBelow_trans {X Y Z : CompletionTree}
    (h : LeafBelow X Y) (k : LeafBelow Y Z) : LeafBelow X Z :=
  fun p b hp => k p b (h p b hp)

private theorem leafBelow_leaf {b : Bool} {X : CompletionTree}
    (h : LeafBelow (leaf b) X) : X = leaf b :=
  (leafAt_root X b).mp (h [] b ((leafAt_leaf b [] b).mpr ⟨rfl, rfl⟩))

private theorem leafBelow_children {l r s t : CompletionTree}
    (h : LeafBelow (node l r) (node s t)) (b : Bool) :
    LeafBelow (if b then r else l) (if b then t else s) := by
  intro p c hp
  exact (leafAt_node_cons s t b p c).mp
    (h (b :: p) c ((leafAt_node_cons l r b p c).mpr hp))

private theorem leafBelow_ext {X Y : CompletionTree}
    (h : LeafBelow X Y) (k : LeafBelow Y X) : X = Y := by
  apply readout_ext
  intro p
  induction p generalizing X Y with
  | nil =>
    induction X using tree_cases with
    | leaf_case b => rw [leafBelow_leaf h]
    | node_case l r =>
      induction Y using tree_cases with
      | leaf_case b => rw [leafBelow_leaf k]
      | node_case s t => rfl
  | cons b p ih =>
    induction X using tree_cases with
    | leaf_case c => rw [leafBelow_leaf h]
    | node_case l r =>
      induction Y using tree_cases with
      | leaf_case c => rw [leafBelow_leaf k]
      | node_case s t =>
        exact ih (leafBelow_children h b) (leafBelow_children k b)

private theorem omega_no_leaf (p : Address) (b : Bool) : ¬ LeafAt Omega p b := by
  have full : Full (p.length + 1) Omega := by
    simpa only [iterate_omega] using iterate_full (p.length + 1) Omega
  have branch := full p (by omega)
  cases b <;> simp [LeafAt, branch]

private theorem omega_below (X : CompletionTree) : LeafBelow Omega X :=
  fun p b h => (omega_no_leaf p b h).elim

private def child (b : Bool) (X : CompletionTree) : CompletionTree :=
  match PFunctor.M.dest X with
  | ⟨.inl _, _⟩ => Omega
  | ⟨.inr _, f⟩ => f b

private theorem child_node (b : Bool) (l r : CompletionTree) :
    child b (node l r) = if b then r else l := by cases b <;> rfl

private def Increasing (C : Nat → CompletionTree) : Prop :=
  ∀ n k, n ≤ k → LeafBelow (C n) (C k)

private noncomputable def nativeLimitStep (C : Nat → CompletionTree) :
    completionFunctor (Nat → CompletionTree) := by
  classical
  exact if h : ∃ b n, C n = leaf b then ⟨.inl (Classical.choose h), Empty.elim⟩
    else ⟨.inr (), fun b n => child b (C n)⟩

private noncomputable def nativeLimit (C : Nat → CompletionTree) : CompletionTree :=
  PFunctor.M.corec nativeLimitStep C

private theorem chain_leaf_bound {C : Nat → CompletionTree} (inc : Increasing C)
    {n : Nat} {b : Bool} (eq : C n = leaf b) (k : Nat) : LeafBelow (C k) (leaf b) := by
  by_cases h : k ≤ n
  · simpa [eq] using inc k n h
  · have h' := inc n k (by omega)
    rw [eq] at h'
    rw [leafBelow_leaf h']
    exact leafBelow_refl _

private theorem nativeLimit_leaf {C : Nat → CompletionTree} (inc : Increasing C)
    {n : Nat} {b : Bool} (eq : C n = leaf b) : nativeLimit C = leaf b := by
  classical
  have exists_ : ∃ c k, C k = leaf c := ⟨b, n, eq⟩
  obtain ⟨k, hk⟩ := Classical.choose_spec exists_
  have tag : Classical.choose exists_ = b := by
    have h := chain_leaf_bound inc eq k
    rw [hk] at h
    have hl := leafBelow_leaf h
    have tags := congrArg (fun T => (PFunctor.M.dest T).1) hl
    have ht : (Sum.inl b : Bool ⊕ Unit) = Sum.inl (Classical.choose exists_) := by
      simpa only [leaf, PFunctor.M.dest_mk] using tags
    exact (Sum.inl.inj ht).symm
  unfold nativeLimit
  rw [PFunctor.M.corec_def]
  unfold nativeLimitStep
  rw [dite_eq_left exists_, tag]
  apply congrArg PFunctor.M.mk
  apply Sigma.ext (by simp [PFunctor.map, PFunctor.Obj.mk, PFunctor.Obj.fst, PFunctor.Obj.snd])
  apply heq_of_eq
  funext e
  exact e.elim

private theorem nativeLimit_node {C : Nat → CompletionTree}
    (no : ¬ ∃ b n, C n = leaf b) :
    nativeLimit C = node (nativeLimit (fun n => child false (C n)))
      (nativeLimit (fun n => child true (C n))) := by
  classical
  unfold nativeLimit
  rw [PFunctor.M.corec_def]
  unfold nativeLimitStep
  rw [dite_eq_right no]
  simp only [PFunctor.map, node]
  congr 2
  funext b
  cases b <;> rfl

private theorem child_increasing {C : Nat → CompletionTree} (inc : Increasing C)
    (no : ¬ ∃ b n, C n = leaf b) (b : Bool) :
    Increasing (fun n => child b (C n)) := by
  intro n k h
  have hn : ¬ ∃ c, C n = leaf c := fun ⟨c, hc⟩ => no ⟨c, n, hc⟩
  have hk : ¬ ∃ c, C k = leaf c := fun ⟨c, hc⟩ => no ⟨c, k, hc⟩
  generalize en : C n = X at *
  generalize ek : C k = Y at *
  induction X using tree_cases with
  | leaf_case c => exact (hn ⟨c, rfl⟩).elim
  | node_case l r =>
    induction Y using tree_cases with
    | leaf_case c => exact (hk ⟨c, rfl⟩).elim
    | node_case s t =>
      change LeafBelow (child b (C n)) (child b (C k))
      rw [en, ek, child_node, child_node]
      exact leafBelow_children (by simpa only [en, ek] using inc n k h) b

private theorem nativeLimit_leaves (C : Nat → CompletionTree) (inc : Increasing C)
    (p : Address) (b : Bool) :
    LeafAt (nativeLimit C) p b ↔ ∃ n, LeafAt (C n) p b := by
  classical
  induction p generalizing C with
  | nil =>
    by_cases h : ∃ c n, C n = leaf c
    · obtain ⟨c, n, hn⟩ := h
      rw [nativeLimit_leaf inc hn]
      constructor
      · intro hp; exact ⟨n, hn.symm ▸ hp⟩
      · rintro ⟨k, hk⟩; exact chain_leaf_bound inc hn k [] b hk
    · rw [nativeLimit_node h]
      constructor
      · exact fun hp => (leafAt_node_nil _ _ _ hp).elim
      · rintro ⟨n, hn⟩; exact (h ⟨b, n, (leafAt_root _ _).mp hn⟩).elim
  | cons c p ih =>
    by_cases h : ∃ d n, C n = leaf d
    · obtain ⟨d, n, hn⟩ := h
      rw [nativeLimit_leaf inc hn]
      constructor
      · intro hp; exact ⟨n, hn.symm ▸ hp⟩
      · rintro ⟨k, hk⟩; exact chain_leaf_bound inc hn k (c :: p) b hk
    · rw [nativeLimit_node h, leafAt_node_cons]
      have hc := child_increasing inc h c
      have shape : (if c then nativeLimit (fun n => child true (C n))
          else nativeLimit (fun n => child false (C n))) =
          nativeLimit (fun n => child c (C n)) := by cases c <;> rfl
      rw [shape, ih _ hc]
      apply exists_congr
      intro n
      generalize en : C n = X
      induction X using tree_cases with
      | leaf_case d => exact (h ⟨d, n, en⟩).elim
      | node_case l r => rw [child_node, leafAt_node_cons]

private theorem rho_leaf_trace (X : CompletionTree) (p : Address) (b : Bool) :
    LeafAt (rho X) p b ↔ ∃ q r c,
      p = q ++ r ∧ LeafAt X q c ∧ LeafAt (rho (leaf c)) r b := by
  induction p generalizing X with
  | nil =>
    induction X using tree_cases with
    | leaf_case d =>
      constructor
      · intro h; exact ⟨[], [], d, rfl, (leafAt_leaf _ _ _).mpr ⟨rfl, rfl⟩, h⟩
      · rintro ⟨q, r, c, eq, src, dst⟩
        obtain ⟨rfl, rfl⟩ := (leafAt_leaf _ _ _).mp src
        simpa using eq ▸ dst
    | node_case l r =>
      rw [rho_node]
      constructor
      · exact fun h => (leafAt_node_nil _ _ _ h).elim
      · rintro ⟨q, s, c, eq, src, _⟩
        have qnil : q = [] := (List.append_eq_nil_iff.mp eq.symm).1
        subst q
        exact (leafAt_node_nil _ _ _ src).elim
  | cons d p ih =>
    induction X using tree_cases with
    | leaf_case c =>
      constructor
      · intro h; exact ⟨[], d :: p, c, rfl, (leafAt_leaf _ _ _).mpr ⟨rfl, rfl⟩, h⟩
      · rintro ⟨q, r, c', eq, src, dst⟩
        obtain ⟨rfl, rfl⟩ := (leafAt_leaf _ _ _).mp src
        simpa using eq ▸ dst
    | node_case l r =>
      rw [rho_node, leafAt_node_cons]
      have shape : (if d then rho r else rho l) = rho (if d then r else l) := by
        cases d <;> rfl
      rw [shape, ih]
      constructor
      · rintro ⟨q, s, c, eq, src, dst⟩
        exact ⟨d :: q, s, c, by simp [eq],
          (leafAt_node_cons _ _ _ _ _).mpr src, dst⟩
      · rintro ⟨q, s, c, eq, src, dst⟩
        cases q with
        | nil => exact (leafAt_node_nil _ _ _ src).elim
        | cons e q =>
          have ee : d = e := (List.cons.inj eq).1
          subst e
          exact ⟨q, s, c, (List.cons.inj eq).2,
            (leafAt_node_cons _ _ _ _ _).mp src, dst⟩

private theorem rho_leafBelow {X Y : CompletionTree} (h : LeafBelow X Y) :
    LeafBelow (rho X) (rho Y) := by
  intro p b hp
  obtain ⟨q, r, c, eq, src, dst⟩ := (rho_leaf_trace X p b).mp hp
  exact (rho_leaf_trace Y p b).mpr ⟨q, r, c, eq, h q c src, dst⟩

private theorem iterate_leafBelow (a : Nat) {X Y : CompletionTree} (h : LeafBelow X Y) :
    LeafBelow (rho^[a] X) (rho^[a] Y) := by
  induction a with
  | zero => exact h
  | succ a ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact rho_leafBelow ih

private def LeafLimit (C : Nat → CompletionTree) (X : CompletionTree) : Prop :=
  ∀ p b, LeafAt X p b ↔ ∃ n, LeafAt (C n) p b

private theorem rho_leafLimit {C : Nat → CompletionTree} {X : CompletionTree}
    (h : LeafLimit C X) : LeafLimit (fun n => rho (C n)) (rho X) := by
  intro p b
  constructor
  · intro hp
    obtain ⟨q, r, c, eq, src, dst⟩ := (rho_leaf_trace X p b).mp hp
    obtain ⟨n, hn⟩ := (h q c).mp src
    exact ⟨n, (rho_leaf_trace _ _ _).mpr ⟨q, r, c, eq, hn, dst⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨q, r, c, eq, src, dst⟩ := (rho_leaf_trace _ _ _).mp hn
    exact (rho_leaf_trace X p b).mpr ⟨q, r, c, eq, (h q c).mpr ⟨n, src⟩, dst⟩

private theorem iterate_leafLimit (a : Nat) {C : Nat → CompletionTree} {X : CompletionTree}
    (h : LeafLimit C X) : LeafLimit (fun n => rho^[a] (C n)) (rho^[a] X) := by
  induction a with
  | zero => exact h
  | succ a ih =>
    simpa only [Function.iterate_succ_apply'] using rho_leafLimit ih

private theorem node_leafBelow {l r s t : CompletionTree}
    (hl : LeafBelow l s) (hr : LeafBelow r t) : LeafBelow (node l r) (node s t) := by
  intro p b hp
  cases p with
  | nil => exact (leafAt_node_nil _ _ _ hp).elim
  | cons c p =>
    rw [leafAt_node_cons] at hp ⊢
    cases c
    · exact hl p b hp
    · exact hr p b hp

private theorem node_leafLimit {C D : Nat → CompletionTree} {X Y : CompletionTree}
    (hx : LeafLimit C X) (hy : LeafLimit D Y) :
    LeafLimit (fun n => node (C n) (D n)) (node X Y) := by
  intro p b
  cases p with
  | nil => simp only [leafAt_node_nil, exists_false]
  | cons c p =>
    cases c
    · simpa only [leafAt_node_cons, Bool.false_eq_true, ite_false] using hx p b
    · simpa only [leafAt_node_cons, ite_true] using hy p b

private theorem value_leafBelow {m : Nat} {v w : Fin m → CompletionTree}
    (h : ∀ i, LeafBelow (v i) (w i)) (E : Expr m) :
    LeafBelow (value v E) (value w E) := by
  induction E with
  | ground t => exact leafBelow_refl _
  | token i c => exact Fin.elim0 i
  | var a i => exact iterate_leafBelow a (h i)
  | pair A B ihA ihB => exact node_leafBelow ihA ihB

private theorem value_leafLimit {m : Nat} {C : Nat → Fin m → CompletionTree}
    {v : Fin m → CompletionTree} (h : ∀ i, LeafLimit (fun n => C n i) (v i))
    (E : Expr m) : LeafLimit (fun n => value (C n) E) (value v E) := by
  induction E with
  | ground t => intro p b; exact ⟨fun hp => ⟨0, hp⟩, fun ⟨_, hp⟩ => hp⟩
  | token i c => exact Fin.elim0 i
  | var a i => exact iterate_leafLimit a (h i)
  | pair A B ihA ihB => exact node_leafLimit ihA ihB

private theorem leafLimit_unique {C : Nat → CompletionTree} {X Y : CompletionTree}
    (hx : LeafLimit C X) (hy : LeafLimit C Y) : X = Y :=
  leafBelow_ext (fun p b hp => (hy p b).mpr ((hx p b).mp hp))
    (fun p b hp => (hx p b).mpr ((hy p b).mp hp))

/-- A boundary is closed under every original occurrence, including occurrences
with zero powers and occurrences below arbitrary ordered pairs. -/
def BoundaryClosed {m : Nat} (S : System m) (B : Fin m → Prop) : Prop :=
  ∀ i E, B i → S i = some E → ∀ p a j,
    CompletionPositiveDriftRegion.Occurs E p a j → B j

/-- Only the original equations belonging to the boundary are required. -/
def BoundaryValid {m : Nat} (S : System m) (B : Fin m → Prop)
    (v : Fin m → CompletionTree) : Prop :=
  ∀ i E, B i → S i = some E → v i = value v E

private noncomputable def extensionStep {m : Nat} (S : System m)
    (B : Fin m → Prop) (v : Fin m → CompletionTree) (w : Fin m → CompletionTree) :
    Fin m → CompletionTree := by
  classical
  exact fun i => if B i then v i else match S i with
    | none => Omega
    | some E => value w E

private theorem extensionStep_mono {m : Nat} (S : System m) (B : Fin m → Prop)
    (v : Fin m → CompletionTree) {w z : Fin m → CompletionTree}
    (h : ∀ i, LeafBelow (w i) (z i)) :
    ∀ i, LeafBelow (extensionStep S B v w i) (extensionStep S B v z i) := by
  classical
  intro i
  unfold extensionStep
  split
  · exact leafBelow_refl _
  · cases S i with
    | none => exact leafBelow_refl _
    | some E => exact value_leafBelow h E

private theorem extensionStep_limit {m : Nat} (S : System m) (B : Fin m → Prop)
    (v : Fin m → CompletionTree) {C : Nat → Fin m → CompletionTree}
    {w : Fin m → CompletionTree} (h : ∀ i, LeafLimit (fun n => C n i) (w i)) :
    ∀ i, LeafLimit (fun n => extensionStep S B v (C n) i)
      (extensionStep S B v w i) := by
  classical
  intro i
  unfold extensionStep
  by_cases bi : B i
  · simp only [ite_eq_left bi]
    intro p b
    exact ⟨fun hp => ⟨0, hp⟩, fun ⟨_, hp⟩ => hp⟩
  · simp only [ite_eq_right bi]
    cases S i with
    | none =>
      intro p b
      exact ⟨fun hp => ⟨0, hp⟩, fun ⟨_, hp⟩ => hp⟩
    | some E => exact value_leafLimit h E

private noncomputable def extensionIterate {m : Nat} (S : System m)
    (B : Fin m → Prop) (v : Fin m → CompletionTree) : Nat → Fin m → CompletionTree
  | 0 => fun _ => Omega
  | n+1 => extensionStep S B v (extensionIterate S B v n)

private theorem extensionIterate_mono {m : Nat} (S : System m)
    (B : Fin m → Prop) (v : Fin m → CompletionTree) :
    ∀ n k, n ≤ k → ∀ i, LeafBelow (extensionIterate S B v n i)
      (extensionIterate S B v k i) := by
  have step : ∀ n i, LeafBelow (extensionIterate S B v n i)
      (extensionIterate S B v (n+1) i) := by
    intro n
    induction n with
    | zero => intro i; exact omega_below _
    | succ n ih => exact extensionStep_mono S B v ih
  intro n k h
  induction h with
  | refl => intro i; exact leafBelow_refl _
  | step hk ih => intro i; exact leafBelow_trans (ih i) (step _ i)

private theorem value_boundary_congr {m : Nat} {B : Fin m → Prop}
    {v w : Fin m → CompletionTree} (same : ∀ i, B i → v i = w i)
    (E : Expr m) (closed : ∀ p a j,
      CompletionPositiveDriftRegion.Occurs E p a j → B j) : value v E = value w E := by
  induction E with
  | ground t => rfl
  | token i c => exact Fin.elim0 i
  | var a i =>
    change rho^[a] (v i) = rho^[a] (w i)
    rw [same i (closed [] a i (.var a i))]
  | pair A B ihA ihB =>
    exact congrArg₂ node
      (ihA (fun p a j h => closed (false :: p) a j (.left h)))
      (ihB (fun p a j h => closed (true :: p) a j (.right h)))

/-- Every closed boundary assignment satisfying its own original equations
extends to a simultaneous solution of the entire native functional system.
The boundary and all other values may be finite or arbitrarily infinite. -/
theorem whole_system_boundary_extension {m : Nat} (S : System m) (B : Fin m → Prop)
    (v : Fin m → CompletionTree) (closed : BoundaryClosed S B)
    (valid : BoundaryValid S B v) :
    ∃ w : Fin m → CompletionTree, Satisfies S w ∧ ∀ i, B i → w i = v i := by
  classical
  let C := extensionIterate S B v
  let w : Fin m → CompletionTree := fun i => nativeLimit (fun n => C n i)
  have lim : ∀ i, LeafLimit (fun n => C n i) (w i) := by
    intro i
    exact nativeLimit_leaves _ (fun n k h => extensionIterate_mono S B v n k h i)
  have shift : ∀ i, LeafLimit (fun n => extensionStep S B v (C n) i) (w i) := by
    intro i p b
    rw [lim i p b]
    constructor
    · rintro ⟨n, hn⟩
      cases n with
      | zero => exact (omega_no_leaf p b hn).elim
      | succ n => exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩; exact ⟨n+1, hn⟩
  have fixed : ∀ i, w i = extensionStep S B v w i := by
    intro i
    exact leafLimit_unique (shift i) (extensionStep_limit S B v lim i)
  have same : ∀ i, B i → w i = v i := by
    intro i hi
    rw [fixed i]
    simp only [extensionStep, ite_eq_left hi]
  refine ⟨w, ?_, same⟩
  intro i E eq
  by_cases hi : B i
  · rw [same i hi, valid i E hi eq]
    exact value_boundary_congr (fun j hj => (same j hj).symm) E (closed i E hi eq)
  · rw [fixed i]
    simp only [extensionStep, ite_eq_right hi, eq]

end D5.S3.Arith.FibonacciAtomic.Observer.NativeFunctionalObstruction
