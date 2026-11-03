/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalObstruction
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Native finite descent, whole-system extension and finite-coordinate perturbation. -/

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
open ActualTreeReadoutAcquisition (Address Reply)

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

def LeafAt (X : CompletionTree) (p : Address) (b : Bool) : Prop :=
  completionReadout p X = if b then Reply.alpha else Reply.beta

theorem leafAt_leaf (c : Bool) (p : Address) (b : Bool) :
    LeafAt (leaf c) p b ↔ p = [] ∧ c = b := by
  cases p <;> cases c <;> cases b <;> simp [LeafAt, completionReadout, leaf]

theorem leafAt_node_nil (l r : CompletionTree) (b : Bool) :
    ¬ LeafAt (node l r) [] b := by
  cases b <;> simp [LeafAt, completionReadout, node]

theorem leafAt_node_cons (l r : CompletionTree) (c : Bool) (p : Address) (b : Bool) :
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

def LeafBelow (X Y : CompletionTree) : Prop :=
  ∀ p b, LeafAt X p b → LeafAt Y p b

private theorem leafBelow_refl (X : CompletionTree) : LeafBelow X X := fun _ _ h => h

private theorem leafBelow_trans {X Y Z : CompletionTree}
    (h : LeafBelow X Y) (k : LeafBelow Y Z) : LeafBelow X Z :=
  fun p b hp => k p b (h p b hp)

theorem leafBelow_leaf {b : Bool} {X : CompletionTree}
    (h : LeafBelow (leaf b) X) : X = leaf b :=
  (leafAt_root X b).mp (h [] b ((leafAt_leaf b [] b).mpr ⟨rfl, rfl⟩))

theorem leafBelow_children {l r s t : CompletionTree}
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

theorem omega_no_leaf (p : Address) (b : Bool) : ¬ LeafAt Omega p b := by
  have full : Full (p.length + 1) Omega := by
    simpa only [iterate_omega] using iterate_full (p.length + 1) Omega
  have branch := full p (by omega)
  cases b <;> simp [LeafAt, branch]

theorem omega_below (X : CompletionTree) : LeafBelow Omega X :=
  fun p b h => (omega_no_leaf p b h).elim

private def child (b : Bool) (X : CompletionTree) : CompletionTree :=
  match PFunctor.M.dest X with
  | ⟨.inl _, _⟩ => Omega
  | ⟨.inr _, f⟩ => f b

private theorem child_node (b : Bool) (l r : CompletionTree) :
    child b (node l r) = if b then r else l := by cases b <;> rfl

def Increasing (C : Nat → CompletionTree) : Prop :=
  ∀ n k, n ≤ k → LeafBelow (C n) (C k)

private noncomputable def nativeLimitStep (C : Nat → CompletionTree) :
    completionFunctor (Nat → CompletionTree) := by
  classical
  exact if h : ∃ b n, C n = leaf b then ⟨.inl (Classical.choose h), Empty.elim⟩
    else ⟨.inr (), fun b n => child b (C n)⟩

noncomputable def nativeLimit (C : Nat → CompletionTree) : CompletionTree :=
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

theorem nativeLimit_leaves (C : Nat → CompletionTree) (inc : Increasing C)
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

def LeafLimit (C : Nat → CompletionTree) (X : CompletionTree) : Prop :=
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

theorem value_leafBelow {m : Nat} {v w : Fin m → CompletionTree}
    (h : ∀ i, LeafBelow (v i) (w i)) (E : Expr m) :
    LeafBelow (value v E) (value w E) := by
  induction E with
  | ground t => exact leafBelow_refl _
  | token i c => exact Fin.elim0 i
  | var a i => exact iterate_leafBelow a (h i)
  | pair A B ihA ihB => exact node_leafBelow ihA ihB

theorem value_leafLimit {m : Nat} {C : Nat → Fin m → CompletionTree}
    {v : Fin m → CompletionTree} (h : ∀ i, LeafLimit (fun n => C n i) (v i))
    (E : Expr m) : LeafLimit (fun n => value (C n) E) (value v E) := by
  induction E with
  | ground t => intro p b; exact ⟨fun hp => ⟨0, hp⟩, fun ⟨_, hp⟩ => hp⟩
  | token i c => exact Fin.elim0 i
  | var a i => exact iterate_leafLimit a (h i)
  | pair A B ihA ihB => exact node_leafLimit ihA ihB

theorem leafLimit_unique {C : Nat → CompletionTree} {X Y : CompletionTree}
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

noncomputable def extensionStep {m : Nat} (S : System m)
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

theorem extensionStep_limit {m : Nat} (S : System m) (B : Fin m → Prop)
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

noncomputable def extensionIterate {m : Nat} (S : System m)
    (B : Fin m → Prop) (v : Fin m → CompletionTree) : Nat → Fin m → CompletionTree
  | 0 => fun _ => Omega
  | n+1 => extensionStep S B v (extensionIterate S B v n)

theorem extensionIterate_mono {m : Nat} (S : System m)
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


private inductive AliasPath {m : Nat} (S : System m) : Fin m → Fin m → Prop where
  | refl (i : Fin m) : AliasPath S i i
  | cons {i j k : Fin m} : S i = some (.var 0 j) → AliasPath S j k → AliasPath S i k

private theorem alias_value {m : Nat} {S : System m} {v : Fin m → CompletionTree}
    (sat : Satisfies S v) {i j : Fin m} (path : AliasPath S i j) : v i = v j := by
  induction path with
  | refl => rfl
  | cons eq _ ih => exact (sat _ _ eq).trans ih

/-- The region whose root-link paths encounter only zero-power aliases or
undefined states. Every original equation in this region is an alias. -/
private def FreeRegion {m : Nat} (S : System m) (i : Fin m) : Prop :=
  ∀ j, AliasPath S i j → ∀ E, S j = some E → ∃ k, E = .var 0 k

private theorem freeRegion_closed {m : Nat} (S : System m) :
    BoundaryClosed S (FreeRegion S) := by
  intro i E hi eq p a j occ
  obtain ⟨k, rfl⟩ := hi i (.refl i) E eq
  cases occ
  intro l path F ef
  exact hi l (.cons eq path) F ef

private theorem freeRegion_valid {m : Nat} (S : System m) (X : CompletionTree) :
    BoundaryValid S (FreeRegion S) (fun _ => X) := by
  intro i E hi eq
  obtain ⟨j, rfl⟩ := hi i (.refl i) E eq
  rfl

private theorem nonalias_occurrence_strict {m : Nat} {E : Expr m}
    (nonalias : ∀ j, E ≠ .var 0 j) {p : Address} {a : Nat} {j : Fin m}
    (occ : CompletionPositiveDriftRegion.Occurs E p a j) : p ≠ [] ∨ 0 < a := by
  cases occ with
  | var a j =>
    right
    by_contra h
    have ha : a = 0 := by omega
    subst a
    exact nonalias j rfl
  | left h => exact Or.inl (List.cons_ne_nil _ _)
  | right h => exact Or.inl (List.cons_ne_nil _ _)

private theorem finite_expression_compare {m : Nat}
    (u v w : Fin m → CompletionTree) (E : Expr m)
    (args : ∀ p a j, CompletionPositiveDriftRegion.Occurs E p a j →
      ∃ t : Source, embed t = w j ∧ (u j ≠ v j → 0 < NativePrefixIdentityReflection.gamma t)) :
    ∃ t : Source, embed t = value w E ∧
      (value u E ≠ value v E → 0 < NativePrefixIdentityReflection.gamma t) := by
  induction E with
  | ground t => exact ⟨t, rfl, fun h => (h rfl).elim⟩
  | token i c => exact Fin.elim0 i
  | var a j =>
    obtain ⟨t, ht, pos⟩ := args [] a j (.var a j)
    refine ⟨substitution^[a] t, ?_, ?_⟩
    · change embed (substitution^[a] t) = rho^[a] (w j)
      rw [← iterate_embed, ht]
    · intro h
      rw [NativePrefixIdentityReflection.gamma_iterate]
      exact pos (fun eq => h (congrArg (rho^[a]) eq))
  | pair A B ihA ihB =>
    obtain ⟨s, hs, ps⟩ := ihA (fun p a j h => args (false :: p) a j (.left h))
    obtain ⟨t, ht, pt⟩ := ihB (fun p a j h => args (true :: p) a j (.right h))
    refine ⟨.mul s t, ?_, ?_⟩
    · change node (embed s) (embed t) = node (value w A) (value w B)
      rw [hs, ht]
    · intro neq
      by_cases hA : value u A = value v A
      · have hB : value u B ≠ value v B := fun hB => neq (congrArg₂ node hA hB)
        exact (pt hB).trans_le (NativePrefixIdentityReflection.gamma_parent s t).2
      · exact (ps hA).trans_le (NativePrefixIdentityReflection.gamma_parent s t).1

/-- Any finite coordinate that can vary between two whole-system solutions
can be made finite with positive native mass in a solution of that same system.
All other original equations, including infinite auxiliaries, remain imposed. -/
theorem finite_coordinate_perturbation {m : Nat} {S : System m}
    {u v : Fin m → CompletionTree} (satU : Satisfies S u) (satV : Satisfies S v)
    {i : Fin m} (finite : IsFinite (v i)) :
    ∃ w : Fin m → CompletionTree, Satisfies S w ∧
      ∃ t : Source, embed t = w i ∧
        (u i ≠ v i → 0 < NativePrefixIdentityReflection.gamma t) := by
  classical
  let seed : Source := .mul (.of true) (.of true)
  have seed_pos : 0 < NativePrefixIdentityReflection.gamma seed := by decide
  obtain ⟨w, satW, same⟩ := whole_system_boundary_extension S (FreeRegion S)
    (fun _ => embed seed) (freeRegion_closed S) (freeRegion_valid S (embed seed))
  have reconstruct : ∀ n (j : Fin m) (s : Source), leafWeight s = n → embed s = v j →
      ∃ t : Source, embed t = w j ∧ (u j ≠ v j → 0 < NativePrefixIdentityReflection.gamma t) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j s weight finiteJ
      by_cases free : FreeRegion S j
      · exact ⟨seed, (same j free).symm, fun _ => seed_pos⟩
      · unfold FreeRegion at free
        push Not at free
        obtain ⟨k, path, E, eq, nonalias⟩ := free
        have vjk := alias_value satV path
        have ujk := alias_value satU path
        have wjk := alias_value satW path
        have args : ∀ p a l, CompletionPositiveDriftRegion.Occurs E p a l →
            ∃ t : Source, embed t = w l ∧
              (u l ≠ v l → 0 < NativePrefixIdentityReflection.gamma t) := by
          intro p a l occ
          let edge : Dependency S k l := ⟨E, eq, p, a, occ⟩
          obtain ⟨t, ht, _, strict⟩ := finite_dependency_descent satV edge s (finiteJ.trans vjk)
          have less : leafWeight t < n := by
            rw [← weight]
            exact strict (nonalias_occurrence_strict nonalias occ)
          exact ih (leafWeight t) less l t rfl ht
        obtain ⟨t, ht, pos⟩ := finite_expression_compare u v w E args
        refine ⟨t, ht.trans ((satW k E eq).symm.trans wjk.symm), ?_⟩
        intro neq
        apply pos
        intro heq
        exact neq (ujk.trans ((satU k E eq).trans (heq.trans ((satV k E eq).symm.trans vjk.symm))))
  obtain ⟨s, hs⟩ := finite
  exact ⟨w, satW, reconstruct (leafWeight s) i s rfl hs⟩


private theorem component_atomic_unique (a : Nat) (H : Homogeneous) (root : PairRoot H)
    (C : Component)
    (contained : projected C ⊆ {X : CompletionTree | rho^[a] X = eval H X})
    {c d : Nat} (hc : atomic c ∈ projected C) (hd : atomic d ∈ projected C) : c = d := by
  classical
  obtain ⟨u, satU, hu⟩ := hc
  obtain ⟨v, satV, hv⟩ := hd
  by_contra different
  have unequal : u C.designated ≠ v C.designated := by
    intro eq
    exact different (CompletionPositiveDriftRegion.atomic_injective (hu.symm.trans (eq.trans hv)))
  have finiteV : IsFinite (v C.designated) := by
    rw [hv]
    exact CompletionPositiveDriftRegion.atomic_finite d
  obtain ⟨w, satW, t, ht, pos⟩ := finite_coordinate_perturbation satU satV finiteV
  have feedback : rho^[a] (embed t) = eval H (embed t) :=
    contained ⟨w, satW, ht.symm⟩
  rcases (completed_homogeneous_split a H root (embed t)).mp feedback with omega | ⟨_, n, atom⟩
  · exact CompletionPositiveDriftRegion.omega_not_finite ⟨t, omega⟩
  · have eq : t = substitution^[n] (.of true) :=
      NativeCompletionSupportClosure.embed_injective (atom.trans (iterate_embed n (.of true)))
    have mass : NativePrefixIdentityReflection.gamma t = 0 := by
      rw [eq, NativePrefixIdentityReflection.gamma_iterate]
      rfl
    have positive := pos unequal
    omega

/-- Under only the original alpha anchor, no finite union of arbitrary
rank-free functional-system projections is the full homogeneous solution set. -/
private theorem distributed_rank_free_obstruction : Obstruction := by
  classical
  intro a H root anchor family equal
  let target : Set CompletionTree := {X | rho^[a] X = eval H X}
  have contained : ∀ C ∈ family, projected C ⊆ target := by
    intro C mem X hx
    have representedX : X ∈ represented family := ⟨C, mem, hx⟩
    rw [← equal] at representedX
    exact representedX
  have finite_orbit : ∀ L : List Component, (∀ C ∈ L, projected C ⊆ target) →
      Set.Finite {n : Nat | atomic n ∈ represented L} := by
    intro L
    induction L with
    | nil =>
      intro _
      have empty : {n : Nat | atomic n ∈ represented []} = ∅ := by
        ext n
        simp [represented]
      rw [empty]
      exact Set.finite_empty
    | cons C L ih =>
      intro subsets
      have singleton : Set.Subsingleton {n : Nat | atomic n ∈ projected C} := by
        intro c hc d hd
        exact component_atomic_unique a H root C (subsets C (by simp)) hc hd
      have tail := ih (fun D mem => subsets D (by simp [mem]))
      have union : {n : Nat | atomic n ∈ represented (C :: L)} =
          {n : Nat | atomic n ∈ projected C} ∪ {n : Nat | atomic n ∈ represented L} := by
        ext n
        simp only [Set.mem_setOf_eq, Set.mem_union, represented, List.mem_cons]
        constructor
        · rintro ⟨D, rfl | mem, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨D, mem, h⟩
        · rintro (h | ⟨D, mem, h⟩)
          · exact ⟨C, Or.inl rfl, h⟩
          · exact ⟨D, Or.inr mem, h⟩
      rw [union]
      exact singleton.finite.union tail
  have all : {n : Nat | atomic n ∈ represented family} = Set.univ := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rw [← equal]
    exact (completed_homogeneous_split a H root (atomic n)).mpr (Or.inr ⟨anchor, n, rfl⟩)
  have finite := finite_orbit family contained
  rw [all] at finite
  exact Set.infinite_univ finite


/-- Arbitrary finite native expressions, with powers allowed at any node. -/
inductive NativeExpr (m : Nat) where
  | ground : Source → NativeExpr m
  | var : Fin m → NativeExpr m
  | shift : Nat → NativeExpr m → NativeExpr m
  | pair : NativeExpr m → NativeExpr m → NativeExpr m

def nativeValue {m : Nat} (v : Fin m → CompletionTree) : NativeExpr m → CompletionTree
  | .ground t => embed t
  | .var i => v i
  | .shift a E => rho^[a] (nativeValue v E)
  | .pair A B => node (nativeValue v A) (nativeValue v B)

abbrev NativeSystem (m : Nat) := Fin m → Option (NativeExpr m)

def NativeSatisfies {m : Nat} (S : NativeSystem m) (v : Fin m → CompletionTree) : Prop :=
  ∀ i E, S i = some E → v i = nativeValue v E

structure NativeComponent where
  states : Nat
  equations : NativeSystem states
  designated : Fin states

def nativeProjected (C : NativeComponent) : Set CompletionTree :=
  {X | ∃ v, NativeSatisfies C.equations v ∧ v C.designated = X}

def nativeRepresented (family : List NativeComponent) : Set CompletionTree :=
  {X | ∃ C ∈ family, X ∈ nativeProjected C}

/-- The full target with arbitrary original placement of native fixed powers. -/
def NativeObstruction : Prop :=
  ∀ (a : Nat) (H : Homogeneous), PairRoot H →
    eval H (leaf true) = atomic a → ∀ family : List NativeComponent,
      {X : CompletionTree | rho^[a] X = eval H X} ≠ nativeRepresented family

private def exprShift {m : Nat} (a : Nat) : Expr m → Expr m
  | .ground t => .ground (substitution^[a] t)
  | .token i _ => Fin.elim0 i
  | .var b i => .var (a+b) i
  | .pair A B => .pair (exprShift a A) (exprShift a B)

private theorem value_exprShift {m : Nat} (a : Nat) (E : Expr m)
    (v : Fin m → CompletionTree) : value v (exprShift a E) = rho^[a] (value v E) := by
  induction E with
  | ground t => exact (iterate_embed a t).symm
  | token i c => exact Fin.elim0 i
  | var b i => exact Function.iterate_add_apply rho a b (v i)
  | pair A B ihA ihB =>
    change node (value v (exprShift a A)) (value v (exprShift a B)) =
      rho^[a] (node (value v A) (value v B))
    rw [ihA, ihB, iterate_node]

private def nativeCompile {m : Nat} : NativeExpr m → Expr m
  | .ground t => .ground t
  | .var i => .var 0 i
  | .shift a E => exprShift a (nativeCompile E)
  | .pair A B => .pair (nativeCompile A) (nativeCompile B)

private theorem nativeCompile_value {m : Nat} (E : NativeExpr m)
    (v : Fin m → CompletionTree) : value v (nativeCompile E) = nativeValue v E := by
  induction E with
  | ground t => rfl
  | var i => rfl
  | shift a E ih =>
    change value v (exprShift a (nativeCompile E)) = rho^[a] (nativeValue v E)
    rw [value_exprShift, ih]
  | pair A B ihA ihB => exact congrArg₂ node ihA ihB

private def systemCompile {m : Nat} (S : NativeSystem m) : System m :=
  fun i => (S i).map nativeCompile

private theorem systemCompile_satisfies {m : Nat} (S : NativeSystem m)
    (v : Fin m → CompletionTree) : NativeSatisfies S v ↔ Satisfies (systemCompile S) v := by
  constructor
  · intro sat i E eq
    cases h : S i with
    | none => simp [systemCompile, h] at eq
    | some F =>
      have ef : nativeCompile F = E := by simpa only [systemCompile, h, Option.map_some,
        Option.some.injEq] using eq
      subst E
      exact (sat i F h).trans (nativeCompile_value F v).symm
  · intro sat i E eq
    have h : systemCompile S i = some (nativeCompile E) := by
      simp only [systemCompile, eq, Option.map_some]
    exact (sat i (nativeCompile E) h).trans (nativeCompile_value E v)

private def componentCompile (C : NativeComponent) : Component :=
  ⟨C.states, systemCompile C.equations, C.designated⟩

private theorem familyCompile_represented (family : List NativeComponent) :
    represented (family.map componentCompile) = nativeRepresented family := by
  ext X
  constructor
  · rintro ⟨D, mem, v, sat, hx⟩
    obtain ⟨C, memC, rfl⟩ := List.mem_map.mp mem
    exact ⟨C, memC, v, (systemCompile_satisfies C.equations v).mpr sat, hx⟩
  · rintro ⟨C, mem, v, sat, hx⟩
    exact ⟨componentCompile C, List.mem_map.mpr ⟨C, mem, rfl⟩,
      v, (systemCompile_satisfies C.equations v).mp sat, hx⟩

/-- The original rank-free obstruction, including arbitrary fixed powers of
subexpressions, all original equations and unrestricted infinite auxiliaries. -/
theorem rank_free_obstruction : NativeObstruction := by
  intro a H root anchor family eq
  apply distributed_rank_free_obstruction a H root anchor (family.map componentCompile)
  exact eq.trans (familyCompile_represented family).symm

end D5.S3.Arith.FibonacciAtomic.Observer.NativeFunctionalObstruction
