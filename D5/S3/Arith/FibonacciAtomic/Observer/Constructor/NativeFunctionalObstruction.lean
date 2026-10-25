/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalObstruction
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Raw finite native functional systems and finite dependency descent. -/

import D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion

/-! Raw functional systems use the existing unrestricted native completion.
Finite dependency descent uses a positive additive weight on actual leaves. -/

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

end D5.S3.Arith.FibonacciAtomic.Observer.NativeFunctionalObstruction
