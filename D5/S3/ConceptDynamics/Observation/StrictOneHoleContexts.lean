/- GID: D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Observation/StrictOneHoleContexts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict one-hole observations give the greatest strong congruence below the readout kernel. -/

import D5.S3.ConceptDynamics.Interventions.DynamicClosureMinimality
import Mathlib.Data.PFun
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Observation.StrictOneHoleContexts

open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S3.ConceptDynamics.Interventions.DynamicClosureMinimality

universe u v w v'

/-- A finite-arity signature of deterministic partial operations. -/
structure PartialSignature (X : Type u) (Symbol : Type v) where
  arity : Symbol → Nat
  operation : (f : Symbol) → (Fin (arity f) → X) → Option X

/-- Domain-subtype operations and Option operations are equivalent, classically. -/
noncomputable def sourceOperationEquiv (X : Type u) (n : Nat) :
    (Σ D : (Fin n → X) → Prop, Subtype D → X) ≃ ((Fin n → X) → Option X) :=
  PFun.equivSubtype.symm.trans (Equiv.piCongrRight fun _ => Part.equivOption)

/-- Interpret a signature presented by arbitrary domains and functions on them. -/
noncomputable def PartialSignature.ofDomains {X : Type u} {Symbol : Type v}
    (arity : Symbol → Nat)
    (operations : (f : Symbol) → Σ D : (Fin (arity f) → X) → Prop, Subtype D → X) :
    PartialSignature X Symbol :=
  ⟨arity, fun f => sourceOperationEquiv X (arity f) (operations f)⟩

private theorem source_operation_domain {X : Type u} {n : Nat}
    (D : (Fin n → X) → Prop) (f : Subtype D → X) (a : Fin n → X) :
    sourceOperationEquiv X n ⟨D, f⟩ a = none ↔ ¬D a := by
  classical
  exact Part.toOption_eq_none (PFun.equivSubtype.symm ⟨D, f⟩ a)

private theorem source_operation_value {X : Type u} {n : Nat}
    (D : (Fin n → X) → Prop) (f : Subtype D → X) (a : Fin n → X) (x : X) :
    sourceOperationEquiv X n ⟨D, f⟩ a = some x ↔ ∃ h : D a, f ⟨a, h⟩ = x := by
  classical
  exact Part.toOption_eq_some_iff

private theorem source_composition {X : Type u} (p : Part X) (f : X → Part X) :
    Part.equivOption (p.bind f) =
      (Part.equivOption p).bind (fun x => Part.equivOption (f x)) := by
  classical
  change (p.bind f).toOption = p.toOption.bind (fun x => (f x).toOption)
  rw [Part.bind_toOption]
  cases p.toOption <;> rfl

/-- A slot and exactly its off-slot parameters; no default state is required. -/
structure Generator {X : Type u} {Symbol : Type v} (S : PartialSignature X Symbol) where
  symbol : Symbol
  slot : Fin (S.arity symbol)
  parameters : {j : Fin (S.arity symbol) // j ≠ slot} → X

private def fill {X : Type u} {Symbol : Type v} {S : PartialSignature X Symbol}
    (g : Generator S) (x : X) (j : Fin (S.arity g.symbol)) : X :=
  if h : j = g.slot then x else g.parameters ⟨j, h⟩

/-- Apply a basic one-hole operation, propagating failure strictly. -/
def strictStep {X : Type u} {Symbol : Type v} (S : PartialSignature X Symbol)
    (g : Generator S) (state : Option X) : Option X :=
  state.bind (fun x => S.operation g.symbol (fill g x))

/-- Actual partial-function denotation of a finite generator word. -/
def contextDenote {X : Type u} {Symbol : Type v} (S : PartialSignature X Symbol)
    (word : List (Generator S)) (x : X) : Option X :=
  runWord (strictStep S) word (some x)

/-- The semantic family is the range of denotation, allowing duplicate words. -/
def ContextFamily {X : Type u} {Symbol : Type v} (S : PartialSignature X Symbol) :
    Set (X → Option X) := Set.range (contextDenote S)

/-- Read a successful result with a tag disjoint from failure. -/
def contextObserve {X : Type u} {Q : Type w} (q : X → Q) (C : X → Option X)
    (x : X) : Option Q := (C x).map q

/-- Equality of all observations in the actual semantic context family. -/
def contextualSetoid {X : Type u} {Symbol : Type v} {Q : Type w}
    (S : PartialSignature X Symbol) (q : X → Q) : Setoid X :=
  Setoid.ker (fun x => fun C : ContextFamily S => contextObserve q C.val x)

/-- Universal semantic-context testing agrees exactly with testing all words. -/
theorem forall_contexts_iff_words {X : Type u} {Symbol : Type v} {Q : Type w}
    (S : PartialSignature X Symbol) (q : X → Q) (x y : X) :
    (contextualSetoid S q).r x y ↔
      ∀ word, contextObserve q (contextDenote S word) x =
        contextObserve q (contextDenote S word) y := by
  constructor
  · intro h word
    exact congrFun h ⟨contextDenote S word, ⟨word, rfl⟩⟩
  · intro h
    funext C
    obtain ⟨word, hword⟩ := C.property
    change contextObserve q C.val x = contextObserve q C.val y
    rw [← hword]
    exact h word

private def profile {X : Type u} {Symbol : Type v} {Q : Type w}
    (S : PartialSignature X Symbol) (q : X → Q) :=
  DynClosure (Option.map q) (strictStep S)

private theorem profile_some_iff {X : Type u} {Symbol : Type v} {Q : Type w}
    (S : PartialSignature X Symbol) (q : X → Q) (x y : X) :
    profile S q (some x) = profile S q (some y) ↔ (contextualSetoid S q).r x y := by
  rw [forall_contexts_iff_words]
  exact funext_iff

/-- Strong congruence preserves the entire operation domain and its defined outputs. -/
def StrongCongruence {X : Type u} {Symbol : Type v}
    (S : PartialSignature X Symbol) (theta : Setoid X) : Prop :=
  ∀ f a b, (∀ j, theta.r (a j) (b j)) →
    (S.operation f a ≠ none ↔ S.operation f b ≠ none) ∧
    (∀ x y, S.operation f a = some x → S.operation f b = some y → theta.r x y)

private theorem finite_coordinate_profile_replacement
    {X : Type u} {Symbol : Type v} {Q : Type w}
    (S : PartialSignature X Symbol) (q : X → Q) (f : Symbol)
    (a b : Fin (S.arity f) → X)
    (related : ∀ j, (contextualSetoid S q).r (a j) (b j)) :
    profile S q (S.operation f a) = profile S q (S.operation f b) := by
  let mixed (m : Nat) (j : Fin (S.arity f)) := if j.val < m then b j else a j
  have chain : ∀ m, m ≤ S.arity f →
      profile S q (S.operation f (mixed 0)) = profile S q (S.operation f (mixed m)) := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      let slot : Fin (S.arity f) := ⟨m, Nat.lt_of_succ_le hm⟩
      let g : Generator S := ⟨f, slot, fun j => mixed m j.val⟩
      have left_fill : fill g (a slot) = mixed m := by
        funext j
        by_cases hj : j = slot
        · subst j
          simp [fill, g, slot, mixed]
        · simp [fill, g, hj]
      have right_fill : fill g (b slot) = mixed (m + 1) := by
        funext j
        by_cases hj : j = slot
        · subst j
          simp [fill, g, slot, mixed]
        · have hv : j.val ≠ m := fun h => hj (Fin.ext h)
          have same : (j.val < m + 1) = (j.val < m) := propext (by omega)
          simp [fill, g, hj, mixed, same]
      have one := dynamic_closure_is_intervention_closed
        (Option.map q) (strictStep S) g (some (a slot)) (some (b slot))
        ((profile_some_iff S q _ _).mpr (related slot))
      change profile S q (S.operation f (fill g (a slot))) =
        profile S q (S.operation f (fill g (b slot))) at one
      rw [left_fill, right_fill] at one
      exact (ih (by omega)).trans one
  have first : mixed 0 = a := by funext j; simp [mixed]
  have last : mixed (S.arity f) = b := by funext j; simp [mixed, j.isLt]
  simpa only [first, last] using chain (S.arity f) le_rfl

/-- The observation relation is the greatest strong congruence below the readout kernel. -/
theorem contextual_equivalence_is_greatest
    {X : Type u} {Symbol : Type v} {Q : Type w}
    (S : PartialSignature X Symbol) (q : X → Q) :
    StrongCongruence S (contextualSetoid S q) ∧
    contextualSetoid S q ≤ Setoid.ker q ∧
    (∀ theta : Setoid X, StrongCongruence S theta → theta ≤ Setoid.ker q →
      theta ≤ contextualSetoid S q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f a b related
    have hp := finite_coordinate_profile_replacement S q f a b related
    have zero := congrFun hp []
    change (S.operation f a).map q = (S.operation f b).map q at zero
    constructor
    · cases ha : S.operation f a <;> cases hb : S.operation f b <;> simp_all
    · intro x y hx hy
      rw [hx, hy] at hp
      exact (profile_some_iff S q x y).mp hp
  · intro x y h
    have zero := (forall_contexts_iff_words S q x y).mp h []
    exact Option.some.inj zero
  · intro theta strong ker x y hxy
    let candidate : Option X → Option (Quotient theta) := Option.map (Quotient.mk theta)
    let recover : Quotient theta → Q := Quotient.lift q (fun _ _ h => ker h)
    have factor : D5.S3.ConceptDynamics.ConceptJoinUniversal.Refines
        (Option.map q) candidate := by
      refine ⟨Option.map recover, ?_⟩
      funext state
      cases state <;> rfl
    have closed : InterventionClosed candidate (strictStep S) := by
      intro g ox oy equal
      cases ox with
      | none => cases oy <;> simp_all [candidate, strictStep]
      | some x =>
        cases oy with
        | none => simp [candidate] at equal
        | some y =>
          have h : theta.r x y := Quotient.exact (Option.some.inj equal)
          have tuples : ∀ j, theta.r (fill g x j) (fill g y j) := by
            intro j
            by_cases hj : j = g.slot
            · simpa [fill, hj] using h
            · simp only [fill, dif_neg hj]
              exact theta.refl _
          obtain ⟨domains, values⟩ := strong g.symbol (fill g x) (fill g y) tuples
          change candidate (S.operation g.symbol (fill g x)) =
            candidate (S.operation g.symbol (fill g y))
          cases hx : S.operation g.symbol (fill g x) with
          | none =>
            cases hy : S.operation g.symbol (fill g y) <;> simp_all [candidate]
          | some a =>
            cases hy : S.operation g.symbol (fill g y) with
            | none => simp_all
            | some b =>
              exact congrArg Option.some (Quotient.sound (values a b hx hy))
    obtain ⟨forget, factors⟩ := dynamic_closure_is_least
      (Option.map q) (strictStep S) candidate factor closed
    apply (profile_some_iff S q x y).mp
    change DynClosure (Option.map q) (strictStep S) (some x) =
      DynClosure (Option.map q) (strictStep S) (some y)
    rw [factors]
    exact congrArg forget (congrArg Option.some (Quotient.sound hxy))

/-- An extension keeps every old arity and the entire old Option-valued operation. -/
structure SignatureExtension {X : Type u} {Symbol : Type v} {Symbol' : Type v'}
    (S : PartialSignature X Symbol) (T : PartialSignature X Symbol') where
  symbols : Symbol ↪ Symbol'
  arities : ∀ f, T.arity (symbols f) = S.arity f
  operations : ∀ f a,
    T.operation (symbols f) (fun i => a (Fin.cast (arities f) i)) = S.operation f a

/-- Formally extending the signature can only refine contextual equivalence. -/
theorem signature_extension_refines {X : Type u} {Symbol : Type v} {Symbol' : Type v'}
    {Q : Type w} (S : PartialSignature X Symbol) (T : PartialSignature X Symbol')
    (extension : SignatureExtension S T) (q : X → Q) :
    contextualSetoid T q ≤ contextualSetoid S q := by
  obtain ⟨strong, ker, _⟩ := contextual_equivalence_is_greatest T q
  apply (contextual_equivalence_is_greatest S q).2.2 _ _ ker
  intro f a b related
  have h := strong (extension.symbols f)
    (fun i => a (Fin.cast (extension.arities f) i))
    (fun i => b (Fin.cast (extension.arities f) i)) (fun i => related _)
  simpa only [extension.operations] using h

end D5.S3.ConceptDynamics.Observation.StrictOneHoleContexts
