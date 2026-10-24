/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalCanonicalClassification
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: kind=checker; basis=terminal=atom:9ee98da0af702130d8831088a460e68998152997b0f3897cd0482ea8b3e8114d; instance=D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalCanonicalClassification.edgeSystem
   digest: Exact native canonical finiteness and terminating inclusive prefixes for original functional cases. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.OriginalNativeConstruction
import D5.S3.Arith.FibonacciAtomic.SourceCoordinates.NativeRotationDepthGap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.OriginalCanonicalClassification

open GenealogicalFiberTransport (Source substitution composition)
open NativeCompletionPrefixLifting
open CompletionHomogeneousFixedPoints
open OriginalFunctionalNormalization
open OriginalNativeConstruction
open ActualTreeReadoutAcquisition (Address Reply readout)

variable {k m : Nat}

private abbrev Derives (E : Definitions k m) (mode : Fin k → Bool) (e : Expr k m) :=
  OriginalFiniteResolution.FiniteDerivation (encodeDefinitions E) (Fin.cases false mode) (encode e)

private def Ready (E : Definitions k m) (mode : Fin k → Bool) (i : Fin m) : Prop :=
  ∃ e, E i = some e ∧ Derives E mode e

private theorem derive_below (E : Definitions k m) (mode : Fin k → Bool)
    (p : Fin k → Nat) (v : Fin m → CompletionTree) (n : Nat)
    (ready : ∀ i t, t.length < n → embed t = v i → Ready E mode i)
    (noOmega : ¬ IsFinite Omega) (e : Expr k m) (t : Source)
    (bound : t.length < n) (eq : embed t = value mode p v e) : Derives E mode e := by
  induction e generalizing t with
  | ground g => exact .ground g
  | token j c =>
      by_cases hm : mode j = true
      · exact .token j.succ c (by simpa using hm)
      · exact (noOmega ⟨t, by simpa [value, hm] using eq⟩).elim
  | omega => exact (noOmega ⟨t, eq⟩).elim
  | var a i =>
      obtain ⟨s, hs⟩ := (finite_iterate_iff a (v i)).mp ⟨t, eq⟩
      have same : substitution^[a] s = t := NativeCompletionSupportClosure.embed_injective
        ((iterate_embed a s).symm.trans ((congrArg (rho^[a]) hs).trans eq.symm))
      have growth : s.length ≤ t.length := by
        have total := ActualObserverAbsorbingNormalization.composition_total s
        have h₁ : 1 ≤ Nat.fib (a+1) := Nat.succ_le_of_lt (Nat.fib_pos.mpr (by omega))
        have h₂ : 1 ≤ Nat.fib (a+2) := Nat.succ_le_of_lt (Nat.fib_pos.mpr (by omega))
        rw [← same, SourceCoordinates.NativeRotationDepthGap.iterate_length]
        nlinarith
      obtain ⟨f, hf, hd⟩ := ready i s (by omega) hs
      exact .var a i (encode f) (by simp [encodeDefinitions, hf]) hd
  | pair e f ihe ihf =>
      cases t with
      | of b =>
          have root := congrArg (fun X => (PFunctor.M.dest X).1) eq
          simp [embed, value, leaf, node] at root
      | mul s t =>
          obtain ⟨hs, ht⟩ := node_inj eq
          have ps := s.length_pos
          have pt := t.length_pos
          simp only [FreeMagma.length] at bound
          exact .pair (encode e) (encode f) (ihe s (by omega) hs) (ihf t (by omega) ht)

/-- Actual finite canonical values have finite syntactic derivations. The
induction measure is a native finite witness, never a supplied graph rank. -/
private theorem canonical_finite_derivation (E : Definitions k m) (guarded : PairGuarded E)
    (mode : Fin k → Bool) (p : Fin k → Nat) (e : Expr k m)
    (finite : IsFinite (value mode p (native E mode p (fun _ => Omega)) e)) :
    Derives E mode e := by
  let v := native E mode p (fun _ => Omega)
  have sol := native_solution E guarded mode p (fun _ => Omega)
  have noOmega : ¬ IsFinite Omega := by
    have avoid : ∀ t : Source, embed t ≠ Omega := by
      intro t
      induction t with
      | of b =>
          intro eq
          have root := congrArg (fun X => (PFunctor.M.dest X).1) (eq.trans omega_node)
          simp [embed, leaf, node] at root
      | mul l r ihl _ =>
          intro eq
          exact ihl (node_inj (eq.trans omega_node)).1
    rintro ⟨t, ht⟩
    exact avoid t ht
  have all : ∀ n i t, t.length = n → embed t = v i → Ready E mode i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i t hn ht
      cases he : E i with
      | none => exact (noOmega ⟨t, ht.trans (sol.2 i he)⟩).elim
      | some f =>
        refine ⟨f, he, ?_⟩
        have eq := ht.trans (sol.1 i f he)
        cases f with
        | var a j => exact (guarded i a j he).elim
        | ground g => exact .ground g
        | token j c =>
          by_cases hm : mode j = true
          · exact .token j.succ c (by simpa using hm)
          · exact (noOmega ⟨t, by simpa [value, hm] using eq⟩).elim
        | omega => exact (noOmega ⟨t, eq⟩).elim
        | pair l r =>
          cases t with
          | of b =>
              have root := congrArg (fun X => (PFunctor.M.dest X).1) eq
              simp [embed, value, leaf, node] at root
          | mul s t =>
              obtain ⟨hs, ht⟩ := node_inj eq
              have ps := s.length_pos
              have pt := t.length_pos
              simp only [FreeMagma.length] at hn
              have ready : ∀ j u, u.length < n → embed u = v j → Ready E mode j := by
                intro j u hu eq
                exact ih u.length hu j u rfl eq
              exact .pair (encode l) (encode r)
                (derive_below E mode p v n ready noOmega l s (by omega) hs)
                (derive_below E mode p v n ready noOmega r t (by omega) ht)
  obtain ⟨t, ht⟩ := finite
  exact derive_below E mode p v (t.length+1)
    (fun i s _ hs => all s.length i s rfl hs) noOmega e t (by omega) ht

private theorem normalized_classifier (E : Definitions k m) (guarded : PairGuarded E)
    (mode : Fin k → Bool) (p : Fin k → Nat) (e : Expr k m) :
    (finiteCompile E mode e).isSome = true ↔
      IsFinite (value mode p (native E mode p (fun _ => Omega)) e) := by
  constructor
  · intro h
    obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp h
    exact ⟨OriginalFiniteResolution.finiteValue p f,
      (finite_compile_sound E mode e f hf p _ (native_solution E guarded mode p _).1).symm⟩
  · intro h
    have hd := canonical_finite_derivation E guarded mode p e h
    have hc := ((OriginalFiniteResolution.original_finite_resolution (k+1) m
      (encodeDefinitions E) (Fin.cases false mode)).1 (encode e)).mpr hd
    simpa [finiteCompile] using hc

/-- Agreement through depths strictly below n includes absent positions. -/
private def Agree (n : Nat) (X Y : CompletionTree) : Prop :=
  ∀ a : Address, a.length < n → completionReadout a X = completionReadout a Y

private theorem agree_mono {n d : Nat} {X Y : CompletionTree}
    (h : Agree n X Y) (le : d ≤ n) : Agree d X Y :=
  fun a ha => h a (by omega)

private theorem agree_node (n : Nat) {l r s t : CompletionTree}
    (hl : Agree n l s) (hr : Agree n r t) :
    Agree (n+1) (node l r) (node s t) := by
  intro a ha
  cases a with
  | nil => rfl
  | cons b a =>
      have len : a.length < n := by simpa using ha
      cases b
      · exact hl a len
      · exact hr a len

private theorem agree_rho (n : Nat) {X Y : CompletionTree}
    (h : Agree n X Y) : Agree n (rho X) (rho Y) := by
  induction n generalizing X Y with
  | zero => intro a ha; simp at ha
  | succ n ih =>
    have root := h [] (by simp)
    induction X using tree_cases with
    | leaf_case b =>
      induction Y using tree_cases with
      | leaf_case c =>
          have eq : b = c := by cases b <;> cases c <;> simp_all [completionReadout, leaf]
          subst c
          intro a _; rfl
      | node_case l r => cases b <;> simp [completionReadout, leaf, node] at root
    | node_case l r =>
      induction Y using tree_cases with
      | leaf_case b => cases b <;> simp [completionReadout, leaf, node] at root
      | node_case s t =>
        rw [rho_node, rho_node]
        apply agree_node n
        · apply ih
          intro a ha
          exact h (false :: a) (by simpa using ha)
        · apply ih
          intro a ha
          exact h (true :: a) (by simpa using ha)

private theorem agree_power (n a : Nat) {X Y : CompletionTree}
    (h : Agree n X Y) : Agree n (rho^[a] X) (rho^[a] Y) := by
  induction a with
  | zero => exact h
  | succ a ih => simpa only [Function.iterate_succ_apply'] using agree_rho n ih

/-- A computable finite filling of the leafless tree through n-1. -/
def bush : Nat → Source
  | 0 => .of true
  | n+1 => .mul (bush n) (bush n)

private theorem bush_agrees (n : Nat) : Agree n (embed (bush n)) Omega := by
  induction n with
  | zero => intro a ha; simp at ha
  | succ n ih =>
      change Agree (n+1) (node (embed (bush n)) (embed (bush n))) Omega
      conv_rhs => rw [omega_node]
      exact agree_node n ih ih

/-- Evaluation uses only finite trees, natural iterations and displayed syntax.
The budget controls Omega filling; it never bounds natural parameters. -/
def finiteEval (mode : Fin k → Bool) (p : Fin k → Nat) (budget : Nat)
    (v : Fin m → Source) : Expr k m → Source
  | .ground t => t
  | .token j c => if mode j then substitution^[p j+c] (.of true) else bush budget
  | .omega => bush budget
  | .var a i => substitution^[a] (v i)
  | .pair l r => .mul (finiteEval mode p budget v l) (finiteEval mode p budget v r)

private theorem finite_eval_agrees (mode : Fin k → Bool) (p : Fin k → Nat)
    (n budget : Nat) (enough : n ≤ budget) (v : Fin m → Source)
    (V : Fin m → CompletionTree) (hv : ∀ i, Agree n (embed (v i)) (V i))
    (e : Expr k m) : Agree n (embed (finiteEval mode p budget v e)) (value mode p V e) := by
  induction e with
  | ground t => intro a _; rfl
  | token j c =>
      by_cases hm : mode j = true
      · simp only [finiteEval, value, hm, ↓reduceIte, atomic]
        rw [← iterate_embed]
        intro a _; rfl
      · simpa only [finiteEval, value, hm, Bool.false_eq_true, ↓reduceIte] using
          agree_mono (bush_agrees budget) enough
  | omega => exact agree_mono (bush_agrees budget) enough
  | var a i =>
      change Agree n (embed (substitution^[a] (v i))) (rho^[a] (V i))
      rw [← iterate_embed]
      exact agree_power n a (hv i)
  | pair l r ihl ihr =>
      exact agree_mono (agree_node n ihl ihr) (by omega)

/-- Guarded iterations, starting from finite fillers, have a primitive recursive
iteration count. Undefined coordinates receive the same Omega filling. -/
def approximate (E : Definitions k m) (mode : Fin k → Bool) (p : Fin k → Nat) :
    Nat → Fin m → Source
  | 0, _ => .of true
  | n+1, i => match E i with
    | none => bush (n+1)
    | some e => finiteEval mode p (n+1) (approximate E mode p n) e

private theorem approximate_agrees (E : Definitions k m) (guarded : PairGuarded E)
    (mode : Fin k → Bool) (p : Fin k → Nat) (n : Nat) :
    ∀ i, Agree n (embed (approximate E mode p n i))
      (native E mode p (fun _ => Omega) i) := by
  induction n with
  | zero => intro i a ha; simp at ha
  | succ n ih =>
    intro i
    have sol := native_solution E guarded mode p (fun _ => Omega)
    cases he : E i with
    | none =>
        rw [sol.2 i he]
        simpa only [approximate, he] using bush_agrees (n+1)
    | some e =>
        rw [sol.1 i e he]
        simp only [approximate, he]
        cases e with
        | var a j => exact (guarded i a j he).elim
        | ground t => intro a _; rfl
        | token j c =>
            by_cases hm : mode j = true
            · simp only [finiteEval, value, hm, ↓reduceIte, atomic]
              rw [← iterate_embed]
              intro a _; rfl
            · simpa only [finiteEval, value, hm, Bool.false_eq_true, ↓reduceIte] using
                bush_agrees (n+1)
        | omega => exact bush_agrees (n+1)
        | pair l r =>
            apply agree_node n
            · exact finite_eval_agrees mode p n (n+1) (by omega) _ _ ih l
            · exact finite_eval_agrees mode p n (n+1) (by omega) _ _ ih r

/-- Canonical native state values, with all original state names restored. -/
def canonical (E : Definitions k m) (mode : Fin k → Bool) (p : Fin k → Nat) :
    Fin m → CompletionTree :=
  reconstruct mode p (normalize E).reconstruction
    (native (normalize E).system mode p (fun _ => Omega))

/-- Complete parameter-independent finite output compiler for original expressions. -/
def canonicalCompile (E : Definitions k m) (mode : Fin k → Bool) (e : Expr k m) :
    Option (OriginalFiniteResolution.FiniteExpr k) :=
  finiteCompile (normalize E).system mode (subst (normalize E).reconstruction e)

/-- The inclusive depth h prefix is computed entirely in the finite Source algebra. -/
def prefixTree (E : Definitions k m) (mode : Fin k → Bool) (p : Fin k → Nat)
    (h : Nat) (e : Expr k m) : Source :=
  finiteEval mode p (h+1) (approximate (normalize E).system mode p (h+1))
    (subst (normalize E).reconstruction e)

/-- An executable four-valued original reply; h=0 includes the root. -/
def prefixReply (E : Definitions k m) (mode : Fin k → Bool) (p : Fin k → Nat)
    (h : Nat) (e : Expr k m) (a : Address) : Reply :=
  readout a (prefixTree E mode p h e)

/-- Two parameter names may coincide; the recurrent state and the genuinely free
state retain their different canonical dependencies. -/
def edgeSystem : Definitions 2 4 := fun i =>
  if i = 0 then some (.token 0 0)
  else if i = 1 then some (.token 1 0)
  else if i = 2 then some (.pair (.var 0 1) (.var 0 2))
  else none

/-- All original equations, coordinates, natural parameters and fixed powers
remain quantified. Finiteness is exact; failed compilation means canonical
infinity only. The executable prefix bound is inclusive and uniform. -/
theorem original_canonical_synthesis (E : Definitions k m) (mode : Fin k → Bool)
    (p : Fin k → Nat) :
    Solution E mode p (canonical E mode p) ∧
    (∀ e : Expr k m, (canonicalCompile E mode e).isSome = true ↔
      IsFinite (value mode p (canonical E mode p) e)) ∧
    (∀ (e : Expr k m) (f : OriginalFiniteResolution.FiniteExpr k),
      canonicalCompile E mode e = some f → ∀ v : Fin m → CompletionTree,
        Solution E mode p v → value mode p v e = embed (OriginalFiniteResolution.finiteValue p f)) ∧
    (∀ e : Expr k m, canonicalCompile E mode e = none →
      ¬ IsFinite (value mode p (canonical E mode p) e)) ∧
    (∀ (h : Nat) (e : Expr k m) (a : Address), a.length ≤ h →
      prefixReply E mode p h e a = completionReadout a (value mode p (canonical E mode p) e)) := by
  let q := normalize E
  have value_eq (e : Expr k m) :
      value mode p (native q.system mode p (fun _ => Omega)) (subst q.reconstruction e) =
        value mode p (canonical E mode p) e := value_subst mode p _ q.reconstruction e
  have classify : ∀ e : Expr k m, (canonicalCompile E mode e).isSome = true ↔
      IsFinite (value mode p (canonical E mode p) e) := by
    intro e
    rw [← value_eq e]
    exact normalized_classifier q.system q.guarded mode p (subst q.reconstruction e)
  refine ⟨q.sound mode p _ (native_solution q.system q.guarded mode p _).1,
    classify, ?_, ?_, ?_⟩
  · intro e f hf v hv
    obtain ⟨hn, hr⟩ := q.recover mode p v hv
    have out := finite_compile_sound q.system mode (subst q.reconstruction e) f hf p v hn
    rw [value_subst, hr] at out
    exact out
  · intro e he fin
    have yes := (classify e).mpr fin
    simp [he] at yes
  · intro h e a ha
    have approx := approximate_agrees q.system q.guarded mode p (h+1)
    have exactPrefix := finite_eval_agrees mode p (h+1) (h+1) (by omega)
      (approximate q.system mode p (h+1)) (native q.system mode p (fun _ => Omega))
      approx (subst q.reconstruction e) a (by omega)
    rw [embed_readout, value_eq] at exactPrefix
    exact exactPrefix




#print axioms original_canonical_synthesis

end D5.S3.Arith.FibonacciAtomic.Observer.OriginalCanonicalClassification
