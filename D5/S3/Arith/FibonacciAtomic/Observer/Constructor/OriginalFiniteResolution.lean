/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalFiniteResolution
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite symbolic resolution and parameter-uniform rigidity of original functional expressions. -/

import D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion
import Mathlib.Data.Fintype.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.OriginalFiniteResolution

open GenealogicalFiberTransport (Source substitution)
open NativeCompletionPrefixLifting
open CompletionHomogeneousFixedPoints (rho atomic Omega IsFinite iterate_embed)
open CompletionPositiveDriftRegion (Expr value)

/-- A functional presentation retains every original state, including undefined states. -/
abbrev Definitions (k m : Nat) := Fin m → Option (Expr k m)

/-- Finite output syntax retains parameter names, fixed powers and ordered pairs. -/
inductive FiniteExpr (k : Nat) where
  | ground : Source → FiniteExpr k
  | token : Fin k → Nat → FiniteExpr k
  | power : Nat → FiniteExpr k → FiniteExpr k
  | pair : FiniteExpr k → FiniteExpr k → FiniteExpr k
  deriving DecidableEq

variable {k m : Nat}

def finiteValue (p : Fin k → Nat) : FiniteExpr k → Source
  | .ground t => t
  | .token j c => substitution^[p j + c] (.of true)
  | .power a e => substitution^[a] (finiteValue p e)
  | .pair e f => .mul (finiteValue p e) (finiteValue p f)

/-- Equations are interpreted in the unrestricted native completion. -/
def Solution (E : Definitions k m) (mode : Fin k → Bool) (p : Fin k → Nat)
    (v : Fin m → CompletionTree) : Prop :=
  ∀ i e, E i = some e → v i = value mode p v e

/-- Resolve one displayed expression without expanding or comparing parameter values. -/
def resolve (mode : Fin k → Bool) (s : Fin m → Option (FiniteExpr k)) :
    Expr k m → Option (FiniteExpr k)
  | .ground t => some (.ground t)
  | .token j c => if mode j then some (.token j c) else none
  | .var a i => (s i).map (.power a)
  | .pair e f => do
      let x ← resolve mode s e
      let y ← resolve mode s f
      pure (.pair x y)

/-- Each round uses the intact original defining expressions. -/
def environment (E : Definitions k m) (mode : Fin k → Bool) :
    Nat → Fin m → Option (FiniteExpr k)
  | 0, _ => none
  | n+1, i => (E i).bind (resolve mode (environment E mode n))

/-- No user-supplied graph rank or finite expansion bound occurs in this compiler. -/
def compile (E : Definitions k m) (mode : Fin k → Bool) (e : Expr k m) :
    Option (FiniteExpr k) := resolve mode (environment E mode m) e

/-- A purely syntactic finite derivation; no semantic finiteness appears here. -/
inductive FiniteDerivation (E : Definitions k m) (mode : Fin k → Bool) : Expr k m → Prop
  | ground (t : Source) : FiniteDerivation E mode (.ground t)
  | token (j : Fin k) (c : Nat) : mode j = true → FiniteDerivation E mode (.token j c)
  | var (a : Nat) (i : Fin m) (e : Expr k m) :
      E i = some e → FiniteDerivation E mode e → FiniteDerivation E mode (.var a i)
  | pair (e f : Expr k m) : FiniteDerivation E mode e → FiniteDerivation E mode f →
      FiniteDerivation E mode (.pair e f)

private def Extends (s t : Fin m → Option (FiniteExpr k)) : Prop :=
  ∀ i f, s i = some f → t i = some f

private theorem resolve_extends (mode : Fin k → Bool)
    {s t : Fin m → Option (FiniteExpr k)} (h : Extends s t) :
    ∀ e f, resolve mode s e = some f → resolve mode t e = some f := by
  intro e
  induction e with
  | ground g => intro f hf; exact hf
  | token j c => intro f hf; exact hf
  | var a i =>
      intro f hf
      cases hs : s i with
      | none => simp [resolve, hs] at hf
      | some g => simpa [resolve, hs, h i g hs] using hf
  | pair e g ihe ihg =>
      intro f hf
      cases he : resolve mode s e with
      | none => simp [resolve, he] at hf
      | some x =>
        cases hg : resolve mode s g with
        | none => simp [resolve, he, hg] at hf
        | some y => simpa [resolve, he, hg, ihe x he, ihg y hg] using hf

private theorem environment_extends (E : Definitions k m) (mode : Fin k → Bool) (n : Nat) :
    Extends (environment E mode n) (environment E mode (n+1)) := by
  induction n with
  | zero => intro i f h; simp [environment] at h
  | succ n ih =>
      intro i f hf
      cases he : E i with
      | none => simp [environment, he] at hf
      | some e =>
        exact resolve_extends mode ih e f (by simpa [environment, he] using hf)

private def support (E : Definitions k m) (mode : Fin k → Bool) (n : Nat) : Finset (Fin m) :=
  Finset.univ.filter (fun i => (environment E mode n i).isSome)

private theorem mem_support (E : Definitions k m) (mode : Fin k → Bool) (n : Nat) (i : Fin m) :
    i ∈ support E mode n ↔ ∃ f, environment E mode n i = some f := by
  simp [support, Option.isSome_iff_exists]

private theorem support_subset (E : Definitions k m) (mode : Fin k → Bool) (n : Nat) :
    support E mode n ⊆ support E mode (n+1) := by
  intro i hi
  obtain ⟨f, hf⟩ := (mem_support E mode n i).mp hi
  exact (mem_support E mode (n+1) i).mpr ⟨f, environment_extends E mode n i f hf⟩

private theorem stable_of_support (E : Definitions k m) (mode : Fin k → Bool) (n : Nat)
    (h : support E mode n = support E mode (n+1)) :
    environment E mode n = environment E mode (n+1) := by
  funext i
  cases hi : environment E mode n i with
  | some f => exact (environment_extends E mode n i f hi).symm
  | none =>
      cases hj : environment E mode (n+1) i with
      | none => rfl
      | some f =>
        have hm := (mem_support E mode (n+1) i).mpr ⟨f, hj⟩
        rw [← h] at hm
        obtain ⟨g, hg⟩ := (mem_support E mode n i).mp hm
        simp [hi] at hg

private theorem stable_succ (E : Definitions k m) (mode : Fin k → Bool) (n : Nat)
    (h : environment E mode n = environment E mode (n+1)) :
    environment E mode (n+1) = environment E mode (n+2) := by
  funext i
  simp only [environment]
  rw [h]

/-- A nonstationary round adds a new original state; there are exactly m states. -/
private theorem saturation_complete (E : Definitions k m) (mode : Fin k → Bool) :
    environment E mode m = environment E mode (m+1) := by
  classical
  have growth : ∀ n, environment E mode n = environment E mode (n+1) ∨
      n ≤ (support E mode n).card := by
    intro n
    induction n with
    | zero => exact Or.inr (Nat.zero_le _)
    | succ n ih =>
      rcases ih with stable | count
      · exact Or.inl (stable_succ E mode n stable)
      · by_cases stable : environment E mode n = environment E mode (n+1)
        · exact Or.inl (stable_succ E mode n stable)
        · have strict : support E mode n ⊂ support E mode (n+1) :=
            (support_subset E mode n).ssubset_of_ne (fun eq =>
              stable (stable_of_support E mode n eq))
          exact Or.inr (by have := Finset.card_lt_card strict; omega)
  rcases growth m with stable | count
  · exact stable
  · have bound : (support E mode m).card ≤ m := by
      simpa using (support E mode m).card_le_univ
    have all : support E mode m = Finset.univ :=
      Finset.eq_univ_of_card _ (by simp; omega)
    funext i
    have hi : i ∈ support E mode m := by rw [all]; simp
    obtain ⟨f, hf⟩ := (mem_support E mode m i).mp hi
    exact hf.trans (environment_extends E mode m i f hf).symm

private theorem resolve_derivation (E : Definitions k m) (mode : Fin k → Bool)
    (s : Fin m → Option (FiniteExpr k))
    (hs : ∀ i f, s i = some f → ∃ e, E i = some e ∧ FiniteDerivation E mode e) :
    ∀ e f, resolve mode s e = some f → FiniteDerivation E mode e := by
  intro e
  induction e with
  | ground t => intros; exact .ground t
  | token j c =>
      intro f hf
      by_cases h : mode j = true
      · exact .token j c h
      · simp [resolve, h] at hf
  | var a i =>
      intro f hf
      cases hi : s i with
      | none => simp [resolve, hi] at hf
      | some g =>
          obtain ⟨e, he, hd⟩ := hs i g hi
          exact .var a i e he hd
  | pair e g ihe ihg =>
      intro f hf
      cases he : resolve mode s e with
      | none => simp [resolve, he] at hf
      | some x =>
        cases hg : resolve mode s g with
        | none => simp [resolve, he, hg] at hf
        | some y => exact .pair e g (ihe x he) (ihg y hg)

private theorem environment_derivation (E : Definitions k m) (mode : Fin k → Bool) (n : Nat) :
    ∀ i f, environment E mode n i = some f →
      ∃ e, E i = some e ∧ FiniteDerivation E mode e := by
  induction n with
  | zero => intro i f hf; simp [environment] at hf
  | succ n ih =>
      intro i f hf
      cases he : E i with
      | none => simp [environment, he] at hf
      | some e =>
        exact ⟨e, he, resolve_derivation E mode _ ih e f (by
          simpa [environment, he] using hf)⟩

private theorem derivation_compile (E : Definitions k m) (mode : Fin k → Bool)
    (e : Expr k m) (h : FiniteDerivation E mode e) : ∃ f, compile E mode e = some f := by
  induction h with
  | ground t => exact ⟨.ground t, rfl⟩
  | token j c h => exact ⟨.token j c, by simp [compile, resolve, h]⟩
  | var a i e he _ ih =>
      obtain ⟨f, hf⟩ := ih
      have state : environment E mode m i = some f := by
        rw [saturation_complete E mode]
        simpa [environment, he, compile] using hf
      exact ⟨.power a f, by simp [compile, resolve, state]⟩
  | pair e g _ _ ihe ihg =>
      obtain ⟨x, hx⟩ := ihe
      obtain ⟨y, hy⟩ := ihg
      exact ⟨.pair x y, by simp [compile, resolve] at hx hy ⊢; rw [hx, hy]; rfl⟩

private theorem resolve_sound (mode : Fin k → Bool) (p : Fin k → Nat)
    (v : Fin m → CompletionTree) (s : Fin m → Option (FiniteExpr k))
    (hs : ∀ i f, s i = some f → v i = embed (finiteValue p f)) :
    ∀ e f, resolve mode s e = some f → value mode p v e = embed (finiteValue p f) := by
  intro e
  induction e with
  | ground t => intro f hf; simpa [resolve] using hf ▸ (rfl : embed t = embed t)
  | token j c =>
      intro f hf
      by_cases h : mode j = true
      · have eq : FiniteExpr.token j c = f := by simpa [resolve, h] using hf
        subst f
        simpa [value, h, finiteValue, atomic] using (iterate_embed (p j+c) (.of true))
      · simp [resolve, h] at hf
  | var a i =>
      intro f hf
      cases hi : s i with
      | none => simp [resolve, hi] at hf
      | some g =>
          have eq : FiniteExpr.power a g = f := by simpa [resolve, hi] using hf
          subst f
          simp only [value, hs i g hi, finiteValue, iterate_embed]
  | pair e g ihe ihg =>
      intro f hf
      cases he : resolve mode s e with
      | none => simp [resolve, he] at hf
      | some x =>
        cases hg : resolve mode s g with
        | none => simp [resolve, he, hg] at hf
        | some y =>
          have eq : FiniteExpr.pair x y = f := by simpa [resolve, he, hg] using hf
          subst f
          simp only [value, finiteValue, embed, ihe x he, ihg y hg]

private theorem environment_sound (E : Definitions k m) (mode : Fin k → Bool)
    (p : Fin k → Nat) (v : Fin m → CompletionTree) (hv : Solution E mode p v) (n : Nat) :
    ∀ i f, environment E mode n i = some f → v i = embed (finiteValue p f) := by
  induction n with
  | zero => intro i f hf; simp [environment] at hf
  | succ n ih =>
      intro i f hf
      cases he : E i with
      | none => simp [environment, he] at hf
      | some e =>
        exact (hv i e he).trans (resolve_sound mode p v _ ih e f (by
          simpa [environment, he] using hf))

/-- The test is syntactic and parameter-independent. Each successful original
expression is the same finite native value in every solution, with shared names,
zero state or parameter counts, arbitrary free values and atomic coincidences. -/
theorem original_finite_resolution :
    ∀ (k m : Nat) (E : Definitions k m) (mode : Fin k → Bool),
      (∀ e : Expr k m, (compile E mode e).isSome = true ↔ FiniteDerivation E mode e) ∧
      (∀ (e : Expr k m) (f : FiniteExpr k), compile E mode e = some f →
        ∀ (p : Fin k → Nat) (v : Fin m → CompletionTree), Solution E mode p v →
          value mode p v e = embed (finiteValue p f)) := by
  intro k m E mode
  constructor
  · intro e
    constructor
    · intro h
      obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp h
      exact resolve_derivation E mode _ (environment_derivation E mode m) e f hf
    · intro h
      obtain ⟨f, hf⟩ := derivation_compile E mode e h
      exact Option.isSome_iff_exists.mpr ⟨f, hf⟩
  · intro e f hf p v hv
    exact resolve_sound mode p v _ (environment_sound E mode p v hv m) e f hf

#print axioms original_finite_resolution

end D5.S3.Arith.FibonacciAtomic.Observer.OriginalFiniteResolution
