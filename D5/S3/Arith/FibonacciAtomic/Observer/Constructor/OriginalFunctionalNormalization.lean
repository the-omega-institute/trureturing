/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalFunctionalNormalization
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Literal-Omega functional syntax and exact root-link elimination with every reconstruction. -/

import D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints
import Mathlib.Data.Fintype.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.OriginalFunctionalNormalization

open GenealogicalFiberTransport (Source substitution)
open NativeCompletionPrefixLifting
open CompletionHomogeneousFixedPoints

/-- Source syntax after distributing fixed powers. Literal Omega has no scalar name. -/
inductive Expr (k m : Nat) where
  | ground : Source → Expr k m
  | token : Fin k → Nat → Expr k m
  | omega : Expr k m
  | var : Nat → Fin m → Expr k m
  | pair : Expr k m → Expr k m → Expr k m
  deriving DecidableEq

variable {k m : Nat}

def value (mode : Fin k → Bool) (p : Fin k → Nat) (v : Fin m → CompletionTree) :
    Expr k m → CompletionTree
  | .ground t => embed t
  | .token j c => if mode j then atomic (p j + c) else Omega
  | .omega => Omega
  | .var a i => rho^[a] (v i)
  | .pair e f => node (value mode p v e) (value mode p v f)

/-- A fixed native power, including powers of arbitrary nested expressions. -/
def power (a : Nat) : Expr k m → Expr k m
  | .ground t => .ground (substitution^[a] t)
  | .token j c => .token j (a+c)
  | .omega => .omega
  | .var b i => .var (a+b) i
  | .pair e f => .pair (power a e) (power a f)

theorem value_power (mode : Fin k → Bool) (p : Fin k → Nat)
    (v : Fin m → CompletionTree) (a : Nat) (e : Expr k m) :
    value mode p v (power a e) = rho^[a] (value mode p v e) := by
  induction e with
  | ground t => exact (iterate_embed a t).symm
  | token j c =>
      by_cases h : mode j = true
      · simp only [power, value, h, ↓reduceIte, atomic]
        rw [← Function.iterate_add_apply]
        exact congrArg (fun n => rho^[n] (leaf true)) (by omega)
      · simp [power, value, h, iterate_omega]
  | omega => exact (iterate_omega a).symm
  | var b i => exact Function.iterate_add_apply rho a b (v i)
  | pair e f ihe ihf => simp only [power, value, ihe, ihf, iterate_node]

def subst (s : Fin m → Expr k m) : Expr k m → Expr k m
  | .ground t => .ground t
  | .token j c => .token j c
  | .omega => .omega
  | .var a i => power a (s i)
  | .pair e f => .pair (subst s e) (subst s f)

def reconstruct (mode : Fin k → Bool) (p : Fin k → Nat)
    (R : Fin m → Expr k m) (v : Fin m → CompletionTree) : Fin m → CompletionTree :=
  fun i => value mode p v (R i)

theorem value_subst (mode : Fin k → Bool) (p : Fin k → Nat)
    (v : Fin m → CompletionTree) (s : Fin m → Expr k m) (e : Expr k m) :
    value mode p v (subst s e) = value mode p (reconstruct mode p s v) e := by
  induction e with
  | ground => rfl
  | token => rfl
  | omega => rfl
  | var a i => exact value_power mode p v a (s i)
  | pair e f ihe ihf => exact congrArg₂ node ihe ihf

abbrev Definitions (k m : Nat) := Fin m → Option (Expr k m)

def Solution (E : Definitions k m) (mode : Fin k → Bool) (p : Fin k → Nat)
    (v : Fin m → CompletionTree) : Prop :=
  ∀ i e, E i = some e → v i = value mode p v e

/-- Guards and all designated original coordinates are data of the same case. -/
structure FunctionalCase (k m r : Nat) where
  definitions : Definitions k m
  mode : Fin k → Bool
  guard : (Fin k → Nat) → Prop
  original : Fin r → Expr k m

def originalValues {r : Nat} (C : FunctionalCase k m r) (p : Fin k → Nat)
    (v : Fin m → CompletionTree) : Fin r → CompletionTree :=
  fun i => value C.mode p v (C.original i)

private def isLink : Option (Expr k m) → Bool
  | some (.var _ _) => true
  | _ => false

private def links (E : Definitions k m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => isLink (E i))

def PairGuarded (E : Definitions k m) : Prop :=
  ∀ i a j, E i ≠ some (.var a j)

private def eliminate (E : Definitions k m) (i : Fin m) (s : Fin m → Expr k m) :
    Definitions k m := fun l => if l = i then none else (E l).map (subst s)

private theorem eliminate_decreases (E : Definitions k m) (i : Fin m)
    (s : Fin m → Expr k m) (hi : i ∈ links E) :
    (links (eliminate E i s)).card < (links E).card := by
  have sub : links (eliminate E i s) ⊆ links E := by
    intro l hl
    have h : isLink (eliminate E i s l) = true := (Finset.mem_filter.mp hl).2
    by_cases eq : l = i
    · simp [eliminate, eq, isLink] at h
    · cases he : E l with
      | none => simp [eliminate, eq, he, isLink] at h
      | some e =>
          cases e <;> simp [eliminate, eq, he, subst, isLink] at h ⊢
          simp [links, he, isLink]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨sub, ?_⟩
  intro eq
  have h : i ∈ links (eliminate E i s) := eq ▸ hi
  simpa [links, eliminate, isLink] using h

private theorem positive_period (a : Nat) (ha : 0 < a) (X : CompletionTree)
    (hx : X = rho^[a] X) : X = Omega := by
  have orbit : ∀ n : Nat, rho^[a*n] X = X := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Nat.mul_succ, Function.iterate_add_apply, ← hx, ih]
  apply eq_omega_of_full X
  intro n
  have arith : a*(2*n) = 2*n + (a-1)*(2*n) := by
    have h : a = (a-1)+1 := by omega
    conv_lhs => rw [h]
    ring
  have full := iterate_full n (rho^[(a-1)*(2*n)] X)
  rw [← Function.iterate_add_apply, ← arith, orbit] at full
  exact full

private theorem elimination_semantics (E : Definitions k m) (i : Fin m)
    (e : Expr k m) (he : E i = some e) (s : Fin m → Expr k m)
    (other : ∀ l, l ≠ i → s l = .var 0 l)
    (law : ∀ mode p u, reconstruct mode p s u i =
      value mode p (reconstruct mode p s u) e)
    (fixed : ∀ mode p v, Solution E mode p v → reconstruct mode p s v = v) :
    (∀ mode p u, Solution (eliminate E i s) mode p u →
      Solution E mode p (reconstruct mode p s u)) ∧
    (∀ mode p v, Solution E mode p v →
      Solution (eliminate E i s) mode p v ∧ reconstruct mode p s v = v) := by
  constructor
  · intro mode p u hu l f hf
    by_cases hli : l = i
    · subst l
      have ef : e = f := Option.some.inj (he.symm.trans hf)
      subst f
      exact law mode p u
    · have hnew : eliminate E i s l = some (subst s f) := by simp [eliminate, hli, hf]
      have h := hu l (subst s f) hnew
      rw [value_subst] at h
      simpa only [reconstruct, other l hli, value, Function.iterate_zero_apply] using h
  · intro mode p v hv
    refine ⟨?_, fixed mode p v hv⟩
    intro l f hf
    by_cases hli : l = i
    · simp [eliminate, hli] at hf
    · cases hE : E l with
      | none => simp [eliminate, hli, hE] at hf
      | some g =>
          have gf : subst s g = f := by simpa [eliminate, hli, hE] using hf
          subst f
          rw [value_subst, fixed mode p v hv]
          exact hv l g hE

private theorem eliminate_link (E : Definitions k m) (i j : Fin m) (a : Nat)
    (he : E i = some (.var a j)) :
    ∃ s : Fin m → Expr k m,
      (∀ mode p u, Solution (eliminate E i s) mode p u →
        Solution E mode p (reconstruct mode p s u)) ∧
      (∀ mode p v, Solution E mode p v →
        Solution (eliminate E i s) mode p v ∧ reconstruct mode p s v = v) := by
  by_cases hij : j = i
  · subst j
    by_cases ha : a = 0
    · subst a
      let s : Fin m → Expr k m := fun l => .var 0 l
      have ident : ∀ mode p u, reconstruct mode p s u = u := by intros; rfl
      refine ⟨s, elimination_semantics E i (.var 0 i) he s (by intros; rfl) ?_ ?_⟩
      · intros; rfl
      · intro mode p v _; exact ident mode p v
    · let s : Fin m → Expr k m := fun l => if l = i then .omega else .var 0 l
      refine ⟨s, elimination_semantics E i (.var a i) he s ?_ ?_ ?_⟩
      · intro l hl; simp [s, hl]
      · intro mode p u
        simp [reconstruct, s, value, iterate_omega]
      · intro mode p v hv
        funext l
        by_cases hl : l = i
        · subst l
          have eq := positive_period a (Nat.pos_of_ne_zero ha) (v i) (hv i _ he)
          simpa [reconstruct, s, value] using eq.symm
        · simp [reconstruct, s, hl, value]
  · let s : Fin m → Expr k m := fun l => if l = i then .var a j else .var 0 l
    refine ⟨s, elimination_semantics E i (.var a j) he s ?_ ?_ ?_⟩
    · intro l hl; simp [s, hl]
    · intro mode p u
      simp [reconstruct, s, value, hij]
    · intro mode p v hv
      funext l
      by_cases hl : l = i
      · subst l
        simpa [reconstruct, s, value] using (hv i _ he).symm
      · simp [reconstruct, s, hl, value]

/-- Normalization retains all original names. Restriction of any original solution
is a normalized solution; reconstruction fixes that original solution exactly.
Every normalized solution reconstructs an original one. No solution is supplied. -/
theorem root_link_normalization (E : Definitions k m) :
    ∃ (N : Definitions k m) (R : Fin m → Expr k m), PairGuarded N ∧
      (∀ mode p u, Solution N mode p u → Solution E mode p (reconstruct mode p R u)) ∧
      (∀ mode p v, Solution E mode p v →
        Solution N mode p v ∧ reconstruct mode p R v = v) := by
  by_cases empty : links E = ∅
  · refine ⟨E, fun i => .var 0 i, ?_, ?_, ?_⟩
    · intro i a j he
      have hi : i ∈ links E := by simp [links, he, isLink]
      rw [empty] at hi
      exact Finset.notMem_empty i hi
    · intro mode p u hu; exact hu
    · intro mode p v hv; exact ⟨hv, rfl⟩
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have link : isLink (E i) = true := (Finset.mem_filter.mp hi).2
    obtain ⟨a, j, he⟩ : ∃ a j, E i = some (.var a j) := by
      cases he : E i with
      | none => simp [he, isLink] at link
      | some e => cases e <;> simp [he, isLink] at link ⊢
    obtain ⟨s, sound, restrict⟩ := eliminate_link E i j a he
    have dec := eliminate_decreases E i s hi
    obtain ⟨N, R, guarded, nsound, nrestrict⟩ := root_link_normalization (eliminate E i s)
    refine ⟨N, fun l => subst R (s l), guarded, ?_, ?_⟩
    · intro mode p u hu
      have h := sound mode p (reconstruct mode p R u) (nsound mode p u hu)
      have eq : reconstruct mode p (fun l => subst R (s l)) u =
          reconstruct mode p s (reconstruct mode p R u) := by
        funext l; exact value_subst mode p u R (s l)
      rwa [eq]
    · intro mode p v hv
      obtain ⟨hv', hs⟩ := restrict mode p v hv
      obtain ⟨hv'', hR⟩ := nrestrict mode p v hv'
      refine ⟨hv'', ?_⟩
      funext l
      rw [reconstruct, value_subst, hR]
      exact congrFun hs l
termination_by (links E).card

#print axioms root_link_normalization

end D5.S3.Arith.FibonacciAtomic.Observer.OriginalFunctionalNormalization
