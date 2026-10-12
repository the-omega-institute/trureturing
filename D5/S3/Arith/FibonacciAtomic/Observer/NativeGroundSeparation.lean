/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Simultaneous finite ground separation in the native Boolean free magma. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns
import D5.S3.Arith.FibonacciAtomic.FourExitRawEndpointSpectrum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSeparation

open GenealogicalFiberTransport (Source)
open FourExitRawEndpointSpectrum (comb comb_foundation)
open scoped BigOperators

abbrev Term (X : Type) := FreeMagma (Bool ⊕ X)

def evaluate {X : Type} (v : X → Source) : Term X →ₙ* Source :=
  FreeMagma.lift (Sum.elim FreeMagma.of v)

/-- Counts of variable and constant occurrences, including repetitions. -/
def counts {X : Type} : Term X → Nat × Nat
  | .of (.inl _) => (0, 1)
  | .of (.inr _) => (1, 0)
  | .mul l r => ((counts l).1 + (counts r).1, (counts l).2 + (counts r).2)

private theorem count_length {X : Type} (t : Term X) :
    (counts t).1 + (counts t).2 = t.length := by
  induction t with
  | of b => cases b <;> rfl
  | mul l r ihl ihr => simp only [counts, FreeMagma.length]; omega

private theorem evaluated_length {X : Type} (v : X → Source) (M : Nat)
    (mass : ∀ x, (v x).length = M) (t : Term X) :
    (evaluate v t).length = M * (counts t).1 + (counts t).2 := by
  induction t with
  | of b => cases b with
    | inl b => rfl
    | inr x => simpa [evaluate, counts] using mass x
  | mul l r ihl ihr =>
      change (evaluate v l).length + (evaluate v r).length = _
      rw [ihl, ihr]
      simp only [counts]
      ring

private theorem compound_mass_ne {X : Type} (v : X → Source) (M : Nat)
    (hm : 2 ≤ M) (mass : ∀ x, (v x).length = M) (l r : Term X)
    (bound : (FreeMagma.mul l r).length < M) :
    (evaluate v (.mul l r)).length ≠ M := by
  rw [evaluated_length v M mass]
  have c := count_length (.mul l r)
  have pos : 2 ≤ (FreeMagma.mul l r).length := by
    have := l.length_pos
    have := r.length_pos
    simp only [FreeMagma.length]; omega
  by_cases hv : (counts (.mul l r)).1 = 0
  · simp only [hv, Nat.mul_zero, Nat.zero_add]
    omega
  · intro eq
    have low : 1 ≤ (counts (.mul l r)).1 := by omega
    by_cases one : (counts (.mul l r)).1 = 1
    · rw [one, Nat.mul_one] at eq
      omega
    · have two : 2 ≤ (counts (.mul l r)).1 := by omega
      nlinarith

theorem bounded_eval_injective {X : Type} (v : X → Source) (M : Nat)
    (hm : 2 ≤ M) (mass : ∀ x, (v x).length = M) (inj : Function.Injective v)
    (s : Term X) : ∀ t : Term X, s.length < M → t.length < M →
    evaluate v s = evaluate v t → s = t := by
  induction s with
  | of a =>
      intro t hs ht eq
      cases a with
      | inl b =>
          cases t with
          | of c => cases c with
            | inl c =>
                have bc : b = c := by injection eq
                subst c; rfl
            | inr x =>
                have len := congrArg FreeMagma.length eq
                simp only [evaluate, FreeMagma.lift_of, Sum.elim_inl, Sum.elim_inr,
                  FreeMagma.length] at len
                rw [mass x] at len
                omega
          | mul l r => change FreeMagma.of b = FreeMagma.mul _ _ at eq; cases eq
      | inr x =>
          cases t with
          | of c => cases c with
            | inl b =>
                have len := congrArg FreeMagma.length eq
                simp only [evaluate, FreeMagma.lift_of, Sum.elim_inl, Sum.elim_inr,
                  FreeMagma.length] at len
                rw [mass x] at len
                omega
            | inr y => exact congrArg (fun z => FreeMagma.of (Sum.inr z)) (inj eq)
          | mul l r =>
              have len := congrArg FreeMagma.length eq
              change (v x).length = (evaluate v (.mul l r)).length at len
              exact False.elim (compound_mass_ne v M hm mass l r ht (len.symm.trans (mass x)))
  | mul l r ihl ihr =>
      intro t hs ht eq
      cases t with
      | of a => cases a with
        | inl b => change FreeMagma.mul _ _ = FreeMagma.of b at eq; cases eq
        | inr x =>
            have len := congrArg FreeMagma.length eq
            change (evaluate v (.mul l r)).length = (v x).length at len
            exact False.elim (compound_mass_ne v M hm mass l r hs (len.trans (mass x)))
      | mul l' r' =>
          change FreeMagma.mul _ _ = FreeMagma.mul _ _ at eq
          injection eq with le re
          have lp := r.length_pos
          have rp := l.length_pos
          have lp' := r'.length_pos
          have rp' := l'.length_pos
          simp only [FreeMagma.length] at hs ht
          exact congrArg₂ FreeMagma.mul (ihl l' (by omega) (by omega) le)
            (ihr r' (by omega) (by omega) re)

/-- One marked leaf in a common finite comb. All variables have the same mass. -/
def code (n : Nat) (i : Fin n) : Source :=
  comb n (fun j => .of (decide (j = i))) (.of false)

theorem code_mass (n : Nat) (i : Fin n) : (code n i).length = n + 1 := by
  rw [code, (comb_foundation n (fun j => .of (decide (j = i)))
    (fun j => .of (decide (j = i))) (.of false) (.of false)).2.1]
  simp

theorem code_injective (n : Nat) : Function.Injective (code n) := by
  intro i j eq
  have heads := (comb_foundation n (fun k => .of (decide (k = i)))
    (fun k => .of (decide (k = j))) (.of false) (.of false)).2.2.1.mp eq
  have label := congrFun heads.1 i
  have b : decide (i = i) = decide (i = j) := by injection label
  simpa using b.symm

/-- Every finite list of syntactically unequal pairs has one simultaneous
actual finite ground solution. The empty variable type is included. -/
theorem simultaneous_ground_separation {X : Type} [Fintype X]
    (pairs : List (Term X × Term X)) :
    (∀ p ∈ pairs, p.1 ≠ p.2) ↔
      ∃ v : X → Source, ∀ p ∈ pairs, evaluate v p.1 ≠ evaluate v p.2 := by
  classical
  constructor
  · intro distinct
    let L := (pairs.map (fun p => max p.1.length p.2.length)).foldr max 0
    let n := max (Fintype.card X) (max L 1)
    let e := Fintype.equivFin X
    let cast : Fin (Fintype.card X) → Fin n := fun i => ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_max_left _ _)⟩
    let v : X → Source := fun x => code n (cast (e x))
    have mass : ∀ x, (v x).length = n+1 := fun x => code_mass n _
    have inj : Function.Injective v := by
      intro x y h
      have q := code_injective n h
      have qv : (e x).val = (e y).val := congrArg (fun z : Fin n => z.val) q
      exact e.injective (Fin.ext qv)
    have member_bound (p : Term X × Term X) (hp : p ∈ pairs) :
        max p.1.length p.2.length ≤ L := by
      have hm : max p.1.length p.2.length ∈ pairs.map (fun p => max p.1.length p.2.length) :=
        List.mem_map.mpr ⟨p, hp, rfl⟩
      change _ ≤ (pairs.map (fun p => max p.1.length p.2.length)).foldr max 0
      generalize pairs.map (fun p => max p.1.length p.2.length) = xs at hm ⊢
      induction xs with
      | nil => simp at hm
      | cons a xs ih =>
          rcases List.mem_cons.mp hm with he | he
          · subst a; exact Nat.le_max_left _ _
          · exact (ih he).trans (Nat.le_max_right _ _)
    refine ⟨v, ?_⟩
    intro p hp eq
    have hb := member_bound p hp
    have hn : L ≤ n := (Nat.le_max_left L 1).trans (Nat.le_max_right _ _)
    have hm : 2 ≤ n+1 := by dsimp [n]; omega
    exact distinct p hp (bounded_eval_injective v (n+1) hm mass inj p.1 p.2
      (by have := Nat.le_max_left p.1.length p.2.length; omega)
      (by have := Nat.le_max_right p.1.length p.2.length; omega) eq)
  · rintro ⟨v, h⟩ p hp eq
    exact h p hp (congrArg (evaluate v) eq)

end D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSeparation
