/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSymbolicRowElimination
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSymbolicRowElimination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact sort-sensitive inversion of symbolic row exteriors into consumed bindings. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Exact sort-sensitive inversion of symbolic row exteriors into consumed bindings. -/

namespace D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSymbolicRowElimination

open GenealogicalFiberTransport (Source)
open NativeGroundSeparation (Term evaluate)
open NativeSymbolicRecutting (SymbolicExterior exteriorFill)
open ActualCutPartitionDecoder (HoleExterior)

def sourceTerm {X : Type} (u : Source) : Term X :=
  FreeMagma.lift (fun b : Bool => .of (.inl b)) u

def decodeHoleFree : HoleExterior → Option Source
  | .of (.inl b) => some (.of b)
  | .of (.inr _) => none
  | .mul l r =>
      match decodeHoleFree l, decodeHoleFree r with
      | some u, some v => some (.mul u v)
      | _, _ => none

def bindingHolds {X : Type} (v : X → Source) : List (X × Term X) → Prop
  | [] => True
  | (x, t) :: rest => v x = evaluate v t ∧ bindingHolds v rest

def matchExterior {X : Type} : SymbolicExterior X → HoleExterior →
    Option (List (X × Term X))
  | .of (.inl (.inl b)), .of (.inl c) =>
      if h : b = c then some [] else none
  | .of (.inl (.inl _)), _ => none
  | .of (.inl (.inr x)), u =>
      (decodeHoleFree u).map (fun s => [(x, sourceTerm s)])
  | .of (.inr q), .of (.inr r) =>
      if h : q = r then some [] else none
  | .of (.inr _), _ => none
  | .mul p q, .mul u v =>
      match matchExterior p u, matchExterior q v with
      | some bp, some bq => some (bp ++ bq)
      | _, _ => none
  | .mul _ _, _ => none

theorem evaluate_sourceTerm {X : Type} (v : X → Source) (u : Source) :
    evaluate v (sourceTerm u) = u := by
  induction u with
  | of b => rfl
  | mul l r ihl ihr =>
      change evaluate v (sourceTerm l) * evaluate v (sourceTerm r) = _
      rw [ihl, ihr]
      rfl

theorem decodeHoleFree_sound (u : HoleExterior) (s : Source)
    (h : decodeHoleFree u = some s) : FreeMagma.map Sum.inl s = u := by
  induction u generalizing s with
  | of a =>
      cases a with
      | inl b =>
          simp only [decodeHoleFree] at h
          cases h
          rfl
      | inr q => simp [decodeHoleFree] at h
  | mul l r ihl ihr =>
      cases hs : decodeHoleFree l with
      | none => simp [decodeHoleFree, hs] at h
      | some sl =>
          cases hr : decodeHoleFree r with
          | none => simp [decodeHoleFree, hs, hr] at h
          | some sr =>
              cases s with
              | of b => simp [decodeHoleFree, hs, hr] at h
              | mul s₁ s₂ =>
                  simp only [decodeHoleFree, hs, hr, Option.some.injEq] at h
                  cases h
                  exact congrArg₂ FreeMagma.mul (ihl sl hs) (ihr sr hr)

theorem decodeHoleFree_map (s : Source) :
    decodeHoleFree (FreeMagma.map Sum.inl s) = some s := by
  induction s with
  | of b => rfl
  | mul l r ihl ihr =>
      change decodeHoleFree
        (FreeMagma.mul (FreeMagma.map Sum.inl l) (FreeMagma.map Sum.inl r)) = _
      simp [decodeHoleFree, ihl, ihr]

theorem bindingHolds_append {X : Type} (v : X → Source)
    (a b : List (X × Term X)) :
    bindingHolds v (a ++ b) ↔ bindingHolds v a ∧ bindingHolds v b := by
  induction a with
  | nil => simp [bindingHolds]
  | cons h a ih =>
      cases h with
      | mk x t => simp only [List.cons_append, bindingHolds, ih, and_assoc]

theorem matchExterior_sound {X : Type} (p : SymbolicExterior X)
    (u : HoleExterior) (v : X → Source) (bs : List (X × Term X))
    (hm : matchExterior p u = some bs) (hb : bindingHolds v bs) :
    exteriorFill v p = u := by
  induction p generalizing u bs with
  | of a =>
      cases a with
      | inl a =>
          cases a with
          | inl b =>
              cases u with
              | of c =>
                  cases c with
                  | inl c =>
                      simp only [matchExterior] at hm
                      split at hm <;> simp_all [exteriorFill]
                  | inr q => simp [matchExterior] at hm
              | mul l r => simp [matchExterior] at hm
          | inr x =>
              obtain ⟨s, hs, hbs⟩ := Option.map_eq_some_iff.mp hm
              subst bs
              have hxs : v x = s := by
                simpa [bindingHolds, evaluate_sourceTerm] using hb
              have hmap := decodeHoleFree_sound u s hs
              simpa [exteriorFill, hxs] using hmap
      | inr q =>
          cases u with
          | of c =>
              cases c with
              | inl b => simp [matchExterior] at hm
              | inr r =>
                  simp only [matchExterior] at hm
                  split at hm <;> simp_all [exteriorFill]
          | mul l r => simp [matchExterior] at hm
  | mul p q ihp ihq =>
      cases u with
      | of a => simp [matchExterior] at hm
      | mul u w =>
          cases hpm : matchExterior p u with
          | none => simp [matchExterior, hpm] at hm
          | some bp =>
              cases hqm : matchExterior q w with
              | none => simp [matchExterior, hpm, hqm] at hm
              | some bq =>
                  have hbs : bp ++ bq = bs := by
                    simpa [matchExterior, hpm, hqm] using hm
                  rw [← hbs] at hb
                  have hsplit := (bindingHolds_append v bp bq).mp hb
                  change exteriorFill v p * exteriorFill v q = u * w
                  rw [ihp u bp hpm hsplit.1, ihq w bq hqm hsplit.2]

theorem matchExterior_complete {X : Type} (p : SymbolicExterior X)
    (u : HoleExterior) (v : X → Source) (he : exteriorFill v p = u) :
    ∃ bs, matchExterior p u = some bs ∧ bindingHolds v bs := by
  induction p generalizing u with
  | of a =>
      cases a with
      | inl a =>
          cases a with
          | inl b =>
              cases u with
              | of c =>
                  cases c with
                  | inl c =>
                      simp only [exteriorFill] at he
                      have : b = c := by cases he; rfl
                      subst c
                      exact ⟨[], by simp [matchExterior], trivial⟩
                  | inr q => cases he
              | mul l r => cases he
          | inr x =>
              have hd : decodeHoleFree u = some (v x) := by
                rw [← he]
                simp [exteriorFill, decodeHoleFree_map]
              exact ⟨[(x, sourceTerm (v x))], by
                simp [matchExterior, hd, evaluate_sourceTerm, bindingHolds]⟩
      | inr q =>
          cases u with
          | of c =>
              cases c with
              | inl b => cases he
              | inr r =>
                  have : q = r := by cases he; rfl
                  subst r
                  exact ⟨[], by simp [matchExterior], trivial⟩
          | mul l r => cases he
  | mul p q ihp ihq =>
      cases u with
      | of a => simp [exteriorFill] at he
      | mul u w =>
          have hp : exteriorFill v p = u := by injection he with hp _
          have hq : exteriorFill v q = w := by injection he with _ hq
          obtain ⟨bp, hbp, hbpp⟩ := ihp u hp
          obtain ⟨bq, hbq, hbqq⟩ := ihq w hq
          exact ⟨bp ++ bq, by simp [matchExterior, hbp, hbq],
            (bindingHolds_append v bp bq).mpr ⟨hbpp, hbqq⟩⟩

theorem exterior_match_exact {X : Type} (p : SymbolicExterior X)
    (u : HoleExterior) (v : X → Source) :
    exteriorFill v p = u ↔
      ∃ bs, matchExterior p u = some bs ∧ bindingHolds v bs := by
  constructor
  · exact matchExterior_complete p u v
  · rintro ⟨bs, hm, hb⟩
    exact matchExterior_sound p u v bs hm hb

end D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSymbolicRowElimination
