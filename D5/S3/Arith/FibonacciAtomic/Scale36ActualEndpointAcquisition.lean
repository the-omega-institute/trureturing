/- GID: D5/S3/Arith/FibonacciAtomic/Scale36ActualEndpointAcquisition
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Literal Scale36 family and actual conditional routing addresses. -/

import D5.S3.Arith.FibonacciAtomic.FourExitRawEndpointSpectrum
import D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutCompletion
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Scale36ActualEndpointAcquisition

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition
open ActualImageSevenLeafSeparation (thirdImage leafAddresses leafLabel Nonconflict)
open FourExitRawEndpointSpectrum (comb comb_slot_readout comb_tail_readout)
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
  (PassiveProtocol runPassiveProtocol)
open scoped BigOperators

local notation "Index" => fun k : Nat => Unit ⊕ (Fin k × Fin 2)
local notation "E" => ActualImageSevenLeafSeparation.E
local notation "A" => ActualImageSevenLeafSeparation.A
local notation "C" => ActualImageSevenLeafSeparation.C
local notation "B" => FourExitRawEndpointSpectrum.B
local notation "Kₜ" => FourExitRawEndpointSpectrum.H
local notation "T" => thirdImage FourExitRawEndpointSpectrum.t
local notation "W₁" => (FreeMagma.mul B C : Source)

/-- Original activity blocks, ordered U then V. -/
def active (r : Fin 2) : Source := if r.val = 0 then T else W₁

/-- The coupled compensation blocks, ordered B then A. -/
def compensation (r : Fin 2) : Source := if r.val = 0 then B else A

/-- Complete original Scale36 prototypes. The left summand is P0. -/
def family (k : Nat) : Index k → Source
  | .inl _ => comb k (fun _ => C) Kₜ
  | .inr (j,r) => comb k (fun i => if i = j then active r else C) (compensation r)

/-- Bracket-preserving original preimages of the prototypes. -/
def preFamily (k : Nat) : Index k → Source
  | .inl _ => comb k (fun _ => .of false) FourExitRawEndpointSpectrum.h
  | .inr (j,r) => comb k (fun i => if i = j then
      (if r.val = 0 then FourExitRawEndpointSpectrum.t else .mul E (.of false))
      else .of false) (if r.val = 0 then E else .of true)

/-- Literal a, b, q, r addresses in an activity slot. -/
def addresses (k : Nat) (j : Fin k) (s : Fin 4) : Address :=
  List.replicate j.val true ++ false ::
    (match s.val with
      | 0 => [false,false,true]
      | 1 => [true,true]
      | 2 => [true,false,false,true]
      | _ => [false,false,false,false,true])

/-- The one additional paid address prescribed by each target/input pair. -/
def extra (k : Nat) (target row : Index k) : Option Address :=
  if target = row then none else
    match row with
    | .inl _ => match target with
      | .inl _ => none
      | .inr (j,_) => some (addresses k j 2)
    | .inr (j,r) =>
      if r.val = 1 then some (addresses k j 0) else
        match target with
        | .inl _ => some (addresses k j 1)
        | .inr (l,s) =>
          if l = j ∧ s.val = 1 then some (addresses k j 3)
          else some (addresses k j 1)

/-- Every literal Scale36 prototype is a distinct positive tree with the same
number of leaves, and all prototype pairs agree on shared leaf labels. -/
theorem family_structure (k : Nat) (hk : 1 ≤ k) :
    Function.Injective (family k) ∧
    (∀ i : Index k, thirdImage (preFamily k i) = family k i ∧
      Positive (family k i) ∧ (family k i).length = 5 * k + 11 ∧
      (leafAddresses (family k i)).card = 5 * k + 11) ∧
    (∀ i j : Index k, Nonconflict (family k i) (family k j)) := by
  classical
  let slots : Index k → Fin k → Source := fun row l => match row with
    | .inl _ => C
    | .inr (j,r) => if l = j then active r else C
  let last : Index k → Source := fun row => match row with
    | .inl _ => Kₜ
    | .inr (_,r) => compensation r
  have assemble (i : Index k) : family k i = comb k (slots i) (last i) := by
    cases i <;> rfl
  have hom : Function.Semiconj₂ thirdImage FreeMagma.mul FreeMagma.mul :=
    Function.Semiconj₂.iterate
      (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
        substitution.map_mul) 3
  have map_comb (n : Nat) : ∀ (f : Fin n → Source) (q : Source),
      thirdImage (comb n f q) = comb n (thirdImage ∘ f) (thirdImage q) := by
    induction n with
    | zero => intros; rfl
    | succ n ih =>
      intro f q
      exact (hom _ _).trans (congrArg (FreeMagma.mul (thirdImage (f 0)))
        (ih (f ∘ Fin.succ) q))
  have image (i : Index k) : thirdImage (preFamily k i) = family k i := by
    cases i with
    | inl u => exact map_comb k _ _
    | inr p =>
      rcases p with ⟨j,r⟩
      unfold preFamily family
      rw [map_comb]
      congr 1
      · funext l
        by_cases h : l = j
        · fin_cases r <;> simp [Function.comp_def, h, active] <;> rfl
        · simp [Function.comp_def, h]; rfl
      · fin_cases r <;> rfl
  have comb_length (n : Nat) : ∀ (f : Fin n → Source) (q : Source),
      (comb n f q).length = (∑ l, (f l).length) + q.length := by
    induction n with
    | zero => intro f q; simp [comb]
    | succ n ih =>
      intro f q
      simp only [comb, FreeMagma.length, ih, Fin.sum_univ_succ, Nat.add_assoc]
  have size (i : Index k) : (family k i).length = 5 * k + 11 := by
    rw [assemble, comb_length]
    cases i with
    | inl u => simp [slots, last, show C.length = 5 from rfl,
        show Kₜ.length = 11 from rfl, Nat.mul_comm]
    | inr p =>
      rcases p with ⟨j,r⟩
      have total : (active r).length + (compensation r).length = 16 := by
        fin_cases r <;> rfl
      have sum_slots : (∑ l : Fin k, (slots (.inr (j,r)) l).length) =
          (k - 1) * 5 + (active r).length := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
        simp only [slots, if_pos rfl]
        have unchanged (l : Fin k) (hl : l ∈ (Finset.univ : Finset (Fin k)).erase j) :
            (if l = j then active r else C).length = 5 := by
          rw [if_neg (Finset.mem_erase.mp hl).1]; rfl
        rw [Finset.sum_congr rfl unchanged]
        simp [Finset.card_erase_of_mem (Finset.mem_univ j)]
      rw [sum_slots]
      change (k - 1) * 5 + (active r).length + (compensation r).length = _
      omega
  have distinct : Function.Injective (family k) := by
    have kind : Function.Injective active := by
      intro r s he
      fin_cases r <;> fin_cases s <;> first | rfl | contradiction
    have different (r : Fin 2) : active r ≠ C := by
      fin_cases r <;> decide
    intro i j he
    have same (l : Fin k) : slots i l = slots j l := by
      have readings (u : Address) : readout u (slots i l) = readout u (slots j l) := by
        rw [← comb_slot_readout k (slots i) (last i) l u,
          ← comb_slot_readout k (slots j) (last j) l u, ← assemble, ← assemble, he]
      exact source_foundation.2.2.1 _ _ (fun u _ => readings u)
    cases i with
    | inl u =>
      cases j with
      | inl v => congr
      | inr p => exact False.elim (different p.2 (by simpa [slots] using (same p.1).symm))
    | inr p =>
      cases j with
      | inl u => exact False.elim (different p.2 (by simpa [slots] using same p.1))
      | inr q =>
        have position : p.1 = q.1 := by
          by_contra hn
          exact different p.2 (by simpa [slots, hn] using same p.1)
        have branch : p.2 = q.2 := kind (by simpa [slots, position] using same p.1)
        exact congrArg Sum.inr (Prod.ext position branch)
  have local_nc : ∀ a ∈ ({C,T,W₁} : Finset Source),
      ∀ b ∈ ({C,T,W₁} : Finset Source), Nonconflict a b := by
    intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> decide
  have tail_nc : ∀ a ∈ ({Kₜ,B,A} : Finset Source),
      ∀ b ∈ ({Kₜ,B,A} : Finset Source), Nonconflict a b := by
    intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> decide
  have lift_nc (n : Nat) : ∀ (f g : Fin n → Source) (q t : Source),
      (∀ l, f l ∈ ({C,T,W₁} : Finset Source)) →
      (∀ l, g l ∈ ({C,T,W₁} : Finset Source)) →
      q ∈ ({Kₜ,B,A} : Finset Source) → t ∈ ({Kₜ,B,A} : Finset Source) →
      Nonconflict (comb n f q) (comb n g t) := by
    induction n with
    | zero => intro f g q t _ _ hq ht; exact tail_nc q hq t ht
    | succ n ih =>
      intro f g q t hf hg hq ht
      exact ⟨local_nc (f 0) (hf 0) (g 0) (hg 0),
        ih (f ∘ Fin.succ) (g ∘ Fin.succ) q t
          (fun l => hf l.succ) (fun l => hg l.succ) hq ht⟩
  have slots_mem (i : Index k) (l : Fin k) : slots i l ∈ ({C,T,W₁} : Finset Source) := by
    cases i with
    | inl u => simp [slots]
    | inr p =>
      rcases p with ⟨j,r⟩
      fin_cases r <;> by_cases h : l = j <;> simp [slots, active, h]
  have last_mem (i : Index k) : last i ∈ ({Kₜ,B,A} : Finset Source) := by
    cases i with
    | inl u => simp [last]
    | inr p => rcases p with ⟨j,r⟩; fin_cases r <;> simp [last, compensation]
  refine ⟨distinct, fun i => ⟨image i, ⟨preFamily k i, image i⟩, size i, ?_⟩, ?_⟩
  · exact (ActualImageSevenLeafSeparation.seven_leaf_separation.1 _).1.trans (size i)
  · intro i j
    rw [assemble, assemble]
    exact lift_nc k _ _ _ _ (slots_mem i) (slots_mem j) (last_mem i) (last_mem j)

end D5.S3.Arith.FibonacciAtomic.Scale36ActualEndpointAcquisition
