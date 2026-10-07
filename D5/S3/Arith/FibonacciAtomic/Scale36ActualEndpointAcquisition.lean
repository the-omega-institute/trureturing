/- GID: D5/S3/Arith/FibonacciAtomic/Scale36ActualEndpointAcquisition
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Complete Scale36 family structure and all coarse-observable actual endpoint bills. -/

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
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist)
open ActualCoarseReadoutHistory (kappa_hist)
open scoped BigOperators

local notation "Index" => fun k : Nat => Unit ⊕ (Fin k × Fin 2)
local notation "E" => ActualImageSevenLeafSeparation.E
local notation "A" => ActualImageSevenLeafSeparation.A
local notation "C" => ActualImageSevenLeafSeparation.C
local notation "B" => FourExitRawEndpointSpectrum.B
local notation "Kₜ" => FourExitRawEndpointSpectrum.H
local notation "T" => thirdImage FourExitRawEndpointSpectrum.t
local notation "W₁" => (FreeMagma.mul B C : Source)
local notation "CH" => Hist (fun _ : Address => Option Bool)
local notation "Route" => fun k : Nat =>
  PassiveProtocol Address (fun _ => Option Bool) × (CH → Option (Index k))

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

/-- The retained slot uses a/q for U and q/r for V. A beta report selects
the global fallback. The baseline stops after the ordinary scan. -/
def retained (k : Nat) : Index k → Route k
  | .inl _ => (.stop, fun _ => some (.inl ()))
  | .inr (j,r) =>
    let first : Fin 4 := if r.val = 0 then 0 else 2
    let second : Fin 4 := if r.val = 0 then 2 else 3
    (.query (addresses k j first) (fun y => match y with
       | some true => .query (addresses k j second) (fun _ => .stop)
       | _ => .stop),
     fun h => match h with
       | x :: rest => match x.2 with
         | none => if r.val = 0 then some (.inr (j,1)) else some (.inl ())
         | some false => none
         | some true => match rest with
           | [] => none
           | y :: _ => match y.2 with
             | none => if r.val = 0 then some (.inl ()) else some (.inr (j,0))
             | some true => some (.inr (j,r))
             | some false => none
       | [] => none)

/-- Ordinary activity slots are scanned in the supplied order. Only two
actual alpha leaf reports continue to the next slot. -/
def scan (k : Nat) (target : Index k) : List (Fin k) → Route k
  | [] => retained k target
  | j :: rest =>
    let next := scan k target rest
    (.query (addresses k j 0) (fun y => match y with
       | none => .stop
       | some false => .stop
       | some true => .query (addresses k j 1) (fun z => match z with
         | some true => next.1
         | _ => .stop)),
     fun h => match h with
       | x :: tail => match x.2 with
         | none => some (.inr (j,1))
         | some false => none
         | some true => match tail with
           | [] => none
           | y :: following => match y.2 with
             | none => some (.inr (j,0))
             | some false => none
             | some true => next.2 following
       | [] => none)

/-- All ordinary slots occur in increasing order; an exceptional target's
own slot is retained for its final two-address rule. -/
def route (k : Nat) (target : Index k) : Route k :=
  scan k target ((List.finRange k).filter (fun j => match target with
    | .inl _ => true
    | .inr (l,_) => j != l))

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
    | inl u =>
      change (∑ _l : Fin k, 5) + 11 = _
      simp [Nat.mul_comm]
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
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      simp only [ActualImageSevenLeafSeparation.C, ActualImageSevenLeafSeparation.A,
        ActualImageSevenLeafSeparation.E, FourExitRawEndpointSpectrum.B, thirdImage,
        FourExitRawEndpointSpectrum.t, Nonconflict]
    all_goals trivial
  have tail_nc : ∀ a ∈ ({Kₜ,B,A} : Finset Source),
      ∀ b ∈ ({Kₜ,B,A} : Finset Source), Nonconflict a b := by
    intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      simp only [FourExitRawEndpointSpectrum.H, FourExitRawEndpointSpectrum.B,
        FourExitRawEndpointSpectrum.h, FourExitRawEndpointSpectrum.t,
        thirdImage, ActualImageSevenLeafSeparation.C, ActualImageSevenLeafSeparation.A,
        ActualImageSevenLeafSeparation.E, Nonconflict]
    all_goals trivial
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

/-- Every target has a coarse-observable original strategy with exactly the
literal routing bill. Its correctness and finite termination cover all sources. -/
theorem result (k : Nat) (hk : 1 ≤ k) :
    Function.Injective (family k) ∧
    (∀ i : Index k, thirdImage (preFamily k i) = family k i ∧
      Positive (family k i) ∧ (family k i).length = 5 * k + 11 ∧
      (leafAddresses (family k i)).card = 5 * k + 11) ∧
    (∀ i j : Index k, Nonconflict (family k i) (family k j)) ∧
    Fintype.card (Index k) = 2 * k + 1 ∧
    (∀ target : Index k, ∃ pi : Strategy, Function.FactorsThrough pi.policy kappa_hist ∧
      (∀ row : Index k,
        paid (terminal pi (family k row)).1 =
          leafAddresses (family k row) ∪ (extra k target row).toFinset ∧
        cost pi (family k row) = 5 * k + 12 - if target = row then 1 else 0)) := by
  classical
  refine ⟨(family_structure k hk).1, (family_structure k hk).2.1,
    (family_structure k hk).2.2, ?_, ?_⟩
  · simp [Fintype.card_sum, Fintype.card_prod, Nat.mul_comm, Nat.add_comm]
  let column : Fin 3 → Fin 4 → Option Bool := fun r q =>
    match r.val, q.val with
    | 0, 0 | 0, 1 | 1, 0 | 1, 2 | 2, 2 | 2, 3 => some true
    | _, _ => none
  have profile (row : Index k) (l : Fin k) (q : Fin 4) :
      leafLabel (family k row) (addresses k l q) =
        match row with
        | .inl _ => column 0 q
        | .inr (j,r) => if l = j then column r.succ q else column 0 q := by
    cases row with
    | inl u =>
      fin_cases q <;>
        simp only [family, addresses, leafLabel, comb_slot_readout, column] <;> rfl
    | inr p =>
      rcases p with ⟨j,r⟩
      by_cases h : l = j
      · subst l
        fin_cases q <;> fin_cases r <;>
          simp only [family, addresses, leafLabel, comb_slot_readout, if_pos rfl,
            active, column] <;> rfl
      · fin_cases q <;>
          simp only [family, addresses, leafLabel, comb_slot_readout, if_neg h, column] <;> rfl
  have leaf_test (U : Source) (q : Address) :
      q ∈ leafAddresses U ↔ leafLabel U q ≠ none := by
    rw [(ActualImageSevenLeafSeparation.seven_leaf_separation.1 U).2 q]
    cases h : leafLabel U q <;> simp [h]
  have retained_data (j : Fin k) (s : Fin 2) (row : Option (Fin 2)) :
      let i : Index k := match row with | none => .inl () | some r => .inr (j,r)
      let p := retained k (.inr (j,s))
      let tr := runPassiveProtocol (fun q W => leafLabel W q) p.1 (family k i)
      p.2 tr = some i ∧
        (tr.map Sigma.fst).toFinset \ leafAddresses (family k i) =
          (extra k (.inr (j,s)) i).toFinset := by
    dsimp only
    have in_leaf (i : Index k) (q : Fin 4)
        (h : leafLabel (family k i) (addresses k j q) = some true) :
        addresses k j q ∈ leafAddresses (family k i) :=
      (leaf_test _ _).mpr (h ▸ Option.some_ne_none _)
    have out_leaf (i : Index k) (q : Fin 4)
        (h : leafLabel (family k i) (addresses k j q) = none) :
        addresses k j q ∉ leafAddresses (family k i) := by
      rw [leaf_test, h]; simp
    cases row with
    | none =>
      have hq := out_leaf (.inl ()) 2 (by simp [profile, column])
      have ha := in_leaf (.inl ()) 0 (by simp [profile, column])
      fin_cases s <;>
        simp [retained, runPassiveProtocol, profile, column, extra,
          ha, hq, Finset.insert_sdiff_of_mem _ ha, Finset.insert_sdiff_of_notMem _ hq]
    | some r =>
      fin_cases r
      · have ha := in_leaf (.inr (j,0)) 0 (by simp [profile, column])
        have hq := in_leaf (.inr (j,0)) 2 (by simp [profile, column])
        have hr := out_leaf (.inr (j,0)) 3 (by simp [profile, column])
        fin_cases s <;>
          simp [retained, runPassiveProtocol, profile, column, extra,
            ha, hq, hr, Finset.insert_sdiff_of_mem _ ha, Finset.insert_sdiff_of_mem _ hq,
            Finset.insert_sdiff_of_notMem _ hr]
      · have ha := out_leaf (.inr (j,1)) 0 (by simp [profile, column])
        have hq := in_leaf (.inr (j,1)) 2 (by simp [profile, column])
        have hr := in_leaf (.inr (j,1)) 3 (by simp [profile, column])
        fin_cases s <;>
          simp [retained, runPassiveProtocol, profile, column, extra,
            ha, hq, hr, Finset.insert_sdiff_of_notMem _ ha, Finset.insert_sdiff_of_mem _ hq,
            Finset.insert_sdiff_of_mem _ hr]
  have scan_data (target : Index k) : ∀ ls : List (Fin k),
      (∀ (j : Fin k) (r : Fin 2), target = .inr (j,r) → j ∉ ls) →
      ∀ row : Index k,
      (∀ (j : Fin k) (r : Fin 2), row = .inr (j,r) →
        j ∈ ls ∨ ∃ s : Fin 2, target = .inr (j,s)) →
      let p := scan k target ls
      let tr := runPassiveProtocol (fun q W => leafLabel W q) p.1 (family k row)
      p.2 tr = some row ∧
        (tr.map Sigma.fst).toFinset \ leafAddresses (family k row) =
          (extra k target row).toFinset := by
    intro ls
    induction ls with
    | nil =>
      intro absent row cover
      cases target with
      | inl u =>
        cases row with
        | inl v => simp [scan, retained, runPassiveProtocol, extra]
        | inr p =>
          obtain ⟨s,hs⟩ := (cover p.1 p.2 rfl).resolve_left (by simp)
          contradiction
      | inr p =>
        rcases p with ⟨j,s⟩
        cases row with
        | inl v => cases v; simpa [scan] using retained_data j s none
        | inr q =>
          obtain ⟨t,ht⟩ := (cover q.1 q.2 rfl).resolve_left (by simp)
          have he : j = q.1 := congrArg Prod.fst (Sum.inr.inj ht)
          subst j
          simpa [scan] using retained_data q.1 s (some q.2)
    | cons l ls ih =>
      intro absent row cover
      dsimp only
      by_cases hit : ∃ r : Fin 2, row = .inr (l,r)
      · obtain ⟨r,rfl⟩ := hit
        have outside : ∀ s : Fin 2, target ≠ .inr (l,s) := by
          intro s h; exact absent l s h (List.mem_cons_self)
        have target_diff : target ≠ .inr (l,r) := outside r
        have target_slot : ∀ (j : Fin k) (s : Fin 2),
            target = .inr (j,s) → j ≠ l := by
          intro j s h he; subst j; exact outside s h
        have ha0 : addresses k l 0 ∈ leafAddresses (family k (.inr (l,0))) := by
          simp [leaf_test, profile, column]
        have hb0 : addresses k l 1 ∉ leafAddresses (family k (.inr (l,0))) := by
          simp [leaf_test, profile, column]
        have ha1 : addresses k l 0 ∉ leafAddresses (family k (.inr (l,1))) := by
          simp [leaf_test, profile, column]
        cases target with
        | inl u =>
          fin_cases r <;>
            simp [scan, runPassiveProtocol, profile, column, extra,
              ha0, hb0, ha1, Finset.insert_sdiff_of_mem _ ha0, Finset.insert_sdiff_of_notMem _ hb0,
              Finset.insert_sdiff_of_notMem _ ha1]
        | inr p =>
          rcases p with ⟨j,s⟩
          have hlj : l ≠ j := (target_slot j s rfl).symm
          fin_cases r <;> fin_cases s <;>
            simp [scan, runPassiveProtocol, profile, column, extra, hlj, Ne.symm hlj,
              ha0, hb0, ha1, Finset.insert_sdiff_of_mem _ ha0, Finset.insert_sdiff_of_notMem _ hb0,
              Finset.insert_sdiff_of_notMem _ ha1]
      · have inactive : ∀ r : Fin 2, row ≠ .inr (l,r) := by simpa using hit
        have replies (q : Fin 4) (hq : q.val < 2) :
            leafLabel (family k row) (addresses k l q) = some true := by
          cases row with
          | inl u => fin_cases q <;> simp [profile, column] at hq ⊢
          | inr p =>
            rcases p with ⟨j,r⟩
            have hlj : l ≠ j := by intro h; subst j; exact inactive r rfl
            fin_cases q <;> simp [profile, hlj, column] at hq ⊢
        have ha := (leaf_test _ _).mpr (show leafLabel (family k row) (addresses k l 0) ≠ none by
          rw [replies 0 (by decide)]; decide)
        have hb := (leaf_test _ _).mpr (show leafLabel (family k row) (addresses k l 1) ≠ none by
          rw [replies 1 (by decide)]; decide)
        have rest_cover : ∀ (j : Fin k) (r : Fin 2), row = .inr (j,r) →
            j ∈ ls ∨ ∃ s : Fin 2, target = .inr (j,s) := by
          intro j r h
          have hj : j ≠ l := by intro he; subst j; exact inactive r h
          simpa [List.mem_cons, hj] using cover j r h
        have rest := ih (fun j r h => List.not_mem_of_not_mem_cons (absent j r h))
          row rest_cover
        simpa [scan, runPassiveProtocol, replies,
          Finset.insert_sdiff_of_mem _ ha, Finset.insert_sdiff_of_mem _ hb] using rest
  intro target
  let p := route k target
  have routes (row : Index k) :
      p.2 (runPassiveProtocol (fun q W => leafLabel W q) p.1 (family k row)) = some row ∧
      ((runPassiveProtocol (fun q W => leafLabel W q) p.1 (family k row)).map Sigma.fst).toFinset
        \ leafAddresses (family k row) = (extra k target row).toFinset := by
    apply scan_data
    · intro j r h; subst target; simp
    · intro j r h
      cases target with
      | inl u => exact Or.inl (by simp)
      | inr q =>
        by_cases hj : j = q.1
        · exact Or.inr ⟨q.2, by rw [hj]⟩
        · exact Or.inl (by simp [hj])
  let e : Index k ≃ Fin (Fintype.card (Index k)) := Fintype.equivFin (Index k)
  let F := family k ∘ e.symm
  let decode : CH → Option (Fin (Fintype.card (Index k))) := fun h => (p.2 h).map e
  obtain ⟨pi, hp, coarse, total, phase, mismatch, fallback, paid_rows⟩ :=
    ActualCoarseReadoutCompletion.completion_contract _ F
      (fun i => (family_structure k hk).2.1 (e.symm i) |>.2.1) p.1 decode
  refine ⟨pi, coarse, ?_⟩
  intro row
  have decoded : decode (runPassiveProtocol (fun q W => leafLabel W q) p.1 (F (e row))) =
      some (e row) := by simpa [decode, F] using congrArg (Option.map e) (routes row).1
  have billed := (paid_rows (e row) decoded).2
  have bill : paid (terminal pi (family k row)).1 =
      leafAddresses (family k row) ∪ (extra k target row).toFinset := by
    simp only [F, Function.comp_apply, e.symm_apply_apply] at billed
    rw [← Finset.sdiff_union_self_eq_union, (routes row).2, Finset.union_comm] at billed
    exact billed
  refine ⟨bill, ?_⟩
  have card_leaves := (family_structure k hk).2.1 row |>.2.2.2
  have separate : Disjoint (leafAddresses (family k row)) (extra k target row).toFinset := by
    rw [← (routes row).2]
    exact Finset.disjoint_sdiff
  change (paid (terminal pi (family k row)).1).card = _
  rw [bill, Finset.card_union_of_disjoint separate, card_leaves]
  by_cases same : target = row
  · subst target
    simp [extra]
  · have one : (extra k target row).toFinset.card = 1 := by
      unfold extra
      rw [if_neg same]
      cases row with
      | inl u => cases target with
        | inl v => exact False.elim (same (by congr))
        | inr p => rfl
      | inr p =>
        rcases p with ⟨j,r⟩
        dsimp only
        by_cases h : r.val = 1
        · rw [if_pos h]; rfl
        · rw [if_neg h]
          cases target with
          | inl u => rfl
          | inr q => dsimp only; split_ifs <;> rfl
    rw [one, if_neg same]
    omega

end D5.S3.Arith.FibonacciAtomic.Scale36ActualEndpointAcquisition
