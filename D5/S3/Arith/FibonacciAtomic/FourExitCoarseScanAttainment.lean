/- GID: D5/S3/Arith/FibonacciAtomic/FourExitCoarseScanAttainment
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/FourExitCoarseScanAttainment
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Three actual coarse scans and rational tail mixtures attain both cost orders. -/

import D5.S3.Arith.FibonacciAtomic.FourExitRawDomination
import D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutCompletion
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.FourExitCoarseScanAttainment

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition
open ActualImageSevenLeafSeparation (leafLabel leafAddresses)
open ActualCoarseReadoutHistory (CoarseObservable)
open FourExitRawEndpointSpectrum
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
  (PassiveProtocol runPassiveProtocol)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist)
open scoped BigOperators

local notation "Index" => fun k : Nat => Unit ⊕ (Fin k × Fin 4)
local notation "CH" => Hist (fun _ : Address => Option Bool)
local notation "Route" => fun k : Nat =>
  PassiveProtocol Address (fun _ => Option Bool) × (CH → Option (Index k))
local notation "Seed" => fun k : Nat => Fin k × Fin 3 × (Fin k → Fin 3)

/-- A route leaf selects a prototype or requests full acquisition. -/
def stopAt {k : Nat} (i : Option (Index k)) : Route k := (.stop, fun _ => i)

/-- A real address query and its three coarse continuations, with chronological decoding. -/
def ask {k : Nat} (q : Address) (nu alpha beta : Route k) : Route k :=
  (.query q (fun y => match y with
    | none => nu.1 | some true => alpha.1 | some false => beta.1),
   fun h => match h with
    | [] => none
    | a :: rest => match a.2 with
      | none => nu.2 rest | some true => alpha.2 rest | some false => beta.2 rest)

/-- The three slot rules use the literal address column of the four-exit family. -/
def scanSlot (k : Nat) (j : Fin k) (s : Fin 3) (next : Route k) : Route k :=
  let q := literal_addresses k j
  let out := fun r : Fin 4 => stopAt (some (.inr (j,r)))
  let bad := stopAt (k := k) none
  match s.val with
  | 0 => ask (q 0) (ask (q 4) (out 0) bad (out 1)) bad
      (ask (q 1) (out 2) bad (ask (q 2) (out 3) bad next))
  | 1 => ask (q 0) (ask (q 6) (out 1) bad (out 0)) bad
      (ask (q 1) (out 2) bad (ask (q 2) (out 3) bad next))
  | _ => ask (q 2) (ask (q 6) (out 3) bad (out 0)) bad
      (ask (q 0) (out 1) bad (ask (q 1) (out 2) bad next))

/-- The A, B, and C tails distinguish the retained five rows using actual requests. -/
def tailRoute (k : Nat) (j : Fin k) (s : Fin 3) : Route k :=
  let q := literal_addresses k j
  let out := fun r : Fin 4 => stopAt (some (.inr (j,r)))
  let base := stopAt (some (.inl ()))
  let bad := stopAt (k := k) none
  match s.val with
  | 0 => ask (q 7) (ask (q 4) (out 2) bad (out 1))
      (ask (q 8) (out 3) bad (ask (q 9) base bad (out 0))) bad
  | 1 => ask (q 0) (ask (q 6) (out 1) bad (out 0)) bad
      (ask (q 2) (out 3) bad (ask (q 3) base bad (out 2)))
  | _ => ask (q 2) (ask (q 5) (out 0) bad (out 3)) bad
      (ask (q 3) base bad (ask (q 4) (out 2) bad (out 1)))

/-- All scan kinds and the tail are fixed before execution. -/
def scanList (k : Nat) (j : Fin k) (s : Fin 3) (d : Fin k → Fin 3) :
    List (Fin k) → Route k
  | [] => tailRoute k j s
  | l :: rest => scanSlot k l (d l) (scanList k j s d rest)

/-- Exact nonleaf column indices for an exceptional row in a scanned slot. -/
def scanNonleaves (s : Fin 3) (r : Fin 4) : Finset (Fin 10) :=
  match s.val, r.val with
  | 0, 0 => {0,4} | 1, 1 => {0,6} | 2, 0 => {2} | 2, 3 => {2,6}
  | _, 0 => {0} | _, 1 => {0} | _, 2 => {1} | _, _ => {2}

/-- Exact nonleaf columns for the baseline and the four retained exceptional rows. -/
def tailNonleaves (s : Fin 3) (r : Option (Fin 4)) : Finset (Fin 10) :=
  match s.val, r with
  | 0, none => {9} | _, none => {3}
  | 0, some r => match r.val with | 0 => ∅ | 1 => {7} | 2 => {7,4} | _ => {8}
  | 1, some r => match r.val with | 0 => {0} | 1 => {0,6} | 2 => ∅ | _ => {2}
  | _, some r => match r.val with | 0 => {2,5} | 1 => ∅ | 2 => {4} | _ => {2}

/-- The real query paths on the four exceptional rows of a scanned slot. -/
def scanColumns (s : Fin 3) (r : Fin 4) : List (Fin 10) :=
  match s.val, r.val with
  | 2, 0 | 2, 3 => [2,6] | 2, 1 => [2,0] | 2, _ => [2,0,1]
  | 0, 0 | 0, 1 => [0,4] | 1, 0 | 1, 1 => [0,6]
  | _, 2 => [0,1] | _, _ => [0,1,2]

/-- The real query paths on the five retained rows. -/
def tailColumns (s : Fin 3) (r : Option (Fin 4)) : List (Fin 10) :=
  match s.val, r with
  | 0, none => [7,8,9]
  | 0, some r => match r.val with
    | 0 => [7,8,9] | 1 | 2 => [7,4] | _ => [7,8]
  | 1, none => [0,2,3]
  | 1, some r => match r.val with
    | 0 | 1 => [0,6] | 2 => [0,2,3] | _ => [0,2]
  | _, none => [2,3]
  | _, some r => match r.val with
    | 0 | 3 => [2,5] | _ => [2,3,4]

/-- The table of actual nonleaf addresses on each evaluation row. -/
def extraAddresses (k : Nat) (seed : Seed k) (i : Index k) : Finset Address :=
  match i with
  | .inl _ => (tailNonleaves seed.2.1 none).image (literal_addresses k seed.1)
  | .inr (l,r) => if l = seed.1 then
      (tailNonleaves seed.2.1 (some r)).image (literal_addresses k l)
    else (scanNonleaves (seed.2.2 l) r).image (literal_addresses k l)

/-- The rational tail weights, with the common k = 5 boundary assigned to the first row. -/
def tailWeight (k : Nat) (s : Fin 3) : ℚ :=
  if k = 1 then 1/3 else if k = 2 then
    ([11/24,5/24,1/3] : List ℚ).getD s.val 0
  else if k ≤ 5 then ([((k:ℚ)+3)/8,(5-(k:ℚ))/8,0] : List ℚ).getD s.val 0
  else if s = 0 then 1 else 0

/-- Independent scan weights; the unused scan at the retained slot is marginalized. -/
def scanWeight (k : Nat) (s : Fin 3) : ℚ :=
  if k = 1 then if s = 0 then 1 else 0
  else if k = 2 then ([3/8,3/8,1/4] : List ℚ).getD s.val 0
  else if k ≤ 5 then
    ([(3*(k:ℚ)+1)/(8*((k:ℚ)-1)),(3*(k:ℚ)-7)/(8*((k:ℚ)-1)),1/4] : List ℚ).getD s.val 0
  else
    ([((k:ℚ)+1)/(3*((k:ℚ)-1)),((k:ℚ)-2)/(3*((k:ℚ)-1)),
      ((k:ℚ)-2)/(3*((k:ℚ)-1))] : List ℚ).getD s.val 0

/-- A finite rational law: uniform retained slot and independent preselected choices. -/
def seedWeight (k : Nat) (seed : Seed k) : ℚ :=
  (tailWeight k seed.2.1 / k) * ∏ l : Fin k, scanWeight k (seed.2.2 l)

/-- The excess vector read from the exact nonleaf address table. -/
def rowExcess (k : Nat) (seed : Seed k) (i : Index k) : Nat :=
  match i with
  | .inl _ => 1
  | .inr (l,r) => if l = seed.1 then
      (match seed.2.1.val with
        | 0 => [0,1,2,1] | 1 => [1,2,0,1] | _ => [2,0,1,1]).getD r.val 0
    else 1 + if (r = 0 ∧ seed.2.2 l = 0) ∨ (r = 1 ∧ seed.2.2 l = 1) ∨
      (r = 3 ∧ seed.2.2 l = 2) then 1 else 0

/-- Every preselected scan-and-tail route completes with its exact actual address cost. -/
private theorem actual_routes (k : Nat) (hk : 1 ≤ k) :
    ∀ seed : Seed k, ∃ pi : Strategy,
      CoarseObservable pi.policy ∧
      (∀ i : Index k,
        paid (terminal pi (family k i)).1 = leafAddresses (family k i) ∪ extraAddresses k seed i ∧
        cost pi (family k i) = 8*k+16 + (extraAddresses k seed i).card) := by
  classical
  let col : Fin 10 → Fin 5 → Option Bool := fun q r =>
    (match q.val with
      | 0 => [some false,none,none,some false,some false]
      | 1 => [some false,none,none,none,some false]
      | 2 => [some false,none,some false,some false,none]
      | 3 => [none,none,some false,some false,none]
      | 4 => [none,none,some false,none,none]
      | 5 => [none,none,none,none,some false]
      | 6 => [none,some false,none,none,none]
      | 7 => [some true,some true,none,none,some true]
      | 8 => [some false,some false,none,some false,none]
      | _ => [none,some false,none,none,none]).getD r.val none
  have profile_base (l : Fin k) (q : Fin 10) :
      leafLabel (family k (.inl ())) (literal_addresses k l q) = col q 0 := by
    fin_cases q <;>
      simp only [literal_addresses,family,comb_slot_readout,comb_tail_readout,leafLabel,col] <;> rfl
  have profile_active (l : Fin k) (q : Fin 10) (r : Fin 4) :
      leafLabel (family k (.inr (l,r))) (literal_addresses k l q) = col q r.succ := by
    fin_cases q <;> fin_cases r <;>
      simp only [literal_addresses,family,comb_slot_readout,comb_tail_readout,
        leafLabel,col,if_pos rfl] <;> rfl
  have leaf_test (U : Source) (q : Address) :
      q ∈ leafAddresses U ↔ leafLabel U q ≠ none := by
    rw [(ActualImageSevenLeafSeparation.seven_leaf_separation.1 U).2 q]
    cases h : leafLabel U q <;> simp [h]
  have table_difference (l : Fin k) (qs : List (Fin 10)) (i : Index k) :
      (qs.map (literal_addresses k l)).toFinset \ leafAddresses (family k i) =
        ((qs.filter (fun q => leafLabel (family k i) (literal_addresses k l q) = none)).map
          (literal_addresses k l)).toFinset := by
    have map_finset (xs : List (Fin 10)) :
        (xs.map (literal_addresses k l)).toFinset = xs.toFinset.image (literal_addresses k l) := by
      simpa only [Multiset.map_coe, List.toFinset_coe] using
        Multiset.toFinset_map (literal_addresses k l) (xs : Multiset (Fin 10))
    rw [map_finset, Finset.sdiff_eq_filter, Finset.filter_image, map_finset,
      List.toFinset_filter]
    congr 1
    apply Finset.filter_congr
    intro q _
    simp only [leaf_test, not_not, decide_eq_true_eq]
  have scan_active (l : Fin k) (s : Fin 3) (next : Route k) (r : Fin 4) :
      let route := scanSlot k l s next
      let U := family k (.inr (l,r))
      let tr := runPassiveProtocol (fun q W => leafLabel W q) route.1 U
      tr = (scanColumns s r).map (fun q => ⟨literal_addresses k l q,
        leafLabel U (literal_addresses k l q)⟩) ∧
      route.2 tr = some (.inr (l,r)) ∧
      (tr.map Sigma.fst).toFinset \ leafAddresses U =
        (scanNonleaves s r).image (literal_addresses k l) := by
    dsimp only
    have trace : runPassiveProtocol (fun q W => leafLabel W q)
        (scanSlot k l s next).1 (family k (.inr (l,r))) =
        (scanColumns s r).map (fun q => ⟨literal_addresses k l q,
          leafLabel (family k (.inr (l,r))) (literal_addresses k l q)⟩) := by
      fin_cases s <;> fin_cases r <;>
        simp only [scanSlot, ask, stopAt, scanColumns, runPassiveProtocol, profile_base, profile_active, col, ne_self_iff_false, and_false, ite_false, OfNat.ofNat, Fin.val_ofNat, Fin.val_mk, Fin.val_succ, Fin.val_zero, Fin.val_one, Nat.reduceMod, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, List.map_cons, List.map_nil] <;> rfl
    refine ⟨trace, ?_, ?_⟩
    · rw [trace]
      fin_cases s <;> fin_cases r <;>
        simp only [scanSlot, ask, stopAt, scanColumns, profile_base, profile_active, col, ne_self_iff_false, and_false, ite_false, OfNat.ofNat, Fin.val_ofNat, Fin.val_mk, Fin.val_succ, Fin.val_zero, Fin.val_one, Nat.reduceMod, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, List.map_cons, List.map_nil] <;> rfl
    · rw [trace]
      simp only [List.map_map, Function.comp_def]
      rw [table_difference]
      fin_cases s <;> fin_cases r <;>
        simp only [scanColumns, scanNonleaves, profile_base, profile_active, col, ne_self_iff_false, and_false, ite_false,
          List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.toFinset_cons,
          List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.image_singleton,
          Fin.val_zero, Fin.val_one, OfNat.ofNat, Fin.val_ofNat, Fin.val_natCast, Nat.reduceMod, Fin.val_succ, List.getD,
          List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Option.some_ne_none, eq_self, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false] <;> rfl
  have tail_actual (l : Fin k) (s : Fin 3) (r : Option (Fin 4)) :
      let i : Index k := match r with | none => .inl () | some r => .inr (l,r)
      let route := tailRoute k l s
      let U := family k i
      let tr := runPassiveProtocol (fun q W => leafLabel W q) route.1 U
      tr = (tailColumns s r).map (fun q => ⟨literal_addresses k l q,
        leafLabel U (literal_addresses k l q)⟩) ∧ route.2 tr = some i ∧
      (tr.map Sigma.fst).toFinset \ leafAddresses U =
        (tailNonleaves s r).image (literal_addresses k l) := by
    dsimp only
    have trace : runPassiveProtocol (fun q W => leafLabel W q)
        (tailRoute k l s).1 (family k (match r with | none => .inl () | some r => .inr (l,r))) =
        (tailColumns s r).map (fun q => ⟨literal_addresses k l q,
          leafLabel (family k (match r with | none => .inl () | some r => .inr (l,r)))
            (literal_addresses k l q)⟩) := by
      cases r with
      | none => fin_cases s <;>
          simp only [tailRoute, ask, stopAt, tailColumns, runPassiveProtocol, profile_base, profile_active, col, ne_self_iff_false, and_false, ite_false, OfNat.ofNat, Fin.val_ofNat, Fin.val_mk, Fin.val_succ, Fin.val_zero, Fin.val_one, Nat.reduceMod, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, List.map_cons, List.map_nil] <;> rfl
      | some r => fin_cases s <;> fin_cases r <;>
          simp only [tailRoute, ask, stopAt, tailColumns, runPassiveProtocol, profile_base, profile_active, col, ne_self_iff_false, and_false, ite_false, OfNat.ofNat, Fin.val_ofNat, Fin.val_mk, Fin.val_succ, Fin.val_zero, Fin.val_one, Nat.reduceMod, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, List.map_cons, List.map_nil] <;> rfl
    refine ⟨trace, ?_, ?_⟩
    · rw [trace]
      cases r with
      | none => fin_cases s <;> simp only [tailRoute, ask, stopAt, tailColumns, profile_base, profile_active, col, ne_self_iff_false, and_false, ite_false, OfNat.ofNat, Fin.val_ofNat, Fin.val_mk, Fin.val_succ, Fin.val_zero, Fin.val_one, Nat.reduceMod, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, List.map_cons, List.map_nil] <;> rfl
      | some r => fin_cases s <;> fin_cases r <;>
          simp only [tailRoute, ask, stopAt, tailColumns, profile_base, profile_active, col, ne_self_iff_false, and_false, ite_false, OfNat.ofNat, Fin.val_ofNat, Fin.val_mk, Fin.val_succ, Fin.val_zero, Fin.val_one, Nat.reduceMod, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, List.map_cons, List.map_nil] <;> rfl
    · rw [trace]
      simp only [List.map_map, Function.comp_def]
      rw [table_difference]
      cases r with
      | none => fin_cases s <;> simp only [tailColumns, tailNonleaves, profile_base, profile_active, col, ne_self_iff_false, and_false, ite_false,
          List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.toFinset_cons,
          List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.image_singleton,
          Fin.val_zero, Fin.val_one, OfNat.ofNat, Fin.val_ofNat, Fin.val_natCast, Nat.reduceMod, Fin.val_succ, List.getD,
          List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Option.some_ne_none, eq_self, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false] <;> rfl
      | some r => fin_cases s <;> fin_cases r <;>
          simp only [tailColumns, tailNonleaves, profile_base, profile_active, col, ne_self_iff_false, and_false, ite_false,
          List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.toFinset_cons,
          List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.image_singleton,
          Fin.val_zero, Fin.val_one, OfNat.ofNat, Fin.val_ofNat, Fin.val_natCast, Nat.reduceMod, Fin.val_succ, List.getD,
          List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Option.some_ne_none, eq_self, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false] <;> rfl
  have scan_inactive (l : Fin k) (s : Fin 3) (next : Route k) (i : Index k)
      (inactive : ∀ r, i ≠ .inr (l,r)) :
      let route := scanSlot k l s next
      let U := family k i
      let tr := runPassiveProtocol (fun q W => leafLabel W q) route.1 U
      route.2 tr = next.2 (runPassiveProtocol (fun q W => leafLabel W q) next.1 U) ∧
      (tr.map Sigma.fst).toFinset \ leafAddresses U =
        ((runPassiveProtocol (fun q W => leafLabel W q) next.1 U).map Sigma.fst).toFinset
          \ leafAddresses U := by
    dsimp only
    have replies (q : Fin 10) (hq : q.val < 3) :
        leafLabel (family k i) (literal_addresses k l q) = some false := by
      cases i with
      | inl u =>
        rw [profile_base]
        fin_cases q <;> simp only [col,Fin.val_mk] at hq ⊢ <;> first | rfl | omega
      | inr p =>
        rcases p with ⟨j,r⟩
        have different : l ≠ j := by
          intro h; subst j; exact inactive r rfl
        fin_cases q <;> simp only [Fin.val_mk] at hq
        all_goals first | omega |
          (simp only [literal_addresses,family,comb_slot_readout,if_neg different,leafLabel]; rfl)
    have leaf0 := (leaf_test _ _).mpr (by rw [replies 0 (by decide)]; decide)
    have leaf1 := (leaf_test _ _).mpr (by rw [replies 1 (by decide)]; decide)
    have leaf2 := (leaf_test _ _).mpr (by rw [replies 2 (by decide)]; decide)
    fin_cases s <;>
      simp [scanSlot, ask, stopAt, runPassiveProtocol, replies,
        Finset.insert_sdiff_of_mem _ leaf0, Finset.insert_sdiff_of_mem _ leaf1,
        Finset.insert_sdiff_of_mem _ leaf2]
  have route_actual (j : Fin k) (s : Fin 3) (d : Fin k → Fin 3) :
      ∀ (ls : List (Fin k)), j ∉ ls → ∀ (i : Index k),
        (Sum.elim (fun _ : Unit => True) (fun p : Fin k × Fin 4 => p.1 = j ∨ p.1 ∈ ls) i) →
        let route := scanList k j s d ls
        let U := family k i
        let tr := runPassiveProtocol (fun q W => leafLabel W q) route.1 U
        route.2 tr = some i ∧ (tr.map Sigma.fst).toFinset \ leafAddresses U =
          extraAddresses k (j,s,d) i := by
    intro ls
    induction ls with
    | nil =>
      intro _ i cover
      cases i with
      | inl u => simpa only [scanList,extraAddresses] using (tail_actual j s none).2
      | inr p =>
        rcases p with ⟨l,r⟩
        have eq : l = j := by simpa using cover
        subst l
        simpa only [scanList,extraAddresses,if_pos rfl,ite_true] using (tail_actual j s (some r)).2
    | cons l ls ih =>
      intro absent i cover
      have jl : j ≠ l := List.ne_of_not_mem_cons absent
      have jr : j ∉ ls := List.not_mem_of_not_mem_cons absent
      by_cases active : ∃ r, i = .inr (l,r)
      · obtain ⟨r,rfl⟩ := active
        simpa only [scanList,extraAddresses,if_neg (Ne.symm jl),ite_false] using
          (scan_active l (d l) (scanList k j s d ls) r).2
      · have inactive : ∀ r, i ≠ .inr (l,r) := by simpa using active
        have rest : (Sum.elim (fun _ : Unit => True) (fun p : Fin k × Fin 4 => p.1 = j ∨ p.1 ∈ ls) i) := by
          cases i with
          | inl u => trivial
          | inr p =>
            rcases p with ⟨t,r⟩
            have tl : t ≠ l := by intro h; subst t; exact inactive r rfl
            simpa [List.mem_cons,tl] using cover
        have next := ih jr i rest
        have same := scan_inactive l (d l) (scanList k j s d ls) i inactive
        exact ⟨same.1.trans next.1, same.2.trans next.2⟩
  have attained (seed : Seed k) : ∃ pi : Strategy,
      CoarseObservable pi.policy ∧
      (∀ i : Index k,
        paid (terminal pi (family k i)).1 = leafAddresses (family k i) ∪ extraAddresses k seed i ∧
        cost pi (family k i) = 8*k+16 + (extraAddresses k seed i).card) := by
    let ls := (List.finRange k).filter (fun l => l ≠ seed.1)
    let route := scanList k seed.1 seed.2.1 seed.2.2 ls
    have facts (i : Index k) :
        route.2 (runPassiveProtocol (fun q W => leafLabel W q) route.1 (family k i)) = some i ∧
        ((runPassiveProtocol (fun q W => leafLabel W q) route.1 (family k i)).map Sigma.fst).toFinset
          \ leafAddresses (family k i) = extraAddresses k seed i := by
      apply route_actual seed.1 seed.2.1 seed.2.2 ls
      · simp [ls]
      · cases i with
        | inl u => trivial
        | inr p =>
            by_cases h : p.1 = seed.1
            · exact Or.inl h
            · exact Or.inr (by simp [ls,h])
    let m := Fintype.card (Index k)
    let e : Fin m ≃ Index k := (Fintype.equivFin (Index k)).symm
    let F : Fin m → Source := fun i => family k (e i)
    let decode : CH → Option (Fin m) := fun h => (route.2 h).map e.symm
    obtain ⟨pi,_,observable,_,_,_,_,selected⟩ :=
      ActualCoarseReadoutCompletion.completion_contract m F
        (fun i => (FourExitRawDomination.result k hk).1 (e i) |>.1) route.1 decode
    refine ⟨pi,observable,?_⟩
    intro i
    have good : decode (runPassiveProtocol (fun q W => leafLabel W q) route.1 (F (e.symm i))) =
        some (e.symm i) := by simp [decode,F,(facts i).1]
    have paid_eq := (selected (e.symm i) good).2
    simp only [F,Equiv.apply_symm_apply] at paid_eq
    rw [← Finset.sdiff_union_self_eq_union, (facts i).2, Finset.union_comm] at paid_eq
    have disjoint : Disjoint (leafAddresses (family k i)) (extraAddresses k seed i) := by
      rw [← (facts i).2]
      exact Finset.disjoint_sdiff
    refine ⟨paid_eq,?_⟩
    change (paid (terminal pi (family k i)).1).card = _
    rw [paid_eq,Finset.card_union_of_disjoint disjoint]
    have leaf_count := (ActualImageSevenLeafSeparation.seven_leaf_separation.1 (family k i)).1
    rw [leaf_count,(FourExitRawDomination.result k hk).1 i |>.2.1]
  exact attained

/-- All parameters are chosen before the input. Costs refer to actual requested addresses. -/
example (k : Nat) (hk : 1 ≤ k) :
    ∃ pi : Seed k → Strategy,
      (∀ seed, 0 ≤ seedWeight k seed) ∧ (∑ seed : Seed k, seedWeight k seed) = 1 ∧
      (∀ seed,
        CoarseObservable (pi seed).policy ∧
        (∀ i : Index k,
          paid (terminal (pi seed) (family k i)).1 =
            leafAddresses (family k i) ∪ extraAddresses k seed i ∧
          cost (pi seed) (family k i) = 8*k+16 + (extraAddresses k seed i).card) ∧
        cost (pi seed) (family k (.inl ())) = 8*k+17 ∧
        (Finset.univ.sup (fun i : Index k => cost (pi seed) (family k i))) = 8*k+18 ∧
        (∑ i : Index k, (extraAddresses k seed i).card) = 5*k) ∧
      (Finset.univ.sup' (Finset.univ_nonempty) (fun i : Index k =>
        ∑ seed : Seed k, seedWeight k seed * (cost (pi seed) (family k i) : ℚ))) =
          (8*k+16 : Nat) + max ((5*(k:ℚ)-1)/(4*k)) ((4*(k:ℚ)-2)/(3*k)) ∧
      (∑ seed : Seed k, seedWeight k seed *
        ((Finset.univ.sup (fun i : Index k => cost (pi seed) (family k i)) : Nat) : ℚ)) =
          (8*k+18 : Nat) := by
  classical
  have table_sizes (seed : Seed k) (i : Index k) :
      (extraAddresses k seed i).card = rowExcess k seed i := by
    have different (l : Fin k) (q t : Fin 10)
        (h : readout (literal_addresses k l q) (family k (.inl ())) ≠
          readout (literal_addresses k l t) (family k (.inl ()))) :
        literal_addresses k l q ≠ literal_addresses k l t := by
      exact ne_of_apply_ne (fun a => readout a (family k (.inl ()))) h
    have d04 (l : Fin k) : literal_addresses k l 0 ≠ literal_addresses k l 4 :=
      different l 0 4 (by simp only [literal_addresses,Fin.val_zero,Fin.val_one,Fin.val_ofNat,OfNat.ofNat,Nat.reduceMod,family,comb_slot_readout]; decide)
    have d06 (l : Fin k) : literal_addresses k l 0 ≠ literal_addresses k l 6 :=
      different l 0 6 (by simp only [literal_addresses,Fin.val_zero,Fin.val_one,Fin.val_ofNat,OfNat.ofNat,Nat.reduceMod,family,comb_slot_readout]; decide)
    have d26 (l : Fin k) : literal_addresses k l 2 ≠ literal_addresses k l 6 :=
      different l 2 6 (by simp only [literal_addresses,Fin.val_zero,Fin.val_one,Fin.val_ofNat,OfNat.ofNat,Nat.reduceMod,family,comb_slot_readout]; decide)
    have d74 (l : Fin k) : literal_addresses k l 7 ≠ literal_addresses k l 4 :=
      different l 7 4 (by simp only [literal_addresses,Fin.val_zero,Fin.val_one,Fin.val_ofNat,OfNat.ofNat,Nat.reduceMod,family,comb_slot_readout,comb_tail_readout]; decide)
    have d25 (l : Fin k) : literal_addresses k l 2 ≠ literal_addresses k l 5 :=
      different l 2 5 (by simp only [literal_addresses,Fin.val_zero,Fin.val_one,Fin.val_ofNat,OfNat.ofNat,Nat.reduceMod,family,comb_slot_readout]; decide)
    rcases seed with ⟨j,s,d⟩
    cases i with
    | inl u =>
      fin_cases s <;> dsimp only [extraAddresses,tailNonleaves,rowExcess]
      all_goals simp only [Finset.image_singleton,Finset.card_singleton]
    | inr p =>
      rcases p with ⟨l,r⟩
      by_cases same : l = j
      · subst l
        fin_cases s <;> fin_cases r <;>
          simp only [extraAddresses,if_pos rfl]
        all_goals dsimp only [tailNonleaves,rowExcess]
        all_goals simp only [if_pos rfl,Finset.image_insert,Finset.image_singleton,
          Finset.image_empty,Finset.card_empty,Finset.card_singleton]
        all_goals first | rfl | exact Finset.card_pair (d06 _) |
          exact Finset.card_pair (d74 _) | exact Finset.card_pair (d25 _)
      · cases ds : d l using Fin.cases with
        | zero =>
          fin_cases r <;>
            simp only [extraAddresses,scanNonleaves,rowExcess,same,ds,ite_true,ite_false,
              Finset.image_insert,Finset.image_empty,Finset.image_singleton,
              Finset.card_empty,Finset.card_singleton,Fin.val_zero,Fin.val_one,
              OfNat.ofNat,Fin.val_ofNat,Fin.val_natCast,Nat.reduceMod,Fin.val_succ,
              List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
          all_goals first | rfl | exact Finset.card_pair (d04 _)
        | succ t =>
          fin_cases t <;> fin_cases r <;>
            simp only [extraAddresses,scanNonleaves,rowExcess,same,ds,ite_true,ite_false,
              Finset.image_insert,Finset.image_empty,Finset.image_singleton,
              Finset.card_empty,Finset.card_singleton,Fin.val_zero,Fin.val_one,
              OfNat.ofNat,Fin.val_ofNat,Fin.val_natCast,Nat.reduceMod,Fin.val_succ,
              List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
          all_goals first | rfl | exact Finset.card_pair (d06 _) | exact Finset.card_pair (d26 _)
  have normalized :
      (∑ s : Fin 3, tailWeight k s) = 1 ∧
      (∑ s : Fin 3, scanWeight k s) = 1 ∧
      ∀ s : Fin 3, 0 ≤ tailWeight k s ∧ 0 ≤ scanWeight k s := by
    by_cases one : k = 1
    · subst k; decide +kernel
    by_cases two : k = 2
    · subst k; decide +kernel
    have three : (3:ℚ) ≤ k := by exact_mod_cast (show 3 ≤ k by omega)
    have den : (k:ℚ)-1 ≠ 0 := by linarith
    by_cases small : k ≤ 5
    · have smallq : (k:ℚ) ≤ 5 := by exact_mod_cast small
      refine ⟨?_,?_,?_⟩
      · simp [tailWeight,one,two,small,Fin.sum_univ_succ]; ring
      · simp [scanWeight,one,two,small,Fin.sum_univ_succ]
        field_simp [den] <;> ring
      · intro s; fin_cases s <;> simp [tailWeight,scanWeight,one,two,small]
        all_goals constructor <;> apply div_nonneg <;> linarith
    · refine ⟨?_,?_,?_⟩
      · simp [tailWeight,one,two,small,Fin.sum_univ_succ]
      · simp [scanWeight,one,two,small,Fin.sum_univ_succ]
        field_simp [den] <;> ring
      · intro s; fin_cases s <;> simp [tailWeight,scanWeight,one,two,small]
        all_goals apply div_nonneg <;> linarith
  have scan_total : (∑ d : Fin k → Fin 3, ∏ l : Fin k, scanWeight k (d l)) = 1 := by
    rw [← Fintype.prod_sum (fun (_ : Fin k) (s : Fin 3) => scanWeight k s)]
    simp only [normalized.2.1, Finset.prod_const_one]
  have scan_mean (l : Fin k) (g : Fin 3 → ℚ) :
      (∑ d : Fin k → Fin 3, (∏ t : Fin k, scanWeight k (d t)) * g (d l)) =
        ∑ s : Fin 3, scanWeight k s * g s := by
    calc
      _ = ∑ d : Fin k → Fin 3, ∏ t : Fin k,
          scanWeight k (d t) * (if t = l then g (d t) else 1) := by
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq' l (fun t => g (d t))]
      _ = ∏ t : Fin k, ∑ s : Fin 3,
          scanWeight k s * (if t = l then g s else 1) := (Fintype.prod_sum (fun (t : Fin k) (s : Fin 3) =>
        scanWeight k s * (if t = l then g s else 1))).symm
      _ = ∏ t : Fin k, if t = l then (∑ s : Fin 3, scanWeight k s * g s) else 1 := by
        apply Finset.prod_congr rfl
        intro t _
        by_cases eq : t = l
        · simp only [if_pos eq]
        · simp only [if_neg eq,mul_one,normalized.2.1]
      _ = _ := Fintype.prod_ite_eq' l (fun _ => ∑ s : Fin 3, scanWeight k s * g s)
  have law_total : (∑ seed : Seed k, seedWeight k seed) = 1 := by
    have nonzero : (k:ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    simp only [seedWeight,Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum,scan_total,mul_one]
    simp [← Finset.sum_div,normalized.1,nonzero]
  have law_nonnegative (seed : Seed k) : 0 ≤ seedWeight k seed := by
    apply mul_nonneg
    · exact div_nonneg (normalized.2.2 seed.2.1).1 (Nat.cast_nonneg k)
    · exact Finset.prod_nonneg (fun l _ => (normalized.2.2 (seed.2.2 l)).2)
  let tailE : Fin 3 → Fin 4 → ℚ := fun s r =>
    ((match s.val with | 0 => [0,1,2,1] | 1 => [1,2,0,1] | _ => [2,0,1,1]).getD r.val 0 : Nat)
  let scanE : Fin 3 → Fin 4 → ℚ := fun s r =>
    (1 + if (r = 0 ∧ s = 0) ∨ (r = 1 ∧ s = 1) ∨ (r = 3 ∧ s = 2) then 1 else 0 : Nat)
  let T : Fin 4 → ℚ := fun r => ∑ s : Fin 3, tailWeight k s * tailE s r
  let S : Fin 4 → ℚ := fun r => ∑ s : Fin 3, scanWeight k s * scanE s r
  have average_row (l : Fin k) (r : Fin 4) :
      (∑ seed : Seed k, seedWeight k seed * (rowExcess k seed (.inr (l,r)) : ℚ)) =
        (T r + ((k:ℚ)-1)*S r)/k := by
    have cast_row (j : Fin k) (s : Fin 3) (d : Fin k → Fin 3) :
        (rowExcess k (j,s,d) (.inr (l,r)) : ℚ) =
          if l = j then tailE s r else scanE (d l) r := by
      by_cases same : l = j <;> simp only [rowExcess,same,ite_true,ite_false] <;> rfl
    have inner (j : Fin k) :
        (∑ s : Fin 3, ∑ d : Fin k → Fin 3,
          seedWeight k (j,s,d) * (rowExcess k (j,s,d) (.inr (l,r)) : ℚ)) =
          if j = l then T r/k else S r/k := by
      simp only [seedWeight,cast_row]
      by_cases same : j = l
      · subst j
        simp only [ite_true]
        have rearrange (s : Fin 3) (d : Fin k → Fin 3) :
            (tailWeight k s/k * ∏ t : Fin k, scanWeight k (d t)) * tailE s r =
              (tailWeight k s * tailE s r / k) * ∏ t : Fin k, scanWeight k (d t) := by ring
        simp_rw [rearrange,← Finset.mul_sum,scan_total,mul_one]
        rw [← Finset.sum_div]
      · have other : l ≠ j := Ne.symm same
        simp only [other,same,ite_false]
        have rearrange (s : Fin 3) (d : Fin k → Fin 3) :
            (tailWeight k s/k * ∏ t : Fin k, scanWeight k (d t)) * scanE (d l) r =
              (tailWeight k s/k) * ((∏ t : Fin k, scanWeight k (d t)) * scanE (d l) r) := by ring
        simp_rw [rearrange,← Finset.mul_sum,scan_mean l (fun s => scanE s r)]
        dsimp only [S]
        rw [← Finset.sum_mul,← Finset.sum_div,normalized.1]
        ring
    simp only [Fintype.sum_prod_type]
    simp_rw [inner]
    rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin k)) _ (Finset.mem_univ l)]
    have others (j : Fin k) (hj : j ∈ (Finset.univ : Finset (Fin k)).erase l) :
        (if j = l then T r/k else S r/k) = S r/k := by
      simp [(Finset.mem_erase.mp hj).1]
    rw [Finset.sum_congr rfl others]
    simp only [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ l),
      Finset.card_univ,Fintype.card_fin,ite_true,nsmul_eq_mul]
    rw [Nat.cast_sub hk]
    push_cast
    ring
  have numerical_row (r : Fin 4) :
      (T r + ((k:ℚ)-1)*S r)/k =
        if k ≤ 5 then 1+((k:ℚ)-1)/(4*k)
        else if r = 2 then 1+1/(k:ℚ) else 1+((k:ℚ)-2)/(3*k) := by
    by_cases one : k = 1
    · subst k; fin_cases r <;> decide +kernel
    by_cases two : k = 2
    · subst k; fin_cases r <;> decide +kernel
    have three : (3:ℚ) ≤ k := by exact_mod_cast (show 3 ≤ k by omega)
    have den : (k:ℚ)-1 ≠ 0 := by linarith
    have nonzero : (k:ℚ) ≠ 0 := by linarith
    by_cases small : k ≤ 5
    · fin_cases r <;> simp [T,S,tailE,scanE,tailWeight,scanWeight,one,two,small,
        Fin.sum_univ_succ,Fin.ext_iff,-Fin.val_eq_zero_iff]
      all_goals field_simp [den,nonzero] <;> ring
    · fin_cases r <;> simp [T,S,tailE,scanE,tailWeight,scanWeight,one,two,small,
        Fin.sum_univ_succ,Fin.ext_iff,-Fin.val_eq_zero_iff]
      all_goals field_simp [den,nonzero] <;> ring
  have average_base :
      (∑ seed : Seed k, seedWeight k seed * (rowExcess k seed (.inl ()) : ℚ)) = 1 := by
    simpa [rowExcess] using law_total
  let target : ℚ := max ((5*(k:ℚ)-1)/(4*k)) ((4*(k:ℚ)-2)/(3*k))
  have positive : (0:ℚ) < k := by exact_mod_cast (show 0 < k by omega)
  have target_value : target = if k ≤ 5 then 1+((k:ℚ)-1)/(4*k)
      else 1+((k:ℚ)-2)/(3*k) := by
    dsimp only [target]
    by_cases small : k ≤ 5
    · have smallq : (k:ℚ) ≤ 5 := by exact_mod_cast small
      rw [if_pos small,max_eq_left]
      · field_simp [positive.ne']; ring
      · apply (div_le_div_iff₀ (by positivity : (0:ℚ)<3*k) (by positivity : (0:ℚ)<4*k)).mpr
        nlinarith
    · have largeq : (5:ℚ) < k := by exact_mod_cast (show 5 < k by omega)
      rw [if_neg small,max_eq_right]
      · field_simp [positive.ne']; ring
      · apply (div_le_div_iff₀ (by positivity : (0:ℚ)<4*k) (by positivity : (0:ℚ)<3*k)).mpr
        nlinarith
  have target_at_least_one : 1 ≤ target := by
    rw [target_value]
    split_ifs with small
    · have one : (1:ℚ) ≤ k := by exact_mod_cast hk
      have nonneg : 0 ≤ ((k:ℚ)-1)/(4*k) := div_nonneg (by linarith) (by positivity)
      linarith
    · have large : (5:ℚ) < k := by exact_mod_cast (show 5 < k by omega)
      have nonneg : 0 ≤ ((k:ℚ)-2)/(3*k) := div_nonneg (by linarith) (by positivity)
      linarith
  have average_bound (i : Index k) :
      (∑ seed : Seed k, seedWeight k seed * (rowExcess k seed i : ℚ)) ≤ target := by
    cases i with
    | inl u => simpa [average_base] using target_at_least_one
    | inr p =>
      rw [average_row,numerical_row,target_value]
      by_cases small : k ≤ 5
      · simp [small]
      · simp only [small,ite_false]
        split_ifs
        · have large : (5:ℚ) < k := by exact_mod_cast (show 5 < k by omega)
          have fraction : 1/(k:ℚ) ≤ ((k:ℚ)-2)/(3*k) := by
            apply (div_le_div_iff₀ positive (by positivity : (0:ℚ)<3*k)).mpr
            nlinarith
          linarith
        · rfl
  have average_top (l : Fin k) :
      (∑ seed : Seed k, seedWeight k seed * (rowExcess k seed (.inr (l,0)) : ℚ)) = target := by
    rw [average_row,numerical_row,target_value]
    simp only [if_neg (by decide : (0 : Fin 4) ≠ 2)]
  have row_limits (seed : Seed k) :
      (∀ i : Index k, rowExcess k seed i ≤ 2) ∧
      ∃ i : Index k, rowExcess k seed i = 2 := by
    rcases seed with ⟨j,s,d⟩
    constructor
    · intro i
      cases i with
      | inl u => simp [rowExcess]
      | inr p =>
        rcases p with ⟨l,r⟩
        by_cases eq : l = j
        · fin_cases s <;> fin_cases r <;> simp [rowExcess,eq]
        · simp only [rowExcess,eq,ite_false]
          split_ifs <;> omega
    · fin_cases s
      · exact ⟨.inr (j,2),by simp [rowExcess]⟩
      · exact ⟨.inr (j,1),by simp [rowExcess]⟩
      · exact ⟨.inr (j,0),by simp [rowExcess]⟩
  have row_total (seed : Seed k) : (∑ i : Index k, rowExcess k seed i) = 5*k := by
    rcases seed with ⟨j,s,d⟩
    have retained : (∑ r : Fin 4, rowExcess k (j,s,d) (.inr (j,r))) = 4 := by
      fin_cases s <;> simp only [rowExcess,if_pos rfl,ite_true] <;> decide
    have scanned (l : Fin k) (different : l ≠ j) :
        (∑ r : Fin 4, rowExcess k (j,s,d) (.inr (l,r))) = 5 := by
      cases ds : d l using Fin.cases with
      | zero => simp only [rowExcess,if_neg different,ds,ite_false] <;> decide
      | succ t => fin_cases t <;> simp only [rowExcess,if_neg different,ds,ite_false] <;> decide
    rw [Fintype.sum_sum_type]
    simp only [Fintype.sum_unique,Fintype.sum_prod_type]
    change 1 + (∑ l : Fin k, ∑ r : Fin 4, rowExcess k (j,s,d) (.inr (l,r))) = _
    rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin k)) _ (Finset.mem_univ j),retained]
    have others (l : Fin k) (hl : l ∈ (Finset.univ : Finset (Fin k)).erase j) :
        (∑ r : Fin 4, rowExcess k (j,s,d) (.inr (l,r))) = 5 :=
      scanned l (Finset.mem_erase.mp hl).1
    rw [Finset.sum_congr rfl others]
    simp only [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    change 1 + ((k-1)*5+4) = 5*k
    omega
  choose pi hpi using actual_routes k hk
  have costs (seed : Seed k) (i : Index k) :
      cost (pi seed) (family k i) = 8*k+16 + rowExcess k seed i := by
    rw [(hpi seed).2 i |>.2,table_sizes]
  have maxima (seed : Seed k) :
      (Finset.univ.sup (fun i : Index k => cost (pi seed) (family k i))) = 8*k+18 := by
    apply le_antisymm
    · apply Finset.sup_le
      intro i _
      rw [costs]
      have bound := (row_limits seed).1 i
      omega
    · obtain ⟨i,hi⟩ := (row_limits seed).2
      apply Finset.le_sup_of_le (Finset.mem_univ i)
      rw [costs,hi]
  have mean_cost (i : Index k) :
      (∑ seed : Seed k, seedWeight k seed * (cost (pi seed) (family k i) : ℚ)) =
        (8*k+16 : Nat) + ∑ seed : Seed k, seedWeight k seed * (rowExcess k seed i : ℚ) := by
    calc
      _ = ∑ seed : Seed k, (seedWeight k seed * ((8*k+16 : Nat) : ℚ) +
          seedWeight k seed * (rowExcess k seed i : ℚ)) := by
        apply Finset.sum_congr rfl
        intro seed _
        rw [costs,Nat.cast_add,mul_add]
      _ = _ := by rw [Finset.sum_add_distrib,← Finset.sum_mul,law_total,one_mul]
  refine ⟨pi,law_nonnegative,law_total,?_,?_,?_⟩
  · intro seed
    refine ⟨(hpi seed).1,(hpi seed).2,?_,maxima seed,?_⟩
    · rw [costs]
      rfl
    · simp_rw [table_sizes]
      exact row_total seed
  · apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      rw [mean_cost]
      exact add_le_add_left (average_bound i) _
    · let l : Fin k := ⟨0,by omega⟩
      apply Finset.le_sup'_of_le (fun i : Index k =>
        ∑ seed : Seed k, seedWeight k seed * (cost (pi seed) (family k i) : ℚ))
        (Finset.mem_univ (.inr (l,0)))
      rw [mean_cost,average_top]
  · simp_rw [maxima]
    rw [← Finset.sum_mul,law_total,one_mul]



end D5.S3.Arith.FibonacciAtomic.FourExitCoarseScanAttainment
