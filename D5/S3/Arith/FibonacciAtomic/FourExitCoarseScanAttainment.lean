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
  have profile (l : Fin k) (q : Fin 10) (i : Index k) :
      leafLabel (family k i) (literal_addresses k l q) =
        col q (match i with
          | .inl _ => 0
          | .inr (j,r) => if q.val < 7 ∧ l ≠ j then 0 else r.succ) := by
    cases i with
    | inl u =>
      fin_cases q <;>
        simp only [literal_addresses, family, comb_slot_readout, comb_tail_readout,
          leafLabel, col] <;> rfl
    | inr p =>
      rcases p with ⟨j,r⟩
      by_cases h : l = j
      · subst j
        fin_cases q <;> fin_cases r <;>
          simp only [literal_addresses, family, comb_slot_readout, comb_tail_readout,
            leafLabel, col, ite_true, ne_self_iff_false, and_false, ite_false, Fin.val_natCast, Fin.val_succ,
          List.getD, Nat.reduceMod, List.map_cons, List.map_nil] <;> rfl
      · fin_cases q <;> fin_cases r <;>
          simp [literal_addresses, family, comb_slot_readout, comb_tail_readout,
            leafLabel, col, h] <;> rfl
  have columns_different (l : Fin k) (q t : Fin 10)
      (different : col q 0 ≠ col t 0) : literal_addresses k l q ≠ literal_addresses k l t := by
    intro same
    apply different
    simpa only [profile] using congrArg (leafLabel (family k (.inl ()))) same
  have leaf_test (U : Source) (q : Address) :
      q ∈ leafAddresses U ↔ leafLabel U q ≠ none := by
    rw [(ActualImageSevenLeafSeparation.seven_leaf_separation.1 U).2 q]
    cases h : leafLabel U q <;> simp [h]
  have table_difference (l : Fin k) (qs : List (Fin 10)) (i : Index k) :
      (qs.map (literal_addresses k l)).toFinset \ leafAddresses (family k i) =
        ((qs.filter (fun q => leafLabel (family k i) (literal_addresses k l q) = none)).map
          (literal_addresses k l)).toFinset := by
    ext a
    simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_map, List.mem_filter,
      decide_eq_true_eq, leaf_test, not_not]
    constructor
    · rintro ⟨⟨q,hq,rfl⟩,hn⟩
      exact ⟨q,⟨hq,hn⟩,rfl⟩
    · rintro ⟨q,⟨hq,hn⟩,rfl⟩
      exact ⟨⟨q,hq,rfl⟩,hn⟩
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
        simp only [scanSlot, ask, stopAt, scanColumns, runPassiveProtocol, profile, col,
          ne_self_iff_false, and_false, ite_false, Fin.val_natCast, Fin.val_succ,
          List.getD, Nat.reduceMod, List.map_cons, List.map_nil] <;> rfl
    refine ⟨trace, ?_, ?_⟩
    · rw [trace]
      fin_cases s <;> fin_cases r <;>
        simp only [scanSlot, ask, stopAt, scanColumns, profile, col,
          ne_self_iff_false, and_false, ite_false, Fin.val_natCast, Fin.val_succ,
          List.getD, Nat.reduceMod, List.map_cons, List.map_nil] <;> rfl
    · rw [trace]
      simp only [List.map_map, Function.comp_def]
      rw [table_difference]
      fin_cases s <;> fin_cases r <;>
        simp [scanColumns, scanNonleaves, profile, col]
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
          simp only [tailRoute, ask, stopAt, tailColumns, runPassiveProtocol, profile, col,
            ne_self_iff_false, and_false, ite_false, Fin.val_natCast, Fin.val_succ,
          List.getD, Nat.reduceMod, List.map_cons, List.map_nil] <;> rfl
      | some r => fin_cases s <;> fin_cases r <;>
          simp only [tailRoute, ask, stopAt, tailColumns, runPassiveProtocol, profile, col,
            ne_self_iff_false, and_false, ite_false, Fin.val_natCast, Fin.val_succ,
          List.getD, Nat.reduceMod, List.map_cons, List.map_nil] <;> rfl
    refine ⟨trace, ?_, ?_⟩
    · rw [trace]
      cases r with
      | none => fin_cases s <;> simp only [tailRoute, ask, stopAt, tailColumns, profile, col,
            ne_self_iff_false, and_false, ite_false, Fin.val_natCast, Fin.val_succ,
          List.getD, Nat.reduceMod, List.map_cons, List.map_nil] <;> rfl
      | some r => fin_cases s <;> fin_cases r <;>
          simp only [tailRoute, ask, stopAt, tailColumns, profile, col,
            ne_self_iff_false, and_false, ite_false, Fin.val_natCast, Fin.val_succ,
          List.getD, Nat.reduceMod, List.map_cons, List.map_nil] <;> rfl
    · rw [trace]
      simp only [List.map_map, Function.comp_def]
      rw [table_difference]
      cases r with
      | none => fin_cases s <;> simp [tailColumns, tailNonleaves, profile, col]
      | some r => fin_cases s <;> fin_cases r <;>
          simp [tailColumns, tailNonleaves, profile, col]
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
      rw [profile]
      cases i with
      | inl u => fin_cases q <;> first | rfl | omega
      | inr p =>
        rcases p with ⟨j,r⟩
        have different : l ≠ j := by
          intro h; subst j; exact inactive r rfl
        have small : q.val < 7 := by omega
        simp only [small,different,true_and,ite_true]
        fin_cases q <;> first | rfl | omega
    have leaf0 := (leaf_test _ _).mpr (by rw [replies 0 (by decide)]; decide)
    have leaf1 := (leaf_test _ _).mpr (by rw [replies 1 (by decide)]; decide)
    have leaf2 := (leaf_test _ _).mpr (by rw [replies 2 (by decide)]; decide)
    fin_cases s <;>
      simp [scanSlot, ask, stopAt, runPassiveProtocol, replies,
        Finset.insert_sdiff_of_mem _ leaf0, Finset.insert_sdiff_of_mem _ leaf1,
        Finset.insert_sdiff_of_mem _ leaf2]
  have route_actual (j : Fin k) (s : Fin 3) (d : Fin k → Fin 3) :
      ∀ (ls : List (Fin k)), j ∉ ls → ∀ (i : Index k),
        (match i with | .inl _ => True | .inr (l,_) => l = j ∨ l ∈ ls) →
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
      | inl u => simpa [scanList,extraAddresses] using (tail_actual j s none).2
      | inr p =>
        rcases p with ⟨l,r⟩
        have eq : l = j := by simpa using cover
        subst l
        simpa [scanList,extraAddresses] using (tail_actual j s (some r)).2
    | cons l ls ih =>
      intro absent i cover
      have jl : j ≠ l := fun h => absent (by simp [h])
      have jr : j ∉ ls := fun h => absent (List.mem_cons_of_mem l h)
      by_cases active : ∃ r, i = .inr (l,r)
      · obtain ⟨r,rfl⟩ := active
        simpa [scanList,extraAddresses,Ne.symm jl] using
          (scan_active l (d l) (scanList k j s d ls) r).2
      · have inactive : ∀ r, i ≠ .inr (l,r) := by simpa using active
        have rest : (match i with | .inl _ => True | .inr (t,_) => t = j ∨ t ∈ ls) := by
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
        | inr p => simp [ls]; exact eq_or_ne p.1 seed.1
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
        (Finset.univ.sup (fun i : Index k => cost (pi seed) (family k i))) = 8*k+18) ∧
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
      intro e; exact h (congrArg (fun a => readout a (family k (.inl ()))) e)
    have d04 (l : Fin k) : literal_addresses k l 0 ≠ literal_addresses k l 4 :=
      different l 0 4 (by simp only [literal_addresses,family,comb_slot_readout]; decide)
    have d06 (l : Fin k) : literal_addresses k l 0 ≠ literal_addresses k l 6 :=
      different l 0 6 (by simp only [literal_addresses,family,comb_slot_readout]; decide)
    have d26 (l : Fin k) : literal_addresses k l 2 ≠ literal_addresses k l 6 :=
      different l 2 6 (by simp only [literal_addresses,family,comb_slot_readout]; decide)
    have d74 (l : Fin k) : literal_addresses k l 7 ≠ literal_addresses k l 4 :=
      different l 7 4 (by simp only [literal_addresses,family,comb_slot_readout,comb_tail_readout]; decide)
    have d25 (l : Fin k) : literal_addresses k l 2 ≠ literal_addresses k l 5 :=
      different l 2 5 (by simp only [literal_addresses,family,comb_slot_readout]; decide)
    rcases seed with ⟨j,s,d⟩
    cases i with
    | inl u => fin_cases s <;> simp [extraAddresses,tailNonleaves,rowExcess]
    | inr p =>
      rcases p with ⟨l,r⟩
      by_cases same : l = j
      · subst l
        fin_cases s <;> fin_cases r <;>
          simp [extraAddresses,tailNonleaves,rowExcess,d04,d06,d26,d74,d25]
      · cases ds : d l using Fin.cases with
        | zero => fin_cases r <;>
            simp [extraAddresses,scanNonleaves,rowExcess,same,ds,d04,d06,d26]
        | succ t => fin_cases t <;> fin_cases r <;>
            simp [extraAddresses,scanNonleaves,rowExcess,same,ds,d04,d06,d26]
  fail "pending finite-law normalization and expectations"

end D5.S3.Arith.FibonacciAtomic.FourExitCoarseScanAttainment
