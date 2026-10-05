/- GID: D5/S3/Arith/FibonacciAtomic/FourExitCoarseLowerBounds
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/FourExitCoarseLowerBounds
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Arbitrary-law coarse four-exit lower bounds from subset potentials. -/

import D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutCompletion
import D5.S3.Arith.FibonacciAtomic.FourExitRawDomination
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.FourExitCoarseLowerBounds

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition
open ActualImageSevenLeafSeparation (leafLabel leafAddresses Nonconflict)
open ActualCoarseReadoutHistory (kappa kappa_hist CoarseObservable)
open ActualCoarseReadoutCompletion (encodeHistory)
open FourExitRawEndpointSpectrum
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute)
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
  (PassiveProtocol runPassiveProtocol)
open scoped BigOperators

local notation "RH" => Hist (fun _ : Address => Reply)
local notation "CH" => Hist (fun _ : Address => Option Bool)
local notation "Index" => fun k : Nat => Unit ⊕ (Fin k × Fin 4)

private theorem leaf_support_geometry (k : Nat) (u : Address) :
    (∀ j : Fin k,
      (Finset.univ.filter (fun r : Fin 4 => u ∈ leafAddresses (family k (.inr (j,r))))).card ≠ 3) ∧
    ((∃ j : Fin k,
      ((Finset.univ.filter (fun r : Fin 4 => u ∈ leafAddresses
        (family k (.inr (j,r))))).erase 2).card = 2) →
      ∀ j : Fin k, ((Finset.univ.filter (fun r : Fin 4 => u ∈ leafAddresses
        (family k (.inr (j,r))))).erase 2).card ≤ 2) ∧
    (∀ j : Fin k,
      (Finset.univ.filter (fun r : Fin 4 => u ∈ leafAddresses
        (family k (.inr (j,r))))).card +
      (if u ∈ leafAddresses (family k (.inl ())) then 1 else 0) ≠ 4) := by
  classical
  have active_support : ∀ v : Address,
      (Finset.univ.filter (fun r : Fin 4 => v ∈ leafAddresses (active r))).card ≤ 2 ∧
      ((Finset.univ.filter (fun r : Fin 4 => v ∈ leafAddresses (active r))).erase 2).card ≤ 1 := by
    let Q := (Finset.univ : Finset (Fin 4)).biUnion (fun r => leafAddresses (active r))
    have finite : ∀ v : Q,
        (Finset.univ.filter (fun r : Fin 4 => v.val ∈ leafAddresses (active r))).card ≤ 2 ∧
        ((Finset.univ.filter (fun r : Fin 4 => v.val ∈ leafAddresses (active r))).erase 2).card ≤ 1 := by
      decide
    intro v
    by_cases hv : v ∈ Q
    · exact finite ⟨v,hv⟩
    · have he : (Finset.univ.filter (fun r : Fin 4 => v ∈ leafAddresses (active r))) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (fun r _ hr =>
          hv (Finset.mem_biUnion.mpr ⟨r,Finset.mem_univ r,hr⟩))
      simp [he]
  have tail_support : ∀ v : Address,
      (Finset.univ.filter (fun r : Fin 4 => v ∈ leafAddresses (comp r))).card ≠ 3 ∧
      (Finset.univ.filter (fun r : Fin 4 => v ∈ leafAddresses (comp r))).card +
        (if v ∈ leafAddresses R₀ then 1 else 0) ≠ 4 := by
    let Q := leafAddresses R₀ ∪
      (Finset.univ : Finset (Fin 4)).biUnion (fun r => leafAddresses (comp r))
    have finite : ∀ v : Q,
        (Finset.univ.filter (fun r : Fin 4 => v.val ∈ leafAddresses (comp r))).card ≠ 3 ∧
        (Finset.univ.filter (fun r : Fin 4 => v.val ∈ leafAddresses (comp r))).card +
          (if v.val ∈ leafAddresses R₀ then 1 else 0) ≠ 4 := by
      decide
    intro v
    by_cases hv : v ∈ Q
    · exact finite ⟨v,hv⟩
    · have he : (Finset.univ.filter (fun r : Fin 4 => v ∈ leafAddresses (comp r))) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (fun r _ hr => hv
          (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r,Finset.mem_univ r,hr⟩)))
      have hn : v ∉ leafAddresses R₀ := fun hm => hv (Finset.mem_union_left _ hm)
      simp [he,hn]
  have joint : ∀ (n : Nat) (f : Index k → Fin n → Source)
      (t : Index k → Source) (v : Address),
      (∀ i, leafLabel (comb n (f i) (t i)) v = none) ∨
      (∃ (j : Fin n) (w : Address), ∀ i,
        leafLabel (comb n (f i) (t i)) v = leafLabel (f i j) w) ∨
      (∃ w : Address, ∀ i,
        leafLabel (comb n (f i) (t i)) v = leafLabel (t i) w) := by
    intro n
    induction n with
    | zero => intro f t v; exact Or.inr (Or.inr ⟨v,fun _ => rfl⟩)
    | succ n ih =>
      intro f t v
      cases v with
      | nil => exact Or.inl (fun _ => rfl)
      | cons d v =>
        cases d with
        | false => exact Or.inr (Or.inl ⟨0,v,fun _ => rfl⟩)
        | true =>
          rcases ih (fun i j => f i j.succ) t v with hn | ⟨j,w,hw⟩ | ⟨w,hw⟩
          · exact Or.inl hn
          · exact Or.inr (Or.inl ⟨j.succ,w,hw⟩)
          · exact Or.inr (Or.inr ⟨w,hw⟩)
  let slot : Index k → Fin k → Source := fun i j => match i with
    | .inl _ => B
    | .inr (l,r) => if j = l then active r else B
  let tail : Index k → Source := fun i => match i with
    | .inl _ => R₀
    | .inr (_,r) => comp r
  have unfold_family (i : Index k) : family k i = comb k (slot i) (tail i) := by
    cases i <;> rfl
  have leaf_iff (W : Source) (v : Address) :
      v ∈ leafAddresses W ↔ ∃ b, leafLabel W v = some b :=
    (ActualImageSevenLeafSeparation.seven_leaf_separation.1 W).2 v
  rcases joint k slot tail u with hn | ⟨l,v,hv⟩ | ⟨v,hv⟩
  · have empty (j : Fin k) :
        (Finset.univ.filter (fun r : Fin 4 => u ∈ leafAddresses
          (family k (.inr (j,r))))) = ∅ := by
      ext r
      simp [leaf_iff, unfold_family, hn]
    simp only [empty, Finset.card_empty, Finset.erase_empty]
    constructor
    · intro j; omega
    constructor
    · rintro ⟨j,hj⟩; omega
    · intro j; split_ifs <;> omega
  · have row (j : Fin k) (r : Fin 4) :
        u ∈ leafAddresses (family k (.inr (j,r))) ↔
        v ∈ leafAddresses (if l = j then active r else B) := by
      rw [leaf_iff, unfold_family, hv (.inr (j,r)), leaf_iff]
    have counts (j : Fin k) :
        (Finset.univ.filter (fun r : Fin 4 => u ∈ leafAddresses
          (family k (.inr (j,r))))) =
        if l = j then Finset.univ.filter (fun r : Fin 4 => v ∈ leafAddresses (active r))
        else if v ∈ leafAddresses B then Finset.univ else ∅ := by
      ext r
      by_cases hlj : l = j <;> by_cases hm : v ∈ leafAddresses B <;>
        simp [row,hlj,hm]
    have four (j : Fin k) :
        (Finset.univ.filter (fun r : Fin 4 => u ∈ leafAddresses
          (family k (.inr (j,r))))).card ≠ 3 := by
      rw [counts]
      split_ifs
      · have ha := (active_support v).1; omega
      · decide
      · decide
    have triple (j : Fin k) :
        ((Finset.univ.filter (fun r : Fin 4 => u ∈ leafAddresses
          (family k (.inr (j,r))))).erase 2).card ≠ 2 := by
      rw [counts]
      split_ifs
      · have ha := (active_support v).2; omega
      · decide
      · decide
    refine ⟨four,fun ⟨j,hj⟩ => False.elim (triple j hj),?_⟩
    have base : u ∈ leafAddresses (family k (.inl ())) ↔ v ∈ leafAddresses B := by
      rw [leaf_iff, unfold_family, hv (.inl ()), leaf_iff]
    intro j
    simp only [counts, base]
    split_ifs
    all_goals first
      | have ha := (active_support v).1; omega
      | decide
  · have row (j : Fin k) (r : Fin 4) :
        u ∈ leafAddresses (family k (.inr (j,r))) ↔ v ∈ leafAddresses (comp r) := by
      rw [leaf_iff, unfold_family, hv (.inr (j,r)), leaf_iff]
    have base : u ∈ leafAddresses (family k (.inl ())) ↔ v ∈ leafAddresses R₀ := by
      rw [leaf_iff, unfold_family, hv (.inl ()), leaf_iff]
    have counts (j : Fin k) :
        (Finset.univ.filter (fun r : Fin 4 => u ∈ leafAddresses
          (family k (.inr (j,r))))) =
        Finset.univ.filter (fun r : Fin 4 => v ∈ leafAddresses (comp r)) := by
      ext r; simp only [Finset.mem_filter, row]
    simp only [counts, base]
    exact ⟨fun _ => (tail_support v).1,fun ⟨_,h⟩ _ => h.le,
      fun _ => (tail_support v).2⟩

private theorem controller_subset_bounds (k : Nat) (hk : 1 ≤ k)
    (π : Strategy) (observable : CoarseObservable π.policy) :
    (5*k-1 ≤ ∑ i ∈ (((Finset.univ : Finset (Fin k)) ×ˢ
      (Finset.univ : Finset (Fin 4))).image Sum.inr), (cost π (family k i) - (8*k+16))) ∧
    (4*k-2 ≤ ∑ i ∈ (((Finset.univ : Finset (Fin k)) ×ˢ
      ((Finset.univ : Finset (Fin 4)).erase 2)).image Sum.inr),
        (cost π (family k i) - (8*k+16))) ∧
    (∃ i : Index k, 8 * k + 18 ≤ cost π (family k i)) := by
  have coarse_trace_run (π : Strategy) (observable : CoarseObservable π.policy) :
      ∀ (n : Nat) (h t : RH) (U : Source) (b : Bool),
        execute readout π.policy n h U = some (t,b) →
        execute (fun q W => leafLabel W q) (fun g => π.policy (encodeHistory g))
          n (kappa_hist h) U = some (kappa_hist t,b) := by
    have section_law (g : CH) : kappa_hist (encodeHistory g) = g := by
      simp only [kappa_hist, encodeHistory, List.map_map]
      calc
        _ = g.map (fun a => a) := by
          apply List.map_congr_left
          intro a _
          rcases a with ⟨q, y⟩
          cases y with
          | none => rfl
          | some b => cases b <;> rfl
        _ = g := List.map_id' _
    have action (h : RH) : π.policy (encodeHistory (kappa_hist h)) = π.policy h :=
      observable _ _ (section_law _)
    intro n
    induction n with
    | zero => intro h t U b run; simp [execute] at run
    | succ n ih =>
      intro h t U b run
      cases step : π.policy h with
      | inr z =>
        simp only [execute, step, Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl,rfl⟩ := run
        rw [execute, action, step]
        rfl
      | inl q =>
        simp only [execute, step, Option.map_eq_some_iff] at run
        obtain ⟨⟨s,z⟩,hs,he⟩ := run
        cases he
        have next := ih (h ++ [⟨q,readout q U⟩]) s U z hs
        simp only [kappa_hist, List.map_append, List.map_cons, List.map_nil] at next
        change execute (fun q W => leafLabel W q) (fun g => π.policy (encodeHistory g))
          n (kappa_hist h ++ [⟨q,leafLabel U q⟩]) U = some (kappa_hist s,z) at next
        rw [execute, action, step]
        change (execute (fun q W => leafLabel W q) (fun g => π.policy (encodeHistory g))
          n (kappa_hist h ++ [⟨q,leafLabel U q⟩]) U).map
            (fun p => (⟨q,leafLabel U q⟩ :: p.1,p.2)) = _
        rw [next]
        rfl
  classical
  have facts := FourExitRawDomination.result k hk
  let F := family k
  let pc : CH → Sum Address Bool := fun h => π.policy (encodeHistory h)
  let read : Address → Source → Option Bool := fun q W => leafLabel W q
  let p : Nat → CH → PassiveProtocol Address (fun _ => Option Bool) := fun n =>
    Nat.rec (fun _ => .stop) (fun _ previous h => match pc h with
      | .inr _ => .stop
      | .inl q => .query q (fun y => previous (h ++ [⟨q,y⟩]))) n
  have p_zero (h : CH) : p 0 h = .stop := rfl
  have p_succ (n : Nat) (h : CH) : p (n+1) h = match pc h with
      | .inr _ => .stop
      | .inl q => .query q (fun y => p n (h ++ [⟨q,y⟩])) := rfl
  have bounded_run : ∀ (a n : Nat) (h t : CH) (i : Index k) (b : Bool),
      a ≤ n → execute read pc a h (F i) = some (t,b) →
      runPassiveProtocol read (p n h) (F i) = t := by
    intro a
    induction a with
    | zero => intro n h t i b _ run; simp [execute] at run
    | succ a ih =>
      intro n h t i b bound run
      cases n with
      | zero => omega
      | succ n =>
        cases step : pc h with
        | inr z =>
          simp only [execute,step,Option.some.injEq,Prod.mk.injEq] at run
          obtain ⟨rfl,rfl⟩ := run
          simp [p_zero,p_succ,step,runPassiveProtocol]
        | inl q =>
          simp only [execute,step,Option.map_eq_some_iff] at run
          obtain ⟨⟨s,z⟩,hs,he⟩ := run
          cases he
          simpa only [p_zero,p_succ,step,runPassiveProtocol] using
            congrArg (fun s => (⟨q,read q (F i)⟩ : Sigma (fun _ : Address => Option Bool)) :: s)
              (ih n (h ++ [⟨q,read q (F i)⟩]) s i z (by omega) hs)
  let fuel : Index k → Nat := fun i => Classical.choose (π.correct (F i))
  let N := Finset.univ.sup fuel
  have initial (i : Index k) : runPassiveProtocol read (p N []) (F i) =
      kappa_hist (terminal π (F i)).1 := by
    have raw := (Classical.choose_spec (Classical.choose_spec (π.correct (F i)))).1
    have coarse := coarse_trace_run π observable (fuel i) [] (terminal π (F i)).1
      (F i) (terminal π (F i)).2 raw
    exact bounded_run (fuel i) N [] _ i _
      (Finset.le_sup (Finset.mem_univ i)) coarse
  have distinct (i l : Index k) (hne : i ≠ l) :
      kappa_hist (terminal π (F i)).1 ≠ kappa_hist (terminal π (F l)).1 := by
    intro same
    obtain ⟨s,q,hi,hl,hd,_⟩ := ActualCoarseReadoutHistory.shared_history_obstruction
      π observable (F i) (F l) (facts.1 i).1 (facts.1 l).1
      (fun he => hne (facts.2.1 he)) (facts.2.2.1 i l) []
      List.nil_prefix List.nil_prefix
    have hpi := List.prefix_iff_eq_take.mp hi
    have hpl := List.prefix_iff_eq_take.mp hl
    simp only [List.nil_append,List.length_append,List.length_singleton] at hpi hpl
    rw [same] at hpi
    have he := List.append_cancel_left (hpi.trans hpl.symm)
    exact hd (congrArg Sigma.snd (List.singleton_inj.mp he))
  let j : Fin k := ⟨0,by omega⟩
  let S : Finset (Index k) := {.inl (),.inr (j,0),.inr (j,1),.inr (j,2),.inr (j,3)}
  have stop_impossible (h : CH)
      (runs : ∀ i ∈ S, h = kappa_hist (terminal π (F i)).1) : False := by
    exact distinct (.inl ()) (.inr (j,0)) (by simp)
      ((runs _ (by simp [S])).symm.trans (runs _ (by simp [S])))
  have nonleaf_paid (i : Index k) (q : Address) (h : CH)
      (pre : (h ++ [(⟨q,none⟩ : Sigma (fun _ : Address => Option Bool))]).IsPrefix (kappa_hist (terminal π (F i)).1))
      (none_reply : leafLabel (F i) q = none) :
      (((h ++ [(⟨q,none⟩ : Sigma (fun _ : Address => Option Bool))]).map Sigma.fst).toFinset \ leafAddresses (F i)).Nonempty := by
    refine ⟨q,Finset.mem_sdiff.mpr ⟨by simp,?_⟩⟩
    intro hq
    obtain ⟨b,hb⟩ := (ActualImageSevenLeafSeparation.seven_leaf_separation.1 (F i)).2 q |>.mp hq
    rw [none_reply] at hb
    cases hb
  have cost_eq (i : Index k) : cost π (F i) = 8 * k + 16 +
      (paid (terminal π (F i)).1 \ leafAddresses (F i)).card := by
    have included := source_foundation.2.2.2.2.1 π (F i) (facts.1 i).1
    have count := Finset.card_sdiff_add_card_eq_card included
    have leaves_count := (ActualImageSevenLeafSeparation.seven_leaf_separation.1 (F i)).1
    rw [(facts.1 i).2.1] at leaves_count
    change (paid (terminal π (F i)).1).card = _
    change (paid (terminal π (F i)).1 \ leafAddresses (F i)).card +
      (leafAddresses (F i)).card = (paid (terminal π (F i)).1).card at count
    omega
  have loop : ∀ (n : Nat) (h : CH),
      (∀ i ∈ S, h ++ runPassiveProtocol read (p n h) (F i) =
        kappa_hist (terminal π (F i)).1) →
      ∃ i : Index k, 8 * k + 18 ≤ cost π (F i) := by
    intro n
    induction n with
    | zero =>
      intro h runs
      exact False.elim (stop_impossible h (by simpa [p_zero,p_succ,runPassiveProtocol] using runs))
    | succ n ih =>
      intro h runs
      cases step : pc h with
      | inr b =>
        exact False.elim (stop_impossible h (by simpa [p_zero,p_succ,step,runPassiveProtocol] using runs))
      | inl q =>
        by_cases all_none : ∀ i ∈ S, read q (F i) = none
        · apply ih (h ++ [(⟨q,none⟩ : Sigma (fun _ : Address => Option Bool))])
          intro i hi
          simpa only [p_zero,p_succ,step,runPassiveProtocol,all_none i hi,List.append_assoc,
            List.singleton_append] using runs i hi
        · push Not at all_none
          obtain ⟨a,ha,hleaf⟩ := all_none
          obtain ⟨b,hb⟩ := Option.ne_none_iff_exists.mp hleaf
          have replies (i : Index k) (hi : i ∈ S) : read q (F i) = none ∨ read q (F i) = some b := by
            cases hr : read q (F i) with
            | none => exact Or.inl rfl
            | some z =>
              right
              have nc := (ActualImageSevenLeafSeparation.seven_leaf_separation.2.1 (F i) (F a)).2.2.mp
                (facts.2.2.1 i a) q z b hr hb.symm
              exact congrArg some nc
          by_cases all_leaf : ∀ i ∈ S, read q (F i) = some b
          · apply ih (h ++ [⟨q,some b⟩])
            intro i hi
            simpa only [p_zero,p_succ,step,runPassiveProtocol,all_leaf i hi,List.append_assoc,
              List.singleton_append] using runs i hi
          · let T := S.filter (fun i => q ∉ leafAddresses (F i))
            have Tnone (i : Index k) (hi : i ∈ T) : read q (F i) = none := by
              rcases replies i (Finset.mem_filter.mp hi).1 with hn | hl
              · exact hn
              · exact False.elim ((Finset.mem_filter.mp hi).2
                  ((ActualImageSevenLeafSeparation.seven_leaf_separation.1 (F i)).2 q |>.mpr ⟨b,hl⟩))
            have Tnonempty : T.Nonempty := by
              push Not at all_leaf
              obtain ⟨i,hi,hn⟩ := all_leaf
              refine ⟨i,Finset.mem_filter.mpr ⟨hi,?_⟩⟩
              intro hm
              obtain ⟨z,hz⟩ := (ActualImageSevenLeafSeparation.seven_leaf_separation.1 (F i)).2 q |>.mp hm
              exact hn ((replies i hi).resolve_left (by change ¬ leafLabel (F i) q = none; rw [hz]; simp))
            have support_count : (S.filter (fun i => q ∈ leafAddresses (F i))).card =
                (Finset.univ.filter (fun r : Fin 4 => q ∈ leafAddresses
                  (F (.inr (j,r))))).card +
                (if q ∈ leafAddresses (F (.inl ())) then 1 else 0) := by
              have rows : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide
              rw [rows]
              by_cases hb : q ∈ leafAddresses (F (.inl ())) <;>
                by_cases h0 : q ∈ leafAddresses (F (.inr (j,0))) <;>
                by_cases h1 : q ∈ leafAddresses (F (.inr (j,1))) <;>
                by_cases h2 : q ∈ leafAddresses (F (.inr (j,2))) <;>
                by_cases h3 : q ∈ leafAddresses (F (.inr (j,3))) <;>
                simp [S,Finset.filter_insert,Finset.filter_singleton,Finset.filter_empty,hb,h0,h1,h2,h3]
            have nefour : (S.filter (fun i => q ∈ leafAddresses (F i))).card ≠ 4 := by
              rw [support_count]
              exact (leaf_support_geometry k q).2.2 j
            have total := Finset.card_filter_add_card_filter_not (s := S)
              (fun i => q ∈ leafAddresses (F i))
            have size : S.card = 5 := by simp [S]
            have large : 1 < T.card := by
              have positive := Finset.card_pos.mpr Tnonempty
              change (S.filter (fun i => q ∈ leafAddresses (F i))).card + T.card = S.card at total
              omega
            obtain ⟨i,hi,l,hl,hne⟩ := Finset.one_lt_card.mp large
            have history_prefix (a : Index k) (ha : a ∈ T) :
                (h ++ [(⟨q,none⟩ : Sigma (fun _ : Address => Option Bool))]).IsPrefix (kappa_hist (terminal π (F a)).1) := by
              rw [← runs a (Finset.mem_filter.mp ha).1]
              simpa only [p_zero,p_succ,step,runPassiveProtocol,Tnone a ha,List.append_assoc,
                List.singleton_append] using
                (List.prefix_append (h ++ [(⟨q,none⟩ : Sigma (fun _ : Address => Option Bool))])
                  (runPassiveProtocol read (p n (h ++ [(⟨q,none⟩ : Sigma (fun _ : Address => Option Bool))])) (F a)))
            obtain ⟨s,r,_,_,_,_,_,two⟩ := ActualCoarseReadoutHistory.shared_history_obstruction
              π observable (F i) (F l) (facts.1 i).1 (facts.1 l).1
              (fun he => hne (facts.2.1 he)) (facts.2.2.1 i l) (h ++ [(⟨q,none⟩ : Sigma (fun _ : Address => Option Bool))])
              (history_prefix i hi) (history_prefix l hl)
            rcases two ⟨nonleaf_paid i q h (history_prefix i hi) (Tnone i hi),
              nonleaf_paid l q h (history_prefix l hl) (Tnone l hl)⟩ with hi2 | hl2
            · exact ⟨i,by rw [cost_eq]; omega⟩
            · exact ⟨l,by rw [cost_eq]; omega⟩
  let excess := fun i : Index k => cost π (F i) - (8*k+16)
  have excess_eq (i : Index k) : excess i =
      (paid (terminal π (F i)).1 \ leafAddresses (F i)).card := by
    dsimp [excess]
    rw [cost_eq]
    omega
  have nonleaf_one (i : Index k) (q : Address) (h : CH)
      (pre : (h ++ [(⟨q,none⟩ : Sigma (fun _ : Address => Option Bool))]).IsPrefix
        (kappa_hist (terminal π (F i)).1))
      (reply : read q (F i) = none) : 1 ≤ excess i := by
    have address : q ∈ (kappa_hist (terminal π (F i)).1).map Sigma.fst :=
      (pre.map Sigma.fst).subset (by simp)
    have paidq : q ∈ paid (terminal π (F i)).1 := by
      simpa only [paid,kappa_hist,List.map_map,Function.comp_def,List.mem_toFinset]
        using address
    have notleaf : q ∉ leafAddresses (F i) := by
      intro hq
      obtain ⟨b,hb⟩ := (ActualImageSevenLeafSeparation.seven_leaf_separation.1 (F i)).2 q |>.mp hq
      change leafLabel (F i) q = none at reply
      rw [reply] at hb
      cases hb
    rw [excess_eq]
    exact Finset.card_pos.mpr ⟨q,Finset.mem_sdiff.mpr ⟨paidq,notleaf⟩⟩
  have nonleaf_pair (i l : Index k) (hne : i ≠ l) (q : Address) (h : CH)
      (pi : (h ++ [(⟨q,none⟩ : Sigma (fun _ : Address => Option Bool))]).IsPrefix
        (kappa_hist (terminal π (F i)).1))
      (pl : (h ++ [(⟨q,none⟩ : Sigma (fun _ : Address => Option Bool))]).IsPrefix
        (kappa_hist (terminal π (F l)).1))
      (ri : read q (F i) = none) (rl : read q (F l) = none) :
      2 ≤ excess i ∨ 2 ≤ excess l := by
    obtain ⟨s,r,_,_,_,_,_,two⟩ := ActualCoarseReadoutHistory.shared_history_obstruction
      π observable (F i) (F l) (facts.1 i).1 (facts.1 l).1
      (fun he => hne (facts.2.1 he)) (facts.2.2.1 i l)
      (h ++ [(⟨q,none⟩ : Sigma (fun _ : Address => Option Bool))]) pi pl
    simpa only [excess_eq] using two
      ⟨nonleaf_paid i q h pi ri,nonleaf_paid l q h pl rl⟩
  have branch_sum (T H : Finset (Index k)) (q : Address) (h : CH)
      (pre : ∀ i ∈ T, (h ++ [(⟨q,none⟩ : Sigma (fun _ : Address => Option Bool))]).IsPrefix
        (kappa_hist (terminal π (F i)).1))
      (reply : ∀ i ∈ T, read q (F i) = none) :
      2*(T ∩ H).card ≤ (∑ i ∈ T ∩ H, excess i) + 1 := by
    let U := T ∩ H
    by_cases bad : ∃ i ∈ U, excess i < 2
    · obtain ⟨i,hi,he⟩ := bad
      have one := nonleaf_one i q h (pre i (Finset.mem_inter.mp hi).1)
        (reply i (Finset.mem_inter.mp hi).1)
      have others : ∀ l ∈ U.erase i, 2 ≤ excess l := by
        intro l hl
        obtain ⟨ne,hl⟩ := Finset.mem_erase.mp hl
        exact (nonleaf_pair i l ne.symm q h
          (pre i (Finset.mem_inter.mp hi).1) (pre l (Finset.mem_inter.mp hl).1)
          (reply i (Finset.mem_inter.mp hi).1) (reply l (Finset.mem_inter.mp hl).1)).resolve_left
            (by omega)
      have summed := Finset.sum_le_sum others
      have card := Finset.card_erase_add_one hi
      have split := Finset.sum_erase_add U excess hi
      simp only [Finset.sum_const,smul_eq_mul] at summed
      change 2*U.card ≤ (∑ i ∈ U, excess i) + 1
      dsimp only [U] at *
      omega
    · push Not at bad
      have summed := Finset.sum_le_sum bad
      simp only [Finset.sum_const,smul_eq_mul] at summed
      change 2*U.card ≤ (∑ i ∈ U, excess i) + 1
      dsimp only [U] at *
      omega
  have lower_from_charge (H : Finset (Index k)) (P B : Finset (Index k) → Nat)
      (terminal_charge : ∀ S : Finset (Index k), S.card ≤ 1 →
        2*(S ∩ H).card ≤ P S + B S)
      (weak : ∀ (S : Finset (Index k)) (q : Address),
        P (S.filter (fun i => q ∈ leafAddresses (F i))) +
          B (S.filter (fun i => q ∈ leafAddresses (F i))) ≤ P S + B S)
      (strong : ∀ (S : Finset (Index k)) (q : Address),
        ((S.filter (fun i => q ∉ leafAddresses (F i))) ∩ H).Nonempty →
        P (S.filter (fun i => q ∈ leafAddresses (F i))) +
          B (S.filter (fun i => q ∈ leafAddresses (F i))) + 1 ≤ P S + B S) :
      ∀ (n : Nat) (h : CH) (S : Finset (Index k)),
        (∀ i ∈ S, h ++ runPassiveProtocol read (p n h) (F i) =
          kappa_hist (terminal π (F i)).1) →
        2*(S ∩ H).card ≤ (∑ i ∈ S ∩ H, excess i) + P S + B S := by
    have stop_bound (h : CH) (S : Finset (Index k))
        (runs : ∀ i ∈ S, h = kappa_hist (terminal π (F i)).1) :
        2*(S ∩ H).card ≤ (∑ i ∈ S ∩ H, excess i) + P S + B S := by
      have size : S.card ≤ 1 := Finset.card_le_one.mpr (by
        intro i hi l hl
        by_contra ne
        exact distinct i l ne ((runs i hi).symm.trans (runs l hl)))
      have bound := terminal_charge S size
      omega
    intro n
    induction n with
    | zero => intro h S runs; exact stop_bound h S (by simpa [p_zero,runPassiveProtocol] using runs)
    | succ n ih =>
      intro h S runs
      cases step : pc h with
      | inr b => exact stop_bound h S (by simpa [p_succ,step,runPassiveProtocol] using runs)
      | inl q =>
        by_cases all_none : ∀ i ∈ S, read q (F i) = none
        · apply ih (h ++ [(⟨q,none⟩ : Sigma (fun _ : Address => Option Bool))]) S
          intro i hi
          simpa only [p_succ,step,runPassiveProtocol,all_none i hi,List.append_assoc,
            List.singleton_append] using runs i hi
        · push Not at all_none
          obtain ⟨a,ha,hleaf⟩ := all_none
          obtain ⟨b,hb⟩ := Option.ne_none_iff_exists.mp hleaf
          let L := S.filter (fun i => q ∈ leafAddresses (F i))
          let T := S.filter (fun i => q ∉ leafAddresses (F i))
          have leaves_reply (i : Index k) (hi : i ∈ L) : read q (F i) = some b := by
            obtain ⟨z,hz⟩ := (ActualImageSevenLeafSeparation.seven_leaf_separation.1 (F i)).2 q |>.mp
              (Finset.mem_filter.mp hi).2
            exact hz.trans (congrArg some
              ((ActualImageSevenLeafSeparation.seven_leaf_separation.2.1 (F i) (F a)).2.2.mp
                (facts.2.2.1 i a) q z b hz hb.symm))
          have none_reply (i : Index k) (hi : i ∈ T) : read q (F i) = none := by
            apply Option.eq_none_iff_forall_not_mem.mpr
            intro b hb
            exact (Finset.mem_filter.mp hi).2
              ((ActualImageSevenLeafSeparation.seven_leaf_separation.1 (F i)).2 q |>.mpr ⟨b,hb⟩)
          have left := ih (h ++ [⟨q,some b⟩]) L (by
            intro i hi
            simpa only [p_succ,step,runPassiveProtocol,leaves_reply i hi,List.append_assoc,
              List.singleton_append] using runs i (Finset.mem_filter.mp hi).1)
          have pre (i : Index k) (hi : i ∈ T) :
              (h ++ [(⟨q,none⟩ : Sigma (fun _ : Address => Option Bool))]).IsPrefix
                (kappa_hist (terminal π (F i)).1) := by
            rw [← runs i (Finset.mem_filter.mp hi).1]
            simpa only [p_succ,step,runPassiveProtocol,none_reply i hi,List.append_assoc,
              List.singleton_append] using
              (List.prefix_append (h ++ [(⟨q,none⟩ : Sigma (fun _ : Address => Option Bool))])
                (runPassiveProtocol read (p n (h ++ [⟨q,none⟩])) (F i)))
          have union : (L ∩ H) ∪ (T ∩ H) = S ∩ H := by
            ext i; simp [L,T]; tauto
          have disjoint : Disjoint (L ∩ H) (T ∩ H) := by
            apply Finset.disjoint_left.mpr
            intro i hi ht
            exact (Finset.mem_filter.mp (Finset.mem_inter.mp ht).1).2
              (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).2
          have counts := Finset.card_union_of_disjoint disjoint
          have sums := Finset.sum_union (f := excess) disjoint
          rw [union] at counts sums
          by_cases hit : (T ∩ H).Nonempty
          · have right := branch_sum T H q h pre none_reply
            have step_bound := strong S q hit
            change P L + B L + 1 ≤ P S + B S at step_bound
            dsimp only [L,T] at *
            omega
          · have empty : T ∩ H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hit
            have step_bound := weak S q
            change P L + B L ≤ P S + B S at step_bound
            simp only [empty,Finset.card_empty,Finset.sum_empty] at counts sums
            dsimp only [L,T] at *
            omega
  have potential_one (S : Finset (Index k)) (q : Address) :
      let L := S.filter (fun i => q ∈ leafAddresses (family k i))
      let φ := fun T : Finset (Index k) =>
        ∑ j : Fin k, min (Finset.univ.filter
          (fun r : Fin 4 => Sum.inr (j,r) ∈ T)).card 3
      (∃ (j : Fin k) (r : Fin 4), Sum.inr (j,r) ∈ S ∧
        q ∉ leafAddresses (family k (.inr (j,r)))) → φ L + 1 ≤ φ S := by
    classical
    intro L φ ⟨j,r,hs,hn⟩
    let C := fun T : Finset (Index k) => fun j : Fin k =>
      (Finset.univ : Finset (Fin 4)).filter (fun r => Sum.inr (j,r) ∈ T)
    have subset (j : Fin k) : C L j ⊆ C S j := by
      intro r hr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ r,
        (Finset.mem_filter.mp (Finset.mem_filter.mp hr).2).1⟩
    have bound (j : Fin k) : (C S j).card ≤ 4 := by
      simpa using (C S j).card_le_univ
    have le (j : Fin k) : min (C L j).card 3 ≤ min (C S j).card 3 :=
      min_le_min_right 3 (Finset.card_le_card (subset j))
    have strict : (C L j).card < (C S j).card := by
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨subset j,?_⟩
      intro same
      have memS : r ∈ C S j := Finset.mem_filter.mpr ⟨Finset.mem_univ r,hs⟩
      rw [← same] at memS
      exact hn (Finset.mem_filter.mp (Finset.mem_filter.mp memS).2).2
    have exceptional : (C S j).card = 4 → (C L j).card ≠ 3 := by
      intro full
      have rows_full : C S j = Finset.univ := (C S j).eq_univ_of_card (by simpa using full)
      have rows : C L j = Finset.univ.filter
          (fun r : Fin 4 => q ∈ leafAddresses (family k (.inr (j,r)))) := by
        ext r
        have inS : Sum.inr (j,r) ∈ S := (Finset.mem_filter.mp
          (show r ∈ C S j from rows_full.symm ▸ Finset.mem_univ r)).2
        simp [C,L,inS]
      rw [rows]
      exact (leaf_support_geometry k q).1 j
    have drop : min (C L j).card 3 < min (C S j).card 3 := by
      have hb := bound j
      by_cases full : (C S j).card = 4
      · have he := exceptional full; omega
      · omega
    have sum_drop := Finset.sum_lt_sum (fun j _ => le j) ⟨j,Finset.mem_univ j,drop⟩
    exact Nat.succ_le_iff.mpr sum_drop

  have potential_two (S : Finset (Index k)) (q : Address) :
      let L := S.filter (fun i => q ∈ leafAddresses (family k i))
      let C := fun T : Finset (Index k) => fun j : Fin k =>
        ((Finset.univ : Finset (Fin 4)).filter (fun r => Sum.inr (j,r) ∈ T)).erase 2
      let φ := fun T : Finset (Index k) => ∑ j : Fin k, min (C T j).card 2
      let credit := fun T : Finset (Index k) => if ∀ j, (C T j).card ≤ 2 then 1 else 2
      (∃ (j : Fin k) (r : Fin 4), r ≠ 2 ∧ Sum.inr (j,r) ∈ S ∧
        q ∉ leafAddresses (family k (.inr (j,r)))) → φ L + credit L + 1 ≤ φ S + credit S := by
    classical
    intro L C φ credit ⟨j,r,hr,hs,hn⟩
    have subset (j : Fin k) : C L j ⊆ C S j := by
      intro r h
      obtain ⟨hr,h⟩ := Finset.mem_erase.mp h
      exact Finset.mem_erase.mpr ⟨hr,Finset.mem_filter.mpr ⟨Finset.mem_univ r,
        (Finset.mem_filter.mp (Finset.mem_filter.mp h).2).1⟩⟩
    have fullsubset (j : Fin k) : C S j ⊆ (Finset.univ : Finset (Fin 4)).erase 2 := by
      intro r h
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp h).1,Finset.mem_univ r⟩
    have bound (j : Fin k) : (C S j).card ≤ 3 := by
      simpa using Finset.card_le_card (fullsubset j)
    have le (j : Fin k) : min (C L j).card 2 ≤ min (C S j).card 2 :=
      min_le_min_right 2 (Finset.card_le_card (subset j))
    have credit_le : credit L ≤ credit S := by
      by_cases good : ∀ j, (C S j).card ≤ 2
      · have better : ∀ j, (C L j).card ≤ 2 := fun j =>
          (Finset.card_le_card (subset j)).trans (good j)
        simp [credit,good,better]
      · simp only [credit,if_neg good]
        split_ifs <;> omega
    by_cases dropped : ∃ j : Fin k, min (C L j).card 2 < min (C S j).card 2
    · obtain ⟨l,hl⟩ := dropped
      have lower := Finset.sum_lt_sum (fun j _ => le j) ⟨l,Finset.mem_univ l,hl⟩
      change φ L < φ S at lower
      omega
    · push Not at dropped
      have equal (j : Fin k) : min (C L j).card 2 = min (C S j).card 2 :=
        (le j).antisymm (dropped j)
      have strict : (C L j).card < (C S j).card := by
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨subset j,?_⟩
        intro same
        have member : r ∈ C S j := Finset.mem_erase.mpr
          ⟨hr,Finset.mem_filter.mpr ⟨Finset.mem_univ r,hs⟩⟩
        rw [← same] at member
        exact hn (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_erase.mp member).2).2).2
      have full : (C S j).card = 3 := by have h := equal j; have b := bound j; omega
      have two : (C L j).card = 2 := by have h := equal j; omega
      have rows_full : C S j = (Finset.univ : Finset (Fin 4)).erase 2 :=
        Finset.eq_of_subset_of_card_le (fullsubset j) (by simp [full])
      have rows : C L j = (Finset.univ.filter
          (fun r : Fin 4 => q ∈ leafAddresses (family k (.inr (j,r))))).erase 2 := by
        ext r
        by_cases hr : r = 2
        · simp [C,hr]
        · have inS : Sum.inr (j,r) ∈ S := (Finset.mem_filter.mp
            (Finset.mem_erase.mp (show r ∈ C S j from
              rows_full.symm ▸ Finset.mem_erase.mpr ⟨hr,Finset.mem_univ r⟩)).2).2
          simp [C,L,hr,inS]
      have global := (leaf_support_geometry k q).2.1 ⟨j,rows ▸ two⟩
      have good : ∀ l : Fin k, (C L l).card ≤ 2 := by
        intro l
        apply (Finset.card_le_card (show C L l ⊆ (Finset.univ.filter
            (fun r : Fin 4 => q ∈ leafAddresses (family k (.inr (l,r))))).erase 2 from ?_)).trans
          (global l)
        intro r h
        obtain ⟨hr,h⟩ := Finset.mem_erase.mp h
        exact Finset.mem_erase.mpr ⟨hr,Finset.mem_filter.mpr ⟨Finset.mem_univ r,
          (Finset.mem_filter.mp (Finset.mem_filter.mp h).2).2⟩⟩
      have bad : ¬ ∀ l : Fin k, (C S l).card ≤ 2 := fun h => by have h := h j; omega
      have same : φ L = φ S := Finset.sum_congr rfl (fun l _ => equal l)
      simp [credit,good,bad,same]

  let H := fun G : Finset (Fin 4) =>
    (((Finset.univ : Finset (Fin k)) ×ˢ G).image
      (fun a : Fin k × Fin 4 => (Sum.inr a : Index k)))
  let C₁ := fun T : Finset (Index k) => fun j : Fin k =>
    (Finset.univ : Finset (Fin 4)).filter (fun r => Sum.inr (j,r) ∈ T)
  let C₂ := fun T : Finset (Index k) => fun j : Fin k => (C₁ T j).erase 2
  let φ₁ := fun T : Finset (Index k) => ∑ j : Fin k, min (C₁ T j).card 3
  let φ₂ := fun T : Finset (Index k) => ∑ j : Fin k, min (C₂ T j).card 2
  let B₂ := fun T : Finset (Index k) => if ∀ j, (C₂ T j).card ≤ 2 then 1 else 2
  have inH (G : Finset (Fin 4)) (i : Index k) :
      i ∈ H G ↔ ∃ j r, r ∈ G ∧ i = Sum.inr (j,r) := by
    simp only [H,Finset.mem_image,Finset.mem_product,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨⟨j,r⟩,hr,he⟩; exact ⟨j,r,hr,he.symm⟩
    · rintro ⟨j,r,hr,rfl⟩; exact ⟨(j,r),hr,rfl⟩
  have Hcard (G : Finset (Fin 4)) : (H G).card = k*G.card := by
    rw [Finset.card_image_of_injective _ Sum.inr_injective,Finset.card_product]
    simp
  have column_subset (S : Finset (Index k)) (q : Address) (j : Fin k) :
      C₁ (S.filter (fun i => q ∈ leafAddresses (F i))) j ⊆ C₁ S j := by
    intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ r,
      (Finset.mem_filter.mp (Finset.mem_filter.mp hr).2).1⟩
  have weak₁ (S : Finset (Index k)) (q : Address) :
      φ₁ (S.filter (fun i => q ∈ leafAddresses (F i))) + 1 ≤ φ₁ S + 1 := by
    apply Nat.add_le_add_right
    exact Finset.sum_le_sum (fun j _ => min_le_min_right 3
      (Finset.card_le_card (column_subset S q j)))
  have weak₂ (S : Finset (Index k)) (q : Address) :
      φ₂ (S.filter (fun i => q ∈ leafAddresses (F i))) +
        B₂ (S.filter (fun i => q ∈ leafAddresses (F i))) ≤ φ₂ S + B₂ S := by
    let L := S.filter (fun i => q ∈ leafAddresses (F i))
    have sub (j : Fin k) : C₂ L j ⊆ C₂ S j :=
      Finset.erase_subset_erase 2 (column_subset S q j)
    have charge : φ₂ L ≤ φ₂ S := Finset.sum_le_sum (fun j _ =>
      min_le_min_right 2 (Finset.card_le_card (sub j)))
    have credit : B₂ L ≤ B₂ S := by
      by_cases good : ∀ j, (C₂ S j).card ≤ 2
      · have better : ∀ j, (C₂ L j).card ≤ 2 := fun j =>
          (Finset.card_le_card (sub j)).trans (good j)
        simp [B₂,good,better]
      · simp only [B₂,if_neg good]; split_ifs <;> omega
    exact Nat.add_le_add charge credit
  have terminal₁ (S : Finset (Index k)) (small : S.card ≤ 1) :
      2*(S ∩ H Finset.univ).card ≤ φ₁ S + 1 := by
    have bound : (S ∩ H Finset.univ).card ≤ 1 :=
      (Finset.card_le_card Finset.inter_subset_left).trans small
    by_cases empty : S ∩ H Finset.univ = ∅
    · simp [empty]
    · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr empty
      obtain ⟨j,r,_,rfl⟩ := (inH _ i).mp (Finset.mem_inter.mp hi).2
      have member : r ∈ C₁ S j := Finset.mem_filter.mpr
        ⟨Finset.mem_univ r,(Finset.mem_inter.mp hi).1⟩
      have positive := Finset.card_pos.mpr ⟨r,member⟩
      have one := Finset.single_le_sum (fun j _ => Nat.zero_le (min (C₁ S j).card 3))
        (Finset.mem_univ j)
      change min (C₁ S j).card 3 ≤ φ₁ S at one
      omega
  have terminal₂ (S : Finset (Index k)) (small : S.card ≤ 1) :
      2*(S ∩ H (Finset.univ.erase 2)).card ≤ φ₂ S + B₂ S := by
    have bound : (S ∩ H (Finset.univ.erase 2)).card ≤ 1 :=
      (Finset.card_le_card Finset.inter_subset_left).trans small
    by_cases empty : S ∩ H (Finset.univ.erase 2) = ∅
    · simp [empty]
    · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr empty
      obtain ⟨j,r,hr,rfl⟩ := (inH _ i).mp (Finset.mem_inter.mp hi).2
      have member : r ∈ C₂ S j := Finset.mem_erase.mpr
        ⟨(Finset.mem_erase.mp hr).1,Finset.mem_filter.mpr
          ⟨Finset.mem_univ r,(Finset.mem_inter.mp hi).1⟩⟩
      have positive := Finset.card_pos.mpr ⟨r,member⟩
      have one := Finset.single_le_sum (fun j _ => Nat.zero_le (min (C₂ S j).card 2))
        (Finset.mem_univ j)
      change min (C₂ S j).card 2 ≤ φ₂ S at one
      have credit : 1 ≤ B₂ S := by simp only [B₂]; split_ifs <;> omega
      omega
  have strong₁ (S : Finset (Index k)) (q : Address)
      (hit : ((S.filter (fun i => q ∉ leafAddresses (F i))) ∩ H Finset.univ).Nonempty) :
      φ₁ (S.filter (fun i => q ∈ leafAddresses (F i))) + 1 + 1 ≤ φ₁ S + 1 := by
    obtain ⟨i,hi⟩ := hit
    obtain ⟨j,r,_,rfl⟩ := (inH _ i).mp (Finset.mem_inter.mp hi).2
    have drop := potential_one S q ⟨j,r,
      (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).1,
      (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).2⟩
    change φ₁ (S.filter (fun i => q ∈ leafAddresses (F i))) + 1 ≤ φ₁ S at drop
    omega
  have strong₂ (S : Finset (Index k)) (q : Address)
      (hit : ((S.filter (fun i => q ∉ leafAddresses (F i))) ∩
        H (Finset.univ.erase 2)).Nonempty) :
      φ₂ (S.filter (fun i => q ∈ leafAddresses (F i))) +
        B₂ (S.filter (fun i => q ∈ leafAddresses (F i))) + 1 ≤ φ₂ S + B₂ S := by
    obtain ⟨i,hi⟩ := hit
    obtain ⟨j,r,hr,rfl⟩ := (inH _ i).mp (Finset.mem_inter.mp hi).2
    exact potential_two S q ⟨j,r,(Finset.mem_erase.mp hr).1,
      (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).1,
      (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).2⟩
  have first := lower_from_charge (H Finset.univ) φ₁ (fun _ => 1)
    terminal₁ weak₁ strong₁ N [] Finset.univ
    (fun i _ => by simpa only [List.nil_append] using initial i)
  have second := lower_from_charge (H (Finset.univ.erase 2)) φ₂ B₂
    terminal₂ weak₂ strong₂ N [] Finset.univ
    (fun i _ => by simpa only [List.nil_append] using initial i)
  have root₁ : φ₁ Finset.univ = 3*k := by simp [φ₁,C₁]; omega
  have root₂ : φ₂ Finset.univ = 2*k := by simp [φ₂,C₂,C₁]; omega
  have credit_root : B₂ Finset.univ = 2 := by
    have bad : ¬ ∀ j, (C₂ Finset.univ j).card ≤ 2 := by
      intro h
      have impossible := h ⟨0,by omega⟩
      simp [C₂,C₁] at impossible
    simp [B₂,bad]
  simp only [Finset.univ_inter,root₁,root₂,credit_root] at first second
  have h₁ := Hcard (Finset.univ : Finset (Fin 4))
  have h₂ := Hcard ((Finset.univ : Finset (Fin 4)).erase 2)
  simp only [Finset.card_univ,Fintype.card_fin,Finset.card_erase_of_mem,
    Finset.mem_univ] at h₁ h₂
  constructor
  · change 5*k-1 ≤ ∑ i ∈ H Finset.univ, excess i
    omega
  constructor
  · change 4*k-2 ≤ ∑ i ∈ H (Finset.univ.erase 2), excess i
    omega
  · exact loop N [] (fun i _ => by simpa only [List.nil_append] using initial i)

/-- Both subset averages and the deterministic two-excess obstruction hold for arbitrary laws. -/
theorem result (k : Nat) (hk : 1 ≤ k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (c : Ω → Strategy)
    (observable : ∀ ω, CoarseObservable (c ω).policy)
    (measurable : ∀ i : Index k,
      Measurable (fun ω => (cost (c ω) (family k i) : ENNReal))) :
    ((8*k+16 : Nat) : ENNReal) + ((5*k-1 : Nat) : ENNReal) / (4*k : Nat) ≤
      ⨆ i : Index k, ∫⁻ ω, (cost (c ω) (family k i) : ENNReal) ∂μ ∧
    ((8*k+16 : Nat) : ENNReal) + ((4*k-2 : Nat) : ENNReal) / (3*k : Nat) ≤
      ⨆ i : Index k, ∫⁻ ω, (cost (c ω) (family k i) : ENNReal) ∂μ ∧
    (∀ π : Strategy, CoarseObservable π.policy →
      ∃ i : Index k, 8*k+18 ≤ cost π (family k i)) ∧
    ((8*k+18 : Nat) : ENNReal) ≤
      ⨅ π : {π : Strategy // CoarseObservable π.policy},
        ⨆ i : Index k, (cost π.val (family k i) : ENNReal) ∧
    ((8*k+18 : Nat) : ENNReal) ≤
      ∫⁻ ω, (⨆ i : Index k, (cost (c ω) (family k i) : ENNReal)) ∂μ := by
  classical
  let n := 8*k+16
  let R := ⨆ i : Index k, ∫⁻ ω, (cost (c ω) (family k i) : ENNReal) ∂μ
  have facts := FourExitRawDomination.result k hk
  have floor (ω : Ω) (i : Index k) : n ≤ cost (c ω) (family k i) :=
    (facts.2.2.2 (c ω)).1 i
  have average (H : Finset (Index k)) (a m : Nat) (positive : 0 < m)
      (size : H.card = m)
      (lower : ∀ ω, a ≤ ∑ i ∈ H, (cost (c ω) (family k i) - n)) :
      (n : ENNReal) + (a : ENNReal) / m ≤ R := by
    have pointwise (ω : Ω) : m*n+a ≤ ∑ i ∈ H, cost (c ω) (family k i) := by
      have split : (∑ i ∈ H, cost (c ω) (family k i)) =
          m*n + ∑ i ∈ H, (cost (c ω) (family k i) - n) := by
        calc
          _ = ∑ i ∈ H, (n + ((cost (c ω) (family k i) - n))) :=
            Finset.sum_congr rfl (fun i _ => by have h := floor ω i; omega)
          _ = _ := by rw [Finset.sum_add_distrib]; simp [size, mul_comm]
      rw [split]
      exact Nat.add_le_add_left (lower ω) _
    have cast_bound (ω : Ω) : ((m*n+a : Nat) : ENNReal) ≤
        ∑ i ∈ H, (cost (c ω) (family k i) : ENNReal) := by
      rw [← Nat.cast_sum]
      exact_mod_cast pointwise ω
    have integrated := MeasureTheory.lintegral_mono (μ := μ) cast_bound
    rw [MeasureTheory.lintegral_const,MeasureTheory.measure_univ,
      mul_one,MeasureTheory.lintegral_finsetSum H (fun i _ => measurable i)] at integrated
    have upper : (∑ i ∈ H, ∫⁻ ω, (cost (c ω) (family k i) : ENNReal) ∂μ) ≤
        (m : ENNReal)*R := by
      have bound := Finset.sum_le_sum (fun i (_ : i ∈ H) =>
        le_iSup (fun i : Index k => ∫⁻ ω, (cost (c ω) (family k i) : ENNReal) ∂μ) i)
      simpa [size,Finset.sum_const, nsmul_eq_mul] using bound
    have zero : (m : ENNReal) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt positive)
    have finite : (m : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top m
    apply (ENNReal.mul_le_mul_iff_right zero finite).mp
    rw [mul_add,ENNReal.mul_div_cancel zero finite]
    simpa only [Nat.cast_add,Nat.cast_mul] using integrated.trans upper
  let H₁ : Finset (Index k) :=
    (((Finset.univ : Finset (Fin k)) ×ˢ (Finset.univ : Finset (Fin 4))).image Sum.inr)
  let H₂ : Finset (Index k) :=
    (((Finset.univ : Finset (Fin k)) ×ˢ
      ((Finset.univ : Finset (Fin 4)).erase 2)).image Sum.inr)
  have size₁ : H₁.card = 4*k := by
    rw [Finset.card_image_of_injective _ Sum.inr_injective,Finset.card_product]
    simp [mul_comm]
  have size₂ : H₂.card = 3*k := by
    rw [Finset.card_image_of_injective _ Sum.inr_injective,Finset.card_product]
    simp [mul_comm]
  have one := average H₁ (5*k-1) (4*k) (by omega) size₁
    (fun ω => (controller_subset_bounds k hk (c ω) (observable ω)).1)
  have two := average H₂ (4*k-2) (3*k) (by omega) size₂
    (fun ω => (controller_subset_bounds k hk (c ω) (observable ω)).2.1)
  have deterministic (π : Strategy) (obs : CoarseObservable π.policy) :
      ∃ i : Index k, 8*k+18 ≤ cost π (family k i) :=
    (controller_subset_bounds k hk π obs).2.2
  have worst (π : Strategy) (obs : CoarseObservable π.policy) :
      ((8*k+18 : Nat) : ENNReal) ≤ ⨆ i : Index k, (cost π (family k i) : ENNReal) := by
    obtain ⟨i,hi⟩ := deterministic π obs
    exact le_iSup_of_le i (by exact_mod_cast hi)
  refine ⟨one,two,deterministic,le_iInf (fun π => worst π.val π.property),?_⟩
  have integrated := MeasureTheory.lintegral_mono (μ := μ) (fun ω => worst (c ω) (observable ω))
  simpa only [MeasureTheory.lintegral_const,MeasureTheory.measure_univ,mul_one] using integrated

end D5.S3.Arith.FibonacciAtomic.FourExitCoarseLowerBounds
