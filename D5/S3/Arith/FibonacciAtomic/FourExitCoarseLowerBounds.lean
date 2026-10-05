/- GID: D5/S3/Arith/FibonacciAtomic/FourExitCoarseLowerBounds
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/FourExitCoarseLowerBounds
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Coarse actual-tree executions and the two four-exit subset potentials. -/

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

private theorem controller_two_excess (k : Nat) (hk : 1 ≤ k)
    (π : Strategy) (observable : CoarseObservable π.policy) :
    ∃ i : Index k, 8 * k + 18 ≤ cost π (family k i) := by
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
  exact loop N [] (fun i _ => by simpa only [List.nil_append] using initial i)

end D5.S3.Arith.FibonacciAtomic.FourExitCoarseLowerBounds
