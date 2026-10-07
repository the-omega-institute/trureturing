/- GID: D5/S3/Arith/FibonacciAtomic/CoarseEndpointPeeling
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/CoarseEndpointPeeling
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Merged nonleaf peeling characterizes actual coarse endpoint controllers. -/

import D5.S3.Arith.FibonacciAtomic.Scale38NestedCompensation
import D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.CoarseEndpointPeeling

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition
open ActualCoarseReadoutHistory (kappa kappa_hist shared_history_obstruction)
open ActualCoarseReadoutCompletion (compileRaw encodeHistory cachedExecute completion_contract)
open ActualJointResponseCostCore (controllerPolicy)
open ActualImageSevenLeafSeparation (leafLabel leafAddresses Nonconflict seven_leaf_separation)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute fiber)
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
  (PassiveProtocol runPassiveProtocol)

local notation "CH" => Hist (fun _ : Address => Option Bool)
local notation "RH" => Hist (fun _ : Address => Reply)
local notation "CoarseObservable" => fun p => Function.FactorsThrough p kappa_hist
local notation "read" => fun {m : Nat} (F : Fin m → Source) (q : Address) (i : Fin m) =>
  leafLabel (F i) q

/-- Keep the target in the survivor set. Branch and absent form one group,
whose cardinality is at most one at every target-leaf request. -/
noncomputable def Peels {m : Nat} (F : Fin m → Source) (z : Fin m) :
    Finset (Fin m) → List Address → Prop
  | S, [] => S ⊆ {z}
  | S, q :: qs => q ∈ leaves (F z) ∧
      (fiber (read F) S q none).card ≤ 1 ∧
      Peels F z (fiber (read F) S q (leafLabel (F z) q)) qs

/-- The finite coarse route stops at its first reply different from the target. -/
def peelRoute {m : Nat} (F : Fin m → Source) (z : Fin m) :
    List Address → PassiveProtocol Address (fun _ => Option Bool)
  | [] => .stop
  | q :: qs => .query q (fun y =>
      if y = leafLabel (F z) q then peelRoute F z qs else .stop)

/-- Decode a reached nonleaf singleton or the target at the end of the route.
Malformed or non-singleton replies select the existing acquisition fallback. -/
noncomputable def peelDecode {m : Nat} (F : Fin m → Source) (z : Fin m) :
    Finset (Fin m) → List Address → CH → Option (Fin m)
  | _, [], _ => some z
  | S, q :: qs, a :: h =>
      if a.1 = q then
        if a.2 = leafLabel (F z) q then
          peelDecode F z (fiber (read F) S q a.2) qs h
        else if unique : ∃ i, fiber (read F) S q a.2 = {i} then
          some (Classical.choose unique)
        else none
      else none
  | _, _ :: _, [] => none


/-- Coarse endpoint costs are equivalent to merged-nonleaf safe peeling. Every
safe list compiles to a globally correct coarse strategy with exact paid sets. -/
theorem result (k : Nat) (hk : 1 ≤ k) :
    let m := Fintype.card (Unit ⊕ (Fin k ⊕ Fin k))
    let e := Fintype.equivFin (Unit ⊕ (Fin k ⊕ Fin k))
    let F := Scale38NestedCompensation.family k ∘ e.symm
    ∀ z : Fin m,
      ((∃ π : Strategy, CoarseObservable π.policy ∧
        ∀ i, cost π (F i) = 3*k+14 - (if i = z then 1 else 0)) ↔
        ∃ qs : List Address, Peels F z Finset.univ qs) ∧
      (∀ qs : List Address, Peels F z Finset.univ qs → ∃ π : Strategy,
        π.policy = (fun h => controllerPolicy
          (compileRaw F (peelDecode F z Finset.univ qs) (peelRoute F z qs) [])
          (encodeHistory (kappa_hist h))) ∧ CoarseObservable π.policy ∧
        (∀ i, cost π (F i) = 3*k+14 - (if i = z then 1 else 0)) ∧
        paid (terminal π (F z)).1 = leafAddresses (F z) ∧
        ∀ i, i ≠ z → ∃ q,
          qs.find? (fun a => decide (leafLabel (F i) a = none)) = some q ∧
          q ∉ leafAddresses (F i) ∧
          paid (terminal π (F i)).1 = leafAddresses (F i) ∪ {q}) := by
  classical
  dsimp only
  let m := Fintype.card (Unit ⊕ (Fin k ⊕ Fin k))
  let e : (Unit ⊕ (Fin k ⊕ Fin k)) ≃ Fin m := Fintype.equivFin _
  let F : Fin m → Source := Scale38NestedCompensation.family k ∘ e.symm
  have foundation := Scale38NestedCompensation.result k hk
  have positive (i : Fin m) : Positive (F i) :=
    ⟨Scale38NestedCompensation.preFamily k (e.symm i), (foundation.2.1 (e.symm i)).2.1⟩
  have injective : Function.Injective F := foundation.1.comp e.symm.injective
  have nc (i j : Fin m) : Nonconflict (F i) (F j) :=
    foundation.2.2.2.1 (e.symm i) (e.symm j)
  have leaf_card (i : Fin m) : (leafAddresses (F i)).card = 3*k+13 :=
    (foundation.2.1 (e.symm i)).2.2.2.2.2
  have leaf_iff (W : Source) (q : Address) :
      q ∈ leafAddresses W ↔ leafLabel W q ≠ none := by
    rw [(seven_leaf_separation.1 W).2 q]
    exact Option.ne_none_iff_exists'.symm
  have matching (q : Address) (i j : Fin m)
      (hi : leafLabel (F i) q ≠ none) (hj : leafLabel (F j) q ≠ none) :
      leafLabel (F i) q = leafLabel (F j) q := by
    obtain ⟨a,ha⟩ := Option.ne_none_iff_exists'.mp hi
    obtain ⟨b,hb⟩ := Option.ne_none_iff_exists'.mp hj
    rw [ha,hb]
    exact congrArg some (((seven_leaf_separation.2.1 (F i) (F j)).2.2.mp
      (nc i j)) q a b ha hb)
  intro z
  have route_bills : ∀ S qs, Peels F z S qs → ∀ i ∈ S,
      let t := runPassiveProtocol (fun q W => leafLabel W q) (peelRoute F z qs) (F i)
      peelDecode F z S qs t = some i ∧
      (t.map Sigma.fst).toFinset ∪ leafAddresses (F i) =
        leafAddresses (F i) ∪ (qs.find? (fun q => decide (leafLabel (F i) q = none))).toFinset ∧
      ((qs.find? (fun q => decide (leafLabel (F i) q = none))) = none ↔ i = z) := by
    intro S qs
    induction qs generalizing S with
    | nil =>
      intro hp i hi
      have eq : i = z := Finset.mem_singleton.mp (hp hi)
      subst i
      simp [peelRoute,peelDecode,runPassiveProtocol]
    | cons q qs ih =>
      intro hp i hi
      obtain ⟨hq,hcount,htail⟩ := hp
      have target : leafLabel (F z) q ≠ none :=
        (leaf_iff (F z) q).mp (List.mem_toFinset.mpr hq)
      by_cases nonleaf : leafLabel (F i) q = none
      · have different : leafLabel (F i) q ≠ leafLabel (F z) q := by
          rw [nonleaf]; exact Ne.symm target
        have member : i ∈ fiber (read F) S q none := by simp [fiber,hi,nonleaf]
        have unique : ∃ j, fiber (read F) S q (leafLabel (F i) q) = {j} := by
          refine ⟨i,?_⟩
          rw [nonleaf]
          exact Finset.eq_singleton_iff_unique_mem.mpr
            ⟨member,fun j hj => Finset.card_le_one.mp hcount j hj i member⟩
        have chosen : Classical.choose unique = i := by
          have mem : i ∈ ({Classical.choose unique} : Finset (Fin m)) := by
            rw [← Classical.choose_spec unique,nonleaf]; exact member
          exact (Finset.mem_singleton.mp mem).symm
        have ne : i ≠ z := by intro eq; subst i; exact target nonleaf
        simp only [peelRoute,runPassiveProtocol,different,↓reduceIte,peelDecode,
          unique,↓reduceDIte,chosen]
        simp [nonleaf,List.find?,ne,Finset.union_singleton]
      · have eq := matching q i z nonleaf target
        have member : i ∈ fiber (read F) S q (leafLabel (F z) q) := by
          simp [fiber,hi,eq]
        obtain ⟨decoded,bill,exit⟩ := ih _ htail i member
        have leaf : q ∈ leafAddresses (F i) := (leaf_iff (F i) q).mpr nonleaf
        simp only [peelRoute,runPassiveProtocol,eq,↓reduceIte,peelDecode,
          List.map_cons,List.toFinset_cons,List.find?,target,decide_false]
        refine ⟨decoded,?_,exit⟩
        rw [Finset.insert_union,bill]
        exact Finset.insert_eq_of_mem (Finset.mem_union_left _ leaf)
  have realize (qs : List Address) (hp : Peels F z Finset.univ qs) :
      ∃ π : Strategy,
        π.policy = (fun h => controllerPolicy
          (compileRaw F (peelDecode F z Finset.univ qs) (peelRoute F z qs) [])
          (encodeHistory (kappa_hist h))) ∧ CoarseObservable π.policy ∧
        (∀ i, cost π (F i) = 3*k+14 - (if i = z then 1 else 0)) ∧
        paid (terminal π (F z)).1 = leafAddresses (F z) ∧
        ∀ i, i ≠ z → ∃ q,
          qs.find? (fun a => decide (leafLabel (F i) a = none)) = some q ∧
          q ∉ leafAddresses (F i) ∧
          paid (terminal π (F i)).1 = leafAddresses (F i) ∪ {q} := by
    obtain ⟨π,policy,observable,_,_,_,_,complete⟩ :=
      completion_contract m F positive (peelRoute F z qs) (peelDecode F z Finset.univ qs)
    have routed (i : Fin m) := route_bills Finset.univ qs hp i (Finset.mem_univ i)
    have bills (i : Fin m) : paid (terminal π (F i)).1 =
        leafAddresses (F i) ∪
          (qs.find? (fun q => decide (leafLabel (F i) q = none))).toFinset :=
      (complete i (routed i).1).2.trans (routed i).2.1
    have exits (i : Fin m) (ne : i ≠ z) : ∃ q,
        qs.find? (fun a => decide (leafLabel (F i) a = none)) = some q ∧
        q ∉ leafAddresses (F i) ∧
        paid (terminal π (F i)).1 = leafAddresses (F i) ∪ {q} := by
      cases he : qs.find? (fun a => decide (leafLabel (F i) a = none)) with
      | none => exact False.elim (ne ((routed i).2.2.mp he))
      | some q =>
        have hn : leafLabel (F i) q = none := of_decide_eq_true
          (List.find?_some (p := fun a : Address => decide (leafLabel (F i) a = none)) he)
        exact ⟨q,rfl,fun h => (leaf_iff (F i) q).mp h hn,
          by simpa only [he,Option.toFinset_some] using bills i⟩
    have target : paid (terminal π (F z)).1 = leafAddresses (F z) := by
      simpa only [(routed z).2.2.mpr rfl,Option.toFinset_none,Finset.union_empty] using bills z
    have costs (i : Fin m) : cost π (F i) = 3*k+14 - (if i = z then 1 else 0) := by
      by_cases eq : i = z
      · subst i
        change (paid (terminal π (F z)).1).card = _
        rw [target,leaf_card z]
        simp
      · obtain ⟨q,_,hn,hbill⟩ := exits i eq
        change (paid (terminal π (F i)).1).card = _
        rw [hbill,Finset.union_singleton,Finset.card_insert_of_notMem hn,leaf_card i]
        simp only [if_neg eq,Nat.sub_zero]
    exact ⟨π,policy,observable,costs,target,exits⟩
  refine ⟨⟨?_,?_⟩,realize⟩
  · rintro ⟨π,observable,hcost⟩
    have actual (i : Fin m) : execute readout π.policy
        (Classical.choose (π.correct (F i))) [] (F i) = some (terminal π (F i)) :=
      (Classical.choose_spec (Classical.choose_spec (π.correct (F i)))).1
    have compulsory (i : Fin m) : leafAddresses (F i) ⊆ paid (terminal π (F i)).1 :=
      source_foundation.2.2.2.2.1 π (F i) (positive i)
    have excess (i : Fin m) :
        (paid (terminal π (F i)).1 \ leafAddresses (F i)).card ≤ 1 := by
      have count := Finset.card_sdiff_add_card_eq_card (compulsory i)
      change _ + (leafAddresses (F i)).card = cost π (F i) at count
      rw [leaf_card i,hcost i] at count
      split_ifs at count <;> omega
    have target_paid : paid (terminal π (F z)).1 = leafAddresses (F z) := by
      apply (Finset.eq_of_subset_of_card_le (compulsory z) ?_).symm
      change cost π (F z) ≤ _
      rw [hcost z,leaf_card z]
      simp
    have next_prefix (W : Source) (q : Address) (h₀ : RH)
        (action : π.policy h₀ = .inl q) :
        ∀ (n : Nat) (a t : RH) (b : Bool) (g : CH),
        execute readout π.policy n a W = some (t,b) →
        g.IsPrefix (kappa_hist t) →
        kappa_hist h₀ = kappa_hist a ++ g →
        (g ++ [(⟨q,leafLabel W q⟩ : Sigma (fun _ : Address => Option Bool))]).IsPrefix
          (kappa_hist t) := by
      intro n
      induction n with
      | zero => intro a t b g run; simp [execute] at run
      | succ n ih =>
        intro a t b g run pre same
        cases step : π.policy a with
        | inr c =>
          simp only [execute,step,Option.some.injEq,Prod.mk.injEq] at run
          rcases run with ⟨rfl,rfl⟩
          have empty : g = [] := List.prefix_nil.mp pre
          subst g
          have eq := observable (by simpa only [List.append_nil] using same)
          rw [action,step] at eq
          cases eq
        | inl r =>
          simp only [execute,step,Option.map_eq_some_iff] at run
          obtain ⟨⟨t',b'⟩,run,eq⟩ := run
          cases eq
          cases g with
          | nil =>
            have eq := observable (by simpa only [List.append_nil] using same)
            have rq : r = q := (Sum.inl.inj (step.symm.trans (eq.symm.trans action)))
            subst r
            exact ⟨kappa_hist t',rfl⟩
          | cons c g =>
            obtain ⟨head,tail⟩ := List.cons_prefix_cons.mp pre
            subst c
            have same' : kappa_hist h₀ =
                kappa_hist (a ++ [⟨r,readout r W⟩]) ++ g := by
              simpa only [kappa_hist,List.map_append,List.map_cons,List.map_nil,
                List.append_assoc,List.singleton_append] using same
            have after := ih _ _ _ g run tail same'
            exact List.cons_prefix_cons.mpr ⟨rfl,after⟩
    have extend (i : Fin m) (h : RH) (q : Address)
        (pre : (kappa_hist h).IsPrefix (kappa_hist (terminal π (F i)).1))
        (action : π.policy h = .inl q) :
        (kappa_hist h ++ [(⟨q,leafLabel (F i) q⟩ :
          Sigma (fun _ : Address => Option Bool))]).IsPrefix
          (kappa_hist (terminal π (F i)).1) :=
      next_prefix (F i) q h action _ [] _ _ (kappa_hist h) (actual i) pre rfl
    have extract : ∀ (n : Nat) (h t : RH) (b : Bool) (S : Finset (Fin m)),
        execute readout π.policy n h (F z) = some (t,b) →
        (terminal π (F z)).1 = h ++ t →
        (∀ i ∈ S, (kappa_hist h).IsPrefix (kappa_hist (terminal π (F i)).1)) →
        Peels F z S (t.map Sigma.fst) := by
      intro n
      induction n with
      | zero => intro h t b S run; simp [execute] at run
      | succ n ih =>
        intro h t b S run full prefixes
        cases step : π.policy h with
        | inr c =>
          simp only [execute,step,Option.some.injEq,Prod.mk.injEq] at run
          rcases run with ⟨rfl,rfl⟩
          change S ⊆ {z}
          intro i hi
          apply Finset.mem_singleton.mpr
          by_contra ne
          have sameZ : kappa_hist (terminal π (F z)).1 = kappa_hist h := by
            rw [full,List.append_nil]
          obtain ⟨s,q,hz,_,_,_,_,_⟩ := shared_history_obstruction π observable
            (F z) (F i) (positive z) (positive i)
            (fun eq => ne (injective eq).symm) (nc z i) (kappa_hist h)
            (by rw [sameZ]) (prefixes i hi)
          rw [sameZ] at hz
          have length := List.IsPrefix.length_le hz
          simp only [List.length_append,List.length_singleton] at length
          omega
        | inl q =>
          simp only [execute,step,Option.map_eq_some_iff] at run
          obtain ⟨⟨t',b'⟩,run,eq⟩ := run
          cases eq
          have leaf : q ∈ leafAddresses (F z) := by
            rw [← target_paid]
            simp [paid,full]
          have target : leafLabel (F z) q ≠ none := (leaf_iff (F z) q).mp leaf
          have group : (fiber (read F) S q none).card ≤ 1 := by
            apply Finset.card_le_one.mpr
            intro i hi j hj
            by_contra ne
            simp only [fiber,Finset.mem_filter] at hi hj
            obtain ⟨hiS,hiN⟩ := hi
            obtain ⟨hjS,hjN⟩ := hj
            let g : CH := kappa_hist h ++ [⟨q,none⟩]
            have preI : g.IsPrefix (kappa_hist (terminal π (F i)).1) := by
              simpa only [g,hiN] using extend i h q (prefixes i hiS) step
            have preJ : g.IsPrefix (kappa_hist (terminal π (F j)).1) := by
              simpa only [g,hjN] using extend j h q (prefixes j hjS) step
            obtain ⟨_,_,_,_,_,_,_,obstruction⟩ := shared_history_obstruction π observable
              (F i) (F j) (positive i) (positive j) (fun eq => ne (injective eq))
              (nc i j) g preI preJ
            have paidQ : q ∈ (g.map Sigma.fst).toFinset := by simp [g]
            have nonleafI : q ∉ leafAddresses (F i) :=
              fun hq => (leaf_iff (F i) q).mp hq hiN
            have nonleafJ : q ∉ leafAddresses (F j) :=
              fun hq => (leaf_iff (F j) q).mp hq hjN
            have bad := obstruction ⟨⟨q,Finset.mem_sdiff.mpr ⟨paidQ,nonleafI⟩⟩,
              ⟨q,Finset.mem_sdiff.mpr ⟨paidQ,nonleafJ⟩⟩⟩
            have boundI := excess i
            have boundJ := excess j
            omega
          simp only [List.map_cons,Peels]
          refine ⟨List.mem_toFinset.mp leaf,group,?_⟩
          apply ih (h ++ [⟨q,readout q (F z)⟩]) t' b' _ run
          · simpa only [List.append_assoc,List.singleton_append] using full
          · intro i hi
            simp only [fiber,Finset.mem_filter] at hi
            obtain ⟨his,matchLabel⟩ := hi
            simpa only [kappa_hist,List.map_append,List.map_cons,List.map_nil,
              show kappa (readout q (F z)) = leafLabel (F z) q from rfl,matchLabel] using
              extend i h q (prefixes i his) step
    exact ⟨((terminal π (F z)).1.map Sigma.fst),extract _ [] _ _ Finset.univ (actual z)
      rfl (fun _ _ => List.nil_prefix)⟩
  · rintro ⟨qs,hqs⟩
    obtain ⟨π,_,observable,hcost,_⟩ := realize qs hqs
    exact ⟨π,observable,hcost⟩

end D5.S3.Arith.FibonacciAtomic.CoarseEndpointPeeling
