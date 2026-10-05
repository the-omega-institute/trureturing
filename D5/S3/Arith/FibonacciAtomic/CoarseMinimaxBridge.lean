/- GID: D5/S3/Arith/FibonacciAtomic/CoarseMinimaxBridge
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/CoarseMinimaxBridge
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Query pruning yields a coarse endpoint and the universal two-excess lower bound. -/

import D5.S3.Arith.FibonacciAtomic.CoarseEndpointSpectrum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.CoarseMinimaxBridge

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition
  (Address Reply readout leaves Strategy cost paid terminal Positive)
open ActualImageSevenLeafSeparation (leafLabel leafAddresses Nonconflict seven_leaf_separation)
open ActualCoarseReadoutHistory (kappa kappa_hist CoarseObservable shared_history_obstruction)
open CoarseEndpointPeeling (Peels)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute fiber)

local notation "Index" => fun k : Nat => Unit ⊕ (Fin k ⊕ Fin k)
local notation "RH" => Hist (fun _ : Address => Reply)
local notation "CH" => Hist (fun _ : Address => Option Bool)
local notation "read" => fun {m : Nat} (F : Fin m → Source) (q : Address) (i : Fin m) =>
  leafLabel (F i) q

/-- Every uniformly one-excess coarse controller yields a safe actual peeling
list. Consequently every coarse strategy incurs at least two excess queries
on some member of every family of size parameter at least three. -/
theorem result (k : Nat) (hk : 1 ≤ k) :
    let m := Fintype.card (Index k)
    let e := Fintype.equivFin (Index k)
    let F := Scale38NestedCompensation.family k ∘ e.symm
    (∀ π : Strategy, CoarseObservable π.policy →
      (∀ i, cost π (F i) ≤ 3*k+14) →
      ∃ (z : Fin m) (qs : List Address), Peels F z Finset.univ qs) ∧
    (3 ≤ k → ∀ π : Strategy, CoarseObservable π.policy →
      ∃ i : Fin m, 3*k+15 ≤ cost π (F i)) := by
  classical
  dsimp only
  let m := Fintype.card (Index k)
  let e : Index k ≃ Fin m := Fintype.equivFin _
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
  have bridge (π : Strategy) (observable : CoarseObservable π.policy)
      (bound : ∀ i, cost π (F i) ≤ 3*k+14) :
      ∃ (z : Fin m) (qs : List Address), Peels F z Finset.univ qs := by
    have excess (i : Fin m) :
        (paid (terminal π (F i)).1 \ leafAddresses (F i)).card ≤ 1 := by
      have compulsory := ActualTreeReadoutAcquisition.source_foundation.2.2.2.2.1
        π (F i) (positive i)
      have count := Finset.card_sdiff_add_card_eq_card compulsory
      change (paid (terminal π (F i)).1 \ leafAddresses (F i)).card +
        (leafAddresses (F i)).card = cost π (F i) at count
      rw [leaf_card i] at count
      have budget := bound i
      omega
    have extract : ∀ (N : Nat) (g : CH) (H T : Fin m → RH)
        (B : Fin m → Bool) (S : Finset (Fin m)),
        S.Nonempty →
        (∀ i ∈ S, kappa_hist (H i) = g) →
        (∀ i ∈ S, (terminal π (F i)).1 = H i ++ T i) →
        (∀ i ∈ S, ∃ n ≤ N,
          execute readout π.policy n (H i) (F i) = some (T i,B i)) →
        ∃ z ∈ S, ∃ qs : List Address,
          Peels F z S qs ∧ qs.Sublist ((T z).map Sigma.fst) := by
      intro N
      induction N with
      | zero =>
        intro g H T B S nonempty common full runs
        obtain ⟨a,ha⟩ := nonempty
        obtain ⟨n,hn,run⟩ := runs a ha
        have zero : n = 0 := by omega
        simp only [zero,execute,reduceCtorEq] at run
      | succ N ih =>
        intro g H T B S nonempty common full runs
        obtain ⟨a,ha⟩ := nonempty
        by_cases small : S.card ≤ 1
        · refine ⟨a,ha,[],?_,List.nil_sublist _⟩
          change S ⊆ {a}
          intro i hi
          exact Finset.mem_singleton.mpr (Finset.card_le_one.mp small i hi a ha)
        have large : 1 < S.card := by omega
        have action (i : Fin m) (hi : i ∈ S) : π.policy (H i) = π.policy (H a) :=
          observable _ _ ((common i hi).trans (common a ha).symm)
        cases step : π.policy (H a) with
        | inr c =>
          have stopped (i : Fin m) (hi : i ∈ S) : T i = [] := by
            obtain ⟨n,_,run⟩ := runs i hi
            cases n with
            | zero => simp [execute] at run
            | succ n =>
              have act := (action i hi).trans step
              simp only [execute,act,Option.some.injEq,Prod.mk.injEq] at run
              exact run.1.symm
          obtain ⟨i,hi,j,hj,ne⟩ := Finset.one_lt_card.mp large
          have endI : kappa_hist (terminal π (F i)).1 = g := by
            rw [full i hi,stopped i hi,List.append_nil,common i hi]
          have endJ : kappa_hist (terminal π (F j)).1 = g := by
            rw [full j hj,stopped j hj,List.append_nil,common j hj]
          obtain ⟨s,q,pre,_,_,_,_,_⟩ := shared_history_obstruction π observable
            (F i) (F j) (positive i) (positive j)
            (fun eq => ne (injective eq)) (nc i j) g
            (by rw [endI]) (by rw [endJ])
          rw [endI] at pre
          have length := pre.length_le
          simp only [List.length_append,List.length_singleton] at length
          omega
        | inl q =>
          let H' : Fin m → RH := fun i => H i ++ [⟨q,readout q (F i)⟩]
          let T' : Fin m → RH := fun i => (T i).tail
          have continued (i : Fin m) (hi : i ∈ S) :
              T i = (⟨q,readout q (F i)⟩ : Sigma (fun _ : Address => Reply)) :: T' i ∧
              ∃ n ≤ N, execute readout π.policy n (H' i) (F i) = some (T' i,B i) := by
            obtain ⟨n,hn,run⟩ := runs i hi
            cases n with
            | zero => simp [execute] at run
            | succ n =>
              have act := (action i hi).trans step
              simp only [execute,act,Option.map_eq_some_iff] at run
              obtain ⟨⟨t,b⟩,tailrun,eq⟩ := run
              have trace : T i = ⟨q,readout q (F i)⟩ :: t :=
                (congrArg Prod.fst eq).symm
              have label : b = B i := congrArg Prod.snd eq
              have tail : T' i = t := by simp only [T',trace,List.tail_cons]
              refine ⟨?_,n,by omega,?_⟩
              · rw [tail]; exact trace
              · simpa only [H',tail,label] using tailrun
          have full' (i : Fin m) (hi : i ∈ S) :
              (terminal π (F i)).1 = H' i ++ T' i := by
            rw [full i hi,(continued i hi).1]
            simp only [H',List.append_assoc,List.singleton_append]
          have nextPrefix (i : Fin m) (hi : i ∈ S) :
              (g ++ [(⟨q,leafLabel (F i) q⟩ :
                Sigma (fun _ : Address => Option Bool))]).IsPrefix
                (kappa_hist (terminal π (F i)).1) := by
            rw [full' i hi]
            refine ⟨kappa_hist (T' i),?_⟩
            simp only [H',kappa_hist,List.map_append,List.map_cons,List.map_nil]
            change _ = kappa_hist (H i) ++ _ ++ _
            rw [common i hi]
            rfl
          have group : (fiber (read F) S q none).card ≤ 1 := by
            apply Finset.card_le_one.mpr
            intro i hi j hj
            by_contra ne
            simp only [fiber,Finset.mem_filter] at hi hj
            obtain ⟨his,hin⟩ := hi
            obtain ⟨hjs,hjn⟩ := hj
            let next : CH := g ++ [⟨q,none⟩]
            have preI : next.IsPrefix (kappa_hist (terminal π (F i)).1) := by
              simpa only [next,hin] using nextPrefix i his
            have preJ : next.IsPrefix (kappa_hist (terminal π (F j)).1) := by
              simpa only [next,hjn] using nextPrefix j hjs
            obtain ⟨_,_,_,_,_,_,_,bad⟩ := shared_history_obstruction π observable
              (F i) (F j) (positive i) (positive j)
              (fun eq => ne (injective eq)) (nc i j) next preI preJ
            have qpaid : q ∈ (next.map Sigma.fst).toFinset := by simp [next]
            have nqi : q ∉ leafAddresses (F i) :=
              fun hq => (leaf_iff (F i) q).mp hq hin
            have nqj : q ∉ leafAddresses (F j) :=
              fun hq => (leaf_iff (F j) q).mp hq hjn
            have contradiction := bad
              ⟨⟨q,Finset.mem_sdiff.mpr ⟨qpaid,nqi⟩⟩,
               ⟨q,Finset.mem_sdiff.mpr ⟨qpaid,nqj⟩⟩⟩
            have ei := excess i
            have ej := excess j
            omega
          have leafExists : ∃ j ∈ S, leafLabel (F j) q ≠ none := by
            by_contra absent
            push Not at absent
            have eq : fiber (read F) S q none = S := by
              ext i
              simp only [fiber,Finset.mem_filter]
              exact ⟨And.left,fun hi => ⟨hi,absent i hi⟩⟩
            rw [eq] at group
            omega
          obtain ⟨j,hj,hlabel⟩ := leafExists
          let S' := fiber (read F) S q (leafLabel (F j) q)
          have member : j ∈ S' := by simp [S',fiber,hj]
          have sub : S' ⊆ S := by
            intro i hi
            simp only [S',fiber,Finset.mem_filter] at hi
            exact hi.1
          have common' (i : Fin m) (hi : i ∈ S') :
              kappa_hist (H' i) =
                g ++ [(⟨q,leafLabel (F j) q⟩ : Sigma (fun _ : Address => Option Bool))] := by
            simp only [S',fiber,Finset.mem_filter] at hi
            obtain ⟨his,hisame⟩ := hi
            simp only [H',kappa_hist,List.map_append,List.map_cons,List.map_nil]
            change kappa_hist (H i) ++ _ = _
            rw [common i his]
            change g ++ [(⟨q,leafLabel (F i) q⟩ :
              Sigma (fun _ : Address => Option Bool))] = _
            rw [hisame]
          obtain ⟨z,hz,qs,safe,sublist⟩ := ih
            (g ++ [⟨q,leafLabel (F j) q⟩]) H' T' B S' ⟨j,member⟩ common'
            (fun i hi => full' i (sub hi)) (fun i hi => (continued i (sub hi)).2)
          have target : leafLabel (F z) q = leafLabel (F j) q := by
            have memberZ := hz
            simp only [S',fiber,Finset.mem_filter] at memberZ
            exact memberZ.2
          by_cases constant : S' = S
          · refine ⟨z,sub hz,qs,?_,?_⟩
            · simpa only [constant] using safe
            · rw [(continued z (sub hz)).1,List.map_cons]
              exact sublist.cons _
          · refine ⟨z,sub hz,q :: qs,?_,?_⟩
            · change q ∈ leaves (F z) ∧ _ ∧ _
              refine ⟨List.mem_toFinset.mp ((leaf_iff (F z) q).mpr ?_),group,?_⟩
              · rw [target]; exact hlabel
              · simpa only [target] using safe
            · rw [(continued z (sub hz)).1,List.map_cons]
              exact sublist.cons_cons q
    let fuel : Fin m → Nat := fun i => Classical.choose (π.correct (F i))
    obtain ⟨z,_,qs,safe,_⟩ := extract (Finset.univ.sup fuel) [] (fun _ => [])
      (fun i => (terminal π (F i)).1) (fun i => (terminal π (F i)).2) Finset.univ
      ⟨e (.inl ()),Finset.mem_univ _⟩ (fun _ _ => rfl) (fun _ _ => rfl)
      (fun i hi => ⟨fuel i,Finset.le_sup hi,
        (Classical.choose_spec (Classical.choose_spec (π.correct (F i)))).1⟩)
    exact ⟨z,qs,safe⟩
  refine ⟨bridge,?_⟩
  intro big π observable
  by_contra low
  push Not at low
  have budget (i : Fin m) : cost π (F i) ≤ 3*k+14 := by
    have hi := low i
    change cost π (F i) < 3*k+15 at hi
    omega
  obtain ⟨z,qs,safe⟩ := bridge π observable budget
  have eligible := ((CoarseEndpointSpectrum.result k hk z).1).mp ⟨qs,safe⟩
  rcases eligible with one | ⟨two,_⟩ <;> omega

end D5.S3.Arith.FibonacciAtomic.CoarseMinimaxBridge
