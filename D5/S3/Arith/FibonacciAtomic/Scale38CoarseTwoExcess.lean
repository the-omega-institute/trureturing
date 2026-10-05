/- GID: D5/S3/Arith/FibonacciAtomic/Scale38CoarseTwoExcess
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Scale38CoarseTwoExcess
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual coarse nested-compensation scanning and exact two-excess bills. -/

import D5.S3.Arith.FibonacciAtomic.Scale38NestedCompensation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Scale38CoarseTwoExcess

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition
open ActualCoarseReadoutHistory (kappa kappa_hist CoarseObservable)
open ActualCoarseReadoutCompletion (compileRaw encodeHistory cachedExecute completion_contract)
open ActualJointResponseCostCore (controllerPolicy)
open ActualImageSevenLeafSeparation (leafLabel leafAddresses seven_leaf_separation A C)
open FourExitRawEndpointSpectrum (comb comb_slot_readout comb_tail_readout)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute)
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
  (PassiveProtocol runPassiveProtocol)
open Scale38NestedCompensation (family query stop route compatible)

local notation "Index" => fun k : Nat => Unit ⊕ (Fin k ⊕ Fin k)
local notation "CH" => Hist (fun _ : Address => Option Bool)
local notation "RH" => Hist (fun _ : Address => Reply)

/-- Zero-based t: the secondary literal address g_(t+1)=p_(t+1)LLLR. -/
def discriminator (t : Nat) : Address :=
  false :: (List.replicate t true ++ [false,false,false,false,true])

/-- A finite coarse scan; an interior first none triggers exactly one secondary query. -/
def scan (k : Nat) : List Nat → PassiveProtocol Address (fun _ => Option Bool)
  | [] => .stop
  | t :: ts => .query (query t) (fun y =>
      if y = some true then scan k ts
      else if y = none ∧ 0 < t ∧ t < k then
        .query (discriminator t) (fun _ => .stop)
      else .stop)

/-- Decode the first merged exception, using its secondary report only at interior slots. -/
def decode (k : Nat) : List Nat → CH → Option (Index k)
  | [], _ => some (.inl ())
  | t :: ts, a :: h =>
      if a.2 = some true then decode k ts h
      else if a.2 = none then
        if ht : t < k then
          if t = 0 then some (.inr (.inl ⟨t,ht⟩))
          else match h with
            | b :: _ =>
                if b.2 = some true then some (.inr (.inl ⟨t,ht⟩))
                else if b.2 = none then some (.inr (.inr ⟨t-1,by omega⟩))
                else none
            | [] => none
        else if ht : t = k ∧ 0 < k then
          some (.inr (.inr ⟨k-1,by omega⟩))
        else none
      else none
  | _ :: _, [] => none

/-- Secondary queries appended to the existing actually reached primary prefix. -/
def secondary (k : Nat) : Index k → List Address
  | .inl _ => []
  | .inr (.inl j) => if 0 < j.val then [discriminator j.val] else []
  | .inr (.inr i) => if i.val + 1 < k then [discriminator (i.val+1)] else []

local notation "extras" => fun k : Nat => Sum.elim (fun _ : Unit => (∅ : Finset Address))
  (Sum.elim (fun j : Fin k => {query j.val}) (fun i : Fin k =>
    if i.val+1 < k then {query (i.val+1),discriminator (i.val+1)} else {query (i.val+1)}))
local notation "excess" => fun k : Nat => Sum.elim (fun _ : Unit => (0 : Nat))
  (Sum.elim (fun _ : Fin k => 1) (fun i : Fin k => if i.val+1 < k then 2 else 1))

/-- An interior first merged exception has exactly two surviving rows, separated by one literal request. -/
theorem result (k : Nat) (hk : 1 ≤ k) :
    (∀ (t : Nat) (ht0 : 0 < t) (ht : t < k),
      (∀ i : Index k,
        (compatible k t i ∧ leafLabel (family k i) (query t) = none) ↔
          i = .inr (.inl ⟨t,ht⟩) ∨ i = .inr (.inr ⟨t-1,by omega⟩)) ∧
      readout (discriminator t) (family k (.inr (.inl ⟨t,ht⟩))) = .alpha ∧
      readout (discriminator t) (family k (.inr (.inr ⟨t-1,by omega⟩))) = .absent ∧
      readout (false :: (List.replicate t true ++ [false]))
        (family k (.inr (.inr ⟨t-1,by omega⟩))) = .beta ∧
      (∀ s : Nat, query s ≠ discriminator t)) ∧
    (∀ i : Index k,
      let h := runPassiveProtocol (fun q U => leafLabel U q) (scan k (List.range (k+1))) (family k i)
      decode k (List.range (k+1)) h = some i ∧
      h = (route k i ++ secondary k i).map (fun q => ⟨q,leafLabel (family k i) q⟩)) ∧
    ∃ π : Strategy,
      (let e : Index k ≃ Fin (Fintype.card (Index k)) := Fintype.equivFin (Index k)
       π.policy = fun h => controllerPolicy
         (compileRaw (family k ∘ e.symm)
           (fun h => (decode k (List.range (k+1)) h).map e)
           (scan k (List.range (k+1))) []) (encodeHistory (kappa_hist h))) ∧
      CoarseObservable π.policy ∧
      (∀ U : Source, ∃ (n : Nat) (t : RH) (b : Bool) (cache : RH),
        execute readout π.policy n [] U = some (t,b) ∧
        cachedExecute π.policy n [] [] U = some ((t,b),cache) ∧
        (t,b) = terminal π U ∧ (b = true ↔ Positive U) ∧
        (cache.map Sigma.fst).Nodup ∧
        (∀ a ∈ cache, a.2 = readout a.1 U) ∧ paid cache = paid t) ∧
      (∀ i : Index k,
        (route k i ++ secondary k i).Nodup ∧
        paid (terminal π (family k i)).1 = leafAddresses (family k i) ∪ extras k i ∧
        paid (terminal π (family k i)).1 \ leafAddresses (family k i) = extras k i ∧
        (∀ q ∈ extras k i,
          q ∈ (runPassiveProtocol (fun q U => leafLabel U q)
            (scan k (List.range (k+1))) (family k i)).map Sigma.fst ∧
          q ∉ leafAddresses (family k i)) ∧
        cost π (family k i) = 3*k+13 + excess k i) ∧
      (3 ≤ k → (∀ i : Index k, cost π (family k i) ≤ 3*k+15) ∧
        ∃ i : Index k, cost π (family k i) = 3*k+15) := by
  classical
  obtain ⟨hinj,rows,hcard,nc,base,xrow,yrow,survivors,raw,hd,qinj⟩ :=
    Scale38NestedCompensation.result k hk
  have gx (j : Fin k) : readout (discriminator j.val)
      (family k (.inr (.inl j))) = .alpha := by
    have supplied := comb_slot_readout k
      (fun l => if l = j then FourExitRawEndpointSpectrum.B else A) C j
      [false,false,false,true]
    simp only [ite_true] at supplied
    exact supplied.trans rfl
  have gy (i : Fin k) : readout (discriminator (i.val+1))
      (family k (.inr (.inr i))) = .absent := by
    have supplied := comb_tail_readout i.val (fun _ => A) C
      [true,false,false,false,false,true]
    change readout (List.replicate (i.val+1) true ++
      [false,false,false,false,true]) (comb i.val (fun _ => A) C) = .absent
    rw [List.replicate_add]
    simpa only [List.replicate_one,List.append_assoc,List.singleton_append] using
      supplied.trans (show readout [true,false,false,false,false,true] C = .absent from rfl)
  have contracted_leaf (i : Fin k) :
      readout (false :: (List.replicate (i.val+1) true ++ [false]))
        (family k (.inr (.inr i))) = .beta := by
    have supplied := comb_tail_readout i.val (fun _ => A) C [true,false]
    change readout (List.replicate (i.val+1) true ++ [false])
      (comb i.val (fun _ => A) C) = .beta
    rw [List.replicate_add]
    simpa only [List.replicate_one,List.append_assoc,List.singleton_append] using
      supplied.trans (show readout [true,false] C = .beta from rfl)
  have different (s t : Nat) : query s ≠ discriminator t := by
    intro eq
    have counts := congrArg (List.count false) eq
    simp [query,discriminator,List.count_replicate] at counts
  have pair (t : Nat) (ht0 : 0 < t) (ht : t < k) (i : Index k) :
      (compatible k t i ∧ leafLabel (family k i) (query t) = none) ↔
        i = .inr (.inl ⟨t,ht⟩) ∨ i = .inr (.inr ⟨t-1,by omega⟩) := by
    constructor
    · rintro ⟨hc,hn⟩
      have hs := (survivors t (by omega) i).mp hc
      cases i with
      | inl u =>
        cases u
        have supplied := base t (by omega)
        simp [leafLabel,supplied] at hn
      | inr p =>
        cases p with
        | inl j =>
          have le : t ≤ j.val := by simpa [stop] using hs
          have eq : t = j.val := by
            by_contra ne
            have supplied := (xrow j).1 t (by omega)
            simp [leafLabel,supplied] at hn
          left
          congr 2
          exact Fin.ext eq.symm
        | inr i =>
          have le : t ≤ i.val+1 := by simpa [stop] using hs
          have eq : t = i.val+1 := by
            by_contra ne
            have supplied := (yrow i).1 t (by omega)
            simp [leafLabel,supplied] at hn
          right
          congr 2
          apply Fin.ext
          simp only [Fin.val_mk]
          omega
    · rintro (rfl | rfl)
      · refine ⟨(survivors t (by omega) _).mpr (Or.inr (by simp [stop])),?_⟩
        simp [leafLabel,(xrow ⟨t,ht⟩).2]
      · refine ⟨(survivors t (by omega) _).mpr (Or.inr (by simp [stop]; omega)),?_⟩
        have eq : t-1+1 = t := by omega
        have supplied := (yrow ⟨t-1,by omega⟩).2
        simp only [Fin.val_mk,eq] at supplied
        simp [leafLabel,supplied]
  have interior_decode (t : Nat) (ht0 : 0 < t) (ht : t < k) (i : Index k)
      (hc : compatible k t i) (hn : leafLabel (family k i) (query t) = none)
      (ts : List Nat) :
      decode k (t :: ts) [⟨query t,none⟩,⟨discriminator t,leafLabel (family k i) (discriminator t)⟩] =
        some i := by
    rcases (pair t ht0 ht i).mp ⟨hc,hn⟩ with rfl | rfl
    · simp [decode,ht,show t ≠ 0 from by omega,leafLabel,gx ⟨t,ht⟩]
    · have supplied := gy ⟨t-1,by omega⟩
      simp only [Fin.val_mk,show t-1+1=t from by omega] at supplied
      simp [decode,ht,show t ≠ 0 from by omega,leafLabel,supplied]
  have advance (U : Source) : ∀ (pre ts : List Nat) (h : CH),
      (∀ s ∈ pre, leafLabel U (query s) = some true) →
      runPassiveProtocol (fun q W => leafLabel W q) (scan k (pre ++ ts)) U =
        pre.map (fun s => ⟨query s,some true⟩) ++
          runPassiveProtocol (fun q W => leafLabel W q) (scan k ts) U ∧
      decode k (pre ++ ts) (pre.map (fun s => ⟨query s,some true⟩) ++ h) = decode k ts h := by
    intro pre
    induction pre with
    | nil => intro ts h _; exact ⟨rfl,rfl⟩
    | cons t pre ih =>
      intro ts h ha
      have head := ha t List.mem_cons_self
      obtain ⟨run,decoded⟩ := ih ts h (fun s hs => ha s (List.mem_cons_of_mem t hs))
      constructor
      · simpa only [List.cons_append,List.map_cons,runPassiveProtocol,scan,head,
          ↓reduceIte] using congrArg (List.cons (⟨query t,some true⟩ : Sigma (fun _ : Address => Option Bool))) run
      · simpa only [List.cons_append,List.map_cons,decode,↓reduceIte] using decoded
  have range_split (t : Nat) (ht : t ≤ k) :
      List.range (k+1) = List.range t ++ t :: List.range' (t+1) (k-t) := by
    rw [List.range_eq_range',List.range_eq_range']
    have eq : k+1 = t + ((k-t)+1) := by omega
    rw [eq,← List.range'_append_1]
    simp only [Nat.zero_add,List.range'_succ]
  have routes (i : Index k) :
      let h := runPassiveProtocol (fun q U => leafLabel U q) (scan k (List.range (k+1))) (family k i)
      decode k (List.range (k+1)) h = some i ∧
      h = (route k i ++ secondary k i).map (fun q => ⟨q,leafLabel (family k i) q⟩) := by
    dsimp only
    cases i with
    | inl u =>
      cases u
      have ha (t : Nat) (ht : t ∈ List.range (k+1)) :
          leafLabel (family k (.inl ())) (query t) = some true := by
        simp [leafLabel,base t (by simpa using List.mem_range.mp ht)]
      obtain ⟨run,decoded⟩ := advance (family k (.inl ())) (List.range (k+1)) [] [] ha
      simp only [List.append_nil,scan,runPassiveProtocol,List.append_nil] at run decoded
      constructor
      · rw [run,decoded]; rfl
      · rw [run]
        simp only [route,stop,secondary,List.append_nil,List.map_map,Function.comp_def]
        apply List.map_congr_left
        intro t ht
        rw [ha t ht]
    | inr p =>
      cases p with
      | inl j =>
        have ha (t : Nat) (ht : t ∈ List.range j.val) :
            leafLabel (family k (.inr (.inl j))) (query t) = some true := by
          simp [leafLabel,(xrow j).1 t (List.mem_range.mp ht)]
        have hn : leafLabel (family k (.inr (.inl j))) (query j.val) = none := by
          simp [leafLabel,(xrow j).2]
        have hg : leafLabel (family k (.inr (.inl j))) (discriminator j.val) = some true := by
          simp [leafLabel,gx j]
        have hc : compatible k j.val (.inr (.inl j)) :=
          (survivors j.val (by omega) _).mpr (Or.inr (by simp [stop]))
        let ts := List.range' (j.val+1) (k-j.val)
        have split := range_split j.val (Nat.le_of_lt j.isLt)
        obtain ⟨pre_run,pre_decode⟩ := advance (family k (.inr (.inl j)))
          (List.range j.val) (j.val :: ts)
          (runPassiveProtocol (fun q W => leafLabel W q) (scan k (j.val :: ts))
            (family k (.inr (.inl j)))) ha
        rw [split]
        rw [pre_run,pre_decode]
        constructor
        · by_cases zero : j.val = 0
          · have hn0 := hn
            rw [zero] at hn0
            simp [scan,runPassiveProtocol,hn0,decode,zero,show 0<k from by omega,Fin.ext_iff]
          · have h0 : 0 < j.val := by omega
            have tail_run : runPassiveProtocol (fun q W => leafLabel W q)
                (scan k (j.val :: ts)) (family k (.inr (.inl j))) =
                [⟨query j.val,none⟩,⟨discriminator j.val,some true⟩] := by
              simp [scan,runPassiveProtocol,hn,h0,j.isLt,hg]
            rw [tail_run]
            simpa only [hg] using interior_decode j.val h0 j.isLt _ hc hn ts
        · simp only [route,stop,secondary,List.range_succ,List.map_append,
            List.map_cons,List.map_nil,List.map_map,Function.comp_def]
          rw [List.map_congr_left (fun t ht => congrArg
            (fun y : Option Bool => (⟨query t,y⟩ : Sigma (fun _ : Address => Option Bool))) (ha t ht))]
          by_cases zero : j.val = 0
          · have hn0 := hn
            rw [zero] at hn0
            simp [scan,runPassiveProtocol,hn0,zero]
          · have h0 : 0 < j.val := by omega
            simp [scan,runPassiveProtocol,hn,h0,j.isLt,hg]
      | inr i =>
        have ha (t : Nat) (ht : t ∈ List.range (i.val+1)) :
            leafLabel (family k (.inr (.inr i))) (query t) = some true := by
          simp [leafLabel,(yrow i).1 t (by have := List.mem_range.mp ht; omega)]
        have hn : leafLabel (family k (.inr (.inr i))) (query (i.val+1)) = none := by
          simp [leafLabel,(yrow i).2]
        have hg : leafLabel (family k (.inr (.inr i))) (discriminator (i.val+1)) = none := by
          simp [leafLabel,gy i]
        have hc : compatible k (i.val+1) (.inr (.inr i)) :=
          (survivors (i.val+1) (by omega) _).mpr (Or.inr (by simp [stop]))
        let ts := List.range' (i.val+2) (k-(i.val+1))
        have split := range_split (i.val+1) (by omega)
        obtain ⟨pre_run,pre_decode⟩ := advance (family k (.inr (.inr i)))
          (List.range (i.val+1)) ((i.val+1) :: ts)
          (runPassiveProtocol (fun q W => leafLabel W q) (scan k ((i.val+1) :: ts))
            (family k (.inr (.inr i)))) ha
        rw [split]
        rw [pre_run,pre_decode]
        constructor
        · by_cases interior : i.val+1 < k
          · have tail_run : runPassiveProtocol (fun q W => leafLabel W q)
                (scan k ((i.val+1) :: ts)) (family k (.inr (.inr i))) =
                [⟨query (i.val+1),none⟩,⟨discriminator (i.val+1),none⟩] := by
              simp [scan,runPassiveProtocol,hn,interior,hg]
            rw [tail_run]
            simpa only [hg] using interior_decode (i.val+1) (by omega) interior _ hc hn ts
          · have last : i.val+1=k := by omega
            have roweq : (⟨k-1,by omega⟩ : Fin k) = i := by apply Fin.ext; simp; omega
            have hnlast := hn
            rw [last] at hnlast
            simp [scan,runPassiveProtocol,hnlast,decode,last,roweq,show 0<k from by omega]
        · simp only [route,stop,secondary]
          rw [List.range_succ (n := i.val+1)]
          simp only [List.map_append,List.map_cons,List.map_nil,List.map_map,Function.comp_def]
          rw [List.map_congr_left (fun t ht => congrArg
            (fun y : Option Bool => (⟨query t,y⟩ : Sigma (fun _ : Address => Option Bool))) (ha t ht))]
          by_cases interior : i.val+1 < k
          · simp [scan,runPassiveProtocol,hn,interior,hg]
          · simp [scan,runPassiveProtocol,hn,interior]
  obtain ⟨rawπ,raw_policy,raw_terminal,raw_rows,raw_nonleaf,raw_cache⟩ := raw
  have primary_bill (i : Index k) :
      (route k i).toFinset ∪ leafAddresses (family k i) =
        leafAddresses (family k i) ∪ Scale38NestedCompensation.extra k i := by
    have supplied := (raw_rows i).2.1
    rw [raw_terminal,(raw_rows i).1] at supplied
    simp only [paid,List.map_append,List.toFinset_append,List.map_map,
      Function.comp_def] at supplied
    convert supplied using 1
    ext q
    simp [leafAddresses]
  have secondary_leaf (j : Fin k) : discriminator j.val ∈ leafAddresses (family k (.inr (.inl j))) :=
    ((seven_leaf_separation.1 _).2 _).mpr ⟨true,by simp [leafLabel,gx j]⟩
  have secondary_nonleaf (i : Fin k) :
      discriminator (i.val+1) ∉ leafAddresses (family k (.inr (.inr i))) := by
    rw [(seven_leaf_separation.1 _).2]
    simp [leafLabel,gy i]
  have extras_nonleaf (i : Index k) : ∀ q ∈ extras k i, q ∉ leafAddresses (family k i) := by
    cases i with
    | inl u => simp
    | inr p => cases p with
      | inl j =>
        intro q hq
        have eq : q = query j.val := Finset.mem_singleton.mp hq
        subst q
        exact raw_nonleaf _ (by simp)
      | inr i =>
        intro q hq
        dsimp only [Sum.elim] at hq
        split_ifs at hq with hi
        · rcases Finset.mem_insert.mp hq with rfl | hq
          · exact raw_nonleaf _ (by simp)
          · have eq : q = discriminator (i.val+1) := Finset.mem_singleton.mp hq
            subst q
            exact secondary_nonleaf i
        · have eq : q = query (i.val+1) := Finset.mem_singleton.mp hq
          subst q
          exact raw_nonleaf _ (by simp)
  have unique (i : Index k) : (route k i ++ secondary k i).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨List.Nodup.map qinj (List.nodup_range _),?_,?_⟩
    · cases i with
      | inl u => simp [secondary]
      | inr p => cases p <;> simp [secondary]
    · intro a ha b hb eq
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ha
      cases i with
      | inl u => simp [secondary] at hb
      | inr p => cases p with
        | inl j =>
          simp only [secondary] at hb
          split_ifs at hb with hj
          · have beq : b = discriminator j.val := List.mem_singleton.mp hb
            exact different s j.val (eq.trans beq)
          · simp at hb
        | inr i =>
          simp only [secondary] at hb
          split_ifs at hb with hi
          · have beq : b = discriminator (i.val+1) := List.mem_singleton.mp hb
            exact different s (i.val+1) (eq.trans beq)
          · simp at hb
  let e : Index k ≃ Fin (Fintype.card (Index k)) := Fintype.equivFin (Index k)
  have positive (i : Index k) : Positive (family k i) :=
    ⟨Scale38NestedCompensation.preFamily k i,(rows i).2.1⟩
  obtain ⟨π,policy,observable,execution,phases,failed,acquisition,account⟩ :=
    completion_contract _ (family k ∘ e.symm) (fun i => positive (e.symm i))
      (scan k (List.range (k+1))) (fun h => (decode k (List.range (k+1)) h).map e)
  have account_i (i : Index k) :
      paid (terminal π (family k i)).1 = (route k i ++ secondary k i).toFinset ∪
        leafAddresses (family k i) := by
    have selected := account (e i)
    have decoded : (decode k (List.range (k+1))
        (runPassiveProtocol (fun q U => leafLabel U q)
          (scan k (List.range (k+1))) ((family k ∘ e.symm) (e i)))).map e = some (e i) := by
      simpa only [Function.comp_apply,e.symm_apply_apply,(routes i).1,Option.map_some]
    have supplied := (selected decoded).2
    simp only [Function.comp_apply,e.symm_apply_apply] at supplied
    rw [(routes i).2] at supplied
    simpa only [List.map_map,Function.comp_def,List.map_id_fun] using supplied
  have bills (i : Index k) :
      paid (terminal π (family k i)).1 = leafAddresses (family k i) ∪ extras k i := by
    rw [account_i,List.toFinset_append,Finset.union_right_comm,primary_bill]
    cases i with
    | inl u => cases u; simp [secondary,Scale38NestedCompensation.extra]
    | inr p => cases p with
      | inl j =>
        simp only [secondary,Scale38NestedCompensation.extra,Sum.inr_ne_inl,↓reduceIte,stop]
        split_ifs with hj
        · simp [Finset.insert_eq_of_mem (secondary_leaf j),Finset.union_assoc,Finset.union_comm,
            Finset.union_left_comm,secondary_leaf j]
        · simp
      | inr i =>
        simp only [secondary,Scale38NestedCompensation.extra,Sum.inr_ne_inl,↓reduceIte,stop]
        split_ifs <;> ext q <;> simp <;> tauto
  have costs (i : Index k) : cost π (family k i) = 3*k+13 + excess k i := by
    unfold cost
    rw [bills]
    have leaf_card := (rows i).2.2.2.2.2
    cases i with
    | inl u => simpa using leaf_card
    | inr p => cases p with
      | inl j =>
        rw [Finset.union_singleton,Finset.card_insert_of_notMem
          (extras_nonleaf _ _ (Finset.mem_singleton_self _)),leaf_card]
      | inr i =>
        dsimp only [Sum.elim]
        split_ifs with hi
        · rw [Finset.union_insert,Finset.union_singleton,
            Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert,not_or]
              exact ⟨different (i.val+1) (i.val+1),raw_nonleaf _ (by simp)⟩),
            Finset.card_insert_of_notMem (secondary_nonleaf i),leaf_card]
          omega
        · rw [Finset.union_singleton,Finset.card_insert_of_notMem
            (raw_nonleaf _ (by simp)),leaf_card]
  refine ⟨?_,routes,π,policy,observable,execution,?_,?_⟩
  · intro t ht0 ht
    refine ⟨pair t ht0 ht,gx ⟨t,ht⟩,?_,?_,(fun s => different s t)⟩
    · have supplied := gy ⟨t-1,by omega⟩
      simpa only [Fin.val_mk,show t-1+1=t from by omega] using supplied
    · have supplied := contracted_leaf ⟨t-1,by omega⟩
      simpa only [Fin.val_mk,show t-1+1=t from by omega] using supplied
  · intro i
    refine ⟨unique i,bills i,?_,?_,costs i⟩
    · rw [bills]
      ext q
      simp only [Finset.mem_sdiff,Finset.mem_union]
      constructor
      · rintro ⟨hl | he,hn⟩
        · exact False.elim (hn hl)
        · exact he
      · intro he
        exact ⟨Or.inr he,extras_nonleaf i q he⟩
    · intro q hq
      refine ⟨?_,extras_nonleaf i q hq⟩
      have requested : q ∈ (route k i ++ secondary k i).toFinset ∪ leafAddresses (family k i) := by
        rw [← account_i,bills]
        exact Finset.mem_union_right _ hq
      have routing : q ∈ (route k i ++ secondary k i).toFinset :=
        (Finset.mem_union.mp requested).resolve_right (extras_nonleaf i q hq)
      rw [(routes i).2]
      simpa only [List.map_map,Function.comp_def,List.map_id_fun] using List.mem_toFinset.mp routing
  · intro hk3
    constructor
    · intro i
      rw [costs]
      cases i with
      | inl u => simp
      | inr p => cases p <;> dsimp only [Sum.elim]; split_ifs <;> omega
    · refine ⟨.inr (.inr ⟨0,by omega⟩),?_⟩
      rw [costs]
      simp only [Sum.elim_inr,Fin.val_mk]
      rw [if_pos (by omega)]
      omega

end D5.S3.Arith.FibonacciAtomic.Scale38CoarseTwoExcess
