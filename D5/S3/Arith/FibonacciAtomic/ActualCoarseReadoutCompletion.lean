/- GID: D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Coarse routing, complete leaf verification, controlled acquisition and exact caching. -/

import D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutHistory
import D5.S3.Arith.FibonacciAtomic.ActualJointResponseCostCore
import D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutCompletion

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition
open ActualCoarseReadoutHistory (kappa kappa_hist CoarseObservable)
open ActualJointResponseCostCore (Controller controllerPolicy controllerOutcome verifyController
  phase_foundation)
open ActualImageSevenLeafSeparation (leafLabel leafAddresses seven_leaf_separation)
open ActualLeafHistoryRigidity (subtree actual_address_geometry)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute)
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
  (PassiveProtocol runPassiveProtocol)

local notation "RH" => Hist (fun _ : Address => Reply)
local notation "CH" => Hist (fun _ : Address => Option Bool)
local notation "κ" => kappa
local notation "κH" => kappa_hist

/-- A section of the reply quotient, used for policy evaluation. The representative
of none is a formal branch symbol, not an existence certificate for its address. -/
def encodeHistory (h : CH) : RH :=
  h.map (fun a => ⟨a.1, match a.2 with
    | some true => Reply.alpha
    | some false => Reply.beta
    | none => Reply.branch⟩)

/-- Compile a finite coarse route. A selected prototype starts the existing complete
leaf verifier; an unselected stop starts acquisition with a fresh logical history. -/
noncomputable def compileRaw {m : Nat} (F : Fin m → Source)
    (decode : CH → Option (Fin m)) : PassiveProtocol Address (fun _ => Option Bool) →
      CH → Controller
  | .stop, h => match decode h with
    | some i => verifyController (F i) (leaves (F i))
    | none => .fallback
  | .query q next, h => .query q (fun y =>
      compileRaw F decode (next (κ y)) (h ++ [⟨q,κ y⟩]))

/-- Each logical request is recorded. Only a cache miss reads the source and adds
one exact address and its actual reply. There is no inferred or prefilled report. -/
noncomputable def cachedExecute (p : Policy) : Nat → RH → RH → Source →
    Option ((RH × Bool) × RH)
  | 0, _, _, _ => none
  | n+1, h, cache, U => match p h with
    | .inr b => some (([],b),cache)
    | .inl q =>
      let hit := cache.find? (fun a => a.1 == q)
      let y := match hit with | some a => a.2 | none => readout q U
      let cache' := match hit with | some _ => cache | none => cache ++ [⟨q,y⟩]
      (cachedExecute p n (h ++ [⟨q,y⟩]) cache' U).map
        (fun z => ((⟨q,y⟩ :: z.1.1,z.1.2),z.2))

/-- Every finite coarse route admits the same all-source completion. Cache reports
come only from actual requests, and none becomes a branch only on an existing node. -/
theorem completion_contract (m : Nat) (F : Fin m → Source)
    (positive : ∀ i, Positive (F i))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (decode : CH → Option (Fin m)) :
    ∃ π : Strategy,
      π.policy = (fun h => controllerPolicy (compileRaw F decode p [])
        (encodeHistory (κH h))) ∧ CoarseObservable π.policy ∧
      (∀ U : Source, ∃ (n : Nat) (t : RH) (b : Bool) (cache : RH),
        execute readout π.policy n [] U = some (t,b) ∧
        cachedExecute π.policy n [] [] U = some ((t,b),cache) ∧
        (t,b) = terminal π U ∧ (b = true ↔ Positive U) ∧
        (cache.map Sigma.fst).Nodup ∧
        (∀ a ∈ cache, a.2 = readout a.1 U) ∧ paid cache = paid t) ∧
      (∀ (U : Source) (h s : RH),
        κH h = runPassiveProtocol (fun q W => leafLabel W q) p U →
        π.policy (h ++ s) = match decode (κH h) with
          | some i => controllerPolicy (verifyController (F i) (leaves (F i)))
              (encodeHistory (κH s))
          | none => acquisitionPolicy (encodeHistory (κH s))) ∧
      (∀ (V : Source) (pre rest : List Address) (q : Address) (y : Reply) (s : RH),
        leaves V = pre ++ q :: rest →
        κ y ≠ leafLabel V q →
        controllerPolicy (verifyController V (leaves V))
          (encodeHistory (κH (pre.map (fun a => ⟨a,readout a V⟩) ++ [⟨q,y⟩] ++ s))) =
            acquisitionPolicy (encodeHistory (κH s))) ∧
      (∀ (U : Source) (h : RH) (q : Address),
        h.IsPrefix (acquisitionTrace [] U) →
        acquisitionPolicy (encodeHistory (κH h)) = .inl q →
        (∃ T : Source, subtree q U = some T) ∧
        (κ (readout q U) = none → ∃ a b : Source, subtree q U = some (.mul a b)) ∧
        (q ≠ [] → ∃ (v : Address) (d : Bool),
          q = v ++ [d] ∧ (⟨v,Reply.branch⟩ : Sigma (fun _ : Address => Reply)) ∈ h)) ∧
      (∀ i : Fin m,
        decode (runPassiveProtocol (fun q W => leafLabel W q) p (F i)) = some i →
        κH (terminal π (F i)).1 =
          runPassiveProtocol (fun q W => leafLabel W q) p (F i) ++
            κH ((leaves (F i)).map (fun q => ⟨q,readout q (F i)⟩)) ∧
        paid (terminal π (F i)).1 =
          ((runPassiveProtocol (fun q W => leafLabel W q) p (F i)).map Sigma.fst).toFinset ∪
            leafAddresses (F i)) := by
  classical
  let norm : RH → RH := fun h => encodeHistory (κH h)
  let repr : Reply → Reply := fun y => match κ y with
    | some true => .alpha
    | some false => .beta
    | none => .branch
  have norm_map (h : RH) : norm h = h.map (fun a => ⟨a.1,repr a.2⟩) := by
    simp only [norm, encodeHistory, kappa_hist, List.map_map, Function.comp_def, repr]
  have norm_append (h k : RH) : norm (h ++ k) = norm h ++ norm k := by
    simp only [norm_map, List.map_append]
  have repr_coarse (y : Reply) : κ (repr y) = κ y := by cases y <;> rfl
  have label (q : Address) (U : Source) : κ (readout q U) = leafLabel U q := by
    rfl
  have norm_trace (u : Address) (T : Source) : norm (acquisitionTrace u T) =
      acquisitionTrace u T := by
    induction T generalizing u with
    | of b => cases b <;> rfl
    | mul a b ha hb =>
      simp only [acquisitionTrace, norm_map, List.map_cons, List.map_append]
      rw [← norm_map, ← norm_map, ha, hb]
      rfl
  have norm_prefix (U : Source) (h : RH) (hp : h.IsPrefix (acquisitionTrace [] U)) :
      norm h = h := by
    have fixed := norm_trace [] U
    rw [norm_map] at fixed ⊢
    calc
      _ = h.map id := List.map_congr_left (fun a ha =>
        List.map_eq_map_iff.mp (fixed.trans (List.map_id _).symm) a (hp.subset ha))
      _ = h := List.map_id h
  have leaf_reply (V : Source) (q : Address) (hq : q ∈ leaves V) :
      readout q V = .alpha ∨ readout q V = .beta := by
    have existsLabel := ((seven_leaf_separation.1 V).2 q).mp
      (List.mem_toFinset.mpr hq)
    obtain ⟨b,hb⟩ := existsLabel
    cases he : readout q V <;> simp [leafLabel, he] at hb
    · exact Or.inl rfl
    · exact Or.inr rfl
  have verify_prefix (V U : Source) (qs : List Address)
      (onlyLeaves : ∀ q ∈ qs, q ∈ leaves V) :
      ∀ h : RH, h.IsPrefix (controllerOutcome (verifyController V qs) U).1 →
        controllerPolicy (verifyController V qs) (norm h) =
          controllerPolicy (verifyController V qs) h := by
    induction qs with
    | nil => intro h _; rfl
    | cons q qs ih =>
      intro h hp
      have hl := leaf_reply V q (onlyLeaves q (List.mem_cons_self))
      have eq_test (y : Reply) : (repr y = readout q V) ↔ (y = readout q V) := by
        rcases hl with hl | hl <;> cases y <;> simp [repr,kappa,hl]
      cases h with
      | nil => rfl
      | cons a h =>
        change (a :: h).IsPrefix (⟨q,readout q U⟩ :: _) at hp
        have head := (List.cons_prefix_cons.mp hp).1
        have tail := (List.cons_prefix_cons.mp hp).2
        subst a
        simp only [norm_map, List.map_cons, verifyController, controllerPolicy]
        simp only [↓reduceIte, eq_test]
        by_cases he : readout q U = readout q V
        · simp only [he, ↓reduceIte] at tail ⊢
          rw [← norm_map h]
          exact ih (fun r hr => onlyLeaves r (List.mem_cons_of_mem q hr)) h tail
        · simp only [he, ↓reduceIte, controllerOutcome] at tail ⊢
          rw [← norm_map h]
          change acquisitionPolicy (norm h) = acquisitionPolicy h
          rw [norm_prefix U h tail]
  have compile_prefix (r : PassiveProtocol Address (fun _ => Option Bool)) :
      ∀ (g : CH) (U : Source) (h : RH),
        h.IsPrefix (controllerOutcome (compileRaw F decode r g) U).1 →
        controllerPolicy (compileRaw F decode r g) (norm h) =
          controllerPolicy (compileRaw F decode r g) h := by
    induction r with
    | stop =>
      intro g U h hp
      cases hd : decode g with
      | none =>
        simp only [compileRaw, hd, controllerOutcome] at hp
        simp only [compileRaw, hd, controllerPolicy]
        exact congrArg acquisitionPolicy (norm_prefix U h hp)
      | some i =>
        simp only [compileRaw, hd] at hp ⊢
        exact verify_prefix (F i) U (leaves (F i)) (by intro q hq; exact hq) h hp
    | query q next ih =>
      intro g U h hp
      cases h with
      | nil => rfl
      | cons a h =>
        change (a :: h).IsPrefix (⟨q,readout q U⟩ :: _) at hp
        have head := (List.cons_prefix_cons.mp hp).1
        have tail := (List.cons_prefix_cons.mp hp).2
        subst a
        simp only [norm_map, List.map_cons, compileRaw, controllerPolicy, ↓reduceIte,
          repr_coarse]
        rw [← norm_map h]
        exact ih (κ (readout q U)) _ U h tail
  have transfer (raw cooked : Policy) (U : Source) :
      ∀ (n : Nat) (h t : RH) (b : Bool),
        execute readout raw n h U = some (t,b) →
        (∀ g : RH, g.IsPrefix t → cooked (h ++ g) = raw (h ++ g)) →
        execute readout cooked n h U = some (t,b) := by
    intro n
    induction n with
    | zero => intro h t b hr _; simp [execute] at hr
    | succ n ih =>
      intro h t b hr agree
      have start := agree [] List.nil_prefix
      simp only [List.append_nil] at start
      rw [execute, start]
      cases step : raw h with
      | inr z => simpa [execute,step] using hr
      | inl q =>
        simp only [execute,step,Option.map_eq_some_iff] at hr
        obtain ⟨⟨t',b'⟩,hr,e⟩ := hr
        cases e
        change (execute readout cooked n (h ++ [⟨q,readout q U⟩]) U).map
          (fun z => (⟨q,readout q U⟩ :: z.1,z.2)) = _
        rw [ih _ _ _ hr]
        · rfl
        · intro g hp
          simpa only [List.append_assoc, List.singleton_append] using
            agree (⟨q,readout q U⟩ :: g) (List.cons_prefix_cons.mpr ⟨rfl,hp⟩)
  have correctness (r : PassiveProtocol Address (fun _ => Option Bool)) :
      ∀ (g : CH) (U : Source),
      (controllerOutcome (compileRaw F decode r g) U).2 = true ↔ Positive U := by
    induction r with
    | stop =>
      intro g U
      cases hd : decode g with
      | none => simpa only [compileRaw, hd, controllerOutcome] using acquisition_foundation.1 U
      | some i => simpa only [compileRaw, hd] using
          phase_foundation.2.1 (F i) (positive i) U
    | query q next ih => intro g U; exact ih (κ (readout q U)) _ U
  let c := compileRaw F decode p []
  let policy : Policy := fun h => controllerPolicy c (norm h)
  have execution (U : Source) : execute readout policy
      ((controllerOutcome c U).1.length+1) [] U = some (controllerOutcome c U) := by
    apply transfer (controllerPolicy c) policy U _ [] _ _ (phase_foundation.1 c U)
    intro g hp
    exact compile_prefix p [] U g hp
  let π : Strategy := ⟨policy, fun U => ⟨_,controllerOutcome c U,execution U,
    correctness p [] U⟩⟩
  have terminal_eq (U : Source) : terminal π U = controllerOutcome c U := by
    apply source_foundation.2.2.2.2.2.2.2 _ _ _ [] U
    · exact (Classical.choose_spec (Classical.choose_spec (π.correct U))).1
    · exact execution U
  have cache_run (raw : Policy) (U : Source) :
      ∀ (n : Nat) (h t cache : RH) (b : Bool),
        execute readout raw n h U = some (t,b) →
        (cache.map Sigma.fst).Nodup → (∀ a ∈ cache, a.2 = readout a.1 U) →
        ∃ cache' : RH, cachedExecute raw n h cache U = some ((t,b),cache') ∧
          (cache'.map Sigma.fst).Nodup ∧ (∀ a ∈ cache', a.2 = readout a.1 U) ∧
          paid cache' = paid cache ∪ paid t := by
    intro n
    induction n with
    | zero => intro h t cache b hr _ _; simp [execute] at hr
    | succ n ih =>
      intro h t cache b hr hn ht
      cases step : raw h with
      | inr z =>
        simp only [execute,step,Option.some.injEq,Prod.mk.injEq] at hr
        rcases hr with ⟨rfl,rfl⟩
        exact ⟨cache, by simp [cachedExecute,step],hn,ht,by simp [paid]⟩
      | inl q =>
        simp only [execute,step,Option.map_eq_some_iff] at hr
        obtain ⟨⟨t',b'⟩,hr,e⟩ := hr
        cases e
        cases hit : cache.find? (fun a => a.1 == q) with
        | some a =>
          have address : a.1 = q := by simpa using List.find?_some hit
          have member := List.mem_of_find?_eq_some hit
          have answer : a.2 = readout q U := by simpa only [address] using ht a member
          obtain ⟨cache',run,hn',ht',cost'⟩ := ih _ _ cache _ hr hn ht
          refine ⟨cache',?_,hn',ht',?_⟩
          · simpa only [cachedExecute,step,hit,answer,Option.map_some] using
              congrArg (Option.map (fun z => ((⟨q,readout q U⟩ :: z.1.1,z.1.2),z.2))) run
          · rw [cost']
            have paidQ : q ∈ paid cache := by
              exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,member,address⟩)
            simp only [paid,List.map_cons,List.toFinset_cons]
            change paid cache ∪ paid t' = paid cache ∪ insert q (paid t')
            rw [Finset.union_insert]
            exact (Finset.insert_eq_of_mem (Finset.mem_union_left _ paidQ)).symm
        | none =>
          have fresh : q ∉ cache.map Sigma.fst := by
            intro hm
            obtain ⟨a,ha,eq⟩ := List.mem_map.mp hm
            have no := List.find?_eq_none.mp hit a ha
            simp [eq] at no
          have hn' : ((cache ++
              [(⟨q,readout q U⟩ : Sigma (fun _ : Address => Reply))]).map Sigma.fst).Nodup := by
            simp only [List.map_append,List.map_cons,List.map_nil]
            apply List.nodup_append.mpr
            refine ⟨hn,by simp,?_⟩
            intro a ha b hb
            have beq : b = q := List.mem_singleton.mp hb
            subst b
            intro eq
            exact fresh (eq ▸ ha)
          have ht' : ∀ a ∈ cache ++ [⟨q,readout q U⟩], a.2 = readout a.1 U := by
            intro a ha
            rcases List.mem_append.mp ha with ha | ha
            · exact ht a ha
            · have e : a = ⟨q,readout q U⟩ := List.mem_singleton.mp ha
              subst a; rfl
          obtain ⟨cache',run,hn'',ht'',cost'⟩ := ih _ _ _ _ hr hn' ht'
          refine ⟨cache',?_,hn'',ht'',?_⟩
          · simpa only [cachedExecute,step,hit,Option.map_some] using
              congrArg (Option.map (fun z => ((⟨q,readout q U⟩ :: z.1.1,z.1.2),z.2))) run
          · rw [cost']
            simp [paid,List.map_append,Finset.union_assoc,Finset.union_left_comm]
  have replay (r : PassiveProtocol Address (fun _ => Option Bool)) :
      ∀ (g : CH) (U : Source) (s : RH),
        controllerPolicy (compileRaw F decode r g)
          (encodeHistory (runPassiveProtocol (fun q W => leafLabel W q) r U) ++ norm s) =
          match decode (g ++ runPassiveProtocol (fun q W => leafLabel W q) r U) with
          | some i => controllerPolicy (verifyController (F i) (leaves (F i))) (norm s)
          | none => acquisitionPolicy (norm s) := by
    induction r with
    | stop =>
      intro g U s
      simp only [compileRaw,runPassiveProtocol,encodeHistory,List.map_nil,
        List.nil_append,List.append_nil]
      cases decode g <;> rfl
    | query q next ih =>
      intro g U s
      simp only [runPassiveProtocol,encodeHistory,List.map_cons,List.cons_append,
        compileRaw,controllerPolicy,↓reduceIte]
      change controllerPolicy (compileRaw F decode (next (κ (repr (readout q U))))
        (g ++ [⟨q,κ (repr (readout q U))⟩]))
        (encodeHistory (runPassiveProtocol (fun q W => leafLabel W q)
          (next (leafLabel U q)) U) ++ norm s) = _
      rw [repr_coarse, label]
      have replayNext := ih (leafLabel U q) (g ++ [⟨q,leafLabel U q⟩]) U s
      rw [List.append_assoc,List.singleton_append] at replayNext
      exact replayNext
  have matched_reset (V : Source) : ∀ (pre tail : List Address) (s : RH),
      (∀ a ∈ pre, a ∈ leaves V) →
      controllerPolicy (verifyController V (pre ++ tail))
        (norm (pre.map (fun a => ⟨a,readout a V⟩) ++ s)) =
          controllerPolicy (verifyController V tail) (norm s) := by
    intro pre
    induction pre with
    | nil => intro tail s _; rfl
    | cons a pre ih =>
      intro tail s hl
      have reply := leaf_reply V a (hl a List.mem_cons_self)
      have fixed : repr (readout a V) = readout a V := by
        rcases reply with e | e <;> rw [e] <;> rfl
      simp only [List.cons_append,List.map_cons,norm_map,List.map_cons,
        verifyController,controllerPolicy,fixed,↓reduceIte]
      rw [← norm_map, ← norm_map]
      exact ih tail s (fun q hq => hl q (List.mem_cons_of_mem a hq))
  rcases actual_address_geometry with
    ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,read_at,subtree_at,_,_⟩
  let Inv (U : Source) (h : RH) : Prop := ∀ q ∈ ActualTreeReadoutAcquisition.frontier h,
    (∃ T : Source, subtree q U = some T) ∧
    (q ≠ [] → ∃ (v : Address) (d : Bool),
      q = v ++ [d] ∧ (⟨v,Reply.branch⟩ : Sigma (fun _ : Address => Reply)) ∈ h)
  have advance_inv (U : Source) (h : RH) (q : Address)
      (inv : Inv U h) (request : acquisitionPolicy h = .inl q) :
      Inv U (h ++ [⟨q,readout q U⟩]) := by
    obtain ⟨rest,front⟩ : ∃ rest, ActualTreeReadoutAcquisition.frontier h = q :: rest := by
      cases hf : ActualTreeReadoutAcquisition.frontier h with
      | nil =>
        cases er : restore (h.length+1) h [] <;>
          simp [acquisitionPolicy,hf,er] at request
      | cons a rest =>
        have ea : a = q := by simpa [acquisitionPolicy,hf] using request
        subst a; exact ⟨rest,rfl⟩
    obtain ⟨⟨T,existsQ⟩,_⟩ := inv q (by rw [front]; exact List.mem_cons_self)
    have root : readout q U = readout [] T := by
      simpa only [List.append_nil,existsQ] using read_at q [] U
    have after : ActualTreeReadoutAcquisition.frontier (h ++ [⟨q,readout q U⟩]) =
        acquisitionStep (q :: rest) ⟨q,readout q U⟩ := by
      simp only [ActualTreeReadoutAcquisition.frontier,List.foldl_append,
        List.foldl_cons,List.foldl_nil]
      change acquisitionStep (ActualTreeReadoutAcquisition.frontier h) _ = _
      rw [front]
    have old (a : Address) (ha : a ∈ rest) :
        (∃ T, subtree a U = some T) ∧
        (a ≠ [] → ∃ v d, a = v ++ [d] ∧
          (⟨v,Reply.branch⟩ : Sigma (fun _ : Address => Reply)) ∈ h ++ [⟨q,readout q U⟩]) := by
      obtain ⟨ex,par⟩ := inv a (by rw [front]; exact List.mem_cons_of_mem q ha)
      refine ⟨ex,fun hn => ?_⟩
      obtain ⟨v,d,e,hm⟩ := par hn
      exact ⟨v,d,e,List.mem_append_left _ hm⟩
    cases T with
    | of b =>
      intro a ha
      rw [after] at ha
      cases b <;> simp only [acquisitionStep,root,readout,↓reduceIte] at ha
      all_goals exact old a ha
    | mul l r =>
      have branch : readout q U = .branch := root
      intro a ha
      rw [after] at ha
      simp only [acquisitionStep,branch,↓reduceIte,List.mem_cons] at ha
      rcases ha with rfl | rfl | ha
      · refine ⟨⟨l,?_⟩,fun _ => ⟨q,false,rfl,?_⟩⟩
        · simpa only [existsQ,Option.bind_some,subtree] using subtree_at q [false] U
        · simp [branch]
      · refine ⟨⟨r,?_⟩,fun _ => ⟨q,true,rfl,?_⟩⟩
        · simpa only [existsQ,Option.bind_some,subtree] using subtree_at q [true] U
        · simp [branch]
      · exact old a ha
  have run_inv (U : Source) : ∀ (n : Nat) (h t : RH) (b : Bool),
      execute readout acquisitionPolicy n h U = some (t,b) → Inv U h →
      ∀ g : RH, g.IsPrefix t → Inv U (h ++ g) := by
    intro n
    induction n with
    | zero => intro h t b run _ _ _; simp [execute] at run
    | succ n ih =>
      intro h t b run inv g hp
      cases step : acquisitionPolicy h with
      | inr z =>
        simp only [execute,step,Option.some.injEq,Prod.mk.injEq] at run
        rcases run with ⟨rfl,rfl⟩
        have empty : g = [] := List.prefix_nil.mp hp
        simpa only [empty,List.append_nil] using inv
      | inl q =>
        simp only [execute,step,Option.map_eq_some_iff] at run
        obtain ⟨⟨t',b'⟩,run,e⟩ := run
        cases e
        cases g with
        | nil => simpa only [List.append_nil] using inv
        | cons a g =>
          obtain ⟨head,tail⟩ := List.cons_prefix_cons.mp hp
          subst a
          simpa only [List.append_assoc,List.singleton_append] using
            ih _ _ _ run (advance_inv U h q inv step) g tail
  have acquisition_inv (U : Source) (h : RH)
      (hp : h.IsPrefix (acquisitionTrace [] U)) : Inv U h := by
    have initial : Inv U [] := by
      intro q hq
      have eq : q = [] := by simpa [ActualTreeReadoutAcquisition.frontier] using hq
      subst q
      exact ⟨⟨U,rfl⟩,by simp⟩
    simpa only [List.nil_append] using run_inv U _ [] _ _
      (acquisition_foundation.2 U) initial h hp
  have selected (r : PassiveProtocol Address (fun _ => Option Bool)) :
      ∀ (g : CH) (i : Fin m),
        decode (g ++ runPassiveProtocol (fun q W => leafLabel W q) r (F i)) = some i →
        κH (controllerOutcome (compileRaw F decode r g) (F i)).1 =
          runPassiveProtocol (fun q W => leafLabel W q) r (F i) ++
            κH ((leaves (F i)).map (fun q => ⟨q,readout q (F i)⟩)) ∧
        paid (controllerOutcome (compileRaw F decode r g) (F i)).1 =
          ((runPassiveProtocol (fun q W => leafLabel W q) r (F i)).map Sigma.fst).toFinset ∪
            leafAddresses (F i) := by
    induction r with
    | stop =>
      intro g i hd
      simp only [runPassiveProtocol,List.append_nil] at hd
      simp only [compileRaw,hd,phase_foundation.2.2.1 (F i),runPassiveProtocol,
        List.nil_append,List.map_nil,List.toFinset_nil,Finset.empty_union]
      exact by simp [paid,leafAddresses,List.map_map,Function.comp_def]
    | query q next ih =>
      intro g i hd
      have nextSelected := ih (leafLabel (F i) q) (g ++ [⟨q,leafLabel (F i) q⟩]) i
        (by simpa only [runPassiveProtocol,List.append_assoc,List.singleton_append] using hd)
      constructor
      · simpa only [compileRaw,controllerOutcome,kappa_hist,List.map_cons,
          runPassiveProtocol,List.cons_append,label] using congrArg
          (List.cons (⟨q,leafLabel (F i) q⟩ : Sigma (fun _ : Address => Option Bool)))
          nextSelected.1
      · simp only [compileRaw,controllerOutcome,paid,List.map_cons,List.toFinset_cons]
        change insert q (paid (controllerOutcome (compileRaw F decode
          (next (leafLabel (F i) q)) (g ++ [⟨q,leafLabel (F i) q⟩])) (F i)).1) = _
        rw [nextSelected.2]
        simp [runPassiveProtocol,Finset.insert_union]
  refine ⟨π,rfl,?_,?_,?_,?_,?_,?_⟩
  · intro h k equal
    change controllerPolicy c (encodeHistory (κH h)) =
      controllerPolicy c (encodeHistory (κH k))
    rw [equal]
  · intro U
    obtain ⟨cache,run,hn,ht,hpaid⟩ := cache_run policy U _ [] _ [] _ (execution U)
      (by simp) (by simp)
    refine ⟨_,_,_,cache,execution U,run,(terminal_eq U).symm,
      correctness p [] U,hn,ht,?_⟩
    simpa [paid] using hpaid
  · intro U h s hh
    change controllerPolicy c (norm (h ++ s)) = _
    rw [norm_append]
    change controllerPolicy c (encodeHistory (κH h) ++ norm s) = _
    rw [hh]
    simpa only [List.nil_append,hh] using replay p [] U s
  · intro V pre rest q y s leavesEq mismatch
    rw [leavesEq]
    change controllerPolicy (verifyController V (pre ++ q :: rest))
      (norm ((pre.map (fun a => ⟨a,readout a V⟩) ++ [⟨q,y⟩]) ++ s)) = _
    rw [List.append_assoc, matched_reset V pre (q :: rest)
      ([(⟨q,y⟩ : Sigma (fun _ : Address => Reply))] ++ s)]
    · have different : repr y ≠ readout q V := by
        intro eq
        apply mismatch
        exact (repr_coarse y).symm.trans ((congrArg κ eq).trans (label q V))
      simp only [norm_map,List.map_append,List.map_cons,List.map_nil,List.cons_append,
        List.nil_append,verifyController,controllerPolicy,↓reduceIte,different]
      rw [← norm_map]
    · intro a ha
      rw [leavesEq]
      exact List.mem_append_left _ ha
  · intro U h q hp query
    change acquisitionPolicy (norm h) = .inl q at query
    rw [norm_prefix U h hp] at query
    have inv := acquisition_inv U h hp
    have member : q ∈ ActualTreeReadoutAcquisition.frontier h := by
      cases hf : ActualTreeReadoutAcquisition.frontier h with
      | nil =>
        cases er : restore (h.length+1) h [] <;>
          simp [acquisitionPolicy,hf,er] at query
      | cons a rest =>
        have e : a = q := by simpa [acquisitionPolicy,hf] using query
        subst a; exact List.mem_cons_self
    obtain ⟨⟨T,existsQ⟩,parent⟩ := inv q member
    refine ⟨⟨T,existsQ⟩,?_,parent⟩
    intro none
    have root : readout q U = readout [] T := by
      simpa only [List.append_nil,existsQ] using read_at q [] U
    cases T with
    | of b => cases b <;> simp [root,readout,kappa] at none
    | mul a b => exact ⟨a,b,existsQ⟩
  · intro i hi
    rw [terminal_eq]
    exact selected p [] i (by simpa only [List.nil_append] using hi)

end D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutCompletion
