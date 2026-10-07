/- GID: D5/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed physical forests have attained joint-tail and threshold minima. -/

import D5.S3.ObserverMemory.Algorithms.FixedForestThresholdAssignment

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.FixedForestUnitCapacity

open StationaryUnitControl FixedForestTargetInventory FixedForestSlotGraph
attribute [local instance] Classical.propDecidable
universe u

variable {P h ell e : Nat} {Node : Type} [Fintype Node] [DecidableEq Node]
variable {hP : 1 < P} (F : PhysicalForest P h ell Node hP) (R : Prescribed F)

namespace OriginalImplementation
variable {Q : Type u} [Fintype Q] [DecidableEq Q] {C : Controller P Q}
    (I : OriginalImplementation (e := e) F R C)

noncomputable abbrev paths := initialize_original_paths F C I.word

private theorem node_read (n : Node) :
    IsRead C (I.readControl n) ∧ ∃ x t, t < (paths F R I).length x ∧
      (C.run hP (x, C.initial) t).2 = I.readControl n := by
  obtain ⟨x, hx⟩ := F.support_nonempty n
  obtain ⟨i, hi, he⟩ := F.support_events n x hx
  have hm := event_time_mono F x (i := i) (j := F.reads x - 1) (by omega)
    (by have := F.reads_pos x; omega)
  have run := I.events x i hi
  rw [he] at run
  refine ⟨?_, x, readTime F n, ?_, congrArg Prod.snd run⟩
  · have hr := I.word.read_event x i hi
    rw [I.events x i hi, he] at hr
    exact hr
  · change readTime F n < stopTime F x
    rw [← he]
    unfold stopTime
    omega

private theorem root_control {n : Node} (hn : F.parent n = none) :
    I.readControl n = prefixState C hP ell := by
  obtain ⟨c, rfl⟩ := (F.roots_exact n).mp hn
  obtain ⟨x, hx⟩ := F.support_nonempty (F.root c)
  obtain ⟨i, hi, he⟩ := F.support_events (F.root c) x hx
  have index := F.event_level x i hi
  rw [he, F.root_level] at index
  have run := I.events x i hi
  rw [he] at run
  have time : readTime F (F.root c) = ell := by simp [readTime, F.root_shift, F.root_level]
  rw [time] at run
  exact (congrArg Prod.snd run).symm.trans
    (by simpa only using
      congrArg Prod.snd (initialized_prefix C hP (paths F R I) x (le_refl ell)))

private theorem nonroot_control {n : Node} (hn : F.parent n ≠ none) :
    I.readControl n ≠ prefixState C hP ell := by
  obtain ⟨x, hx⟩ := F.support_nonempty n
  obtain ⟨i, hi, he⟩ := F.support_events n x hx
  have positive : 0 < i := by
    cases hp : F.parent n with
    | none => exact False.elim (hn hp)
    | some p =>
      have level := F.child_level n p hp
      have index := F.event_level x i hi
      rw [he] at index
      omega
  have hm := event_time_mono F x (i := 1) (j := i) positive hi
  rw [event_time_step F x 0 (by omega), event_time_zero F x] at hm
  have last := event_time_mono F x (i := i) (j := F.reads x - 1) (by omega)
    (by omega)
  have late : ell < readTime F n := by rw [← he]; omega
  have bound : readTime F n ≤ (paths F R I).length x := by
    change readTime F n ≤ stopTime F x
    rw [← he]; unfold stopTime; omega
  have no := prefix_first_read_no_return C hP (paths F R I) x
    (le_refl ell) late bound
  rw [← he, I.events x i hi] at no
  simpa only [he] using no

private noncomputable def requestRead (n : Node) (hn : F.Internal n) :
    NonrootRead C hP (paths F R I) := by
  refine ⟨⟨I.requestTarget n, ?_⟩, ?_⟩
  · obtain ⟨m, hm⟩ := hn
    have hp := (Finset.mem_filter.mp hm).2
    rw [← I.child_target m n hp]
    exact node_read F R I m
  · change I.requestTarget n ≠ prefixState C hP ell
    obtain ⟨m, hm⟩ := hn
    have hp := (Finset.mem_filter.mp hm).2
    have nr : F.parent m ≠ none := by rw [hp]; simp
    rw [← I.child_target m n hp]
    exact nonroot_control F R I nr

private theorem actual_node (q : ActualRead C hP (paths F R I)) :
    ∃ n, I.readControl n = q.val := by
  obtain ⟨x, t, ht, he⟩ := q.property.2
  have hr : IsRead C (C.run hP (x, C.initial) t).2 := he ▸ q.property.1
  obtain ⟨i, hi, time⟩ := (original_reads_exact F C I.word x ht).mp hr
  rw [time, I.events x i hi] at he
  exact ⟨F.event x i, he⟩

private theorem nonroot_request (q : NonrootRead C hP (paths F R I)) :
    ∃ n, ∃ _hn : F.Internal n, I.requestTarget n = q.val.val := by
  obtain ⟨m, hm⟩ := actual_node F R I q.val
  cases hp : F.parent m with
  | none => exact False.elim (q.property (hm ▸ root_control F R I hp))
  | some n => exact ⟨n, child_internal F hp, (I.child_target m n hp).symm.trans hm⟩

private theorem nonroot_card :
    Fintype.card (NonrootRead C hP (paths F R I)) = 3 * (P - 1) + e := by
  let root : ActualRead C hP (paths F R I) :=
    ⟨prefixState C hP ell, (paths F R I).shape 0 |>.first_read,
      0, ell, (paths F R I).shape 0 |>.first_before_stop, rfl⟩
  change Fintype.card {q : ActualRead C hP (paths F R I) //
    q.val ≠ prefixState C hP ell} = _
  let eqv : {q : ActualRead C hP (paths F R I) // q.val ≠ prefixState C hP ell} ≃
      {q : ActualRead C hP (paths F R I) // ¬ q = root} :=
    Equiv.subtypeEquiv (Equiv.refl _) (by intro q; simp [root, Subtype.ext_iff])
  rw [Fintype.card_congr eqv, Fintype.card_subtype_compl]
  simp only [Fintype.card_unique]
  have hc := I.actual_reads
  change Fintype.card (ActualRead C hP (paths F R I)) = _ at hc
  rw [hc]
  omega

private abbrev Core := BinaryTarget F R ⊕ Unit

private noncomputable def coreRead : Core F R → NonrootRead C hP (paths F R I)
  | .inl b => requestRead F R I b.val (Finset.card_pos.mp (by rw [b.property.1]; omega))
  | .inr _ => requestRead F R I R.H1 (Finset.card_pos.mp (by rw [R.H1_unary]; omega))

private theorem coreRead_injective : Function.Injective (coreRead F R I) := by
  intro a b he
  have controls := congrArg (fun q : NonrootRead C hP (paths F R I) => q.val.val) he
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have eq := (I.binary_targets a.val b.val a.property.1 b.property.1).mp controls
      rcases eq with hh | ⟨_, bad⟩ | ⟨bad, _⟩
      · exact congrArg Sum.inl (Subtype.ext hh)
      · exact False.elim (b.property.2 bad)
      · exact False.elim (a.property.2 bad)
    | inr b => exact False.elim (I.resolving_separate a.val a.property.1 controls.symm)
  | inr a =>
    cases b with
    | inl b => exact False.elim (I.resolving_separate b.val b.property.1 controls)
    | inr b => cases a; cases b; rfl

private abbrev Extra :=
  {q : NonrootRead C hP (paths F R I) // q ∉ Set.range (coreRead F R I)}

private theorem extra_card : Fintype.card (Extra F R I) = e := by
  have hc := target_card (e := 0) F R
  simp only [Target, Fintype.card_sum, Fintype.card_unique, Fintype.card_fin,
    Nat.add_zero] at hc
  have coreCard : Fintype.card (Core F R) = 3 * (P - 1) := by
    simpa only [Core, Fintype.card_sum, Fintype.card_unique] using hc
  have rangeCard := Fintype.card_congr (Equiv.ofInjective (coreRead F R I)
    (coreRead_injective F R I))
  change Fintype.card {q : NonrootRead C hP (paths F R I) //
    ¬ q ∈ Set.range (coreRead F R I)} = e
  rw [Fintype.card_subtype_compl, nonroot_card F R I, ← rangeCard, coreCard]
  omega

/-- Enumerate every actual nonroot target. Extra indices enumerate the exact
complement of the forced binary and resolving targets, including all e extras. -/
noncomputable def targetEquiv : Target (e := e) F R ≃ NonrootRead C hP (paths F R I) :=
  (Equiv.sumAssoc (BinaryTarget F R) Unit (Fin e)).symm.trans
    ((Equiv.sumCongr (Equiv.ofInjective (coreRead F R I) (coreRead_injective F R I))
      (Fintype.equivFinOfCardEq (extra_card F R I)).symm).trans
        (Equiv.sumCompl (fun q => q ∈ Set.range (coreRead F R I))))

private theorem targetEquiv_binary (n : Node) (hn : F.Binary n) :
    (targetEquiv F R I (binaryTarget (e := e) F R n hn)).val.val = I.requestTarget n := by
  unfold binaryTarget
  split_ifs with hb
  · subst n
    exact AB_target F R I
  · rfl

private theorem targetEquiv_resolving :
    (targetEquiv F R I (resolvingTarget F R)).val.val = I.requestTarget R.H1 := rfl


private theorem targetEquiv_forced {n : Node} {q : Target (e := e) F R} {c : Fin 3}
    (hf : forcedRow F R n = some (.inr q, c)) :
    (I.readControl n, F.color n) = ((targetEquiv F R I q).val.val, c) := by
  cases hp : F.parent n with
  | none => simp [forcedRow, hp] at hf
  | some p =>
    have old := forced_control F R I hp hf
    cases q with
    | inl b => exact old
    | inr q =>
      cases q with
      | inl u => exact old
      | inr i =>
        unfold forcedRow at hf
        simp only [hp] at hf
        split_ifs at hf <;> simp [binaryTarget, resolvingTarget] at hf

private theorem ordinary_child_unmarked (d : Ordinary F R) :
    demandChild F R d ≠ R.H ∧ demandChild F R d ≠ R.K ∧
    demandChild F R d ≠ R.H1 ∧ demandChild F R d ≠ R.K1 := by
  have parent := demand_child_parent F R d
  have binaryParent (n : Node) (hn : F.Binary n)
      (hp : F.parent (demandChild F R d) = some n) : False := by
    have he := Option.some.inj (parent.symm.trans hp)
    exact binary_not_unary F hn (he ▸ d.property.1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro he
    rcases R.HK_parents with hh | hh
    · exact binaryParent R.A R.A_binary (he ▸ hh.1)
    · exact binaryParent R.B R.B_binary (he ▸ hh.1)
  · intro he
    rcases R.HK_parents with hh | hh
    · exact binaryParent R.B R.B_binary (he ▸ hh.2)
    · exact binaryParent R.A R.A_binary (he ▸ hh.2)
  · intro he
    exact binaryParent R.H R.H_binary (he ▸ R.first_children.1)
  · intro he
    exact d.property.2.1 (Option.some.inj (parent.symm.trans (he ▸ R.first_children.2)))

private theorem row_fibers {n m : Node} (hn : F.parent n ≠ none)
    (hm : F.parent m ≠ none)
    (he : (I.readControl n, F.color n) = (I.readControl m, F.color m)) : Shared F R n m := by
  have hw : (I.readControl R.H, F.color R.H) = (I.readControl R.K, F.color R.K) := by
    rcases R.HK_parents with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · rw [I.child_target _ _ hp, I.child_target _ _ hq, AB_target F R I, R.HK_color]
    · rw [I.child_target _ _ hp, I.child_target _ _ hq, AB_target F R I, R.HK_color]
  have hv : (I.readControl R.H1, F.color R.H1) =
      (I.readControl R.K1, F.color R.K1) := by
    rw [I.child_target _ _ R.first_children.1, I.child_target _ _ R.first_children.2,
      I.production_target, R.child_color]
  exact raw_fibers_only F R (fun n => (I.readControl n, F.color n)) hw hv
    I.shared_distinct I.indegree_surplus I.edge_surplus hn hm he

private theorem ordinary_row_unique (d : Ordinary F R) {m : Node}
    (hm : F.parent m ≠ none)
    (he : (I.readControl (demandChild F R d), F.color (demandChild F R d)) =
      (I.readControl m, F.color m)) : demandChild F R d = m := by
  have hn : F.parent (demandChild F R d) ≠ none := by rw [demand_child_parent]; simp
  have hs := row_fibers F R I hn hm he
  have unmarked := ordinary_child_unmarked F R d
  rcases hs with he | ⟨bad, _⟩ | ⟨bad, _⟩ | ⟨bad, _⟩ | ⟨bad, _⟩
  · exact he
  · exact False.elim (unmarked.1 bad)
  · exact False.elim (unmarked.2.1 bad)
  · exact False.elim (unmarked.2.2.1 bad)
  · exact False.elim (unmarked.2.2.2 bad)

private noncomputable def ordinarySlot (d : Ordinary F R) : SpareSlot (e := e) F R := by
  let q := (targetEquiv F R I).symm (requestRead F R I d.val (ordinary_internal F R d))
  refine ⟨(q, F.color (demandChild F R d)), ?_⟩
  intro m hf
  have actual := targetEquiv_forced F R I hf
  have tq : (targetEquiv F R I q).val.val = I.requestTarget d.val := by
    exact congrArg (fun r : NonrootRead C hP (paths F R I) => r.val.val)
      ((targetEquiv F R I).apply_symm_apply _)
  rw [tq] at actual
  have collision : (I.readControl (demandChild F R d), F.color (demandChild F R d)) =
      (I.readControl m, F.color m) := by
    rw [I.child_target _ _ (demand_child_parent F R d)]
    exact actual.symm
  have nonroot : F.parent m ≠ none := by
    intro hp
    simp [forcedRow, hp] at hf
  have same := ordinary_row_unique F R I d nonroot collision
  have parent := demand_child_parent F R d
  rw [same] at parent
  unfold forcedRow at hf
  simp only [parent] at hf
  have nb : ¬ F.Binary d.val := fun hb => binary_not_unary F hb d.property.1
  simp [nb, d.property.2.1, d.property.2.2.1, d.property.2.2.2] at hf

private theorem ordinarySlot_injective : Function.Injective (ordinarySlot F R I) := by
  intro d f he
  have pair := congrArg Subtype.val he
  have targets := congrArg (fun q : Target (e := e) F R =>
    (targetEquiv F R I q).val.val) (congrArg Prod.fst pair)
  have controls : I.requestTarget d.val = I.requestTarget f.val := by
    simpa only [ordinarySlot, Equiv.apply_symm_apply, requestRead] using targets
  have colors : F.color (demandChild F R d) = F.color (demandChild F R f) :=
    congrArg Prod.snd pair
  have collision : (I.readControl (demandChild F R d), F.color (demandChild F R d)) =
      (I.readControl (demandChild F R f), F.color (demandChild F R f)) := by
    rw [I.child_target _ _ (demand_child_parent F R d),
      I.child_target _ _ (demand_child_parent F R f), controls, colors]
  have nr : F.parent (demandChild F R f) ≠ none := by rw [demand_child_parent]; simp
  have child := ordinary_row_unique F R I d nr collision
  have parent := congrArg F.parent child
  rw [demand_child_parent, demand_child_parent] at parent
  exact Subtype.ext (Option.some.inj parent)


private theorem ordinarySlot_target (d : Ordinary F R) :
    (targetEquiv F R I (ordinarySlot F R I d).val.1).val.val = I.requestTarget d.val := by
  exact congrArg (fun r : NonrootRead C hP (paths F R I) => r.val.val)
    ((targetEquiv F R I).apply_symm_apply _)

private theorem extra_not_core (i : Fin e) (a : Core F R) :
    targetEquiv F R I (extraTarget F R i) ≠ coreRead F R I a := by
  intro he
  have notin := ((Fintype.equivFinOfCardEq (extra_card F R I)).symm i).property
  exact notin ⟨a, he.symm⟩

/-- Raw J=Xi=1, the prescribed identities and actual reachability force an
injective same-digit assignment covering every extra actual target. -/
noncomputable def assignment : Assignment (e := e) F R where
  slot := ordinarySlot F R I
  injective := ordinarySlot_injective F R I
  same_digit _ := rfl
  hits_extra i := by
    let q := targetEquiv F R I (extraTarget F R i)
    obtain ⟨n, hn, ht⟩ := nonroot_request F R I q
    have notcore (a : Core F R) : I.requestTarget n ≠ (coreRead F R I a).val.val := by
      intro he
      have eq : q = coreRead F R I a := Subtype.ext (Subtype.ext (ht.symm.trans he))
      exact extra_not_core F R I i a eq
    have nb : ¬ F.Binary n := by
      intro hb
      have eq := targetEquiv_binary F R I n hb
      unfold binaryTarget at eq
      split_ifs at eq with hB
      · exact notcore (.inl ⟨R.A, R.A_binary, R.AB_distinct⟩) eq.symm
      · exact notcore (.inl ⟨n, hb, hB⟩) eq.symm
    have nk : n ≠ R.K := by
      intro he
      subst n
      have eq := targetEquiv_binary F R I R.H R.H_binary
      unfold binaryTarget at eq
      split_ifs at eq with hB
      · exact notcore (.inl ⟨R.A, R.A_binary, R.AB_distinct⟩)
          (I.production_target.trans eq.symm)
      · exact notcore (.inl ⟨R.H, R.H_binary, hB⟩)
          (I.production_target.trans eq.symm)
    have nh : n ≠ R.H1 := by
      intro he; subst n
      exact notcore (.inr ()) rfl
    have nk1 : n ≠ R.K1 := by
      intro he; subst n
      exact notcore (.inr ()) I.resolving_target
    let d : Ordinary F R := ⟨n, (internal_binary_or_unary F hn).resolve_left nb, nk, nh, nk1⟩
    refine ⟨d, ?_⟩
    apply (targetEquiv F R I).injective
    apply Subtype.ext
    apply Subtype.ext
    exact (ordinarySlot_target F R I d).trans ht

/-- All original internal requests, including the two absorbed shared-row
requests, correspond to their actual nonroot controls under one enumeration. -/
theorem request_target {n : Node} (hn : F.Internal n) :
    (targetEquiv F R I (nextTarget F R (assignment F R I) n)).val.val = I.requestTarget n := by
  unfold nextTarget
  split_ifs with hb hk hr hd
  · exact targetEquiv_binary F R I n hb
  · subst n
    exact (targetEquiv_binary F R I R.H R.H_binary).trans I.production_target.symm
  · rcases hr with rfl | rfl
    · exact targetEquiv_resolving F R I
    · exact I.resolving_target.symm
  · exact ordinarySlot_target F R I ⟨n, hd⟩
  · have hu := (internal_binary_or_unary F hn).resolve_left hb
    exact False.elim (hd ⟨hu, hk, fun he => hr (Or.inl he), fun he => hr (Or.inr he)⟩)

end OriginalImplementation

namespace OriginalImplementation
variable {Q : Type u} [Fintype Q] [DecidableEq Q] {C : Controller P Q}
    (I : OriginalImplementation (e := e) F R C)

private theorem waits_event {n : Node} (hn : F.Internal n) {x : Label P} {i : Nat}
    (hi : i < F.reads x) (he : F.event x i = n) :
    Waits C (F.delay n) (C.run hP (x, C.initial) (readTime F n + 1)).2
      (I.requestTarget n) := by
  obtain ⟨row, ins, hw⟩ := I.literal_requests n hn
  have hx : x ∈ F.support n := he ▸ F.event_support x i hi
  have run := I.events x i hi
  rw [he] at run
  have step : C.run hP (x, C.initial) (readTime F n + 1) =
      C.next hP (C.run hP (x, C.initial) (readTime F n)) :=
    Function.iterate_succ_apply' _ _ _
  rw [step, run]
  simpa only [Controller.next, Controller.step, ins, support_digit F hx, Option.getD_some]
    using hw

private theorem request_arrival (n : Node) (hn : F.Internal n) :
    Nonempty (Arrival C hP (paths F R I) (I.requestTarget n) (F.delay n)) := by
  obtain ⟨x, hx⟩ := F.support_nonempty n
  obtain ⟨i, hi, he⟩ := F.support_events n x hx
  have more := internal_event_more F hn hi he
  have hp := F.successor x i more
  have htime := event_time_step F x i more
  rw [he] at htime hp
  have hm := event_time_mono F x (i := i + 1) (j := F.reads x - 1) (by omega) (by omega)
  refine ⟨⟨x, readTime F n, internal_positive F hn, ?_, ?_,
    waits_event F R I hn hi he, ?_⟩⟩
  · have hr := I.word.read_event x i hi
    simpa only [he] using hr
  · change readTime F n + 1 + F.delay n < stopTime F x
    rw [← htime]
    unfold stopTime
    omega
  · rw [← htime, I.events x (i + 1) more]
    exact I.child_target _ _ hp

/-- The joint target maximum equals the actual maximum of all literal
incoming waits on the original initialized controller. -/
theorem actualL_transport (q : Target (e := e) F R) :
    L F R (assignment F R I) q =
      actualL C hP (paths F R I) (targetEquiv F R I q) := by
  apply le_antisymm
  · obtain ⟨n, hn, ht, hd⟩ := longest_request F R (assignment F R I) q
    have arrival := request_arrival F R I n hn
    have eq : requestRead F R I n hn = targetEquiv F R I q := by
      apply Subtype.ext
      apply Subtype.ext
      exact (request_target F R I hn).symm.trans
        (congrArg (fun t : Target (e := e) F R => (targetEquiv F R I t).val.val) ht)
    have bound : F.delay n ≤ actualL C hP (paths F R I) (requestRead F R I n hn) :=
      Finset.le_max' _ _ ((mem_arrival_lengths C hP (paths F R I) _ _).2 arrival)
    rw [eq, hd] at bound
    exact bound
  · let a := longestArrival C hP (paths F R I) (targetEquiv F R I q)
    have live : a.time < stopTime F a.input := by
      have := a.within
      change _ < stopTime F _ at this
      omega
    obtain ⟨i, hi, htime⟩ := (original_reads_exact F C I.word a.input live).mp a.source_read
    have more : i + 1 < F.reads a.input := by
      by_contra hh
      have last : i = F.reads a.input - 1 := by omega
      have within := a.within
      change a.time + 1 + _ < stopTime F a.input at within
      rw [htime, last] at within
      unfold stopTime at within
      omega
    have hn := child_internal F (F.successor a.input i more)
    have hw := waits_event F R I hn hi rfl
    rw [← htime] at hw
    have eq := waits_to_read_unique C a.waits hw (targetEquiv F R I q).val.property.1
      (requestRead F R I _ hn).val.property.1
    have target : nextTarget F R (assignment F R I) (F.event a.input i) = q := by
      apply (targetEquiv F R I).injective
      apply Subtype.ext
      apply Subtype.ext
      exact (request_target F R I hn).trans eq.2.symm
    have lengthEq := eq.1
    change actualL C hP (paths F R I) (targetEquiv F R I q) =
      F.delay (F.event a.input i) at lengthEq
    have bound := request_bound F R (assignment F R I) hn
    rw [target] at bound
    exact le_trans lengthEq.le bound

/-- The same extracted assignment and full nominal resource embedding give
the universal lower bound, charging unused states in the original Q. -/
theorem nominal_lower_bound :
    3 * P + 2 * (3 * (P - 1)) + 1 + ell + 2 * e +
      ∑ q : Target (e := e) F R, (L F R (assignment F R I) q - 1) ≤ Fintype.card Q := by
  letI : NeZero (3 * P) := ⟨by omega⟩
  let J := paths F R I
  obtain ⟨embedding⟩ := full_nominal_resource_embedding C hP J
  have bound := Fintype.card_le_of_embedding embedding
  have targetSum := (targetEquiv F R I).sum_comp (actualL C hP J)
  have sumEq : (∑ q : Target (e := e) F R, L F R (assignment F R I) q) =
      ∑ q : NonrootRead C hP J, actualL C hP J q := by
    rw [← targetSum]
    apply Finset.sum_congr rfl
    intro q _
    exact actualL_transport F R I q
  have tailSum : (∑ q : Target (e := e) F R, L F R (assignment F R I) q) =
      Fintype.card (Target (e := e) F R) +
        ∑ q : Target (e := e) F R, (L F R (assignment F R I) q - 1) := by
    rw [show Fintype.card (Target (e := e) F R) =
      ∑ _q : Target (e := e) F R, (1 : Nat) by simp, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    have pos := L_positive F R (assignment F R I) q
    omega
  simp only [Resource, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin,
    ZMod.card] at bound
  change 3 * P + (Fintype.card (ActualRead C hP J) +
    (ell + ∑ q : NonrootRead C hP J, actualL C hP J q)) ≤ Fintype.card Q at bound
  have reads : Fintype.card (ActualRead C hP J) = 3 * (P - 1) + 1 + e := by
    simpa only [Fintype.card_eq_nat_card] using I.actual_reads
  rw [reads, ← sumEq, tailSum, target_card F R] at bound
  omega

end OriginalImplementation


/-- Nominal capacities of precisely the original fixed-domain implementations.
Every finite carrier, including its unused nominal states, is counted. -/
def capacities : Set Nat := {n | ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q)
    (C : Controller P Q), Nonempty (OriginalImplementation (e := e) F R C) ∧ Fintype.card Q = n}

/-- Raw compatibility is required independently of numerical matching. -/
theorem original_domain_iff : (capacities (e := e) F R).Nonempty ↔
    Compatible (e := e) F R ∧ Nonempty (Assignment (e := e) F R) := by
  constructor
  · rintro ⟨n, Q, fQ, dQ, C, ⟨I⟩, _⟩
    letI := fQ
    letI := dQ
    exact ⟨I.compatible F R, ⟨I.assignment F R⟩⟩
  · rintro ⟨hc, α⟩
    obtain ⟨α⟩ := α
    letI : NeZero (3 * P) := ⟨by omega⟩
    exact ⟨Fintype.card (State F R α), State F R α, inferInstance, Classical.decEq _,
      controller F R α, ⟨(realize F R hc α).original⟩, rfl⟩

/-- One finite minimizer of the joint maximum at each target is realized by
one total stationary table and bounds every arbitrary nominal controller.
No minimum is asserted when the original fixed domain is empty. -/
theorem attained_fixed_minimum (hc : Compatible (e := e) F R)
    (ha : Nonempty (Assignment (e := e) F R)) :
    ∃ α : Assignment (e := e) F R,
      Nonempty (Realization F R α) ∧
      (∀ β : Assignment (e := e) F R,
        (∑ q : Target (e := e) F R, (L F R α q - 1)) ≤
          ∑ q : Target (e := e) F R, (L F R β q - 1)) ∧
      IsLeast (capacities (e := e) F R)
        (3 * P + 2 * (3 * (P - 1)) + 1 + ell + 2 * e +
          ∑ q : Target (e := e) F R, (L F R α q - 1)) ∧
      (∀ (Q : Type u) [Fintype Q] [DecidableEq Q] (C : Controller P Q),
        OriginalImplementation (e := e) F R C →
          3 * P + 2 * (3 * (P - 1)) + 1 + ell + 2 * e +
            ∑ q : Target (e := e) F R, (L F R α q - 1) ≤ Fintype.card Q) := by
  let cost := fun α : Assignment (e := e) F R =>
    ∑ q : Target (e := e) F R, (L F R α q - 1)
  obtain ⟨α, _, hmin⟩ := Finset.exists_min_image Finset.univ cost
    (by obtain ⟨β⟩ := ha; exact ⟨β, Finset.mem_univ β⟩)
  have minimum (β : Assignment (e := e) F R) : cost α ≤ cost β := hmin β (Finset.mem_univ β)
  have lower {Q : Type u} [Fintype Q] [DecidableEq Q] (C : Controller P Q)
      (I : OriginalImplementation (e := e) F R C) :
      3 * P + 2 * (3 * (P - 1)) + 1 + ell + 2 * e + cost α ≤ Fintype.card Q :=
    le_trans (Nat.add_le_add_left (minimum (I.assignment F R)) _)
      (I.nominal_lower_bound F R)
  refine ⟨α, ⟨realize F R hc α⟩, minimum, ⟨?_, ?_⟩, ?_⟩
  · letI : NeZero (3 * P) := ⟨by omega⟩
    exact ⟨State F R α, inferInstance, Classical.decEq _, controller F R α,
      ⟨(realize F R hc α).original⟩, (realize F R hc α).capacity⟩
  · rintro n ⟨Q, fQ, dQ, C, ⟨I⟩, card⟩
    letI := fQ
    letI := dQ
    rw [← card]
    exact le_trans (Nat.add_le_add_left (minimum (I.assignment F R)) _)
      (I.nominal_lower_bound F R)
  · intro Q fQ dQ C I
    exact lower C I

/-- Incompatible identities and empty assignment classes have no original
capacity and therefore no attained minimum. -/
theorem empty_domain_no_minimum
    (hempty : ¬ (Compatible (e := e) F R ∧ Nonempty (Assignment (e := e) F R))) :
    capacities (e := e) F R = ∅ ∧ ∀ n, ¬ IsLeast (capacities (e := e) F R) n := by
  have hn : ¬ (capacities (e := e) F R).Nonempty := fun hs =>
    hempty ((original_domain_iff F R).mp hs)
  have empty : capacities (e := e) F R = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
  refine ⟨empty, ?_⟩
  intro n least
  exact hn ⟨n, least.1⟩

/-- The e=0 threshold formula is an attained minimum over the original
operational domain. One alpha simultaneously attains every k, and every
arbitrary nominal controller is charged in its full original carrier. -/
theorem attained_e0_threshold_minimum (hc : Compatible (e := 0) F R)
    (ha : ∀ c, A F R c 1 ≤ B F R c 1) :
    ∃ α : Assignment (e := 0) F R,
      Nonempty (Realization F R α) ∧
      (∀ c k, (Finset.univ.filter (fun d : ColorDemand F R c =>
        k ≤ F.delay d.val.val ∧ baseline F R (α.slot d.val).val.1 < k)).card =
          A F R c k - B F R c k) ∧
      (∑ q : Target (e := 0) F R, (L F R α q - 1)) = thresholdExcess F R ∧
      IsLeast (capacities (e := 0) F R)
        (3 * P + 2 * (3 * (P - 1)) + 1 + ell + thresholdExcess F R) ∧
      (∀ (Q : Type u) [Fintype Q] [DecidableEq Q] (C : Controller P Q),
        OriginalImplementation (e := 0) F R C →
          3 * P + 2 * (3 * (P - 1)) + 1 + ell + thresholdExcess F R ≤
            Fintype.card Q) ∧
      (∀ c k, thresholdMax F R < k → A F R c k = 0 ∧ B F R c k = 0) := by
  have hn (c : Fin 3) : Fintype.card (ColorDemand F R c) ≤
      Fintype.card (ColorSlot F R c) := by
    simpa only [(counts_one F R c).1, (counts_one F R c).2] using ha c
  let α := sortedAssignment F R hn
  have cost := sorted_cost F R hn
  have lower {Q : Type u} [Fintype Q] [DecidableEq Q] (C : Controller P Q)
      (I : OriginalImplementation (e := 0) F R C) :
      3 * P + 2 * (3 * (P - 1)) + 1 + ell + thresholdExcess F R ≤ Fintype.card Q := by
    have bound := I.nominal_lower_bound F R
    simp only [Nat.mul_zero, Nat.add_zero] at bound
    exact le_trans (Nat.add_le_add_left (cost.2 (I.assignment F R)) _) bound
  refine ⟨α, ⟨realize F R hc α⟩, sorted_thresholds F R hn, cost.1, ⟨?_, ?_⟩, ?_,
    fun c k hk => thresholds_vanish F R k hk c⟩
  · letI : NeZero (3 * P) := ⟨by omega⟩
    refine ⟨State F R α, inferInstance, Classical.decEq _, controller F R α,
      ⟨(realize F R hc α).original⟩, ?_⟩
    have card := (realize F R hc α).capacity
    simp only [Nat.mul_zero, Nat.add_zero] at card
    exact card.trans (congrArg (fun t => 3 * P + 2 * (3 * (P - 1)) + 1 + ell + t) cost.1)
  · rintro n ⟨Q, fQ, dQ, C, ⟨I⟩, card⟩
    letI := fQ
    letI := dQ
    rw [← card]
    have bound := I.nominal_lower_bound F R
    simp only [Nat.mul_zero, Nat.add_zero] at bound
    exact le_trans (Nat.add_le_add_left (cost.2 (I.assignment F R)) _) bound
  · intro Q fQ dQ C I
    exact lower C I

end D5.S3.ObserverMemory.Algorithms.FixedForestUnitCapacity

namespace D5.S3.ObserverMemory.Algorithms.FixedForestUnitCapacity
open StationaryUnitControl FixedForestTargetInventory FixedForestSlotGraph
attribute [local instance] Classical.propDecidable
universe u

/-- The original integer parameter and its natural presentation have the
same physical domain. The joint minimum and its e=0 threshold specialization
refer to that same forest, stationary tables and full nominal carriers. -/
theorem original_context8319 (p : Int) (hp : 1 < p)
    {h ell e : Nat} {Node : Type} [Fintype Node] [DecidableEq Node]
    (F : PhysicalForest p.toNat h ell Node (by omega)) (R : Prescribed F) :
    ((3 * p.toNat : Nat) : Int) = 3 * p ∧
    ((3 * (p.toNat - 1) : Nat) : Int) = 3 * (p - 1) ∧
    ((capacities (e := e) F R).Nonempty ↔
      Compatible (e := e) F R ∧ Nonempty (Assignment (e := e) F R)) ∧
    (Compatible (e := e) F R → Nonempty (Assignment (e := e) F R) →
      ∃ α : Assignment (e := e) F R,
      Nonempty (Realization F R α) ∧
      (∀ β : Assignment (e := e) F R,
        (∑ q : Target (e := e) F R, (L F R α q - 1)) ≤
          ∑ q : Target (e := e) F R, (L F R β q - 1)) ∧
      IsLeast (capacities (e := e) F R)
        (3 * p.toNat + 2 * (3 * (p.toNat - 1)) + 1 + ell + 2 * e +
          ∑ q : Target (e := e) F R, (L F R α q - 1)) ∧
      (∀ (Q : Type u) [Fintype Q] [DecidableEq Q] (C : Controller p.toNat Q),
        OriginalImplementation (e := e) F R C →
          3 * p.toNat + 2 * (3 * (p.toNat - 1)) + 1 + ell + 2 * e +
            ∑ q : Target (e := e) F R, (L F R α q - 1) ≤ Fintype.card Q)) ∧
    (¬ (Compatible (e := e) F R ∧ Nonempty (Assignment (e := e) F R)) →
      capacities (e := e) F R = ∅ ∧ ∀ n, ¬ IsLeast (capacities (e := e) F R) n) ∧
    ((capacities (e := 0) F R).Nonempty ↔
      Compatible (e := 0) F R ∧ ∀ c, A F R c 1 ≤ B F R c 1) ∧
    (Compatible (e := 0) F R → (∀ c, A F R c 1 ≤ B F R c 1) →
      ∃ α : Assignment (e := 0) F R,
      Nonempty (Realization F R α) ∧
      (∀ c k, (Finset.univ.filter (fun d : ColorDemand F R c =>
        k ≤ F.delay d.val.val ∧ baseline F R (α.slot d.val).val.1 < k)).card =
          A F R c k - B F R c k) ∧
      (∑ q : Target (e := 0) F R, (L F R α q - 1)) = thresholdExcess F R ∧
      IsLeast (capacities (e := 0) F R)
        (3 * p.toNat + 2 * (3 * (p.toNat - 1)) + 1 + ell + thresholdExcess F R) ∧
      (∀ (Q : Type u) [Fintype Q] [DecidableEq Q] (C : Controller p.toNat Q),
        OriginalImplementation (e := 0) F R C →
          3 * p.toNat + 2 * (3 * (p.toNat - 1)) + 1 + ell + thresholdExcess F R ≤
            Fintype.card Q) ∧
      (∀ c k, thresholdMax F R < k → A F R c k = 0 ∧ B F R c k = 0)) := by
  refine ⟨by omega, by omega, original_domain_iff F R,
    attained_fixed_minimum F R, empty_domain_no_minimum F R, ?_,
    attained_e0_threshold_minimum F R⟩
  rw [original_domain_iff, assignment_e0_iff]

end D5.S3.ObserverMemory.Algorithms.FixedForestUnitCapacity
