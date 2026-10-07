/- GID: D5/S3/ObserverMemory/Algorithms/FixedForestOriginalImplementation
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/FixedForestOriginalImplementation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed physical forests admit faithful stationary realizations. -/

import D5.S3.ObserverMemory.Algorithms.FixedForestPhysicalExecution

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.FixedForestUnitCapacity

open StationaryUnitControl FixedForestTargetInventory FixedForestSlotGraph
attribute [local instance] Classical.propDecidable
universe u

variable {P h ell e : Nat} {Node : Type} [Fintype Node] [DecidableEq Node]
variable {hP : 1 < P} (F : PhysicalForest P h ell Node hP) (R : Prescribed F)

/-- The original fixed-domain implementation, expressed on its full nominal
carrier. The history and target maps are proof metadata recovered from its
runs, never extra inputs to the stationary table. No alpha or compatibility
premise occurs here. -/
structure OriginalImplementation {Q : Type u} [Fintype Q] [DecidableEq Q]
    (C : Controller P Q) where
  word : OriginalWordData F C
  readControl : Node → Q
  requestTarget : Node → Q
  events : ∀ x i, i < F.reads x →
    C.run hP (x, C.initial) (readTime F (F.event x i)) =
      (x + (F.shift (F.event x i) : Label P), readControl (F.event x i))
  child_target : ∀ n p, F.parent n = some p → readControl n = requestTarget p
  literal_requests : ∀ n, F.Internal n → ∃ row,
    C.instruction (readControl n) = .read row ∧
      Waits C (F.delay n) (row (F.color n)) (requestTarget n)
  binary_targets : ∀ n m, F.Binary n → F.Binary m →
    (requestTarget n = requestTarget m ↔
      n = m ∨ (n = R.A ∧ m = R.B) ∨ (n = R.B ∧ m = R.A))
  production_target : requestTarget R.K = requestTarget R.H
  resolving_target : requestTarget R.K1 = requestTarget R.H1
  resolving_separate : ∀ n, F.Binary n → requestTarget R.H1 ≠ requestTarget n
  shared_distinct : (readControl R.H, F.color R.H) ≠ (readControl R.H1, F.color R.H1)
  indegree_surplus : rawJ F (fun n => (readControl n, F.color n)) = 1
  edge_surplus : rawXi F (fun n => (readControl n, F.color n)) = 1
  actual_reads : Fintype.card (ActualRead C hP (initialize_original_paths F C word)) =
    3 * (P - 1) + 1 + e

theorem target_card : Fintype.card (Target (e := e) F R) = 3 * (P - 1) + e := by
  have erase : (Finset.univ.filter (fun n => F.Binary n ∧ n ≠ R.B)) =
      (Finset.univ.filter F.Binary).erase R.B := by
    ext n
    simp [and_comm]
  have hb : R.B ∈ Finset.univ.filter F.Binary := by simp [R.B_binary]
  have same : Finset.univ.filter F.Binary =
      Finset.univ.filter (fun n =>
        (Finset.univ.filter (fun m => F.parent m = some n)).card = 2) := by
    ext n
    simp [PhysicalForest.Binary, PhysicalForest.children]
  have count : (Finset.univ.filter F.Binary).card = 3 * (P - 1) := by
    rw [same]
    exact F.binary_count
  have hc : Fintype.card (BinaryTarget F R) = 3 * (P - 1) - 1 := by
    rw [Fintype.card_subtype, erase, Finset.card_erase_of_mem hb, count]
  simp only [Target, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, hc]
  omega

theorem ordinary_internal (d : Ordinary F R) : F.Internal d.val :=
  Finset.card_pos.mp (by rw [d.property.1]; omega)

namespace OriginalImplementation
variable {Q : Type u} [Fintype Q] [DecidableEq Q] {C : Controller P Q}
    (I : OriginalImplementation (e := e) F R C)

theorem AB_target : I.requestTarget R.A = I.requestTarget R.B :=
  (I.binary_targets R.A R.B R.A_binary R.B_binary).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))

private def targetControl (q : Target (e := e) F R) : Q :=
  match q with
  | .inl b => I.requestTarget b.val
  | .inr (.inl _) => I.requestTarget R.H1
  | .inr (.inr _) => C.initial

private theorem binary_control (n : Node) (hn : F.Binary n) :
    targetControl F R I (binaryTarget (e := e) F R n hn) = I.requestTarget n := by
  unfold binaryTarget
  split_ifs with hb
  · subst n
    exact AB_target F R I
  · rfl

theorem forced_control {n p : Node} {q : Target (e := e) F R} {c : Fin 3}
    (hp : F.parent n = some p)
    (hf : forcedRow F R n = some (.inr q, c)) :
    (I.readControl n, F.color n) = (targetControl F R I q, c) := by
  have child := I.child_target n p hp
  unfold forcedRow at hf
  simp only [hp] at hf
  split_ifs at hf with hb hk hr
  · have pair : binaryTarget (e := e) F R p hb = q ∧ F.color n = c := by simpa using hf
    rw [child, ← pair.1, binary_control F R I p hb, pair.2]
  · have pair : binaryTarget (e := e) F R R.H R.H_binary = q ∧ F.color n = c := by
      simpa using hf
    subst p
    rw [child, I.production_target, ← pair.1, binary_control F R I _ R.H_binary, pair.2]
  · have pair : resolvingTarget (e := e) F R = q ∧ F.color n = c := by simpa using hf
    rw [child, ← pair.1, pair.2]
    rcases hr with rfl | rfl
    · rfl
    · exact congrArg (fun z => (z, c)) I.resolving_target

/-- Every original implementation satisfies the finite source-only
compatibility check. J and Xi account for all history multiplicity; their
sum is exhausted by the two prescribed distinct double rows. -/
theorem compatible (I : OriginalImplementation (e := e) F R C) : Compatible (e := e) F R := by
  have hw : (I.readControl R.H, F.color R.H) = (I.readControl R.K, F.color R.K) := by
    rcases R.HK_parents with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · rw [I.child_target _ _ hp, I.child_target _ _ hq, AB_target F R I, R.HK_color]
    · rw [I.child_target _ _ hp, I.child_target _ _ hq, AB_target F R I, R.HK_color]
  have hv : (I.readControl R.H1, F.color R.H1) =
      (I.readControl R.K1, F.color R.K1) := by
    rw [I.child_target _ _ R.first_children.1, I.child_target _ _ R.first_children.2,
      I.production_target, R.child_color]
  intro n m row hn hm
  cases hpn : F.parent n with
  | none =>
    cases hpm : F.parent m with
    | none =>
      have cn : (.inl (), F.color n) = row := by simpa [forcedRow, hpn] using hn
      have cm : (.inl (), F.color m) = row := by simpa [forcedRow, hpm] using hm
      obtain ⟨a, ha⟩ := (F.roots_exact n).mp hpn
      obtain ⟨b, hb⟩ := (F.roots_exact m).mp hpm
      have ce : F.color n = F.color m := congrArg Prod.snd (cn.trans cm.symm)
      rw [ha, hb, F.root_color, F.root_color] at ce
      exact Or.inl (ha.trans (ce ▸ hb.symm))
    | some p =>
      have cn : (.inl (), F.color n) = row := by simpa [forcedRow, hpn] using hn
      unfold forcedRow at hm
      simp only [hpm] at hm
      split_ifs at hm <;> rw [← cn] at hm <;> simp at hm
  | some p =>
    cases hpm : F.parent m with
    | none =>
      have cm : (.inl (), F.color m) = row := by simpa [forcedRow, hpm] using hm
      unfold forcedRow at hn
      simp only [hpn] at hn
      split_ifs at hn <;> rw [← cm] at hn <;> simp at hn
    | some s =>
      obtain ⟨q, c⟩ := row
      cases q with
      | inl u =>
        unfold forcedRow at hn
        simp only [hpn] at hn
        split_ifs at hn <;> simp at hn
      | inr q =>
        have ne : F.parent n ≠ none := by rw [hpn]; simp
        have me : F.parent m ≠ none := by rw [hpm]; simp
        exact raw_fibers_only F R (fun n => (I.readControl n, F.color n)) hw hv
          I.shared_distinct I.indegree_surplus I.edge_surplus ne me
          ((forced_control F R I hpn hn).trans (forced_control F R I hpm hm).symm)



end OriginalImplementation

/-- Incompatible raw prescribed identities have no original implementation
on any finite nominal carrier. This branch assumes neither alpha nor a
capacity bound and retains the original stationary operational contract. -/
theorem incompatible_domain_empty (hc : ¬ Compatible (e := e) F R)
    {Q : Type u} [Fintype Q] [DecidableEq Q] (C : Controller P Q) :
    ¬ Nonempty (OriginalImplementation (e := e) F R C) := by
  rintro ⟨I⟩
  exact hc (OriginalImplementation.compatible F R I)

theorem wordData (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) : OriginalWordData F (controller F R α) where
  prefix_wait x t ht := prefix_is_wait F R α x ht
  read_event x i hi := event_is_read F R hc α x hi
  wait_event x i k hi hk := event_is_wait F R hc α x hi hk
  final_halt x := by rw [physical_terminal_run F R hc α x]; rfl

/-- U1 Initialized is supplied by the constructed total stationary table. -/
noncomputable def initialized (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) : Initialized (controller F R α) hP ell h :=
  initialize_original_paths F (controller F R α) (wordData F R hc α)

private theorem ordinary_target (α : Assignment (e := e) F R) (d : Ordinary F R) :
    nextTarget F R α d.val = (α.slot d).val.1 := by
  have nb : ¬ F.Binary d.val := fun hb => binary_not_unary F hb d.property.1
  simp [nextTarget, nb, d.property.2.1, d.property.2.2.1, d.property.2.2.2, d.property]


private theorem resolving_request (α : Assignment (e := e) F R) :
    nextTarget F R α R.H1 = resolvingTarget F R := by
  have nb : ¬ F.Binary R.H1 := fun hb => binary_not_unary F hb R.H1_unary
  have ne : R.H1 ≠ R.K := by
    have hs := (List.pairwise_cons.mp (List.pairwise_cons.mp R.marked_distinct).2).1
    exact Ne.symm (hs R.H1 (by simp))
  simp [nextTarget, nb, ne]

private theorem target_has_request (α : Assignment (e := e) F R)
    (q : Target (e := e) F R) :
    ∃ n, F.Internal n ∧ nextTarget F R α n = q := by
  cases q with
  | inl b =>
    refine ⟨b.val, Finset.card_pos.mp (by rw [b.property.1]; omega), ?_⟩
    simp [nextTarget, b.property.1, binaryTarget, b.property.2]
  | inr t =>
    cases t with
    | inl u =>
      cases u
      exact ⟨R.H1, Finset.card_pos.mp (by rw [R.H1_unary]; omega),
        resolving_request F R α⟩
    | inr i =>
      obtain ⟨d, hd⟩ := α.hits_extra i
      exact ⟨d.val, ordinary_internal F R d, (ordinary_target F R α d).trans hd⟩

noncomputable def requestLengths (α : Assignment (e := e) F R)
    (q : Target (e := e) F R) : Finset Node :=
  Finset.univ.filter (fun n => F.Internal n ∧ nextTarget F R α n = q)

/-- The joint maximum is exactly the maximum of actual source requests,
including binary parents, resolving histories, and all ordinary assignments. -/
private theorem L_is_request_max (α : Assignment (e := e) F R)
    (q : Target (e := e) F R) : L F R α q = (requestLengths F R α q).sup F.delay := by
  apply le_antisymm
  · apply max_le
    · cases q with
      | inl b =>
        apply Finset.sup_le
        intro p _
        split_ifs with hb ht
        · have hn : F.Internal p := Finset.card_pos.mp (by rw [hb]; omega)
          apply Finset.le_sup
          simp only [requestLengths, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hn, by simpa [nextTarget, hb] using ht⟩
        · exact Nat.zero_le _
        · exact Nat.zero_le _
      | inr t =>
        cases t with
        | inl u =>
          cases u
          change F.delay R.H1 ≤ _
          exact Finset.le_sup (s := requestLengths F R α (resolvingTarget F R))
            (f := F.delay) (b := R.H1) (by
            simp only [requestLengths, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨Finset.card_pos.mp (by rw [R.H1_unary]; omega),
              resolving_request F R α⟩)
        | inr i =>
          obtain ⟨n, hn, ht⟩ := target_has_request F R α (extraTarget F R i)
          exact le_trans (internal_positive F hn) (Finset.le_sup (by
            simp only [requestLengths, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hn, ht⟩))
    · apply Finset.sup_le
      intro d _
      split_ifs with hd
      · apply Finset.le_sup
        simp only [requestLengths, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨ordinary_internal F R d, (ordinary_target F R α d).trans hd⟩
      · exact Nat.zero_le _
  · apply Finset.sup_le
    intro n hn
    obtain ⟨hi, ht⟩ := (Finset.mem_filter.mp hn).2
    rw [← ht]
    exact request_bound F R α hi

theorem longest_request (α : Assignment (e := e) F R)
    (q : Target (e := e) F R) :
    ∃ n, F.Internal n ∧ nextTarget F R α n = q ∧ F.delay n = L F R α q := by
  have nonempty : (requestLengths F R α q).Nonempty := by
    obtain ⟨n, hn, ht⟩ := target_has_request F R α q
    exact ⟨n, by simp [requestLengths, hn, ht]⟩
  obtain ⟨n, hn, he⟩ := Finset.exists_mem_eq_sup _ nonempty F.delay
  obtain ⟨hi, ht⟩ := (Finset.mem_filter.mp hn).2
  exact ⟨n, hi, ht, he.symm.trans (L_is_request_max F R α q).symm⟩

theorem L_positive (α : Assignment (e := e) F R) (q : Target (e := e) F R) :
    0 < L F R α q := by
  obtain ⟨n, hn, _, hd⟩ := longest_request F R α q
  rw [← hd]
  exact internal_positive F hn

/-- Reachability concerns nominal control states, without restricting their
charged codomain or demanding all phase-control combinations be reachable. -/
def Reachable (α : Assignment (e := e) F R) (q : State F R α) : Prop :=
  ∃ x t, t ≤ stopTime F x ∧
    ((controller F R α).run hP (x, (controller F R α).initial) t).2 = q

private theorem event_reachable (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) (n : Node) :
    Reachable F R α (readState F R α (placement F R α n).1) := by
  obtain ⟨x, hx⟩ := F.support_nonempty n
  let source := (eventIncidenceEquiv F).symm ⟨(x, n), hx⟩
  have pair := congrArg Subtype.val ((eventIncidenceEquiv F).apply_symm_apply ⟨(x, n), hx⟩)
  have label : source.val.1 = x := congrArg Prod.fst pair
  let i := source.val.2.val
  have hi : i < F.reads x := label ▸ source.property
  have he : F.event x i = n := by
    have histories : F.event source.val.1 i = n := congrArg Prod.snd pair
    simpa only [label] using histories
  have hm := event_time_mono F x (i := i) (j := F.reads x - 1) (by omega) (by omega)
  refine ⟨x, readTime F (F.event x i), by unfold stopTime; omega, ?_⟩
  rw [physical_event_run F R hc α x i hi, he]

private theorem read_reachable (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) (q : ReadTarget (e := e) F R) :
    Reachable F R α (readState F R α q) := by
  cases q with
  | inl u =>
    cases u
    refine ⟨0, ell, Nat.le_of_lt ((initialized F R hc α).shape 0).first_before_stop, ?_⟩
    simp [prefix_run F R α 0 ell (le_refl ell), prefixAt]
  | inr q =>
    obtain ⟨n, hn, ht⟩ := target_has_request F R α q
    obtain ⟨m, hm⟩ := hn
    have hp := (Finset.mem_filter.mp hm).2
    have hr := event_reachable F R hc α m
    simpa [placement, hp, ht] using hr

theorem internal_event_more {n : Node} {x : Label P} {i : Nat}
    (hn : F.Internal n) (hi : i < F.reads x) (he : F.event x i = n) :
    i + 1 < F.reads x := by
  by_contra hh
  have hl : i = F.reads x - 1 := by omega
  obtain ⟨m, hm⟩ := hn
  apply F.last x m
  rw [← hl, he]
  exact (Finset.mem_filter.mp hm).2

private theorem tail_reachable (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) (q : Target (e := e) F R) (j : Fin (L F R α q)) :
    Reachable F R α (tail F R α q j) := by
  obtain ⟨n, hn, ht, hd⟩ := longest_request F R α q
  obtain ⟨x, hx⟩ := F.support_nonempty n
  obtain ⟨i, hi, he⟩ := F.support_events n x hx
  have more := internal_event_more F hn hi he
  let k := F.delay n - 1 - j.val
  have hk : k < F.delay (F.event x i) := by rw [he, hd]; have := j.isLt; omega
  have hp := physical_wait_run F R hc α x i k more hk
  have hm := event_time_mono F x (i := i + 1) (j := F.reads x - 1) (by omega) (by omega)
  rw [event_time_step F x i more] at hm
  refine ⟨x, readTime F (F.event x i) + 1 + k, by unfold stopTime; omega, ?_⟩
  rw [hp]
  simp only [he, tail]
  apply congrArg (fun p : Σ q : Target (e := e) F R, Fin (L F R α q) =>
    (Sum.inr (Sum.inr (Sum.inr p)) : State F R α))
  have ht' : nextTarget F R α (F.event x i) = q := he ▸ ht
  apply Sigma.ext ht'
  apply (Fin.heq_ext_iff (congrArg (L F R α) ht')).mpr
  change F.delay n - 1 - k = j.val
  have hj := j.isLt
  unfold k
  omega

/-- Every terminal, inventory read, prefix position and longest-tail unit is
visited by an original initialized input, including targets on read cycles. -/
theorem all_states_reachable (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) (q : State F R α) : Reachable F R α q := by
  rcases q with x | (r | (i | ⟨r, j⟩))
  · exact ⟨x, stopTime F x, le_refl _,
      congrArg Prod.snd (physical_terminal_run F R hc α x)⟩
  · exact read_reachable F R hc α r
  · refine ⟨0, i.val, Nat.le_of_lt (lt_trans i.isLt
        ((initialized F R hc α).shape 0).first_before_stop), ?_⟩
    simp [prefix_run F R α 0 i.val (Nat.le_of_lt i.isLt), prefixAt, i.isLt, prefixTag]
  · exact tail_reachable F R hc α r j


/-- All tags, rather than a reachable subtype, are charged in the exact
original nominal formula. An extra target pays its joint maximum once. -/
theorem nominal_capacity (α : Assignment (e := e) F R) :
    Fintype.card (State F R α) =
      3 * P + 2 * (3 * (P - 1)) + 1 + ell + 2 * e +
        ∑ q : Target (e := e) F R, (L F R α q - 1) := by
  let : NeZero (3 * P) := ⟨by omega⟩
  have sum_eq : (∑ q : Target (e := e) F R, L F R α q) =
      (∑ q : Target (e := e) F R, (L F R α q - 1)) + Fintype.card (Target (e := e) F R) := by
    calc
      _ = ∑ q : Target (e := e) F R, ((L F R α q - 1) + 1) :=
        Finset.sum_congr rfl (fun q _ => (Nat.sub_add_cancel (L_positive F R α q)).symm)
      _ = _ := by simp [Finset.sum_add_distrib]
  simp only [State, ReadTarget, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin,
    Fintype.card_unit, ZMod.card, target_card F R, sum_eq]
  omega

private noncomputable def readAsActual (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) (q : ReadTarget (e := e) F R) :
    ActualRead (controller F R α) hP (initialized F R hc α) := by
  refine ⟨readState F R α q, ?_⟩
  obtain ⟨x, t, ht, he⟩ := read_reachable F R hc α q
  have hr : IsRead (controller F R α) (readState F R α q) := ⟨_, rfl⟩
  have less : t < stopTime F x := by
    by_contra hh
    have eq : t = stopTime F x := by omega
    subst t
    obtain ⟨row, hrow⟩ := hr
    rw [← he, (wordData F R hc α).final_halt x] at hrow
    cases hrow
  exact ⟨hr, x, t, less, he⟩

/-- The entire canonical inventory is exactly the actual read-state carrier;
unused states are still charged by State and are not removed by this map. -/
noncomputable def actualReadEquiv (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) : ReadTarget (e := e) F R ≃
      ActualRead (controller F R α) hP (initialized F R hc α) := by
  apply Equiv.ofBijective (readAsActual F R hc α)
  constructor
  · intro q r he
    have hval := congrArg Subtype.val he
    simpa [readAsActual, readState] using hval
  · rintro ⟨state, ⟨row, hr⟩, live⟩
    rcases state with x | (q | (i | ⟨q, j⟩))
    · cases hr
    · exact ⟨q, Subtype.ext rfl⟩
    · cases hr
    · cases hr

private theorem actual_read_card (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) :
    Fintype.card (ActualRead (controller F R α) hP (initialized F R hc α)) =
      3 * (P - 1) + 1 + e := by
  rw [← Fintype.card_congr (actualReadEquiv F R hc α)]
  simp [ReadTarget, target_card F R, Nat.add_comm, Nat.add_left_comm]

/-- Actual used digit rows coincide with the complete-history placement.
Every original event is retained; no reachable-only carrier is charged. -/
theorem actual_row_correspondence (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) (q : ReadTarget (e := e) F R) (c : Fin 3) :
    (∃ x t, t < stopTime F x ∧
      ((controller F R α).run hP (x, (controller F R α).initial) t).2 = readState F R α q ∧
      digit hP ((controller F R α).run hP (x, (controller F R α).initial) t).1 = c) ↔
    ∃ n, placement F R α n = (q, c) := by
  have snd (n : Node) : (placement F R α n).2 = F.color n := by
    cases hp : F.parent n <;> simp [placement, hp]
  constructor
  · rintro ⟨x, t, ht, he, hd⟩
    have hr : IsRead (controller F R α)
        ((controller F R α).run hP (x, (controller F R α).initial) t).2 := by
      rw [he]; exact ⟨_, rfl⟩
    obtain ⟨i, hi, htime⟩ := (original_reads_exact F (controller F R α)
      (wordData F R hc α) x ht).mp hr
    rw [htime, physical_event_run F R hc α x i hi] at he hd
    have hq : (placement F R α (F.event x i)).1 = q := by simpa [readState] using he
    refine ⟨F.event x i, Prod.ext hq ?_⟩
    rw [snd]
    exact (support_digit F (F.event_support x i hi)).symm.trans hd
  · rintro ⟨n, hn⟩
    obtain ⟨x, hx⟩ := F.support_nonempty n
    obtain ⟨i, hi, he⟩ := F.support_events n x hx
    have hm := event_time_mono F x (i := i) (j := F.reads x - 1) (by omega) (by omega)
    refine ⟨x, readTime F (F.event x i), by unfold stopTime; omega, ?_, ?_⟩
    · rw [physical_event_run F R hc α x i hi, he, hn]
    · rw [physical_event_run F R hc α x i hi, he]
      exact (support_digit F hx).trans ((snd n).symm.trans (congrArg Prod.snd hn))


/-- The tagged read-state map is injective on the full canonical inventory. -/
private theorem readState_injective (α : Assignment (e := e) F R) :
    Function.Injective (readState F R α) := by
  intro q r he
  simpa [readState] using he

private noncomputable def rowState (α : Assignment (e := e) F R)
    (row : Row (e := e) F R) : State F R α × Fin 3 :=
  (readState F R α row.1, row.2)

private theorem rowState_injective (α : Assignment (e := e) F R) :
    Function.Injective (rowState F R α) := by
  intro a b he
  exact Prod.ext (readState_injective F R α (congrArg Prod.fst he))
    (by simpa [rowState] using congrArg Prod.snd he)

private theorem rowState_placement (α : Assignment (e := e) F R) :
    rowState F R α ∘ placement F R α =
      fun n => (readState F R α (placement F R α n).1, F.color n) := by
  funext n
  cases hp : F.parent n <;> simp [rowState, placement, hp]

private theorem binary_target_equal (α : Assignment (e := e) F R)
    {n m : Node} (hn : F.Binary n) (hm : F.Binary m) :
    nextTarget F R α n = nextTarget F R α m ↔
      n = m ∨ (n = R.A ∧ m = R.B) ∨ (n = R.B ∧ m = R.A) := by
  simp only [nextTarget, dif_pos hn, dif_pos hm]
  by_cases mb : m = R.B
  · subst m
    have targetB : binaryTarget (e := e) F R R.B hm =
        .inl ⟨R.A, R.A_binary, R.AB_distinct⟩ := by simp [binaryTarget]
    rw [targetB, binary_representative F R n hn]
    simp [Ne.symm R.AB_distinct, or_comm]
  · have targetM : binaryTarget (e := e) F R m hm = .inl ⟨m, hm, mb⟩ := by
      simp [binaryTarget, mb]
    rw [targetM, binary_representative F R n hn]
    simp [mb, and_comm]

/-- Every feasible assignment implements the original fixed-domain contract
on the existing total table and its entire charged nominal carrier. -/
noncomputable def originalImplementation (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) :
    OriginalImplementation (e := e) F R (controller F R α) where
  word := wordData F R hc α
  readControl n := readState F R α (placement F R α n).1
  requestTarget n := readState F R α (.inr (nextTarget F R α n))
  events := physical_event_run F R hc α
  child_target n p hp := by simp [placement, hp]
  literal_requests n hn := by
    refine ⟨fun c => readRow F R α ((placement F R α n).1, c), rfl, ?_⟩
    have row : ((placement F R α n).1, F.color n) = placement F R α n := by
      cases hp : F.parent n <;> simp [placement, hp]
    dsimp only
    rw [row, read_row_at F R hc α, requestState, dif_pos hn]
    have hw := tail_chain F R α (nextTarget F R α n) (F.delay n - 1)
      (by have := request_bound F R α hn; have := internal_positive F hn; omega)
    have hd := internal_positive F hn
    simpa only [Nat.sub_add_cancel hd] using hw
  binary_targets n m hn hm := by
    rw [(readState_injective F R α).eq_iff, Sum.inr.injEq]
    exact binary_target_equal F R α hn hm
  production_target := by
    have nb : ¬ F.Binary R.K := fun hb => binary_not_unary F hb R.K_unary
    simp [nextTarget, nb, R.H_binary]
  resolving_target := by
    have nb : ¬ F.Binary R.K1 := fun hb => binary_not_unary F hb R.K1_unary
    have ne : R.K1 ≠ R.K := by
      have hs := (List.pairwise_cons.mp (List.pairwise_cons.mp R.marked_distinct).2).1
      exact Ne.symm (hs R.K1 (by simp))
    rw [resolving_request F R α]
    simp [nextTarget, nb, ne]
  resolving_separate n hn := by
    rw [resolving_request F R α]
    simp [nextTarget, hn, resolvingTarget, binaryTarget, readState]
  shared_distinct := by
    have hw := congrFun (rowState_placement F R α) R.H
    have hv := congrFun (rowState_placement F R α) R.H1
    rw [← hw, ← hv]
    exact fun he => shared_rows_distinct F R hc α (rowState_injective F R α he)
  indegree_surplus := by
    rw [← rowState_placement F R α, rawJ_map F (placement F R α)
      (rowState F R α) (rowState_injective F R α), rawJ_placement]
    exact incoming_excess F R hc α
  edge_surplus := by
    rw [← rowState_placement F R α, rawXi_map F (placement F R α)
      (rowState F R α) (rowState_injective F R α), rawXi_placement]
    exact repetition_excess F R hc α
  actual_reads := actual_read_card F R hc α

/-- The operational handoff supplies the original implementation, U1
initialization, all charged-state reachability and the exact nominal count. -/
theorem operational_realization (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) :
    Nonempty (OriginalImplementation (e := e) F R (controller F R α)) ∧
    Nonempty (Initialized (controller F R α) hP ell h) ∧
    (∀ state, Reachable F R α state) ∧
    Fintype.card (State F R α) =
      3 * P + 2 * (3 * (P - 1)) + 1 + ell + 2 * e +
        ∑ q : Target (e := e) F R, (L F R α q - 1) :=
  ⟨⟨originalImplementation F R hc α⟩, ⟨initialized F R hc α⟩,
    all_states_reachable F R hc α, nominal_capacity F R α⟩

/-- The construction's complete operational evidence. This is an upper-bound
realization, not the converse or the attained minimum over arbitrary tables. -/
structure Realization (α : Assignment (e := e) F R) where
  original : OriginalImplementation (e := e) F R (controller F R α)
  initialized : Initialized (controller F R α) hP ell h
  events : ∀ x i, i < F.reads x →
    (controller F R α).run hP (x, (controller F R α).initial)
      (readTime F (F.event x i)) =
    (x + (F.shift (F.event x i) : Label P),
      readState F R α (placement F R α (F.event x i)).1)
  unit_phases : ∀ x i k, i + 1 < F.reads x → k < F.delay (F.event x i) →
    ((controller F R α).run hP (x, (controller F R α).initial)
      (readTime F (F.event x i) + 1 + k)).1 =
        x + (F.shift (F.event x i) : Label P) + (k : Label P)
  final_output : ∀ x, (controller F R α).run hP (x, (controller F R α).initial) (stopTime F x) =
    (x + (F.shift (F.event x (F.reads x - 1)) : Label P), terminal F R α x)
  reachable : ∀ state, Reachable F R α state
  reads : Fintype.card (ActualRead (controller F R α) hP initialized) = 3 * (P - 1) + 1 + e
  roots : (Finset.univ.image F.root).card = 3
  leaves : Fintype.card {n : Node // ¬ F.Internal n} = 3 * P
  graph : J F R α = 1 ∧ sharing F R α = 1 ∧ Xi F R α = 1
  inventory : ∀ q : Target (e := e) F R, (occupied F R q).card = match q with
    | .inl b => if b.val = R.A then 3 else 2
    | .inr (.inl _) => 2
    | .inr (.inr _) => 0
  capacity : Fintype.card (State F R α) =
    3 * P + 2 * (3 * (P - 1)) + 1 + ell + 2 * e +
      ∑ q : Target (e := e) F R, (L F R α q - 1)

/-- Every feasible alpha constructs one total stationary unit table preserving
all original finite paths, labelled events, literal phases and deadlines. -/
noncomputable def realize (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) : Realization F R α where
  original := Classical.choice (operational_realization F R hc α).1
  initialized := initialized F R hc α
  events := physical_event_run F R hc α
  unit_phases x i k hi hk := congrArg Prod.fst (physical_wait_run F R hc α x i k hi hk)
  final_output := physical_terminal_run F R hc α
  reachable := all_states_reachable F R hc α
  reads := actual_read_card F R hc α
  roots := root_count F
  leaves := leaf_count F
  graph := ⟨incoming_excess F R hc α, sharing_excess F R α, repetition_excess F R hc α⟩
  inventory := occupied_counts F R
  capacity := nominal_capacity F R α


end D5.S3.ObserverMemory.Algorithms.FixedForestUnitCapacity
