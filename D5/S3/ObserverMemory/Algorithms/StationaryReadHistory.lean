/- GID: D5/S3/ObserverMemory/Algorithms/StationaryReadHistory
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/StationaryReadHistory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual original controller histories and their forest laws. -/

import D5.S3.ObserverMemory.Algorithms.StationaryHistoryRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.StationaryReadHistory

open StationaryUnitControl
open scoped BigOperators
open private replay_append trace_length shift_append read_time_mem event_time_bound event_is_read
  trace_eq_map trace_take trace_get action_read_iff count_reads_trace reads_pos reads_bound
  first_read_time last_read_time read_rank event_level event_time event_shift support_nonempty
  previous_times_event previous_prefix_actual previous_time_last trace_common digit_block
  first_event_word root_word_actual first_event first_parent event_color trace_counts
  post_event_control final_halt terminal_event_iff event_parent_or_first parent_level
  support_parent from D5.S3.ObserverMemory.Algorithms.StationaryHistoryPrefix
open private indexed_disjoint literal_gap_positive root_data from
  D5.S3.ObserverMemory.Algorithms.StationaryHistoryContinuation
open private consecutive_waits same_row_post trace_wait_segment event_word_successor chosen_child
  supported_color digit_translate from D5.S3.ObserverMemory.Algorithms.StationaryHistoryRows
attribute [local instance] Classical.propDecidable

universe u
variable {P ell h : Nat} {Q : Type u} (C : Controller P Q) (hP : 1 < P)
    (I : Initialized C hP ell h)

private theorem same_digit_span [NeZero (3 * P)] {a b : ZMod (3 * P)}
    (hd : digit hP a = digit hP b) : a.val < b.val + P ∧ b.val < a.val + P := by
  have hdiv : a.val / P = b.val / P := congrArg Fin.val hd
  have ha := Nat.div_add_mod a.val P
  have hb := Nat.div_add_mod b.val P
  rw [hdiv] at ha
  have ham := Nat.mod_lt a.val (by omega : 0 < P)
  have hbm := Nat.mod_lt b.val (by omega : 0 < P)
  omega

private theorem val_add_cases [NeZero (3 * P)] (a d : ZMod (3 * P)) :
    (a + d).val = a.val + d.val ∨ (a + d).val + 3 * P = a.val + d.val := by
  by_cases hh : a.val + d.val < 3 * P
  · exact Or.inl (ZMod.val_add_of_lt hh)
  · right
    have he := ZMod.val_add_val_of_le (a := a) (b := d) (by omega)
    omega

private theorem translation_between [NeZero (3 * P)] {a b c : ZMod (3 * P)}
    (d : ZMod (3 * P)) (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val)
    (hac : digit hP a = digit hP c) (ht : digit hP (a + d) = digit hP (c + d)) :
    (a + d).val ≤ (b + d).val ∧ (b + d).val ≤ (c + d).val ∧
      digit hP (b + d) = digit hP (a + d) := by
  have hspan := same_digit_span hP hac
  have htspan := same_digit_span hP ht
  have ha := val_add_cases a d
  have hb := val_add_cases b d
  have hc := val_add_cases c d
  have hav := (a + d).val_lt
  have hbv := (b + d).val_lt
  have hcv := (c + d).val_lt
  have horder : (a + d).val ≤ (b + d).val ∧ (b + d).val ≤ (c + d).val := by
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;> omega
  refine ⟨horder.1,horder.2,?_⟩
  apply Fin.ext
  change (b + d).val / P = (a + d).val / P
  have hda := Nat.div_le_div_right horder.1 (c := P)
  have hdc := Nat.div_le_div_right horder.2 (c := P)
  have he : (a + d).val / P = (c + d).val / P := congrArg Fin.val ht
  omega

/-- Inside its current absolute digit block, every actual full-history fiber is
an interval. This convexity follows through literal translations and read cuts. -/
theorem history_phase_convex [NeZero (3 * P)] (n : History C hP I)
    (x y z : ZMod (3 * P)) (hx : x ∈ support C hP I n) (hz : z ∈ support C hP I n)
    (hy : digit hP (y + (historyShift C hP I n : ZMod (3 * P))) = color C hP I n)
    (hxy : (x + (historyShift C hP I n : ZMod (3 * P))).val ≤
      (y + (historyShift C hP I n : ZMod (3 * P))).val)
    (hyz : (y + (historyShift C hP I n : ZMod (3 * P))).val ≤
      (z + (historyShift C hP I n : ZMod (3 * P))).val) : y ∈ support C hP I n := by
  generalize hl : level C hP I n = k
  induction k using Nat.strong_induction_on generalizing n with
  | h k ih =>
    cases hp : parent C hP I n with
    | none =>
      obtain ⟨c,he⟩ := (roots_exact C hP I n).1 hp
      subst n
      rw [(root_data C hP I c).1,(root_data C hP I c).2.1] at hy
      exact (root_support C hP I c y).2 hy
    | some p =>
      have hxp := support_parent C hP I hp hx
      have hzp := support_parent C hP I hp hz
      have hxn := supported_color C hP I n x hx
      have hzn := supported_color C hP I n z hz
      have hxc := supported_color C hP I p x hxp
      have hzc := supported_color C hP I p z hzp
      have ht := translation_between hP (-(delay C hP I p : ZMod (3 * P))) hxy hyz
        (hxn.trans hzn.symm) (by
          rw [(child_delay_target C hP I hp).2.2.2,Nat.cast_add]
          simpa only [add_assoc,add_neg_cancel,add_zero] using hxc.trans hzc.symm)
      rw [(child_delay_target C hP I hp).2.2.2,Nat.cast_add] at ht
      simp only [add_assoc,add_neg_cancel,add_zero] at ht
      have hym : y ∈ support C hP I p := ih (level C hP I p) (by
        have hh := parent_level C hP I hp; omega) p hxp hzp
          (ht.2.2.trans hxc) ht.1 ht.2.1 rfl
      exact (child_support C hP I hp y).2 ⟨hym,hy⟩

private theorem digit_block_bounds [NeZero (3 * P)] {s : ZMod (3 * P)} {c : Fin 3}
    (hc : digit hP s = c) : c.val * P ≤ s.val ∧ s.val < c.val * P + P := by
  have he := Nat.div_add_mod s.val P
  have hd : s.val / P = c.val := congrArg Fin.val hc
  rw [hd,Nat.mul_comm] at he
  have hm := Nat.mod_lt s.val (by omega : 0 < P)
  omega

/-- Actual supports have nonempty half-open physical intervals within their
current absolute digit block, for every full history of any Initialized C. -/
theorem history_interval_exists [NeZero (3 * P)] (n : History C hP I) :
    ∃ ab : Nat × Nat, ab.1 < ab.2 ∧ ab.2 ≤ P ∧ ∀ x : ZMod (3 * P),
      x ∈ support C hP I n ↔
        (color C hP I n).val * P + ab.1 ≤ (x + (historyShift C hP I n : ZMod (3 * P))).val ∧
        (x + (historyShift C hP I n : ZMod (3 * P))).val < (color C hP I n).val * P + ab.2 := by
  let v := (support C hP I n).image (fun x => (x + (historyShift C hP I n : ZMod (3 * P))).val)
  have hv : v.Nonempty := (support_nonempty C hP I n).image _
  obtain ⟨x,hx,hxmin⟩ := Finset.mem_image.mp (v.min'_mem hv)
  obtain ⟨z,hz,hzmax⟩ := Finset.mem_image.mp (v.max'_mem hv)
  have hxb := digit_block_bounds hP (supported_color C hP I n x hx)
  have hzb := digit_block_bounds hP (supported_color C hP I n z hz)
  have hminmax : v.min' hv ≤ v.max' hv := Finset.min'_le _ _ (v.max'_mem hv)
  let base := (color C hP I n).val * P
  have hmin : base ≤ v.min' hv := by rw [hxmin] at hxb; exact hxb.1
  have hmax : v.max' hv < base + P := by rw [hzmax] at hzb; exact hzb.2
  refine ⟨(v.min' hv - base,v.max' hv - base + 1), by dsimp only; omega,
    by dsimp only; omega,?_⟩
  intro y
  dsimp only
  constructor
  · intro hy
    have hym : (y + (historyShift C hP I n : ZMod (3 * P))).val ∈ v :=
      Finset.mem_image.mpr ⟨y,hy,rfl⟩
    have ha := v.min'_le _ hym
    have hb := v.le_max' _ hym
    change base + (v.min' hv - base) ≤ _ ∧ _ < base + (v.max' hv - base + 1)
    omega
  · rintro ⟨ha,hb⟩
    have ha' : v.min' hv ≤ (y + (historyShift C hP I n : ZMod (3 * P))).val := by
      change base + (v.min' hv - base) ≤ _ at ha
      omega
    have hb' : (y + (historyShift C hP I n : ZMod (3 * P))).val ≤ v.max' hv := by
      change _ < base + (v.max' hv - base + 1) at hb
      omega
    have hc : digit hP (y + (historyShift C hP I n : ZMod (3 * P))) = color C hP I n := by
      apply Fin.ext
      apply Nat.div_eq_of_lt_le (by dsimp only [base] at *; omega)
        (by simp only [Nat.add_mul,Nat.one_mul]; dsimp only [base] at *; omega)
    exact history_phase_convex C hP I n x y z hx hz hc (by rwa [hxmin]) (by rwa [hzmax])

noncomputable def intervalEndpoints [NeZero (3 * P)] (n : History C hP I) : Nat × Nat :=
  Classical.choose (history_interval_exists C hP I n)

noncomputable def lower [NeZero (3 * P)] (n : History C hP I) : Nat :=
  (intervalEndpoints C hP I n).1
noncomputable def upper [NeZero (3 * P)] (n : History C hP I) : Nat :=
  (intervalEndpoints C hP I n).2

private theorem interval_data [NeZero (3 * P)] (n : History C hP I) :
    lower C hP I n < upper C hP I n ∧ upper C hP I n ≤ P ∧ ∀ x,
      x ∈ support C hP I n ↔
        (color C hP I n).val * P + lower C hP I n ≤
          (x + (historyShift C hP I n : ZMod (3 * P))).val ∧
        (x + (historyShift C hP I n : ZMod (3 * P))).val <
          (color C hP I n).val * P + upper C hP I n :=
  Classical.choose_spec (history_interval_exists C hP I n)

noncomputable def forestEvent [NeZero (3 * P)] (x : ZMod (3 * P)) (i : Nat) : History C hP I :=
  if hi : i < reads C hP I x then event C hP I ⟨x,⟨i, hi⟩⟩ else root C hP I 0

/-- Every PhysicalForest field, including intervals, branching and binary_count,
is obtained from this one Initialized implementation and its full indexed words. -/
noncomputable def physicalForest [NeZero (3 * P)] :
    FixedForestTargetInventory.PhysicalForest P h ell (History C hP I) hP where
  parent := parent C hP I
  root := root C hP I
  color := color C hP I
  shift := historyShift C hP I
  level := level C hP I
  delay := delay C hP I
  leafLabel := leafLabel C hP I
  support := support C hP I
  lower := lower C hP I
  upper := upper C hP I
  reads := reads C hP I
  event := forestEvent C hP I
  reads_pos := reads_pos C hP I
  reads_bound := reads_bound C hP I
  root_parent := fun c => (roots_exact C hP I _).2 ⟨c,rfl⟩
  root_color := fun c => (root_data C hP I c).1
  root_shift := fun c => (root_data C hP I c).2.1
  root_level := fun c => (root_data C hP I c).2.2
  roots_exact := roots_exact C hP I
  first := by
    intro x
    simp only [forestEvent,dif_pos (reads_pos C hP I x)]
    exact first_event C hP I x
  event_level := by
    intro x i hi
    simp only [forestEvent,dif_pos hi]
    exact event_level C hP I ⟨x,⟨i, hi⟩⟩
  event_support := by
    intro x i hi
    simp only [forestEvent,dif_pos hi]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨i, hi⟩,rfl⟩
  support_events := by
    intro n x hx
    obtain ⟨_,i, hi⟩ := Finset.mem_filter.mp hx
    refine ⟨i.val,i.isLt,?_⟩
    simpa only [forestEvent,dif_pos i.isLt] using hi
  support_nonempty := support_nonempty C hP I
  interval := fun n x => (interval_data C hP I n).2.2 x
  interval_bounds := fun n => ⟨(interval_data C hP I n).1,(interval_data C hP I n).2.1⟩
  child_shift := fun _ _ hp => (child_delay_target C hP I hp).2.2.2
  child_level := fun _ _ hp => parent_level C hP I hp
  child_digit_injective := fun _ _ _ hn hm hc => child_digit_injective C hP I hn hm hc
  successor := by
    intro x i hi
    simp only [forestEvent,dif_pos hi,dif_pos (show i < reads C hP I x from by omega)]
    exact parent_successor C hP I x i hi
  last := by
    intro x n
    have hi : reads C hP I x - 1 < reads C hP I x := by
      have := reads_pos C hP I x; omega
    simp only [forestEvent,dif_pos hi]
    have hl : IsLeaf C hP I (event C hP I (finalEvent C hP I x)) :=
      (leaf_iff_terminal C hP I _).2 ⟨x,final_halt C hP I x⟩
    exact hl n
  leaf_original := fun n x hx hn => (actual_history_data C hP I).leaf_original n x hn hx
  positive := by
    intro n hn
    obtain ⟨m,hm⟩ := hn
    exact (child_delay_target C hP I hm).1
  branching := branching C hP I
  binary_count := binary_count C hP I

noncomputable def modularCut [NeZero (3 * P)] (n : History C hP I) : Nat :=
  P - delay C hP I n % P

private theorem support_low_bounds [NeZero (3 * P)] (n : History C hP I)
    (x : ZMod (3 * P)) (hx : x ∈ support C hP I n) :
    lower C hP I n ≤ (x + (historyShift C hP I n : ZMod (3 * P))).val % P ∧
    (x + (historyShift C hP I n : ZMod (3 * P))).val % P < upper C hP I n := by
  have hi := ((interval_data C hP I n).2.2 x).1 hx
  have hc : (x + (historyShift C hP I n : ZMod (3 * P))).val / P =
      (color C hP I n).val := congrArg Fin.val (supported_color C hP I n x hx)
  have he := Nat.div_add_mod (x + (historyShift C hP I n : ZMod (3 * P))).val P
  rw [hc,Nat.mul_comm] at he
  omega

/-- A binary full history crosses the common modular cut in its actual source
digit. Unary histories may lie wholly on either side, including singleton paths. -/
theorem binary_crosses_cut [NeZero (3 * P)] (p : History C hP I)
    (hp : (children C hP I p).card = 2) :
    lower C hP I p < modularCut C hP I p ∧ modularCut C hP I p < upper C hP I p := by
  obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp hp
  have ha : parent C hP I a = some p :=
    (Finset.mem_filter.mp (show a ∈ children C hP I p by rw [he]; simp)).2
  have hb : parent C hP I b = some p :=
    (Finset.mem_filter.mp (show b ∈ children C hP I p by rw [he]; simp)).2
  have hcne : color C hP I a ≠ color C hP I b :=
    fun hc => hab (child_digit_injective C hP I ha hb hc)
  obtain ⟨x,hx⟩ := support_nonempty C hP I a
  obtain ⟨y,hy⟩ := support_nonempty C hP I b
  have hxp := support_parent C hP I ha hx
  have hyp := support_parent C hP I hb hy
  have hxl := support_low_bounds C hP I p x hxp
  have hyl := support_low_bounds C hP I p y hyp
  have hxd := supported_color C hP I p x hxp
  have hyd := supported_color C hP I p y hyp
  have hxc := supported_color C hP I a x hx
  have hyc := supported_color C hP I b y hy
  have htx := digit_translate hP (x + (historyShift C hP I p : ZMod (3 * P))) (delay C hP I p)
  have hty := digit_translate hP (y + (historyShift C hP I p : ZMod (3 * P))) (delay C hP I p)
  rw [(child_delay_target C hP I ha).2.2.2,Nat.cast_add,← add_assoc] at hxc
  rw [(child_delay_target C hP I hb).2.2.2,Nat.cast_add,← add_assoc] at hyc
  rw [hxd,hxc] at htx
  rw [hyd,hyc] at hty
  have hrem := Nat.mod_lt (delay C hP I p) (by omega : 0 < P)
  dsimp only [modularCut]
  by_cases hhx : P ≤ (x + (historyShift C hP I p : ZMod (3 * P))).val % P + delay C hP I p % P <;>
    by_cases hhy : P ≤ (y + (historyShift C hP I p : ZMod (3 * P))).val % P + delay C hP I p % P
  · rw [if_pos hhx] at htx
    rw [if_pos hhy] at hty
    exact False.elim (hcne (Fin.ext (htx.trans hty.symm)))
  · omega
  · omega
  · rw [if_neg hhx] at htx
    rw [if_neg hhy] at hty
    exact False.elim (hcne (Fin.ext (htx.trans hty.symm)))

/-- At most one binary full history occupies any actual source row. Shared rows
have a common literal wait and hence one cut; disjoint intervals cannot both cross it. -/
theorem binary_row_unique [NeZero (3 * P)] {n m : History C hP I}
    (hn : (children C hP I n).card = 2) (hm : (children C hP I m).card = 2)
    (hq : readControl C hP I n = readControl C hP I m)
    (hc : color C hP I n = color C hP I m) : n = m := by
  have hni : (children C hP I n).Nonempty := Finset.card_pos.mp (by omega)
  have hd := (row_delay_target C hP I hni hq hc).1
  have hcut : modularCut C hP I n = modularCut C hP I m := by simp only [modularCut,hd]
  have hnc := binary_crosses_cut C hP I n hn
  have hmc := binary_crosses_cut C hP I m hm
  have hnu := (interval_data C hP I n).2.1
  let v : ZMod (3 * P) := (((color C hP I n).val * P + modularCut C hP I n : Nat) : ZMod (3 * P))
  have hvlt : (color C hP I n).val * P + modularCut C hP I n < 3 * P := by
    have hb := Nat.mul_le_mul_right P
      (show (color C hP I n).val + 1 ≤ 3 from by have := (color C hP I n).isLt; omega)
    simp only [Nat.add_mul,Nat.one_mul] at hb
    omega
  have hv : v.val = (color C hP I n).val * P + modularCut C hP I n :=
    ZMod.val_natCast_of_lt hvlt
  have phase_member (p : History C hP I) (hpc : color C hP I p = color C hP I n)
      (hpk : modularCut C hP I p = modularCut C hP I n)
      (hp : lower C hP I p < modularCut C hP I p ∧ modularCut C hP I p < upper C hP I p) :
      v ∈ phaseSupport C hP I p := by
    apply Finset.mem_image.mpr
    refine ⟨v - (historyShift C hP I p : ZMod (3 * P)),?_,sub_add_cancel _ _⟩
    apply ((interval_data C hP I p).2.2 _).2
    rw [sub_add_cancel,hv,hpc]
    rw [hpk] at hp
    omega
  have hvn := phase_member n rfl rfl hnc
  have hvm := phase_member m hc.symm hcut.symm hmc
  by_contra hne
  exact Finset.disjoint_left.mp (same_control_phase_disjoint C hP I hne hq) hvn hvm


end D5.S3.ObserverMemory.Algorithms.StationaryReadHistory
