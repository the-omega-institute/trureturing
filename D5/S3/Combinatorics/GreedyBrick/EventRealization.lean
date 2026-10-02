/- GID: D5/S3/Combinatorics/GreedyBrick/EventRealization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GreedyBrick/EventRealization
   mirror-E: none(waiver:infinite-rest-history)
   anchors: [mathlib/module/Mathlib.Data.Nat.Find]
   utility: none
   digest: Actual rest histories have finite coordinate budgets and recurring labels. -/

import D5.S3.Combinatorics.GreedyBrick.SuccessorBand
import Mathlib.Data.Nat.Find

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GreedyBrick.EventRealization
open D5.S3.Combinatorics.GreedyBrick.SuccessorBand

/-- Later labels are the actual first-zero labels of the supplied rest
transitions. Event zero of a bare history has no initialization constraint. -/
structure RestHistory where
  state : ℕ → RestState
  bin : ℕ → ℕ
  step : ∀ t, RestEventStep (state t) (state (t + 1)) (bin (t + 1))

/-- Initial source endpoint and unbounded-height supplier. -/
structure RestTrace extends RestHistory where
  initial_endpoint : (state 0).endpoint = 1
  initial_capacity : (state 0).capacity = [1]
  initial_bin : bin 0 = 1
  unbounded : ∀ h, ∃ t, h ≤ (state t).capacity.length

instance : Coe RestTrace RestHistory := ⟨RestTrace.toRestHistory⟩

/-- Higher events in the next d transitions after e. -/
def higherSteps (T : RestHistory) (i e d : ℕ) : Finset ℕ :=
  (Finset.range d).filter fun q => i < T.bin (e + q + 1)

/-- With no reset of an extant coordinate, each higher event consumes one
unit of its finite capacity. Every new height consumes one such unit too.
The option-valued coordinates ensure absent bins receive no capacity. -/
theorem no_reset_budget (T : RestHistory) (i e d c : ℕ)
    (hi : 0 < i)
    (hc : (T.state e).capacity[i - 1]? = some c)
    (hn : ∀ g, e < g → g ≤ e + d → T.bin g ≠ i) :
    ∃ r, (T.state (e + d)).capacity[i - 1]? = some r ∧
      r + (higherSteps T i e d).card = c ∧
      (T.state (e + d)).capacity.length ≤
        (T.state e).capacity.length + (higherSteps T i e d).card := by
  classical
  induction d with
  | zero => exact ⟨c, by simpa using hc, by simp [higherSteps], by simp [higherSteps]⟩
  | succ d ih =>
    obtain ⟨r, hr, hbudget, hheight⟩ := ih (fun g hg hgd => hn g hg (by omega))
    let s := T.state (e + d)
    let t := T.state (e + d + 1)
    let k := T.bin (e + d + 1)
    have step : RestEventStep s t k := T.step (e + d)
    have hlen : i ≤ s.capacity.length := by
      have hmem := List.getElem?_eq_some_iff.mp hr
      obtain ⟨hlt, _⟩ := hmem
      dsimp [s]
      omega
    have hik : k ≠ i := hn _ (by omega) (by omega)
    have hcard : (higherSteps T i e (d + 1)).card =
        (higherSteps T i e d).card + (if i < k then 1 else 0) := by
      simp only [higherSteps, Finset.range_add_one, Finset.filter_insert]
      by_cases h : i < k
      · rw [if_pos h, Finset.card_insert_of_notMem]
        · rw [if_pos h]
        · simp
      · rw [if_neg h, if_neg h]
        omega
    let j : Fin s.capacity.length := ⟨i - 1, by omega⟩
    have hget : s.capacity.get j = r := by
      have hj : s.capacity[j.val]? = some (s.capacity.get j) := by simp
      have : some (s.capacity.get j) = some r := hj.symm.trans hr
      exact Option.some.inj this
    by_cases h : i < k
    · have hp := step.prefix_pos j (by dsimp [j]; omega)
      have hd := step.prefix_decrement j (by dsimp [j]; omega)
      rw [hget] at hp hd
      refine ⟨r - 1, ?_, ?_, ?_⟩
      · simpa [t, j, Nat.add_assoc] using hd
      · rw [hcard, if_pos h]
        omega
      · have ht : t.capacity.length ≤ s.capacity.length + 1 := by
          rw [step.height_eq]
          exact max_le (by omega) step.label_le
        have hh : s.capacity.length ≤ (T.state e).capacity.length +
            (higherSteps T i e d).card := hheight
        have hb : t.capacity.length ≤ (T.state e).capacity.length +
            (higherSteps T i e d).card + 1 := by omega
        rw [hcard, if_pos h]
        simpa only [t, Nat.add_assoc] using hb
    · have hs := step.suffix_unchanged j (by dsimp [j]; omega)
      rw [hget] at hs
      refine ⟨r, ?_, ?_, ?_⟩
      · simpa [t, j, Nat.add_assoc] using hs
      · rw [hcard, if_neg h]
        omega
      · have ht := step.height_eq
        have hk : k ≤ s.capacity.length := by omega
        rw [max_eq_left hk] at ht
        rw [hcard, if_neg h]
        simpa only [t, Nat.add_assoc, Nat.add_zero] using ht.le.trans hheight

/-- Each actual event has a later occurrence of the same bin. Unbounded
height supplies more higher events than a never-reset finite bin can pay. -/
theorem future_same_bin (T : RestTrace) (e : ℕ) :
    ∃ f, e < f ∧ T.bin f = T.bin e := by
  have hpos : ∀ t, 0 < T.bin t := by
    intro t
    cases t with
    | zero => rw [T.initial_bin]; omega
    | succ t => exact (T.step t).label_pos
  have hbin : ∀ t, T.bin t ≤ (T.state t).capacity.length := by
    intro t
    cases t with
    | zero => simp [T.initial_bin, T.initial_capacity]
    | succ t =>
      rw [(T.step t).height_eq]
      exact Nat.le_max_right _ _
  have hmono : Monotone (fun t => (T.state t).capacity.length) :=
    monotone_nat_of_le_succ fun t => by
      rw [(T.step t).height_eq]
      exact Nat.le_max_left _ _
  obtain ⟨c, hc⟩ : ∃ c, (T.state e).capacity[T.bin e - 1]? = some c := by
    have hb : T.bin e - 1 < (T.state e).capacity.length := by
      have := hpos e; have := hbin e; omega
    exact ⟨(T.state e).capacity[T.bin e - 1], List.getElem?_eq_getElem hb⟩
  by_contra hn
  have hn' : ∀ g, e < g → T.bin g ≠ T.bin e := by
    intro g hg heq
    exact hn ⟨g, hg, heq⟩
  obtain ⟨n, hlarge⟩ := T.unbounded ((T.state e).capacity.length + c + 1)
  have hen : e ≤ n := by
    by_contra bad
    have hm : (T.state n).capacity.length ≤ (T.state e).capacity.length :=
      hmono (show n ≤ e by omega)
    omega
  have hadd : e + (n - e) = n := by omega
  obtain ⟨r, _, hb, hh⟩ := no_reset_budget T (T.bin e) e (n - e) c
    (hpos e) hc (fun g hg _ => hn' g hg)
  rw [hadd] at hh
  omega

/-- The zero-height value is unused. Positive births are genuine least
indices, whose existence is supplied by the unbounded-height premise. -/
noncomputable def events (T : RestTrace) : EventSequence where
  endpoint t := (T.state t).endpoint
  bin := T.bin
  height t := (T.state t).capacity.length
  birth h := Nat.find (T.unbounded h)
  pred f := Nat.findGreatest (fun e => T.bin e = T.bin f) (f - 1)

/-- These are the chronological fields of EventLaws, with reset balance
kept separate until its capacity and birth-count arguments are supplied. -/
structure Chronology (E : EventSequence) : Prop where
  bin_pos : ∀ t, 0 < E.bin t
  bin_le_height : ∀ t, E.bin t ≤ E.height t
  height_mono : Monotone E.height
  birth_height : ∀ h, 0 < h → E.height (E.birth h) = h
  birth_bin : ∀ h, 0 < h → E.bin (E.birth h) = h
  birth_cut : ∀ h, 0 < h → ∀ t, E.height t < h ↔ t < E.birth h
  endpoint_step : ∀ t, E.endpoint (t + 1) = E.endpoint t + E.bin (t + 1)
  pred_lt : ∀ f, E.Renewal f → E.pred f < f
  pred_bin : ∀ f, E.Renewal f → E.bin (E.pred f) = E.bin f
  pred_immediate : ∀ f, E.Renewal f → ∀ g,
    E.pred f < g → g < f → E.bin g ≠ E.bin f

/-- Least future occurrence, whose existence follows from the actual
capacity budget, rather than from chronological EventLaws. -/
noncomputable def successor (T : RestTrace) (e : ℕ) : ℕ :=
  Nat.find (future_same_bin T e)

/-- Exact reset balance is obtained by telescoping the real coordinate and
splitting higher events into the unique height births and renewals. -/
theorem event_laws_realization (T : RestTrace) : EventLaws (events T) := by
  classical
  let E := events T
  have C : Chronology E := by
    have hp : ∀ t, 0 < E.bin t := by
      intro t
      cases t with
      | zero => simpa only [E, events, T.initial_bin] using (show 0 < 1 by decide)
      | succ t => exact (T.step t).label_pos
    have hb : ∀ t, E.bin t ≤ E.height t := by
      intro t
      cases t with
      | zero => simp [E, events, T.initial_bin, T.initial_capacity]
      | succ t =>
        change T.bin (t + 1) ≤ (T.state (t + 1)).capacity.length
        rw [(T.step t).height_eq]
        exact Nat.le_max_right _ _
    have hm : Monotone E.height := monotone_nat_of_le_succ fun t => by
      change (T.state t).capacity.length ≤ (T.state (t + 1)).capacity.length
      rw [(T.step t).height_eq]
      exact Nat.le_max_left _ _
    have cut : ∀ h, 0 < h → ∀ t, E.height t < h ↔ t < E.birth h := by
      intro h _ t
      constructor
      · intro ht
        by_contra hn
        have hs : h ≤ E.height (E.birth h) := Nat.find_spec (T.unbounded h)
        have hh : E.height (E.birth h) ≤ E.height t := hm (by omega)
        omega
      · intro ht
        have hn := Nat.find_min (T.unbounded h) ht
        change ¬ h ≤ E.height t at hn
        omega
    have birth : ∀ h, 0 < h → E.height (E.birth h) = h ∧ E.bin (E.birth h) = h := by
      intro h hh
      have hs : h ≤ E.height (E.birth h) := Nat.find_spec (T.unbounded h)
      cases hq : E.birth h with
      | zero =>
        have hheight : E.height 0 = 1 := by simp [E, events, T.initial_capacity]
        have hbin : E.bin 0 = 1 := T.initial_bin
        rw [hq] at hs
        constructor <;> omega
      | succ q =>
        have hprev : E.height q < h := (cut h hh q).mpr (by omega)
        have hs' := (T.step q).height_eq
        have hl := (T.step q).label_le
        change E.height (q + 1) = max (E.height q) (E.bin (q + 1)) at hs'
        change E.bin (q + 1) ≤ E.height q + 1 at hl
        rw [hq] at hs
        constructor <;> omega
    have earlier : ∀ f, E.Renewal f → ∃ e, e < f ∧ E.bin e = E.bin f := by
      intro f hf
      let b := E.birth (E.bin f)
      have hbl : b ≤ f := by
        by_contra hn
        have hc := (cut (E.bin f) (hp f) f).mpr (show f < b by omega)
        have := hb f
        omega
      have hne : f ≠ b := hf
      exact ⟨b, by omega, (birth _ (hp f)).2⟩
    refine ⟨hp, hb, hm, (fun h hh => (birth h hh).1),
      (fun h hh => (birth h hh).2), cut, ?_, ?_, ?_, ?_⟩
    · intro t
      exact (T.step t).endpoint_eq
    · intro f hf
      obtain ⟨e, he, _⟩ := earlier f hf
      have hpred : E.pred f ≤ f - 1 := Nat.findGreatest_le _
      omega
    · intro f hf
      obtain ⟨e, he, heb⟩ := earlier f hf
      exact Nat.findGreatest_spec (P := fun e => T.bin e = T.bin f)
        (show e ≤ f - 1 by omega) heb
    · intro f _ g hg hgf
      exact (Nat.findGreatest_eq_iff (P := fun e => T.bin e = T.bin f)
        (k := f - 1) (m := E.pred f) |>.mp rfl).2.2 hg (by omega)
  let A (i t : ℕ) := ((Finset.range t).filter fun g => i < T.bin g).card
  have update (i t : ℕ) : A i (t + 1) = A i t + (if i < T.bin t then 1 else 0) := by
    dsimp [A]
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h : i < T.bin t
    · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
    · rw [if_neg h, if_neg h]
      omega
  have cumulative (i e d : ℕ) : A i (e + d + 1) =
      A i (e + 1) + (higherSteps T i e d).card := by
    induction d with
    | zero => simp [higherSteps]
    | succ d ih =>
      have hc : (higherSteps T i e (d + 1)).card =
          (higherSteps T i e d).card + (if i < T.bin (e + d + 1) then 1 else 0) := by
        simp only [higherSteps, Finset.range_add_one, Finset.filter_insert]
        by_cases h : i < T.bin (e + d + 1)
        · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
        · rw [if_neg h, if_neg h]
          omega
      rw [show e + (d + 1) + 1 = (e + d + 1) + 1 by omega, update, ih, hc]
      omega
  have split (i t : ℕ) (ht : E.bin t = i) :
      A i t = E.height t - i + (higherRenewals E i t).card := by
    let S := (Finset.range t).filter fun g => i < E.bin g
    let B := S.filter fun g => ¬ E.Renewal g
    have hB : B.card = (Finset.Ico (i + 1) (E.height t + 1)).card := by
      apply Finset.card_bij (fun g _ => E.bin g)
      · intro g hg
        obtain ⟨hs, hr⟩ := Finset.mem_filter.mp hg
        obtain ⟨hgt, hgi⟩ := Finset.mem_filter.mp hs
        have hlt : g < t := Finset.mem_range.mp hgt
        have hbirth : g = E.birth (E.bin g) := by
          simpa [EventSequence.Renewal] using hr
        have hh : E.height g = E.bin g := by
          exact (congrArg E.height hbirth).trans (C.birth_height _ (C.bin_pos g))
        have hm : E.height g ≤ E.height t := C.height_mono (by omega)
        apply Finset.mem_Ico.mpr
        omega
      · intro a ha b hb hab
        have hba : a = E.birth (E.bin a) := by
          simpa [EventSequence.Renewal] using (Finset.mem_filter.mp ha).2
        have hbb : b = E.birth (E.bin b) := by
          simpa [EventSequence.Renewal] using (Finset.mem_filter.mp hb).2
        exact hba.trans ((congrArg E.birth hab).trans hbb.symm)
      · intro h hh
        obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hh
        have hp : 0 < h := by omega
        have hb : E.birth h ≤ t := by
          by_contra bad
          have hh' := (C.birth_cut h hp t).mpr (by omega)
          omega
        have hbin := C.birth_bin h hp
        have hbt : E.birth h < t := by
          by_contra bad
          have heq : E.birth h = t := by omega
          rw [heq, ht] at hbin
          omega
        refine ⟨E.birth h, ?_, hbin⟩
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_range.mpr hbt, by omega⟩
        · simp only [EventSequence.Renewal, hbin, not_not]
    have hcard : B.card = E.height t - i := by
      rw [Nat.card_Ico] at hB
      omega
    have hr : S.filter E.Renewal = higherRenewals E i t := by
      ext g
      simp [S, higherRenewals, and_assoc]
    have hs := Finset.card_filter_add_card_filter_not (s := S) E.Renewal
    rw [hr] at hs
    change (higherRenewals E i t).card + B.card = A i t at hs
    omega
  refine {
    bin_pos := C.bin_pos
    bin_le_height := C.bin_le_height
    height_mono := C.height_mono
    birth_height := C.birth_height
    birth_bin := C.birth_bin
    birth_cut := C.birth_cut
    endpoint_step := C.endpoint_step
    pred_lt := C.pred_lt
    pred_bin := C.pred_bin
    pred_immediate := C.pred_immediate
    reset_balance := ?_ }
  intro f hf
  let e := E.pred f
  let i := E.bin f
  have hef : e < f := C.pred_lt f hf
  have hei : E.bin e = i := C.pred_bin f hf
  have hip : 0 < i := C.bin_pos f
  have hil : i ≤ E.height e := by rw [← hei]; exact C.bin_le_height e
  have hreset : (T.state e).capacity[i - 1]? = some (E.endpoint e) := by
    cases hx : e with
    | zero =>
      have hi1 : i = 1 := by
        rw [hx] at hei
        exact hei.symm.trans T.initial_bin
      simp [hi1, E, events, T.initial_capacity, T.initial_endpoint]
    | succ q =>
      have hres := (T.step q).reset
      have hbin : T.bin (q + 1) = i := by simpa only [hx, E, events] using hei
      rw [hbin] at hres
      simpa [hx, E, events] using hres
  have hfirst : (T.state (f - 1)).capacity[i - 1]? = some 0 := by
    have hfpos : 0 < f := by omega
    have hsucc : f - 1 + 1 = f := by omega
    have hs := T.step (f - 1)
    have hmono : E.height e ≤ E.height (f - 1) := C.height_mono (by omega)
    have hle : i ≤ (T.state (f - 1)).capacity.length := by
      change i ≤ E.height (f - 1)
      omega
    simpa [hsucc, i, E, events] using hs.first_zero (by simpa [hsucc, i, E, events] using hle)
  let d := f - 1 - e
  have hde : e + d = f - 1 := by dsimp [d]; omega
  obtain ⟨r, hr, hbudget, _⟩ := no_reset_budget T i e d (E.endpoint e) hip hreset (by
    intro g heg hgd
    exact C.pred_immediate f hf g heg (by omega))
  rw [hde, hfirst] at hr
  have hr0 : r = 0 := (Option.some.inj hr).symm
  rw [hr0, Nat.zero_add] at hbudget
  have hcum := cumulative i e d
  have hfde : e + d + 1 = f := by omega
  have heib : T.bin e = i := hei
  rw [hfde, update, heib, if_neg (by omega : ¬ i < i), Nat.add_zero, hbudget] at hcum
  have se := split i e hei
  have sf := split i f rfl
  have hif : i ≤ E.height f := C.bin_le_height f
  change E.endpoint e + E.height e + (higherRenewals E i e).card =
    E.height f + (higherRenewals E i f).card
  omega

/-- All same-bin successor and predecessor inverse laws for the supplied
trace. No event is excluded, including event zero and every birth. -/
theorem successor_inverse_laws (T : RestTrace) :
    (∀ e, e < successor T e ∧ (events T).bin (successor T e) = (events T).bin e ∧
      (events T).Renewal (successor T e) ∧ (events T).pred (successor T e) = e ∧
      ∀ g, e < g → g < successor T e → (events T).bin g ≠ (events T).bin e) ∧
    (∀ f, (events T).Renewal f → successor T ((events T).pred f) = f) := by
  classical
  let E := events T
  have C : EventLaws E := event_laws_realization T
  have spec (e : ℕ) : e < successor T e ∧ E.bin (successor T e) = E.bin e :=
    Nat.find_spec (future_same_bin T e)
  have immediate (e g : ℕ) (heg : e < g) (hgs : g < successor T e) :
      E.bin g ≠ E.bin e := by
    intro heq
    exact Nat.find_min (future_same_bin T e) hgs ⟨heg, heq⟩
  have sr (e : ℕ) : E.Renewal (successor T e) := by
    have hs := spec e
    have hb : E.birth (E.bin e) ≤ e := by
      by_contra hn
      have hc := (C.birth_cut (E.bin e) (C.bin_pos e) e).mpr (by omega)
      have hh := C.bin_le_height e
      omega
    change successor T e ≠ E.birth (E.bin (successor T e))
    rw [hs.2]
    omega
  have ps (e : ℕ) : E.pred (successor T e) = e := by
    have hs := spec e
    have hp := C.pred_lt _ (sr e)
    have hb := C.pred_bin _ (sr e)
    have he : e ≤ E.pred (successor T e) :=
      Nat.le_findGreatest (by omega) hs.2.symm
    by_contra hn
    exact immediate e _ (by omega) hp (hb.trans hs.2)
  constructor
  · intro e
    exact ⟨(spec e).1, (spec e).2, sr e, ps e, immediate e⟩
  · intro f hf
    change successor T (E.pred f) = f
    have hp := C.pred_lt f hf
    have hb := C.pred_bin f hf
    have hle : successor T (E.pred f) ≤ f :=
      Nat.find_min' (future_same_bin T (E.pred f)) ⟨hp, hb.symm⟩
    have hs := spec (E.pred f)
    by_contra hn
    exact C.pred_immediate f hf _ hs.1 (by omega) (hs.2.trans hb)

#print axioms event_laws_realization
#print axioms no_reset_budget
#print axioms future_same_bin
#print axioms successor_inverse_laws
end D5.S3.Combinatorics.GreedyBrick.EventRealization
