/- GID: D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Restricted suffix tables count and reconstruct original native words. -/

import D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Exact suffix counts and deterministic reconstruction for the original high-to-low reader. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeSuffixAcquisition

open LiteralWindowEnd (Window first last)
open NullReplyFiber (NativeHistory native_execution bitComposition)
open GraftAffineClosure (step residue)
open ImmediateWindowStateCapacity (rawMachine)

/-- One explicitly stored count for each of the two original seams. -/
abbrev Row := ℕ × ℕ

def entry (r : Row) (s : Bool) : ℕ := if s then r.2 else r.1

def terminal (B : Finset Bool) : Row :=
  (if false ∈ B then 1 else 0, if true ∈ B then 1 else 0)

/-- Distinct letters contribute separately, including letters with the same successor. -/
def advance (a : Finset Window) (r : Row) : Row :=
  (∑ b ∈ a, if ¬ (false = true ∧ last b = true) then entry r (first b) else 0,
   ∑ b ∈ a, if ¬ (true = true ∧ last b = true) then entry r (first b) else 0)

/-- The head is the current row; the final row is the terminal indicator. -/
def table (B : Finset Bool) : List (Finset Window) → List Row
  | [] => [terminal B]
  | a :: as => let tail := table B as; advance a (tail.headD (terminal B)) :: tail

def counts (B : Finset Bool) (as : List (Finset Window)) : Row :=
  (table B as).headD (terminal B)

/-- A finite set of words used for the specification, not for computing the table. -/
def completions (B : Finset Bool) : List (Finset Window) → Bool → Finset (List Window)
  | [], s => if s ∈ B then {[]} else ∅
  | a :: as, s => (a.filter (fun b => ¬ (s = true ∧ last b = true))).biUnion
      (fun b => (completions B as (first b)).image (List.cons b))

/-- Local restrictions on the original word, retaining all positions. -/
def Allowed : List (Finset Window) → List Window → Prop
  | [], [] => True
  | a :: as, b :: w => b ∈ a ∧ Allowed as w
  | _, _ => False

/-- The fixed source order is null, low, middle, high, ends. Printed bits remain low to high. -/
def modes : List Window := [.zero, .low, .middle, .high, .ends]

def pick (a : Finset Window) (r : Row) (s : Bool) : Option Window :=
  modes.find? (fun b => decide
    (b ∈ a ∧ ¬ (s = true ∧ last b = true) ∧ 0 < entry r (first b)))

/-- Reconstruction reads one already acquired child row at each step. -/
def reconstruct (B : Finset Bool) :
    List (Finset Window) → List Row → Bool → Option (List Window)
  | [], _, s => if s ∈ B then some [] else none
  | a :: as, _ :: child :: tail, s => do
      let b ← pick a child s
      let w ← reconstruct B as (child :: tail) (first b)
      pure (b :: w)
  | _ :: _, _, _ => none

def acquire (B : Finset Bool) (as : List (Finset Window)) (s : Bool) :
    List Row × Option (List Window) :=
  let rows := table B as
  (rows, reconstruct B as rows s)

private theorem entry_terminal (B : Finset Bool) (s : Bool) :
    entry (terminal B) s = if s ∈ B then 1 else 0 := by cases s <;> rfl

private theorem entry_advance (a : Finset Window) (r : Row) (s : Bool) :
    entry (advance a r) s =
      ∑ b ∈ a, if ¬ (s = true ∧ last b = true) then entry r (first b) else 0 := by
  cases s <;> rfl

private theorem counts_cons (B : Finset Bool) (a : Finset Window)
    (as : List (Finset Window)) : counts B (a :: as) = advance a (counts B as) := rfl

private theorem table_length (B : Finset Bool) (as : List (Finset Window)) :
    (table B as).length = as.length + 1 := by
  induction as with
  | nil => rfl
  | cons a as ih => simpa [table] using congrArg Nat.succ ih

private theorem table_index (B : Finset Bool) (as : List (Finset Window))
    (t : ℕ) (ht : t ≤ as.length) :
    (table B as)[t]? = some (counts B (as.drop t)) := by
  induction as generalizing t with
  | nil =>
      have : t = 0 := by simpa using ht
      subst t
      rfl
  | cons a as ih =>
      cases t with
      | zero => rfl
      | succ t => simpa [table] using ih t (by simpa using ht)

private theorem completions_card (B : Finset Bool) (as : List (Finset Window))
    (s : Bool) : (completions B as s).card = entry (counts B as) s := by
  induction as generalizing s with
  | nil => simp only [completions, counts, table, List.headD_cons, entry_terminal]
           split <;> simp
  | cons a as ih =>
      rw [counts_cons, entry_advance]
      unfold completions
      rw [Finset.card_biUnion]
      · have hc (b : Window) :
            ((completions B as (first b)).image (List.cons b)).card =
              (completions B as (first b)).card :=
          Finset.card_image_of_injective _ (by intro u v h; exact (List.cons.inj h).2)
        simp only [hc, ih]
        exact Finset.sum_filter _ _
      · intro b _ c _ hbc
        apply Finset.disjoint_left.mpr
        intro w hb hc
        obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hb
        obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hc
        exact hbc (List.cons.inj (hu.trans hv.symm)).1

private theorem count_bound (B : Finset Bool) (as : List (Finset Window)) (s : Bool) :
    entry (counts B as) s ≤ 5 ^ as.length := by
  induction as generalizing s with
  | nil => simp [counts, table, entry_terminal]; split <;> omega
  | cons a as ih =>
      rw [counts_cons, entry_advance]
      have term (b : Window) :
          (if ¬ (s = true ∧ last b = true) then entry (counts B as) (first b) else 0) ≤
            5 ^ as.length := by
        split
        · exact ih (first b)
        · exact Nat.zero_le _
      calc
        _ ≤ ∑ _b ∈ a, 5 ^ as.length := Finset.sum_le_sum (fun b _ => term b)
        _ = a.card * 5 ^ as.length := by simp
        _ ≤ 5 * 5 ^ as.length := Nat.mul_le_mul_right _ (by
          have := Finset.card_le_card (Finset.subset_univ a)
          have h : (Finset.univ : Finset Window).card = 5 := by decide
          omega)
        _ = 5 ^ (a :: as).length := by simp [pow_succ, Nat.mul_comm]

private theorem completions_native (B : Finset Bool) (as : List (Finset Window))
    (s : Bool) (c : ℕ × ℕ) (w : List Window) :
    w ∈ completions B as s ↔ Allowed as w ∧
      ∃ t ∈ B, ∃ d : ℕ × ℕ, NativeHistory s c w t d := by
  induction as generalizing s c w with
  | nil =>
      cases w with
      | nil =>
          simp only [completions, Allowed, true_and]
          constructor
          · intro h
            have hs : s ∈ B := by by_contra hn; simp [hn] at h
            exact ⟨s, hs, c, .nil s c⟩
          · rintro ⟨t, ht, d, hh⟩
            cases hh
            simp [ht]
      | cons b w => simp only [completions, Allowed, false_and]
                    split <;> simp
  | cons a as ih =>
      cases w with
      | nil => simp [completions, Allowed]
      | cons b w =>
          simp only [completions, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image]
          constructor
          · rintro ⟨b', ⟨hb, hg⟩, v, hv, he⟩
            obtain ⟨rfl, rfl⟩ := List.cons.inj he
            obtain ⟨ha, t, ht, d, hh⟩ := (ih (first b')
              (step (step (step c)) + bitComposition b') v).mp hv
            exact ⟨⟨hb, ha⟩, t, ht, d, .cons hg hh⟩
          · rintro ⟨⟨hb, ha⟩, t, ht, d, hh⟩
            cases hh with
            | cons hg tail =>
                exact ⟨b, ⟨hb, hg⟩, w,
                  (ih _ _ _).mpr ⟨ha, t, ht, d, tail⟩, rfl⟩

private theorem allowed_length (as : List (Finset Window)) (w : List Window)
    (h : Allowed as w) : w.length = as.length := by
  induction as generalizing w with
  | nil => cases w <;> simp_all [Allowed]
  | cons a as ih => cases w <;> simp_all [Allowed]

private theorem pick_none (a : Finset Window) (r : Row) (s : Bool) :
    pick a r s = none ↔ entry (advance a r) s = 0 := by
  rw [entry_advance]
  constructor
  · intro h
    have hf := List.find?_eq_none.mp h
    apply Finset.sum_eq_zero
    intro b hb
    split
    · rename_i hg
      have hm : b ∈ modes := by cases b <;> simp [modes]
      have hn := hf b hm
      simp only [decide_eq_true_eq] at hn
      have : ¬ 0 < entry r (first b) := fun hp => hn ⟨hb, hg, hp⟩
      omega
    · rfl
  · intro h
    apply List.find?_eq_none.mpr
    intro b _
    simp only [decide_eq_true_eq]
    rintro ⟨hb, hg, hp⟩
    have hz := (Finset.sum_eq_zero_iff.mp h) b hb
    rw [if_pos hg] at hz
    omega

private theorem pick_some (a : Finset Window) (r : Row) (s : Bool) (b : Window)
    (h : pick a r s = some b) :
    b ∈ a ∧ ¬ (s = true ∧ last b = true) ∧ 0 < entry r (first b) := by
  have hp : decide (b ∈ a ∧ ¬ (s = true ∧ last b = true) ∧
      0 < entry r (first b)) = true :=
    List.find?_some (p := fun b => decide
      (b ∈ a ∧ ¬ (s = true ∧ last b = true) ∧ 0 < entry r (first b))) h
  exact of_decide_eq_true hp

private theorem reconstruct_spec (B : Finset Bool) (as : List (Finset Window))
    (s : Bool) :
    (reconstruct B as (table B as) s = none ↔ entry (counts B as) s = 0) ∧
    ∀ w, reconstruct B as (table B as) s = some w → w ∈ completions B as s := by
  induction as generalizing s with
  | nil =>
      simp only [reconstruct, counts, table, List.headD_cons, entry_terminal, completions]
      split <;> simp_all
  | cons a as ih =>
      have ht := table_length B as
      cases hr : table B as with
      | nil => simp [hr] at ht
      | cons r rs =>
          have hc : counts B as = r := by simp [counts, hr]
          cases hp : pick a r s with
          | none =>
              have hz := (pick_none a r s).mp hp
              simp [table, hr, counts, reconstruct, hp, hz]
          | some b =>
              obtain ⟨hb, hg, hpos⟩ := pick_some a r s b hp
              have hn : entry (advance a r) s ≠ 0 := by
                intro hz
                have := (pick_none a r s).mpr hz
                simp [hp] at this
              have hi := ih (first b)
              rw [hr, hc] at hi
              have htail : reconstruct B as (r :: rs) (first b) ≠ none := by
                intro hz
                have := hi.1.mp hz
                omega
              obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp htail
              constructor
              · simp [table, hr, counts, reconstruct, hp, hw, hn]
              · intro v hv
                have hv' : b :: w = v := by
                  simpa [table, hr, reconstruct, hp, hw] using hv
                subst v
                exact Finset.mem_biUnion.mpr
                  ⟨b, Finset.mem_filter.mpr ⟨hb, hg⟩,
                    Finset.mem_image.mpr ⟨w, hi.2 w hw, rfl⟩⟩

/-- The complete deterministic source algorithm, with no certified-table premise.
This is a correctness theorem about natural-number operations, not a bit-time theorem. -/
theorem native_suffix_acquisition (L : ℕ) (A : Fin L → Finset Window)
    (B : Finset Bool) :
    let as := List.ofFn A
    (table B as).length = L + 1 ∧
    (∀ (t : Fin (L + 1)) (s : Bool),
      (table B as)[t.val]? = some (counts B (as.drop t.val)) ∧
      entry (counts B (as.drop t.val)) s = (completions B (as.drop t.val) s).card ∧
      entry (counts B (as.drop t.val)) s ≤ 5 ^ (L - t.val) ∧
      ∀ (c : ℕ × ℕ) (w : List Window),
        w ∈ completions B (as.drop t.val) s ↔
          Allowed (as.drop t.val) w ∧ ∃ u ∈ B, ∃ d : ℕ × ℕ, NativeHistory s c w u d) ∧
    (∀ s : Bool,
      ((acquire B as s).2 = none ↔ entry (counts B as) s = 0) ∧
      (entry (counts B as) s = 0 ↔
        ¬ ∃ (w : List Window) (u : Bool) (d : ℕ × ℕ),
          Allowed as w ∧ u ∈ B ∧ NativeHistory s (0, 0) w u d) ∧
      (0 < entry (counts B as) s →
        ∃ (w : List Window) (u : Bool) (d : ℕ × ℕ),
          (acquire B as s).2 = some w ∧ w.length = L ∧ Allowed as w ∧ u ∈ B ∧
          NativeHistory s (0, 0) w u d ∧
          (rawMachine 0).toDFA.evalFrom (some (s, residue 0 (0, 0))) w =
            some (u, residue 0 d))) := by
  dsimp only
  let as := List.ofFn A
  have hl : as.length = L := List.length_ofFn
  refine ⟨by rw [table_length, List.length_ofFn], ?_, ?_⟩
  · intro t s
    refine ⟨table_index B as t.val (by have := t.isLt; omega),
      (completions_card B _ s).symm, ?_, completions_native B _ s⟩
    simpa [List.length_drop, hl] using count_bound B (as.drop t.val) s
  · intro s
    have hr := reconstruct_spec B as s
    have hz : entry (counts B as) s = 0 ↔
        ¬ ∃ (w : List Window) (u : Bool) (d : ℕ × ℕ),
          Allowed as w ∧ u ∈ B ∧ NativeHistory s (0, 0) w u d := by
      rw [← completions_card, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      constructor
      · rintro hn ⟨w, u, d, ha, hu, hh⟩
        exact hn w ((completions_native B as s (0, 0) w).mpr ⟨ha, u, hu, d, hh⟩)
      · intro hn w hw
        obtain ⟨ha, u, hu, d, hh⟩ := (completions_native B as s (0, 0) w).mp hw
        exact hn ⟨w, u, d, ha, hu, hh⟩
    refine ⟨hr.1, hz, ?_⟩
    intro hp
    have hn : reconstruct B as (table B as) s ≠ none := by
      intro he
      exact (Nat.ne_of_gt hp) (hr.1.mp he)
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hn
    obtain ⟨ha, u, hu, d, hh⟩ :=
      (completions_native B as s (0, 0) w).mp (hr.2 w hw)
    refine ⟨w, u, d, hw, (allowed_length as w ha).trans hl, ha, hu, hh, ?_⟩
    exact (native_execution s (0, 0) w).2 u (residue 0 d) |>.mpr ⟨d, hh, rfl⟩

#print axioms native_suffix_acquisition

end D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeSuffixAcquisition
