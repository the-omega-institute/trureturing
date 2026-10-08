/- GID: D5/S3/ObserverMemory/Algorithms/SaturatedSlotUnfolding
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/SaturatedSlotUnfolding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Saturated histories exhaust actual slot edges and determine terminal supports. -/

import D5.S3.ObserverMemory.Algorithms.ActualControlSlots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.SaturatedSlotUnfolding

open ActualControlSlots

variable {p P : Nat} {Q : Type}
variable (hp : 2 ≤ p) (hP : 0 < P) (C : Controller p P Q)
variable (I : C.Correct hp hP)

attribute [local instance] Classical.propDecidable
local notation "Source" => ZMod (p * P)
local notation "Slot" => {q : Q // ∃ b, C.Used I q b} × Fin p

/-- A complete binary expansion with its original-input supports and actual
read times. Branches use the same original input at their parent and child;
intermediate actions are actual waits. No runtime clock is added to Q. -/
inductive SaturatedHistory : Nat → Slot → Finset Source → (Source → Nat) → Type where
  | leaf {a : Source → Nat} (u : Slot) (x : Source)
      (occurs : C.Occurs I x (a x) u) (last : a x + 1 = I.length x) :
      SaturatedHistory 0 u {x} a
  | fork {j : Nat} {u v w : Slot} {S T : Finset Source} {a b c : Source → Nat}
      (different : v ≠ w) (separate : Disjoint S T)
      (left : SaturatedHistory j v S b) (right : SaturatedHistory j w T c)
      (parent : ∀ x ∈ S ∪ T, C.Occurs I x (a x) u)
      (left_next : ∀ x ∈ S, a x < b x ∧
        ∀ t, a x < t → t < b x → C.action (C.run hp hP x t).2 = .wait)
      (right_next : ∀ x ∈ T, a x < c x ∧
        ∀ t, a x < t → t < c x → C.action (C.run hp hP x t).2 = .wait) :
      SaturatedHistory (j + 1) u (S ∪ T) a

/-- Global slot paths may combine edges realized on different inputs.
The label is the fixed terminal output, and n counts subsequent reads. -/
def TerminatesIn : Nat → Slot → Source → Prop
  | 0, u, x => C.action (C.readNext u.1.val u.2) = .halt ∧
      C.output (C.readNext u.1.val u.2) = x
  | n + 1, u, x => ∃ v, C.Edge I u v ∧ TerminatesIn n v x

theorem occurrence_advance {x : Source} {t : Nat} {u : Slot}
    (h : C.Occurs I x t u) :
    (C.run hp hP x (t + 1)).2 = C.readNext u.1.val u.2 := by
  obtain ⟨d, y, k, hk, hq, hr, hd⟩ := u.1.property
  have read : C.action (C.run hp hP x t).2 = .read := h.2.1 ▸ hr
  simp only [Controller.run, Function.iterate_succ_apply']
  change (C.step hp hP (C.run hp hP x t)).2 = _
  simp only [Controller.step, read]
  rw [h.2.1, h.2.2]

private theorem terminal_no_edge {u v : Slot}
    (halt : C.action (C.readNext u.1.val u.2) = .halt) : ¬ C.Edge I u v := by
  rintro ⟨x, i, j, hi, hj, hij, waits⟩
  have advance := occurrence_advance hp hP C I hi
  have jlen := hj.1
  have live := I.live x (i + 1) (by omega)
  exact live (advance ▸ halt)

theorem history_data {j : Nat} {u : Slot} {S : Finset Source}
    {a : Source → Nat} (H : SaturatedHistory hp hP C I j u S a) :
    S.card = 2 ^ j ∧ S.Nonempty ∧ ∀ x ∈ S, C.Occurs I x (a x) u := by
  induction H with
  | leaf u x occurs last =>
    exact ⟨by simp, by simp, by simpa using occurs⟩
  | @fork j u v w S T a b c different separate left right parent ln rn ihl ihr =>
    refine ⟨?_, ?_, parent⟩
    · rw [Finset.card_union_of_disjoint separate, ihl.1, ihr.1, pow_succ]
      omega
    · exact ihl.2.1.mono Finset.subset_union_left

private theorem edge_exhaustion [Finite Q] {u v w : Slot} (different : v ≠ w)
    (left : C.Edge I u v) (right : C.Edge I u w) :
    ∀ z, C.Edge I u z ↔ z = v ∨ z = w := by
  classical
  let _ := Fintype.ofFinite Q
  obtain ⟨G, root, used, edges, rest⟩ := C.result I
  have pair : ({v, w} : Finset Slot) ⊆ G.next u := by
    intro z hz
    rcases Finset.mem_insert.mp hz with he | hz
    · rw [he]
      exact (edges u v).mpr left
    · rw [Finset.mem_singleton.mp hz]
      exact (edges u w).mpr right
  have full : ({v, w} : Finset Slot) = G.next u :=
    Finset.eq_of_subset_of_card_le pair
      (by simpa [Finset.card_pair different] using G.at_most_two u)
  intro z
  rw [← edges, ← full]
  simp

private theorem unfolding_support [Finite Q] {j : Nat} {u : Slot} {S : Finset Source}
    {a : Source → Nat} (H : SaturatedHistory hp hP C I j u S a) :
    ∀ n x, TerminatesIn hp hP C I n u x ↔ n = j ∧ x ∈ S := by
  induction H with
  | leaf u x occurs last =>
    have advance := occurrence_advance hp hP C I occurs
    have halt : C.action (C.readNext u.1.val u.2) = .halt := by
      rw [← advance, last]
      exact I.halt x
    have label : C.output (C.readNext u.1.val u.2) = x := by
      rw [← advance, last]
      exact I.output x
    intro n y
    cases n with
    | zero => simp [TerminatesIn, halt, label, eq_comm]
    | succ n =>
      simp only [TerminatesIn, Nat.succ_ne_zero, false_and]
      exact ⟨fun ⟨v, edge, _⟩ => terminal_no_edge hp hP C I halt edge, False.elim⟩
  | @fork j u v w S T a b c different separate left right parent ln rn ihl ihr =>
    obtain ⟨x, hx⟩ := (history_data hp hP C I left).2.1
    obtain ⟨y, hy⟩ := (history_data hp hP C I right).2.1
    have ev : C.Edge I u v := ⟨x, a x, b x,
      parent x (Finset.mem_union_left T hx),
      (history_data hp hP C I left).2.2 x hx, (ln x hx).1, (ln x hx).2⟩
    have ew : C.Edge I u w := ⟨y, a y, c y,
      parent y (Finset.mem_union_right S hy),
      (history_data hp hP C I right).2.2 y hy, (rn y hy).1, (rn y hy).2⟩
    have exhaustive := edge_exhaustion hp hP C I different ev ew
    intro n z
    cases n with
    | zero =>
      simp only [TerminatesIn, Nat.zero_ne_add_one, false_and]
      exact ⟨fun ⟨halt, _⟩ => terminal_no_edge hp hP C I halt ev, False.elim⟩
    | succ n =>
      simp only [TerminatesIn, Nat.add_right_cancel_iff, Finset.mem_union]
      constructor
      · rintro ⟨s, edge, tail⟩
        rcases (exhaustive s).mp edge with rfl | rfl
        · exact ⟨(ihl n z).mp tail |>.1, Or.inl ((ihl n z).mp tail).2⟩
        · exact ⟨(ihr n z).mp tail |>.1, Or.inr ((ihr n z).mp tail).2⟩
      · rintro ⟨depth, hz | hz⟩
        · exact ⟨v, ev, (ihl n z).mpr ⟨depth, hz⟩⟩
        · exact ⟨w, ew, (ihr n z).mpr ⟨depth, hz⟩⟩

/-- A slot determines the remaining height and the entire original-label
support of every saturated actual history based there. -/
theorem result [Finite Q] {j k : Nat} {u v : Slot} {S T : Finset Source}
    {a b : Source → Nat}
    (H : SaturatedHistory hp hP C I j u S a)
    (K : SaturatedHistory hp hP C I k v T b) :
    (∀ n x, TerminatesIn hp hP C I n u x ↔ n = j ∧ x ∈ S) ∧
    S.card = 2 ^ j ∧ (u = v → j = k ∧ S = T) := by
  have hs := unfolding_support hp hP C I H
  have ht := unfolding_support hp hP C I K
  refine ⟨hs, (history_data hp hP C I H).1, ?_⟩
  intro eq
  subst v
  obtain ⟨x, hx⟩ := (history_data hp hP C I H).2.1
  have depth : j = k := ((ht j x).mp ((hs j x).mpr ⟨rfl, hx⟩)).1
  refine ⟨depth, ?_⟩
  ext y
  exact ⟨fun hy => ((ht j y).mp ((hs j y).mpr ⟨rfl, hy⟩)).2,
    fun hy => ((hs k y).mp ((ht k y).mpr ⟨rfl, hy⟩)).2⟩

end D5.S3.ObserverMemory.Algorithms.SaturatedSlotUnfolding
