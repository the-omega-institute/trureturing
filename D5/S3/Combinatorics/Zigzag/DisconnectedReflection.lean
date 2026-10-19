/- GID: D5/S3/Combinatorics/Zigzag/DisconnectedReflection
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Zigzag/DisconnectedReflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: Labelled sector reflection preserves actual active weak support. -/

import D5.S3.Combinatorics.Zigzag.DisconnectedSupport
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Zigzag

private theorem step_reflection_pairs (n j : Nat) (hj : j ≤ n+1)
    (s : State) (i : StepIndex s) :
    formPair n j (stepValue (h := .negative) i).low =
      (formPair n (highClass n j) (stepValue (h := .positive) i).high).swap ∧
    formPair n (highClass n j) (stepValue (h := .negative) i).high =
      (formPair n j (stepValue (h := .positive) i).low).swap := by
  have hh : (highClass n j : ZMod n) = 1-(j : ZMod n) := by
    simp only [highClass, Nat.cast_sub hj, Nat.cast_add, ZMod.natCast_self,
      Nat.cast_one, zero_add]
  constructor <;> fin_cases s <;> fin_cases i <;> apply Prod.ext <;>
    simp [List.get, Form.I, Form.II, Form.III, Form.IV, Form.V, Form.VI, stepValue, positiveStepLabel, negativeStepLabel, formPair, hh,
      State.A, State.D, State.E, State.H, State.I] <;> ring

private theorem even_cap_reflection_pairs (n j : Nat) (hn : n = 2*j)
    (s : State) (p : EvenTerminalIndex .positive s) :
    formPair n j (evenTerminalValue (h := .negative) p).low =
      (formPair n (highClass n j) (evenTerminalValue (h := .positive) p).high).swap ∧
    formPair n (highClass n j) (evenTerminalValue (h := .negative) p).high =
      (formPair n j (evenTerminalValue (h := .positive) p).low).swap := by
  have hh : (highClass n j : ZMod n) = 1-(j : ZMod n) := by
    simp only [highClass, Nat.cast_sub (by omega : j ≤ n+1), Nat.cast_add,
      ZMod.natCast_self, Nat.cast_one, zero_add]
  have ha : (j : ZMod n) = -(j : ZMod n) := by
    rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add]
    rw [show j+j=n by omega]
    exact ZMod.natCast_self n
  constructor <;> fin_cases s <;> fin_cases p <;> apply Prod.ext <;>
    simp [List.get, Form.I, Form.II, Form.III, Form.IV, Form.V, Form.VI, evenTerminalValue, formPair, hh, State.A, State.D, State.E,
      State.H, State.I] <;> linear_combination ha

private theorem odd_cap_reflection_pair (n j : Nat) (hn : n+1 = 2*j)
    (s : State) (p : OddTerminalIndex .positive s) :
    formPair n j (oddTerminalValue (h := .negative) p).label =
      (formPair n j (oddTerminalValue (h := .positive) p).label).swap := by
  have ha : (j : ZMod n)+(j : ZMod n) = 1 := by
    rw [← Nat.cast_add, show j+j=n+1 by omega]
    simp
  have hb : -(j : ZMod n) = (j : ZMod n)-1 := by
    calc
      -(j : ZMod n) = (j : ZMod n)-((j : ZMod n)+(j : ZMod n)) := by ring
      _ = (j : ZMod n)-1 := by rw [ha]
  have hc : 1-(j : ZMod n) = (j : ZMod n) := by
    calc
      1-(j : ZMod n) = ((j : ZMod n)+(j : ZMod n))-(j : ZMod n) := by rw [ha]
      _ = (j : ZMod n) := by ring
  fin_cases s <;> fin_cases p <;> apply Prod.ext <;>
    simp [List.get, Form.I, Form.II, Form.III, Form.IV, Form.V, Form.VI, oddTerminalValue, formPair, State.A, State.D, State.E, State.H, State.I,
      hb, hc]

private theorem all_edges_peel {α : Type} (P : α → Prop) (a b : α) (es : List α) :
    (∀ e ∈ a :: (es ++ [b]), P e) ↔ P a ∧ (∀ e ∈ es, P e) ∧ P b := by
  simp only [List.mem_cons, List.mem_append, List.mem_nil_iff, or_false,
    or_imp, forall_and, forall_eq]

private theorem even_tail_reflection_property (n : Nat)
    (P : ZMod n × ZMod n → Prop) (hs : ∀ e, P e.swap ↔ P e) :
    (m : Nat) → (s : State) → (p : EvenTail .positive m s) → (j : Nat) →
    3 ≤ j → n = 2*(j+m) →
    ((∀ e ∈ formsEdges n j (evenTailLowForms (evenTailReflection m s p) ++
      (evenTailHighForms (evenTailReflection m s p)).reverse), P e) ↔
      ∀ e ∈ formsEdges n j (evenTailLowForms p ++ (evenTailHighForms p).reverse), P e)
  | 0, s, p, j, hj, hn => by
      have hk : highClass n j = j+1 := by simp only [highClass]; omega
      obtain ⟨hl, hh⟩ := even_cap_reflection_pairs n j (by omega) s p
      change (∀ e ∈ [formPair n j (evenTerminalValue (h := .negative) p).low,
        formPair n (j+1) (evenTerminalValue (h := .negative) p).high], P e) ↔ _
      simp only [← hk, List.mem_cons, List.mem_nil_iff, or_false,
        forall_eq_or_imp, forall_eq]
      rw [hl, hh, hs, hs]
      change (P (formPair n (highClass n j) (evenTerminalValue p).high) ∧
        P (formPair n j (evenTerminalValue p).low)) ↔ _
      simp [evenTailLowForms, evenTailHighForms, formsEdges, ← hk, and_comm]
  | m+1, s, ⟨i, p⟩, j, hj, hn => by
      rw [show evenTailReflection (m+1) s ⟨i, p⟩ =
        ⟨i, evenTailReflection m (stepTarget i) p⟩ from rfl]
      rw [even_edges_peel (h := .negative) i _ (by omega),
        even_edges_peel (h := .positive) i p (by omega), all_edges_peel, all_edges_peel]
      obtain ⟨hl, hh⟩ := step_reflection_pairs n j (by omega) s i
      rw [hl, hh, hs, hs, even_tail_reflection_property n P hs m (stepTarget i) p
        (j+1) (by omega) (by omega)]
      tauto

private theorem odd_tail_reflection_property (n : Nat)
    (P : ZMod n × ZMod n → Prop) (hs : ∀ e, P e.swap ↔ P e) :
    (m : Nat) → (s : State) → (p : OddTail .positive m s) → (j : Nat) →
    3 ≤ j → n+1 = 2*(j+m) →
    ((∀ e ∈ formsEdges n j (oddTailLowForms (oddTailReflection m s p) ++
      (oddTailHighForms (oddTailReflection m s p)).reverse), P e) ↔
      ∀ e ∈ formsEdges n j (oddTailLowForms p ++ (oddTailHighForms p).reverse), P e)
  | 0, s, p, j, hj, hn => by
      have hl := odd_cap_reflection_pair n j (by omega) s p
      change (∀ e ∈ [formPair n j (oddTerminalValue (h := .negative) p).label], P e) ↔ _
      simp only [List.mem_singleton, forall_eq]
      rw [hl, hs]
      simp [oddTailLowForms, oddTailHighForms, formsEdges]
  | m+1, s, ⟨i, p⟩, j, hj, hn => by
      rw [show oddTailReflection (m+1) s ⟨i, p⟩ =
        ⟨i, oddTailReflection m (stepTarget i) p⟩ from rfl]
      rw [odd_edges_peel (h := .negative) i _ (by omega),
        odd_edges_peel (h := .positive) i p (by omega), all_edges_peel, all_edges_peel]
      obtain ⟨hl, hh⟩ := step_reflection_pairs n j (by omega) s i
      rw [hl, hh, hs, hs, odd_tail_reflection_property n P hs m (stepTarget i) p
        (j+1) (by omega) (by omega)]
      tauto

private theorem start_reflection_pair (n : Nat) (i : Fin 2) :
    formPair n 2 (startValue (h := .negative) i).label =
      (formPair n 2 (startValue (h := .positive) i).label).swap := by
  fin_cases i <;> apply Prod.ext <;> simp [List.get, Form.I, Form.II, Form.III, Form.IV, Form.V, Form.VI, startValue, starts, formPair] <;> ring

theorem even_reflection_edge_property (r : Nat) (hr : 1 ≤ r)
    (p : EvenPath .positive (3*r-3)) (P : ZMod (3*(2*r)) × ZMod (3*(2*r)) → Prop)
    (hs : ∀ e, P e.swap ↔ P e) :
    (∀ i, P (chosenPair (evenPathChoices r hr (evenPathReflection _ p)) i)) ↔
      ∀ i, P (chosenPair (evenPathChoices r hr p) i) := by
  have hc (c : Choices (2*r)) : (∀ i, P (chosenPair c i)) ↔
      ∀ e ∈ formsEdges (3*(2*r)) 2 (choiceForms c), P e := by
    constructor
    · intro h e hm
      obtain ⟨i, rfl⟩ := (choice_edges_mem c e).mp hm
      exact h i
    · intro h i
      exact h _ ((choice_edges_mem c _).mpr ⟨i, rfl⟩)
  rw [hc, hc, even_decode_forms, even_decode_forms]
  rcases p with ⟨i, p⟩
  change (∀ e ∈ formPair _ 2 (startValue (h := .negative) i).label ::
    formsEdges _ 3 (evenTailLowForms (evenTailReflection _ _ p) ++
      (evenTailHighForms (evenTailReflection _ _ p)).reverse), P e) ↔ _
  simp only [List.mem_cons, forall_eq_or_imp]
  rw [start_reflection_pair, hs, even_tail_reflection_property _ P hs _ _ p 3
    (by omega) (by omega)]
  simp only [evenPathForms, formsEdges, List.mem_cons, forall_eq_or_imp]

theorem odd_reflection_edge_property (r : Nat) (hr : 1 ≤ r)
    (p : OddPath .positive (3*r-1)) (P : ZMod (3*(2*r+1)) × ZMod (3*(2*r+1)) → Prop)
    (hs : ∀ e, P e.swap ↔ P e) :
    (∀ i, P (chosenPair (oddPathChoices r hr (oddPathReflection _ p)) i)) ↔
      ∀ i, P (chosenPair (oddPathChoices r hr p) i) := by
  have hc (c : Choices (2*r+1)) : (∀ i, P (chosenPair c i)) ↔
      ∀ e ∈ formsEdges (3*(2*r+1)) 2 (choiceForms c), P e := by
    constructor
    · intro h e hm
      obtain ⟨i, rfl⟩ := (choice_edges_mem c e).mp hm
      exact h i
    · intro h i
      exact h _ ((choice_edges_mem c _).mpr ⟨i, rfl⟩)
  rw [hc, hc, odd_decode_forms, odd_decode_forms]
  rcases p with ⟨i, p⟩
  change (∀ e ∈ formPair _ 2 (startValue (h := .negative) i).label ::
    formsEdges _ 3 (oddTailLowForms (oddTailReflection _ _ p) ++
      (oddTailHighForms (oddTailReflection _ _ p)).reverse), P e) ↔ _
  simp only [List.mem_cons, forall_eq_or_imp]
  rw [start_reflection_pair, hs, odd_tail_reflection_property _ P hs _ _ p 3
    (by omega) (by omega)]
  simp only [oddPathForms, formsEdges, List.mem_cons, forall_eq_or_imp]

private theorem support_mono {t : Nat} (c d : Choices t)
    (he : ∀ i, (supportSetoid d).r (chosenPair c i).1 (chosenPair c i).2)
    {u v : ZMod (3*t)} (h : (supportSetoid c).r u v) :
    (supportSetoid d).r u v := by
  induction h with
  | rel u v h =>
      obtain ⟨i, hi⟩ := h
      simpa only [hi, Prod.fst, Prod.snd] using he i
  | refl => exact (supportSetoid d).refl _
  | symm u v h ih => exact (supportSetoid d).symm ih
  | trans u v w h h' ih ih' => exact (supportSetoid d).trans ih ih'

theorem even_reflection_support (r : Nat) (hr : 1 ≤ r)
    (p : EvenPath .positive (3*r-3)) (u v : ZMod (3*(2*r))) :
    (supportSetoid (evenPathChoices r hr (evenPathReflection _ p))).r u v ↔
      (supportSetoid (evenPathChoices r hr p)).r u v := by
  let c := evenPathChoices r hr p
  let d := evenPathChoices r hr (evenPathReflection _ p)
  have edges (a : Choices (2*r)) (i : Fin (3*(2*r)-3)) :
      (supportSetoid a).r (chosenPair a i).1 (chosenPair a i).2 :=
    Relation.EqvGen.rel _ _ ⟨i, Prod.eta _⟩
  constructor
  · apply support_mono d c
    exact (even_reflection_edge_property r hr p
      (fun e => (supportSetoid c).r e.1 e.2)
      (fun _ => ⟨(supportSetoid c).symm, (supportSetoid c).symm⟩)).mpr (edges c)
  · apply support_mono c d
    exact (even_reflection_edge_property r hr p
      (fun e => (supportSetoid d).r e.1 e.2)
      (fun _ => ⟨(supportSetoid d).symm, (supportSetoid d).symm⟩)).mp (edges d)

theorem odd_reflection_support (r : Nat) (hr : 1 ≤ r)
    (p : OddPath .positive (3*r-1)) (u v : ZMod (3*(2*r+1))) :
    (supportSetoid (oddPathChoices r hr (oddPathReflection _ p))).r u v ↔
      (supportSetoid (oddPathChoices r hr p)).r u v := by
  let c := oddPathChoices r hr p
  let d := oddPathChoices r hr (oddPathReflection _ p)
  have edges (a : Choices (2*r+1)) (i : Fin (3*(2*r+1)-3)) :
      (supportSetoid a).r (chosenPair a i).1 (chosenPair a i).2 :=
    Relation.EqvGen.rel _ _ ⟨i, Prod.eta _⟩
  constructor
  · apply support_mono d c
    exact (odd_reflection_edge_property r hr p
      (fun e => (supportSetoid c).r e.1 e.2)
      (fun _ => ⟨(supportSetoid c).symm, (supportSetoid c).symm⟩)).mpr (edges c)
  · apply support_mono c d
    exact (odd_reflection_edge_property r hr p
      (fun e => (supportSetoid d).r e.1 e.2)
      (fun _ => ⟨(supportSetoid d).symm, (supportSetoid d).symm⟩)).mp (edges d)

theorem even_reflection_active (r : Nat) (hr : 1 ≤ r)
    (p : EvenPath .positive (3*r-3)) (v : ZMod (3*(2*r))) :
    Active (evenPathChoices r hr (evenPathReflection _ p)) v ↔
      Active (evenPathChoices r hr p) v := by
  classical
  have h := even_reflection_edge_property r hr p
    (fun e => e.1 ≠ v ∧ e.2 ≠ v) (fun _ => and_comm)
  have hn : ¬ Active (evenPathChoices r hr (evenPathReflection _ p)) v ↔
      ¬ Active (evenPathChoices r hr p) v := by
    simpa only [Active, not_exists, not_or] using h
  exact not_iff_not.mp hn

theorem odd_reflection_active (r : Nat) (hr : 1 ≤ r)
    (p : OddPath .positive (3*r-1)) (v : ZMod (3*(2*r+1))) :
    Active (oddPathChoices r hr (oddPathReflection _ p)) v ↔
      Active (oddPathChoices r hr p) v := by
  classical
  have h := odd_reflection_edge_property r hr p
    (fun e => e.1 ≠ v ∧ e.2 ≠ v) (fun _ => and_comm)
  have hn : ¬ Active (oddPathChoices r hr (oddPathReflection _ p)) v ↔
      ¬ Active (oddPathChoices r hr p) v := by
    simpa only [Active, not_exists, not_or] using h
  exact not_iff_not.mp hn

theorem even_reflection_connected (r : Nat) (hr : 1 ≤ r)
    (p : EvenPath .positive (3*r-3)) :
    ActiveConnected (evenPathChoices r hr (evenPathReflection _ p)) ↔
      ActiveConnected (evenPathChoices r hr p) := by
  constructor
  · intro h u v
    exact (even_reflection_support r hr p u.1 v.1).mp (h
      ⟨u.1, (even_reflection_active r hr p u.1).mpr u.2⟩
      ⟨v.1, (even_reflection_active r hr p v.1).mpr v.2⟩)
  · intro h u v
    exact (even_reflection_support r hr p u.1 v.1).mpr (h
      ⟨u.1, (even_reflection_active r hr p u.1).mp u.2⟩
      ⟨v.1, (even_reflection_active r hr p v.1).mp v.2⟩)

theorem odd_reflection_connected (r : Nat) (hr : 1 ≤ r)
    (p : OddPath .positive (3*r-1)) :
    ActiveConnected (oddPathChoices r hr (oddPathReflection _ p)) ↔
      ActiveConnected (oddPathChoices r hr p) := by
  constructor
  · intro h u v
    exact (odd_reflection_support r hr p u.1 v.1).mp (h
      ⟨u.1, (odd_reflection_active r hr p u.1).mpr u.2⟩
      ⟨v.1, (odd_reflection_active r hr p v.1).mpr v.2⟩)
  · intro h u v
    exact (odd_reflection_support r hr p u.1 v.1).mpr (h
      ⟨u.1, (odd_reflection_active r hr p u.1).mp u.2⟩
      ⟨v.1, (odd_reflection_active r hr p v.1).mp v.2⟩)

end D5.S3.Combinatorics.Zigzag
