/- GID: D5/S3/Combinatorics/Zigzag/ActiveSupport
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Zigzag/ActiveSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation, mathlib/module/Mathlib.SetTheory.Cardinal.Finite]
   utility: none
   digest: Actual labelled edge support and semitone anchoring of retirement paths. -/

import D5.S3.Combinatorics.Zigzag.EvenPaths
import D5.S3.Combinatorics.Zigzag.OddPaths
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Finite
import Aesop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Zigzag

/-- The index is the original class label, even when endpoint pairs coincide. -/
def chosenPair {t : Nat} (c : Choices t) (i : Fin (3 * t - 3)) :=
  formPair (3 * t) (classIndex i) (c.1 i)

/-- Only endpoints of actually chosen edges are active. -/
def Active {t : Nat} (c : Choices t) (v : ZMod (3 * t)) : Prop :=
  ∃ i, (chosenPair c i).1 = v ∨ (chosenPair c i).2 = v

abbrev ActiveVertex {t : Nat} (c : Choices t) := {v // Active c v}

/-- The directed generator retains the original class as its witness. -/
def SupportArrow {t : Nat} (c : Choices t) (u v : ZMod (3 * t)) : Prop :=
  ∃ i, chosenPair c i = (u, v)

/-- Equivalence closure of the actual directed edges ignores orientation. -/
def supportSetoid {t : Nat} (c : Choices t) : Setoid (ZMod (3 * t)) :=
  Relation.EqvGen.setoid (SupportArrow c)

def activeSetoid {t : Nat} (c : Choices t) : Setoid (ActiveVertex c) :=
  Setoid.comap Subtype.val (supportSetoid c)

/-- Unused residues have no representatives in this quotient. -/
def ActiveComponent {t : Nat} (c : Choices t) := Quotient (activeSetoid c)

noncomputable def activeComponentCount {t : Nat} (c : Choices t) : Nat :=
  Nat.card (ActiveComponent c)

private def semitone (n : Nat) (b : Bool) : ZMod n := if b then 1 else -1

private def Rooted {n : Nat} (R : Setoid (ZMod n)) (v : ZMod n) : Prop :=
  R.r v 1 ∨ R.r v (-1)

private theorem rooted_plus {n : Nat} (R : Setoid (ZMod n)) : Rooted R 1 :=
  Or.inl (R.refl _)

private theorem rooted_minus {n : Nat} (R : Setoid (ZMod n)) : Rooted R (-1) :=
  Or.inr (R.refl _)

private theorem rooted_forward {n : Nat} {R : Setoid (ZMod n)}
    {u v : ZMod n} (h : R.r u v) (hu : Rooted R u) : Rooted R v := by
  rcases hu with hu | hu
  · exact Or.inl (R.trans (R.symm h) hu)
  · exact Or.inr (R.trans (R.symm h) hu)

private theorem rooted_backward {n : Nat} {R : Setoid (ZMod n)}
    {u v : ZMod n} (h : R.r u v) (hv : Rooted R v) : Rooted R u :=
  rooted_forward (R.symm h) hv

private def FrontierRooted {n : Nat} (R : Setoid (ZMod n)) (s : State)
    (j : Nat) : Prop :=
  (statePositive s ≠ 0 → Rooted R (j : ZMod n)) ∧
  (stateNegative s ≠ 0 → Rooted R (-(j : ZMod n)))

private def EdgesRooted {n : Nat} (R : Setoid (ZMod n))
    (es : List (ZMod n × ZMod n)) : Prop :=
  ∀ e ∈ es, Rooted R e.1 ∧ Rooted R e.2

private def EdgesRelated {n : Nat} (R : Setoid (ZMod n))
    (es : List (ZMod n × ZMod n)) : Prop := ∀ e ∈ es, R.r e.1 e.2

def formsEdges (n k : Nat) : List Form → List (ZMod n × ZMod n)
  | [] => []
  | f :: fs => formPair n k f :: formsEdges n (k + 1) fs

private theorem formsEdges_append (n k : Nat) (xs ys : List Form) :
    formsEdges n k (xs ++ ys) =
      formsEdges n k xs ++ formsEdges n (k + xs.length) ys := by
  induction xs generalizing k with
  | nil => simp [formsEdges]
  | cons f fs ih => simp [formsEdges, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem start_rooted (n : Nat) (R : Setoid (ZMod n)) (h : Half)
    (i : StartIndex h)
    (he : R.r (formPair n 2 (startValue i).label).1
      (formPair n 2 (startValue i).label).2) :
    FrontierRooted R (startTarget i) 2 ∧
      EdgesRooted R [formPair n 2 (startValue i).label] := by
  have hp := rooted_plus R
  have hm := rooted_minus R
  have htwo : (2 : ZMod n) - 1 = 1 := by ring
  have htwo' : 1 - (2 : ZMod n) = -1 := by ring
  cases h <;> fin_cases i <;>
    simp [FrontierRooted, EdgesRooted, startValue, starts, startTarget, startTargets,
      statePositive, stateNegative, State.A, State.D, formPair, Form.II, Form.III, Form.IV, Form.V,
      htwo, htwo'] at he ⊢ <;>
    aesop (add safe forward [rooted_forward, rooted_backward])

private theorem transition_rooted (n j : Nat) (hj : 1 ≤ j) (hjn : j ≤ n + 1)
    (R : Setoid (ZMod n)) (h : Half) (s : State) (i : StepIndex s)
    (hf : FrontierRooted R s (j - 1))
    (hl : R.r (formPair n j (stepValue (h := h) i).low).1
      (formPair n j (stepValue (h := h) i).low).2)
    (hh : R.r (formPair n (highClass n j) (stepValue (h := h) i).high).1
      (formPair n (highClass n j) (stepValue (h := h) i).high).2) :
    FrontierRooted R (stepTarget i) j ∧
      EdgesRooted R [formPair n j (stepValue (h := h) i).low,
        formPair n (highClass n j) (stepValue (h := h) i).high] := by
  have hp := rooted_plus R
  have hm := rooted_minus R
  have hsub : ((j - 1 : Nat) : ZMod n) = (j : ZMod n) - 1 := by
    rw [Nat.cast_sub hj]; push_cast; rfl
  have hhigh : (highClass n j : ZMod n) = 1 - (j : ZMod n) := by
    simp only [highClass, Nat.cast_sub hjn, Nat.cast_add, ZMod.natCast_self,
      Nat.cast_one, zero_add]
  have hhighSub : (highClass n j : ZMod n) - 1 = -(j : ZMod n) := by
    rw [hhigh]; ring
  have honeHigh : 1 - (highClass n j : ZMod n) = (j : ZMod n) := by
    rw [hhigh]; ring
  have hnegHigh : -(highClass n j : ZMod n) = (j : ZMod n) - 1 := by
    rw [hhigh]; ring
  have hnegSub : -((j : ZMod n) - 1) = 1 - (j : ZMod n) := by ring
  cases h <;> fin_cases s <;> fin_cases i <;>
    simp [FrontierRooted, EdgesRooted, stepValue, positiveStepLabel, negativeStepLabel,
      stepTarget, stepTargets, statePositive, stateNegative, State.A, State.D,
      State.E, State.H, State.I, formPair, Form.I, Form.II, Form.III, Form.IV,
      Form.V, Form.VI, hsub, hhigh, hhighSub, honeHigh, hnegHigh, hnegSub] at hf hl hh ⊢ <;>
    aesop (add safe forward [rooted_forward, rooted_backward])

private theorem even_cap_rooted (n j : Nat) (R : Setoid (ZMod n))
    (hn : n = 2 * j) (hjn : j ≤ n + 1) (h : Half) (s : State)
    (e : EvenTerminalIndex h s)
    (hl : R.r (formPair n j (evenTerminalValue e).low).1
      (formPair n j (evenTerminalValue e).low).2)
    (hh : R.r (formPair n (highClass n j) (evenTerminalValue e).high).1
      (formPair n (highClass n j) (evenTerminalValue e).high).2) :
    EdgesRooted R [formPair n j (evenTerminalValue e).low,
      formPair n (highClass n j) (evenTerminalValue e).high] := by
  have hp := rooted_plus R
  have hm := rooted_minus R
  have hanti : (j : ZMod n) = -(j : ZMod n) := by
    rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add]
    have hjj : j + j = n := by omega
    rw [hjj]; exact ZMod.natCast_self n
  have hhigh : (highClass n j : ZMod n) = 1 - (j : ZMod n) := by
    simp only [highClass, Nat.cast_sub hjn, Nat.cast_add, ZMod.natCast_self,
      Nat.cast_one, zero_add]
  have hhighSub : (highClass n j : ZMod n) - 1 = -(j : ZMod n) := by
    rw [hhigh]; ring
  have honeHigh : 1 - (highClass n j : ZMod n) = (j : ZMod n) := by
    rw [hhigh]; ring
  have hnegHigh : -(highClass n j : ZMod n) = (j : ZMod n) - 1 := by
    rw [hhigh]; ring
  cases h <;> fin_cases s
  all_goals first | exact Fin.elim0 e | skip
  all_goals fin_cases e
  all_goals simp [EdgesRooted, evenTerminalValue, formPair, Form.III, Form.IV,
    Form.V, Form.II, Form.I, Form.VI, hhigh, hhighSub, honeHigh, hnegHigh] at hl hh ⊢
  all_goals
    have hrootAnti : Rooted R (j : ZMod n) → Rooted R (-(j : ZMod n)) :=
      fun hj => hanti ▸ hj
    have hrootAnti' : Rooted R (-(j : ZMod n)) → Rooted R (j : ZMod n) :=
      fun hj => hanti.symm ▸ hj
    clear hanti
    aesop (add safe forward [rooted_forward, rooted_backward, hrootAnti, hrootAnti'])

private theorem odd_cap_rooted (n j : Nat) (R : Setoid (ZMod n))
    (h : Half) (s : State) (e : OddTerminalIndex h s)
    (he : R.r (formPair n j (oddTerminalValue e).label).1
      (formPair n j (oddTerminalValue e).label).2) :
    EdgesRooted R [formPair n j (oddTerminalValue e).label] := by
  have hp := rooted_plus R
  have hm := rooted_minus R
  cases h <;> fin_cases s
  all_goals first | exact Fin.elim0 e | skip
  all_goals fin_cases e
  all_goals simp [EdgesRooted, oddTerminalValue, formPair, Form.I, Form.III,
    Form.V, Form.VI] at he ⊢
  all_goals aesop (add safe forward [rooted_forward, rooted_backward])

theorem even_edges_peel {h : Half} {m n j : Nat} {s : State}
    (i : StepIndex s) (p : EvenTail h m (stepTarget i))
    (hn : n = 2 * (j + m + 1)) :
    formsEdges n j (evenTailLowForms (m := m + 1) ⟨i, p⟩ ++
      (evenTailHighForms (m := m + 1) ⟨i, p⟩).reverse) =
    formPair n j (stepValue (h := h) i).low ::
      (formsEdges n (j + 1) (evenTailLowForms p ++ (evenTailHighForms p).reverse) ++
        [formPair n (highClass n j) (stepValue (h := h) i).high]) := by
  have hlen : (evenTailLowForms p ++ (evenTailHighForms p).reverse).length = 2 * m + 2 := by
    simp; omega
  have hk : j + 1 + (2 * m + 2) = highClass n j := by simp only [highClass]; omega
  have hforms : evenTailLowForms (m := m + 1) ⟨i, p⟩ ++
      (evenTailHighForms (m := m + 1) ⟨i, p⟩).reverse =
      (stepValue (h := h) i).low ::
        ((evenTailLowForms p ++ (evenTailHighForms p).reverse) ++
          [(stepValue (h := h) i).high]) := by
    simp [evenTailLowForms, evenTailHighForms, List.append_assoc]
  rw [hforms]
  simp only [formsEdges]
  rw [formsEdges_append n (j + 1)
    (evenTailLowForms p ++ (evenTailHighForms p).reverse), hlen, hk]
  rfl

theorem odd_edges_peel {h : Half} {m n j : Nat} {s : State}
    (i : StepIndex s) (p : OddTail h m (stepTarget i))
    (hn : n + 1 = 2 * (j + m + 1)) :
    formsEdges n j (oddTailLowForms (m := m + 1) ⟨i, p⟩ ++
      (oddTailHighForms (m := m + 1) ⟨i, p⟩).reverse) =
    formPair n j (stepValue (h := h) i).low ::
      (formsEdges n (j + 1) (oddTailLowForms p ++ (oddTailHighForms p).reverse) ++
        [formPair n (highClass n j) (stepValue (h := h) i).high]) := by
  have hlen : (oddTailLowForms p ++ (oddTailHighForms p).reverse).length = 2 * m + 1 := by
    simp; omega
  have hk : j + 1 + (2 * m + 1) = highClass n j := by simp only [highClass]; omega
  have hforms : oddTailLowForms (m := m + 1) ⟨i, p⟩ ++
      (oddTailHighForms (m := m + 1) ⟨i, p⟩).reverse =
      (stepValue (h := h) i).low ::
        ((oddTailLowForms p ++ (oddTailHighForms p).reverse) ++
          [(stepValue (h := h) i).high]) := by
    simp [oddTailLowForms, oddTailHighForms, List.append_assoc]
  rw [hforms]
  simp only [formsEdges]
  rw [formsEdges_append n (j + 1)
    (oddTailLowForms p ++ (oddTailHighForms p).reverse), hlen, hk]
  rfl

private theorem even_tail_rooted {n : Nat} (R : Setoid (ZMod n)) (h : Half) :
    {m : Nat} → {s : State} → (p : EvenTail h m s) → (j : Nat) →
    3 ≤ j → n = 2 * (j + m) → FrontierRooted R s (j - 1) →
    EdgesRelated R (formsEdges n j (evenTailLowForms p ++ (evenTailHighForms p).reverse)) →
    EdgesRooted R (formsEdges n j (evenTailLowForms p ++ (evenTailHighForms p).reverse))
  | 0, s, p, j, hj, hn, _, he => by
      simp only [evenTailLowForms, evenTailHighForms, List.reverse_singleton,
        List.singleton_append, formsEdges, List.nil_append] at he ⊢
      have hk : j + 1 = highClass n j := by simp only [highClass]; omega
      rw [hk] at he ⊢
      exact even_cap_rooted n j R (by omega) (by omega) h s p
        (he _ (by simp)) (he _ (by simp))
  | m + 1, s, ⟨i, p⟩, j, hj, hn, hf, he => by
      rw [even_edges_peel i p (by omega)] at he ⊢
      have hl := he _ (List.mem_cons_self ..)
      have hh := he (formPair n (highClass n j) (stepValue (h := h) i).high) (by simp)
      have hinner : EdgesRelated R
          (formsEdges n (j + 1) (evenTailLowForms p ++ (evenTailHighForms p).reverse)) := by
        intro e he'; exact he e (by simp [he'])
      obtain ⟨hf', ha⟩ := transition_rooted n j (by omega) (by omega) R h s i hf hl hh
      have hi := even_tail_rooted R h p (j + 1) (by omega) (by omega)
        (by simpa using hf') hinner
      intro e he'
      simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at he'
      rcases he' with rfl | he' | rfl
      · exact ha _ (by simp)
      · exact hi _ he'
      · exact ha _ (by simp)

private theorem odd_tail_rooted {n : Nat} (R : Setoid (ZMod n)) (h : Half) :
    {m : Nat} → {s : State} → (p : OddTail h m s) → (j : Nat) →
    3 ≤ j → n + 1 = 2 * (j + m) → FrontierRooted R s (j - 1) →
    EdgesRelated R (formsEdges n j (oddTailLowForms p ++ (oddTailHighForms p).reverse)) →
    EdgesRooted R (formsEdges n j (oddTailLowForms p ++ (oddTailHighForms p).reverse))
  | 0, s, p, j, _, _, _, he => by
      simp only [oddTailLowForms, oddTailHighForms, List.reverse_nil,
        List.append_nil, formsEdges] at he ⊢
      exact odd_cap_rooted n j R h s p (he _ (by simp))
  | m + 1, s, ⟨i, p⟩, j, hj, hn, hf, he => by
      rw [odd_edges_peel i p (by omega)] at he ⊢
      have hl := he _ (List.mem_cons_self ..)
      have hh := he (formPair n (highClass n j) (stepValue (h := h) i).high) (by simp)
      have hinner : EdgesRelated R
          (formsEdges n (j + 1) (oddTailLowForms p ++ (oddTailHighForms p).reverse)) := by
        intro e he'; exact he e (by simp [he'])
      obtain ⟨hf', ha⟩ := transition_rooted n j (by omega) (by omega) R h s i hf hl hh
      have hi := odd_tail_rooted R h p (j + 1) (by omega) (by omega)
        (by simpa using hf') hinner
      intro e he'
      simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at he'
      rcases he' with rfl | he' | rfl
      · exact ha _ (by simp)
      · exact hi _ he'
      · exact ha _ (by simp)

private theorem even_path_rooted (r : Nat) (hr : 1 ≤ r) (h : Half)
    (p : EvenPath h (3 * r - 3)) (R : Setoid (ZMod (3 * (2 * r))))
    (he : EdgesRelated R (formsEdges (3 * (2 * r)) 2 (evenPathForms p))) :
    EdgesRooted R (formsEdges (3 * (2 * r)) 2 (evenPathForms p)) := by
  rcases p with ⟨i, p⟩
  simp only [evenPathForms, formsEdges] at he ⊢
  obtain ⟨hf, hs⟩ := start_rooted (3 * (2 * r)) R h i (he _ (by simp))
  have hi := even_tail_rooted R h p 3 (by omega) (by omega) hf
    (by intro e he'; exact he e (by simp [he']))
  intro e he'
  simp only [List.mem_cons] at he'
  rcases he' with rfl | he'
  · exact hs _ (by simp)
  · exact hi _ he'

private theorem odd_path_rooted (r : Nat) (hr : 1 ≤ r) (h : Half)
    (p : OddPath h (3 * r - 1)) (R : Setoid (ZMod (3 * (2 * r + 1))))
    (he : EdgesRelated R (formsEdges (3 * (2 * r + 1)) 2 (oddPathForms p))) :
    EdgesRooted R (formsEdges (3 * (2 * r + 1)) 2 (oddPathForms p)) := by
  rcases p with ⟨i, p⟩
  simp only [oddPathForms, formsEdges] at he ⊢
  obtain ⟨hf, hs⟩ := start_rooted (3 * (2 * r + 1)) R h i (he _ (by simp))
  have hi := odd_tail_rooted R h p 3 (by omega) (by omega) hf
    (by intro e he'; exact he e (by simp [he']))
  intro e he'
  simp only [List.mem_cons] at he'
  rcases he' with rfl | he'
  · exact hs _ (by simp)
  · exact hi _ he'

private theorem formsEdges_length (n k : Nat) (xs : List Form) :
    (formsEdges n k xs).length = xs.length := by
  induction xs generalizing k with
  | nil => rfl
  | cons f fs ih => simpa only [formsEdges, List.length_cons] using congrArg Nat.succ (ih (k+1))

private theorem formsEdges_get (n k : Nat) (xs : List Form) (i : Fin xs.length) :
    (formsEdges n k xs).get ⟨i.val, by simpa only [formsEdges_length] using i.isLt⟩ =
      formPair n (k + i.val) (xs.get i) := by
  induction xs generalizing k with
  | nil => exact Fin.elim0 i
  | cons f fs ih =>
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [formsEdges]
      · simpa [formsEdges, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k+1) i

theorem choice_edges_mem {t : Nat} (c : Choices t) (e : ZMod (3*t) × ZMod (3*t)) :
    e ∈ formsEdges (3*t) 2 (choiceForms c) ↔ ∃ i, chosenPair c i = e := by
  constructor
  · intro he
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp he
    have hil : i.val < (choiceForms c).length := by
      simpa only [formsEdges_length] using i.isLt
    have he' := formsEdges_get (3*t) 2 (choiceForms c) ⟨i.val, hil⟩
    have hv : (⟨i.val, by simpa only [formsEdges_length] using hil⟩ :
        Fin (formsEdges (3*t) 2 (choiceForms c)).length) = i := Fin.ext rfl
    rw [hv, hi] at he'
    refine ⟨⟨i.val, by simpa [choiceForms] using hil⟩, ?_⟩
    simpa [chosenPair, classIndex, choiceForms, List.get_ofFn, Nat.add_comm] using he'.symm
  · rintro ⟨i, rfl⟩
    have hi : i.val < (choiceForms c).length := by simpa [choiceForms] using i.isLt
    have he := formsEdges_get (3*t) 2 (choiceForms c) ⟨i.val, hi⟩
    apply List.mem_iff_get.mpr
    refine ⟨⟨i.val, by simpa only [formsEdges_length] using hi⟩, ?_⟩
    simpa [chosenPair, classIndex, choiceForms, List.get_ofFn, Nat.add_comm] using he

private theorem choice_edges_related {t : Nat} (c : Choices t) :
    EdgesRelated (supportSetoid c) (formsEdges (3*t) 2 (choiceForms c)) := by
  intro e he
  obtain ⟨i, hi⟩ := (choice_edges_mem c e).mp he
  exact Relation.EqvGen.rel _ _ ⟨i, hi⟩

theorem even_decode_forms (r : Nat) (hr : 1 ≤ r) {h : Half}
    (p : EvenPath h (3*r-3)) :
    choiceForms (evenPathChoices r hr p) = evenPathForms p := by
  apply List.ext_get
  · simp [choiceForms]; omega
  · intro i hi hj
    simp [choiceForms, evenPathChoices]
    rfl

theorem odd_decode_forms (r : Nat) (hr : 1 ≤ r) {h : Half}
    (p : OddPath h (3*r-1)) :
    choiceForms (oddPathChoices r hr p) = oddPathForms p := by
  apply List.ext_get
  · simp [choiceForms]; omega
  · intro i hi hj
    simp [choiceForms, oddPathChoices]
    rfl

private theorem balanced_edges_rooted (t : Nat) (ht : 2 ≤ t) (c : Choices t)
    (hc : Balanced c) :
    EdgesRooted (supportSetoid c) (formsEdges (3*t) 2 (choiceForms c)) := by
  by_cases hm : t % 2 = 0
  · have he : t = 2 * (t/2) := by omega
    obtain ⟨r, rfl⟩ : ∃ r, t = 2*r := ⟨t/2, he⟩
    have hr : 1 ≤ r := by omega
    have hs : Function.Surjective (evenZeroPathChoices r hr) :=
      (evenBalancedChoicesEquiv r hr).symm.surjective
    obtain ⟨p, hp⟩ := hs ⟨c, hc⟩
    cases p with
    | inl p =>
        have hp' : evenPathChoices r hr p.1 = c := congrArg Subtype.val hp
        subst c
        rw [even_decode_forms]
        apply even_path_rooted r hr .positive p.1
        rw [← even_decode_forms r hr p.1]
        exact choice_edges_related _
    | inr p =>
        have hp' : evenPathChoices r hr p.1 = c := congrArg Subtype.val hp
        subst c
        rw [even_decode_forms]
        apply even_path_rooted r hr .negative p.1
        rw [← even_decode_forms r hr p.1]
        exact choice_edges_related _
  · have he : t = 2 * (t/2) + 1 := by omega
    obtain ⟨r, rfl⟩ : ∃ r, t = 2*r+1 := ⟨t/2, he⟩
    have hr : 1 ≤ r := by omega
    have hs : Function.Surjective (oddZeroPathChoices r hr) :=
      (oddBalancedChoicesEquiv r hr).symm.surjective
    obtain ⟨p, hp⟩ := hs ⟨c, hc⟩
    cases p with
    | inl p =>
        have hp' : oddPathChoices r hr p.1 = c := congrArg Subtype.val hp
        subst c
        rw [odd_decode_forms]
        apply odd_path_rooted r hr .positive p.1
        rw [← odd_decode_forms r hr p.1]
        exact choice_edges_related _
    | inr p =>
        have hp' : oddPathChoices r hr p.1 = c := congrArg Subtype.val hp
        subst c
        rw [odd_decode_forms]
        apply odd_path_rooted r hr .negative p.1
        rw [← odd_decode_forms r hr p.1]
        exact choice_edges_related _

theorem active_iff_of_related {t : Nat} (c : Choices t)
    {u v : ZMod (3*t)} (h : (supportSetoid c).r u v) : Active c u ↔ Active c v := by
  induction h with
  | rel u v h =>
      obtain ⟨i, hi⟩ := h
      have hu : Active c u := ⟨i, Or.inl (congrArg Prod.fst hi)⟩
      have hv : Active c v := ⟨i, Or.inr (congrArg Prod.snd hi)⟩
      exact ⟨fun _ => hv, fun _ => hu⟩
  | refl => exact Iff.rfl
  | symm u v h ih => exact ih.symm
  | trans u v w h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem active_rooted (t : Nat) (ht : 2 ≤ t) (c : Choices t)
    (hc : Balanced c) (v : ActiveVertex c) : Rooted (supportSetoid c) v.1 := by
  obtain ⟨i, hi⟩ := v.2
  have he := balanced_edges_rooted t ht c hc (chosenPair c i)
    ((choice_edges_mem c _).mpr ⟨i, rfl⟩)
  rcases hi with hi | hi
  · simpa only [hi] using he.1
  · simpa only [hi] using he.2

/-- Every actual active weak component contains an actually used semitone.
The semitone subtype may have one element; no activity assumption is imposed on either sign. -/
theorem active_component_count_le_two (t : Nat) (ht : 2 ≤ t)
    (c : Choices t) (hc : Balanced c) : activeComponentCount c ≤ 2 := by
  classical
  let S := {b : Bool // Active c (semitone (3*t) b)}
  let f : S → ActiveComponent c := fun b =>
    Quotient.mk (activeSetoid c) ⟨semitone (3*t) b.1, b.2⟩
  have hs : Function.Surjective f := by
    intro q
    refine Quotient.inductionOn q ?_
    intro v
    obtain hv | hv := active_rooted t ht c hc v
    · refine ⟨⟨true, ?_⟩, ?_⟩
      · exact (active_iff_of_related c hv).mp v.2
      · apply Quotient.sound
        exact (supportSetoid c).symm hv
    · refine ⟨⟨false, ?_⟩, ?_⟩
      · exact (active_iff_of_related c hv).mp v.2
      · apply Quotient.sound
        exact (supportSetoid c).symm hv
  have hcard := Nat.card_le_card_of_surjective f hs
  have hsub := Nat.card_le_card_of_injective (fun b : S => b.1) Subtype.val_injective
  have hbool : Nat.card Bool = 2 := by simp
  exact hcard.trans (hsub.trans_eq hbool)


end D5.S3.Combinatorics.Zigzag
