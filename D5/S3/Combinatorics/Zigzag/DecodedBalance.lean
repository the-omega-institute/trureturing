/- GID: D5/S3/Combinatorics/Zigzag/DecodedBalance
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Zigzag/DecodedBalance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Group.Fin]
   utility: none
   digest: Literal balance of decoded zero-charge retirement paths. -/

import D5.S3.Combinatorics.Zigzag.PathEncoding
import D5.S3.Combinatorics.Zigzag.ChoiceClassification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Fin.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Zigzag

theorem formsFlow_eq_fin_sum (n k : Nat) (xs : List Form) :
    formsFlow n k xs =
      ∑ i : Fin xs.length, edgeFlow n (k + i.val) (xs.get i) := by
  induction xs generalizing k with
  | nil => simp [formsFlow]
  | cons x xs ih =>
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simp only [formsFlow, List.length_cons, List.get_eq_getElem,
        Fin.val_zero, List.getElem_cons_zero, Fin.val_succ,
        List.getElem_cons_succ]
      rw [ih]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def choiceForms {t : Nat} (c : Choices t) : List Form := List.ofFn c.1

theorem imbalance_eq_formsFlow {t : Nat} (c : Choices t) :
    imbalance c = formsFlow (3 * t) 2 (choiceForms c) := by
  rw [formsFlow_eq_fin_sum]
  funext v
  simp only [imbalance, Finset.sum_apply]
  let e : Fin (3 * t - 3) ≃ Fin (choiceForms c).length :=
    (Fin.castOrderIso (by simp [choiceForms])).toEquiv
  apply Fintype.sum_equiv e
  intro i
  have hev : (e i).val = i.val := rfl
  have hget : (choiceForms c).get (e i) = c.1 i := by
    simp only [choiceForms, List.get_ofFn]
    apply congrArg c.1
    exact Fin.ext hev
  rw [show classIndex i = i.val + 2 by rfl, hev, hget]
  simp [edgeFlow, vertexFlow, Nat.add_comm]

/-- Peeling the first and last forms of a contiguous retirement interval gives
the literal low/high pair plus the strictly inner interval. -/
theorem formsFlow_peel (n j : Nat) (low high : Form) (inner : List Form)
    (hlen : j + 1 + inner.length = highClass n j) :
    formsFlow n j (low :: (inner ++ [high])) =
      pairedFlow n j low high + formsFlow n (j + 1) inner := by
  simp only [formsFlow, formsFlow_append, List.length_singleton]
  rw [hlen]
  simp [formsFlow, pairedFlow]
  abel

/-- Every edge in the strictly inner interval misses the two nodes retired at
level `j`. -/
theorem formsFlow_future_zero (n j k : Nat) (xs : List Form)
    (hj : 3 ≤ j) (hjk : j < k) (hk : k + xs.length ≤ n - j + 1) :
    formsFlow n k xs ((j - 1 : Nat) : ZMod n) = 0 ∧
      formsFlow n k xs (-((j - 1 : Nat) : ZMod n)) = 0 := by
  induction xs generalizing k with
  | nil => simp [formsFlow]
  | cons f fs ih =>
      have he := edgeFlow_future_zero n j k f hj hjk (by simp at hk; omega)
      have ht := ih (k + 1) (by omega) (by simp at hk ⊢; omega)
      simp only [formsFlow]
      constructor <;> simp [he.1, he.2, ht.1, ht.2]

theorem evenPathChoices_imbalance (r : Nat) (hr : 1 ≤ r) {h : Half}
    (p : EvenPath h (3 * r - 3)) :
    imbalance (evenPathChoices r hr p) =
      boundaryFlow (3 * (2 * r)) (evenPathCharge p) := by
  rw [imbalance_eq_formsFlow]
  have hforms : choiceForms (evenPathChoices r hr p) = evenPathForms p := by
    apply List.ext_get
    · simp [choiceForms]
      omega
    · intro i hi hj
      simp [choiceForms, evenPathChoices]
      rfl
  rw [hforms, evenPathForms_flow r hr p, evenPathFlow_eq_boundary r hr p]

theorem oddPathChoices_imbalance (r : Nat) (hr : 1 ≤ r) {h : Half}
    (p : OddPath h (3 * r - 1)) :
    imbalance (oddPathChoices r hr p) =
      boundaryFlow (3 * (2 * r + 1)) (oddPathCharge p) := by
  rw [imbalance_eq_formsFlow]
  have hforms : choiceForms (oddPathChoices r hr p) = oddPathForms p := by
    apply List.ext_get
    · simp [choiceForms]
      omega
    · intro i hi hj
      simp [choiceForms, oddPathChoices]
      rfl
  rw [hforms, oddPathForms_flow r hr p, oddPathFlow_eq_boundary r hr p]

private theorem evenTailForms_injective (h : Half) :
    (m : Nat) -> (s : State) -> Function.Injective fun p : EvenTail h m s =>
      evenTailLowForms p ++ (evenTailHighForms p).reverse
  | 0, s => by
      intro p q _
      cases h <;> fin_cases s <;>
        simp only [EvenTail, EvenTerminalIndex] at p q <;>
        exact Subsingleton.elim p q
  | m + 1, s => by
      rintro ⟨i, p⟩ ⟨k, q⟩ heq
      simp only [evenTailLowForms, evenTailHighForms, List.reverse_cons,
        List.singleton_append, List.append_assoc] at heq
      have hc := List.cons.inj heq
      have hh : (stepValue (h := h) i).high = (stepValue (h := h) k).high := by
        have := congrArg List.getLast? hc.2
        simpa using this
      have hinj : Function.Injective fun x : StepIndex s =>
          ((stepValue (h := h) x).low, (stepValue (h := h) x).high) := by
        cases h <;> fin_cases s <;> decide
      have hik := hinj (Prod.ext hc.1 hh)
      subst k
      congr 1
      apply evenTailForms_injective h m (stepTarget i)
      apply List.append_cancel_right
      rw [List.append_assoc, List.append_assoc]
      exact hc.2

private theorem oddTailForms_injective (h : Half) :
    (m : Nat) -> (s : State) -> Function.Injective fun p : OddTail h m s =>
      oddTailLowForms p ++ (oddTailHighForms p).reverse
  | 0, s => by
      intro p q _
      cases h <;> fin_cases s <;>
        simp only [OddTail, OddTerminalIndex] at p q <;>
        exact Subsingleton.elim p q
  | m + 1, s => by
      rintro ⟨i, p⟩ ⟨k, q⟩ heq
      simp only [oddTailLowForms, oddTailHighForms, List.reverse_cons,
        List.singleton_append, List.append_assoc] at heq
      have hc := List.cons.inj heq
      have hh : (stepValue (h := h) i).high = (stepValue (h := h) k).high := by
        have := congrArg List.getLast? hc.2
        simpa using this
      have hinj : Function.Injective fun x : StepIndex s =>
          ((stepValue (h := h) x).low, (stepValue (h := h) x).high) := by
        cases h <;> fin_cases s <;> decide
      have hik := hinj (Prod.ext hc.1 hh)
      subst k
      congr 1
      apply oddTailForms_injective h m (stepTarget i)
      apply List.append_cancel_right
      rw [List.append_assoc, List.append_assoc]
      exact hc.2

theorem evenPathForms_injective (h : Half) (m : Nat) :
    Function.Injective (evenPathForms : EvenPath h m -> List Form) := by
  rintro ⟨i, p⟩ ⟨k, q⟩ heq
  simp only [evenPathForms] at heq
  have hc := List.cons.inj heq
  have hinj : Function.Injective fun x : StartIndex h => (startValue x).label := by
    cases h <;> decide
  have hik := hinj hc.1
  subst k
  congr 1
  exact evenTailForms_injective h m (startTarget i) hc.2

theorem oddPathForms_injective (h : Half) (m : Nat) :
    Function.Injective (oddPathForms : OddPath h m -> List Form) := by
  rintro ⟨i, p⟩ ⟨k, q⟩ heq
  simp only [oddPathForms] at heq
  have hc := List.cons.inj heq
  have hinj : Function.Injective fun x : StartIndex h => (startValue x).label := by
    cases h <;> decide
  have hik := hinj hc.1
  subst k
  congr 1
  exact oddTailForms_injective h m (startTarget i) hc.2

abbrev EvenZeroPaths (r : Nat) :=
  {p : EvenPath .positive (3 * r - 3) // evenPathCharge p = 0} ⊕
    {p : EvenPath .negative (3 * r - 3) // evenPathCharge p = 0}

abbrev OddZeroPaths (r : Nat) :=
  {p : OddPath .positive (3 * r - 1) // oddPathCharge p = 0} ⊕
    {p : OddPath .negative (3 * r - 1) // oddPathCharge p = 0}

def evenZeroPathChoices (r : Nat) (hr : 1 ≤ r) :
    EvenZeroPaths r -> {c : Choices (2 * r) // Balanced c}
  | .inl ⟨p, hp⟩ =>
      ⟨evenPathChoices r hr p, by
        intro v _
        rw [evenPathChoices_imbalance r hr p, hp]
        simp [boundaryFlow]⟩
  | .inr ⟨p, hp⟩ =>
      ⟨evenPathChoices r hr p, by
        intro v _
        rw [evenPathChoices_imbalance r hr p, hp]
        simp [boundaryFlow]⟩

def oddZeroPathChoices (r : Nat) (hr : 1 ≤ r) :
    OddZeroPaths r -> {c : Choices (2 * r + 1) // Balanced c}
  | .inl ⟨p, hp⟩ =>
      ⟨oddPathChoices r hr p, by
        intro v _
        rw [oddPathChoices_imbalance r hr p, hp]
        simp [boundaryFlow]⟩
  | .inr ⟨p, hp⟩ =>
      ⟨oddPathChoices r hr p, by
        intro v _
        rw [oddPathChoices_imbalance r hr p, hp]
        simp [boundaryFlow]⟩

theorem evenZeroPathChoices_injective (r : Nat) (hr : 1 ≤ r) :
    Function.Injective (evenZeroPathChoices r hr) := by
  have encode (h : Half) (p : EvenPath h (3 * r - 3)) :
      choiceForms (evenPathChoices r hr p) = evenPathForms p := by
    apply List.ext_get
    · simp [choiceForms]
      omega
    · intro i hi hj
      simp [choiceForms, evenPathChoices]
      rfl
  intro p q heq
  cases p with
  | inl p =>
      cases q with
      | inl q =>
          congr 1
          apply Subtype.ext
          apply evenPathForms_injective .positive _
          have hc := congrArg Subtype.val heq
          change evenPathChoices r hr p.1 = evenPathChoices r hr q.1 at hc
          rw [← encode .positive p.1, ← encode .positive q.1]
          exact congrArg choiceForms hc
      | inr q =>
          exfalso
          have hc := congrArg Subtype.val heq
          change evenPathChoices r hr p.1 = evenPathChoices r hr q.1 at hc
          have hf : evenPathForms p.1 = evenPathForms q.1 := by
            rw [← encode .positive p.1, ← encode .negative q.1]
            exact congrArg choiceForms hc
          rcases p with ⟨⟨i, p⟩, hp⟩
          rcases q with ⟨⟨k, q⟩, hq⟩
          simp only [evenPathForms, List.cons.injEq] at hf
          fin_cases i <;> fin_cases k <;>
            simp [startValue, starts, Form.II, Form.III, Form.IV, Form.V] at hf
  | inr p =>
      cases q with
      | inl q =>
          exfalso
          have hc := congrArg Subtype.val heq
          change evenPathChoices r hr p.1 = evenPathChoices r hr q.1 at hc
          have hf : evenPathForms p.1 = evenPathForms q.1 := by
            rw [← encode .negative p.1, ← encode .positive q.1]
            exact congrArg choiceForms hc
          rcases p with ⟨⟨i, p⟩, hp⟩
          rcases q with ⟨⟨k, q⟩, hq⟩
          simp only [evenPathForms, List.cons.injEq] at hf
          fin_cases i <;> fin_cases k <;>
            simp [startValue, starts, Form.II, Form.III, Form.IV, Form.V] at hf
      | inr q =>
          congr 1
          apply Subtype.ext
          apply evenPathForms_injective .negative _
          have hc := congrArg Subtype.val heq
          change evenPathChoices r hr p.1 = evenPathChoices r hr q.1 at hc
          rw [← encode .negative p.1, ← encode .negative q.1]
          exact congrArg choiceForms hc

theorem oddZeroPathChoices_injective (r : Nat) (hr : 1 ≤ r) :
    Function.Injective (oddZeroPathChoices r hr) := by
  have encode (h : Half) (p : OddPath h (3 * r - 1)) :
      choiceForms (oddPathChoices r hr p) = oddPathForms p := by
    apply List.ext_get
    · simp [choiceForms]
      omega
    · intro i hi hj
      simp [choiceForms, oddPathChoices]
      rfl
  intro p q heq
  cases p with
  | inl p =>
      cases q with
      | inl q =>
          congr 1
          apply Subtype.ext
          apply oddPathForms_injective .positive _
          have hc := congrArg Subtype.val heq
          change oddPathChoices r hr p.1 = oddPathChoices r hr q.1 at hc
          rw [← encode .positive p.1, ← encode .positive q.1]
          exact congrArg choiceForms hc
      | inr q =>
          exfalso
          have hc := congrArg Subtype.val heq
          change oddPathChoices r hr p.1 = oddPathChoices r hr q.1 at hc
          have hf : oddPathForms p.1 = oddPathForms q.1 := by
            rw [← encode .positive p.1, ← encode .negative q.1]
            exact congrArg choiceForms hc
          rcases p with ⟨⟨i, p⟩, hp⟩
          rcases q with ⟨⟨k, q⟩, hq⟩
          simp only [oddPathForms, List.cons.injEq] at hf
          fin_cases i <;> fin_cases k <;>
            simp [startValue, starts, Form.II, Form.III, Form.IV, Form.V] at hf
  | inr p =>
      cases q with
      | inl q =>
          exfalso
          have hc := congrArg Subtype.val heq
          change oddPathChoices r hr p.1 = oddPathChoices r hr q.1 at hc
          have hf : oddPathForms p.1 = oddPathForms q.1 := by
            rw [← encode .negative p.1, ← encode .positive q.1]
            exact congrArg choiceForms hc
          rcases p with ⟨⟨i, p⟩, hp⟩
          rcases q with ⟨⟨k, q⟩, hq⟩
          simp only [oddPathForms, List.cons.injEq] at hf
          fin_cases i <;> fin_cases k <;>
            simp [startValue, starts, Form.II, Form.III, Form.IV, Form.V] at hf
      | inr q =>
          congr 1
          apply Subtype.ext
          apply oddPathForms_injective .negative _
          have hc := congrArg Subtype.val heq
          change oddPathChoices r hr p.1 = oddPathChoices r hr q.1 at hc
          rw [← encode .negative p.1, ← encode .negative q.1]
          exact congrArg choiceForms hc

end D5.S3.Combinatorics.Zigzag
