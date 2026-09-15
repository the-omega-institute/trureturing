/- GID: D5/S0/Rewriting/BoundedSuccessorObservationCount
   generality: G
   mirror-B: D5/B/S0/Rewriting/BoundedSuccessorObservationCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded successor observations are counted by their first visible failure times. -/

import Mathlib.Logic.Function.Iterate
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

namespace D5.S0.Rewriting.BoundedSuccessorObservationCount

/-- The strict successor on the finite interval, with an absorbing failure state. -/
def strictSuccessor (B : ℕ) : Option (Fin (B + 1)) → Option (Fin (B + 1))
  | none => none
  | some n => if hn : n.val < B then some ⟨n.val + 1, by omega⟩ else none

/-- The state reached after the specified number of strict successor steps. -/
def trajectory (B : ℕ) (n : Fin (B + 1)) (t : ℕ) : Option (Fin (B + 1)) :=
  (strictSuccessor B)^[t] (some n)

/-- Each start first fails at time B minus n plus one. Constant successful readouts give
exactly the minimum of B plus one and h plus one observation classes through time h;
arbitrary readouts give between this minimum and B plus one classes. First failure times
and complete observed futures distinguish all starts. -/
theorem bounded_successor_observation_count (B h : ℕ) {A : Type*} (q : Fin (B + 1) → A) :
    let Q := fun n : Fin (B + 1) => fun t : Fin (h + 1) =>
      Option.map q (trajectory B n t.val)
    (∀ (n : Fin (B + 1)) (t : ℕ), trajectory B n t =
      if ht : n.val + t ≤ B then some ⟨n.val + t, by omega⟩ else none) ∧
    (∀ n : Fin (B + 1), trajectory B n (B - n.val + 1) = none ∧
      ∀ t < B - n.val + 1, (trajectory B n t).isSome = true) ∧
    ((∀ n m, q n = q m) → Nat.card (Set.range Q) = min (B + 1) (h + 1)) ∧
    (min (B + 1) (h + 1) ≤ Nat.card (Set.range Q) ∧
      Nat.card (Set.range Q) ≤ B + 1) ∧
    Function.Injective (fun n : Fin (B + 1) => B - n.val + 1) ∧
    Function.Injective (fun n : Fin (B + 1) => fun t : ℕ =>
      Option.map q (trajectory B n t)) := by
  classical
  dsimp only
  have htraj : ∀ (n : Fin (B + 1)) (t : ℕ), trajectory B n t =
      if ht : n.val + t ≤ B then some ⟨n.val + t, by omega⟩ else none := by
    intro n t
    induction t with
    | zero => simp [trajectory, show n.val ≤ B by omega]
    | succ t ih =>
        rw [trajectory, Function.iterate_succ_apply']
        change strictSuccessor B (trajectory B n t) = _
        rw [ih]
        by_cases ht : n.val + t ≤ B
        · rw [dif_pos ht]
          by_cases hlt : n.val + t < B
          · simp [strictSuccessor, hlt, show n.val + (t + 1) ≤ B by omega,
              Nat.add_assoc]
          · simp [strictSuccessor, hlt, show ¬ n.val + (t + 1) ≤ B by omega]
        · simp [ht, strictSuccessor, show ¬ n.val + (t + 1) ≤ B by omega]
  let Q := fun n : Fin (B + 1) => fun t : Fin (h + 1) =>
    Option.map q (trajectory B n t.val)
  have hsuccess (n : Fin (B + 1)) (t : ℕ) :
      (Option.map q (trajectory B n t)).isSome = true ↔ t ≤ B - n.val := by
    rw [htraj]
    by_cases ht : n.val + t ≤ B
    · simp [ht, show t ≤ B - n.val by omega]
    · simp [ht, show ¬ t ≤ B - n.val by have := n.isLt; omega]
  have hfirst : ∀ n : Fin (B + 1), trajectory B n (B - n.val + 1) = none ∧
      ∀ t < B - n.val + 1, (trajectory B n t).isSome = true := by
    intro n
    constructor
    · rw [htraj, dif_neg (by have := n.isLt; omega)]
    · intro t ht
      rw [htraj, dif_pos (by have := n.isLt; omega)]
      rfl
  have hsep (n m : Fin (B + 1)) (t : Fin (h + 1))
      (hn : t.val ≤ B - n.val) (hm : B - m.val < t.val) : Q n ≠ Q m := by
    intro heq
    have he := congrArg Option.isSome (congrFun heq t)
    have hn' := (hsuccess n t.val).2 hn
    have hm' := (hsuccess m t.val).1 (he.symm.trans hn')
    omega
  let rep : Fin (min (B + 1) (h + 1)) → Fin (B + 1) :=
    fun i => ⟨B - i.val, by omega⟩
  have hr (i : Fin (min (B + 1) (h + 1))) : B - (rep i).val = i.val := by
    dsimp [rep]
    have := i.isLt
    omega
  have hinj : Function.Injective (fun i => Q (rep i)) := by
    intro i j heq
    apply Fin.ext
    rcases lt_trichotomy i.val j.val with hij | hij | hij
    · have ht : i.val + 1 < h + 1 := by have := j.isLt; omega
      exact False.elim ((hsep (rep j) (rep i) ⟨i.val + 1, ht⟩
        (by dsimp only; rw [hr]; omega) (by simp only [hr]; omega)) heq.symm)
    · exact hij
    · have ht : j.val + 1 < h + 1 := by have := i.isLt; omega
      exact False.elim ((hsep (rep i) (rep j) ⟨j.val + 1, ht⟩
        (by dsimp only; rw [hr]; omega) (by simp only [hr]; omega)) heq)
  let : Finite (Set.range Q) :=
    Finite.of_surjective (Set.rangeFactorization Q) Set.rangeFactorization_surjective
  have hlower : min (B + 1) (h + 1) ≤ Nat.card (Set.range Q) := by
    let f : Fin (min (B + 1) (h + 1)) → Set.range Q :=
      fun i => ⟨Q (rep i), ⟨rep i, rfl⟩⟩
    have hf : Function.Injective f := by
      intro i j heq
      exact hinj (congrArg Subtype.val heq)
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf
  have hupper : Nat.card (Set.range Q) ≤ B + 1 := by
    simpa only [Nat.card_fin] using
      Nat.card_le_card_of_surjective (Set.rangeFactorization Q) Set.rangeFactorization_surjective
  have hconst (hq : ∀ n m, q n = q m) :
      Nat.card (Set.range Q) = min (B + 1) (h + 1) := by
    have hcover : ∀ n, ∃ i, Q (rep i) = Q n := by
      intro n
      let i : Fin (min (B + 1) (h + 1)) :=
        ⟨min (B - n.val) h, by have := n.isLt; omega⟩
      refine ⟨i, ?_⟩
      funext t
      have hcut : (rep i).val + t.val ≤ B ↔ n.val + t.val ≤ B := by
        have hi := hr i
        have ht := t.isLt
        have hn := n.isLt
        have hp := (rep i).isLt
        change B - (rep i).val = min (B - n.val) h at hi
        omega
      dsimp only [Q]
      rw [htraj, htraj]
      by_cases ht : n.val + t.val ≤ B
      · rw [dif_pos (hcut.mpr ht), dif_pos ht]
        simp only [Option.map_some]
        exact congrArg some (hq _ _)
      · rw [dif_neg (mt hcut.mp ht), dif_neg ht]
    have heq : Set.range Q = Set.range (fun i => Q (rep i)) := by
      ext y
      constructor
      · rintro ⟨n, rfl⟩
        exact hcover n
      · rintro ⟨i, rfl⟩
        exact ⟨rep i, rfl⟩
    rw [heq, Nat.card_range_of_injective hinj, Nat.card_fin]
  have htau : Function.Injective (fun n : Fin (B + 1) => B - n.val + 1) := by
    intro n m heq
    change B - n.val + 1 = B - m.val + 1 at heq
    apply Fin.ext
    have := n.isLt
    have := m.isLt
    omega
  have hfuture : Function.Injective (fun n : Fin (B + 1) => fun t : ℕ =>
      Option.map q (trajectory B n t)) := by
    intro n m heq
    apply htau
    have horder : ∀ a b : Fin (B + 1),
        (∀ t, Option.map q (trajectory B a t) = Option.map q (trajectory B b t)) →
        B - a.val ≤ B - b.val := by
      intro a b hab
      by_contra hlt
      have ha := (hsuccess a (B - b.val + 1)).2 (by omega)
      have he := congrArg Option.isSome (hab (B - b.val + 1))
      have hb := (hsuccess b (B - b.val + 1)).1 (he.symm.trans ha)
      omega
    have hnm := horder n m (congrFun heq)
    have hmn := horder m n (congrFun heq.symm)
    change B - n.val + 1 = B - m.val + 1
    omega
  exact ⟨htraj, hfirst, hconst, ⟨hlower, hupper⟩, htau, hfuture⟩

#print axioms bounded_successor_observation_count

end D5.S0.Rewriting.BoundedSuccessorObservationCount
