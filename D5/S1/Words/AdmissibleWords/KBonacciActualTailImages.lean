/- GID: D5/S1/Words/AdmissibleWords/KBonacciActualTailImages
   generality: I
   mirror-B: D5/B/S1/Words/AdmissibleWords/KBonacciActualTailImages
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact terminal-one and trailing-zero images of actual admissible words. -/

import D5.S0.Tower.DBonacci.Substitution
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace D5.S1.Words.AdmissibleWords.KBonacciActualTailImages

open Finset
open D5.S0.Tower.DBonacci.Names D5.S0.Tower.DBonacci.Substitution
open D5.S0.Tower.DBonacci.Values

/-- Exact suffix images of the original scanner, with every zero occupying a position. -/
theorem actual_tail_zero_image_decomposition {C : Type*} [CommRing C]
    (x : C) (k : ℕ) (hk : 2 ≤ k) :
    let E := fun (m : ℕ) (w : Fin m → Bool) =>
      ∑ i : Fin m, if w i then x ^ i.val else 0
    let I := fun m => {y : C | ∃ w : Fin m → Bool, DBonacciAdmissible k m w ∧ E m w = y}
    let ExactTail := fun (n s : ℕ) (w : Fin n → Bool) =>
      s ≤ n ∧ (∀ i : Fin n, n - s ≤ i.val → w i = true) ∧
        (∀ i : Fin n, i.val + s + 1 = n → w i = false)
    let Zeros := fun (n z : ℕ) (w : Fin n → Bool) =>
      z ≤ n ∧ ∀ i : Fin n, n - z ≤ i.val → w i = false
    let T := fun n s => {y : C | ∃ w : Fin n → Bool,
      DBonacciAdmissible k n w ∧ ExactTail n s w ∧ E n w = y}
    let Z := fun n z => {y : C | ∃ w : Fin n → Bool,
      DBonacciAdmissible k n w ∧ Zeros n z w ∧ E n w = y}
    let S := fun s => ∑ j ∈ range s, x ^ j
    ∀ n s z : ℕ, s < k → 1 ≤ z →
      (n < s → T n s = ∅) ∧
      (n = s → T n s = {S s}) ∧
      (s + 1 ≤ n → T n s = (fun y => y + x ^ (n - s) * S s) '' I (n - s - 1)) ∧
      (n < z → Z n z = ∅) ∧
      (z ≤ n → Z n z = I (n - z)) := by
  classical
  dsimp only
  let E := fun (m : ℕ) (w : Fin m → Bool) =>
    ∑ i : Fin m, if w i then x ^ i.val else 0
  let I := fun m => {y : C | ∃ w : Fin m → Bool, DBonacciAdmissible k m w ∧ E m w = y}
  let ExactTail := fun (n s : ℕ) (w : Fin n → Bool) =>
    s ≤ n ∧ (∀ i : Fin n, n - s ≤ i.val → w i = true) ∧
      (∀ i : Fin n, i.val + s + 1 = n → w i = false)
  let Zeros := fun (n z : ℕ) (w : Fin n → Bool) =>
    z ≤ n ∧ ∀ i : Fin n, n - z ≤ i.val → w i = false
  let T := fun n s => {y : C | ∃ w : Fin n → Bool,
    DBonacciAdmissible k n w ∧ ExactTail n s w ∧ E n w = y}
  let Z := fun n z => {y : C | ∃ w : Fin n → Bool,
    DBonacciAdmissible k n w ∧ Zeros n z w ∧ E n w = y}
  let S := fun s => ∑ j ∈ range s, x ^ j
  change ∀ n s z : ℕ, s < k → 1 ≤ z →
    (n < s → T n s = ∅) ∧ (n = s → T n s = {S s}) ∧
    (s + 1 ≤ n → T n s = (fun y => y + x ^ (n - s) * S s) '' I (n - s - 1)) ∧
    (n < z → Z n z = ∅) ∧ (z ≤ n → Z n z = I (n - z))
  have hshort : ∀ m (w : Fin m → Bool), m < k → DBonacciAdmissible k m w := by
    intro m w hm
    cases k with
    | zero => omega
    | succ M => exact runAdmissible_eq_true_of_length_le M M m w (by omega) le_rfl
  have hscan : ∀ (M m fuel t : ℕ) (f : ℕ → Bool), f m = false →
      runAdmissible M fuel (m + (t + 1)) (fun i => f i.val) =
        (runAdmissible M fuel m (fun i => f i.val) &&
          runAdmissible M M t (fun i => f (m + 1 + i.val))) := by
    intro M m
    induction m with
    | zero =>
      intro fuel t f hf
      simp only [Nat.zero_add]
      have he := congrArg
        (fun n => runAdmissible M M n (fun i => f (i.val + 1))) (Nat.zero_add t)
      cases fuel <;>
        simp only [runAdmissible, Fin.val_zero, hf, Bool.false_eq_true,
          ↓reduceIte, Bool.true_and, Nat.add_comm] <;> exact he
    | succ m ih =>
      intro fuel t f hf
      have hh : (fun j => f (j + 1)) m = false := hf
      have htail : ∀ l, Fin.tail (fun i : Fin (l + 1) => f i.val) =
          (fun i : Fin l => f (i.val + 1)) := fun _ => rfl
      rw [show m + 1 + (t + 1) = (m + (t + 1)) + 1 by omega]
      cases fuel with
      | zero =>
        cases hhead : f 0 with
        | true => simp [runAdmissible, hhead]
        | false =>
          simp only [runAdmissible, Fin.val_zero, hhead, Bool.false_eq_true,
            ↓reduceIte]
          simpa only [htail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih M t (fun j => f (j + 1)) hh
      | succ fuel =>
        cases hhead : f 0 with
        | true =>
          simp only [runAdmissible, Fin.val_zero, hhead, ↓reduceIte]
          simpa only [htail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih fuel t (fun j => f (j + 1)) hh
        | false =>
          simp only [runAdmissible, Fin.val_zero, hhead, Bool.false_eq_true, ↓reduceIte]
          simpa only [htail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih M t (fun j => f (j + 1)) hh
  have hjoin : ∀ (M fuel m t : ℕ) (v : Fin m → Bool) (u : Fin t → Bool),
      runAdmissible M fuel (m + (t + 1)) (Fin.append v (Fin.cons false u)) =
        (runAdmissible M fuel m v && runAdmissible M M t u) := by
    intro M fuel m t v u
    let w := Fin.append v (Fin.cons false u)
    let f : ℕ → Bool := fun j => if hj : j < m + (t + 1) then w ⟨j, hj⟩ else false
    have hfull : (fun i : Fin (m + (t + 1)) => f i.val) = w := by
      funext i; simp [f, i.isLt]
    have hpre : (fun i : Fin m => f i.val) = v := by
      funext i
      have hi : i.val < m + (t + 1) := by omega
      simp only [f, dif_pos hi]
      exact Fin.append_left v (Fin.cons false u) i
    have hsuf : (fun i : Fin t => f (m + 1 + i.val)) = u := by
      funext i
      have hi : m + 1 + i.val < m + (t + 1) := by have := i.isLt; omega
      simp only [f, dif_pos hi]
      have he : (⟨m + 1 + i.val, hi⟩ : Fin (m + (t + 1))) = Fin.natAdd m i.succ := by
        apply Fin.ext; simp; omega
      rw [he]
      exact (Fin.append_right v (Fin.cons false u) i.succ).trans (Fin.cons_succ ..)
    have hm : f m = false := by
      have hi : m < m + (t + 1) := by omega
      simp only [f, dif_pos hi]
      have he : (⟨m, hi⟩ : Fin (m + (t + 1))) = Fin.natAdd m 0 := by
        apply Fin.ext; simp
      rw [he]
      exact (Fin.append_right v (Fin.cons false u) 0).trans (Fin.cons_zero ..)
    have he := hscan M m fuel t f hm
    simpa only [hfull, hpre, hsuf] using he
  have hprefix : ∀ (m t : ℕ) (w : Fin (m + t) → Bool),
      DBonacciAdmissible k (m + t) w →
        DBonacciAdmissible k m (fun i => w ⟨i.val, by have := i.isLt; omega⟩) := by
    intro m t
    induction t with
    | zero => intro w hw; simpa using hw
    | succ t ih =>
      intro w hw
      have hp := ih (Fin.init w) (admissible_init k (m + t) w hw)
      exact hp
  have heval : ∀ (m t : ℕ) (v : Fin m → Bool) (u : Fin t → Bool),
      E (m + t) (Fin.append v u) = E m v + x ^ m * E t u := by
    intro m t v u
    dsimp only [E]
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd]
    rw [mul_sum]
    congr 1
    apply sum_congr rfl
    intro i _
    cases u i <;> simp [pow_add]
  have hcons : ∀ t (u : Fin t → Bool), E (t + 1) (Fin.cons false u) = x * E t u := by
    intro t u
    dsimp only [E]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, ↓reduceIte, zero_add]
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    cases u i <;> simp [pow_succ, mul_comm]
  have hones : ∀ s, E s (fun _ => true) = S s := by
    intro s; simp only [E, S, ↓reduceIte, Fin.sum_univ_eq_sum_range]
  have hfalse : ∀ s, E s (fun _ => false) = 0 := by intro s; simp [E]
  have htail : ∀ m s, s < k →
      T (m + (s + 1)) s = (fun y => y + x ^ (m + 1) * S s) '' I m := by
    intro m s hs
    ext y
    constructor
    · rintro ⟨w, hw, ht, he⟩
      let v : Fin m → Bool := fun i => w (Fin.castAdd (s + 1) i)
      have hv : DBonacciAdmissible k m v := hprefix m (s + 1) w hw
      have hword : w = Fin.append v (Fin.cons false (fun _ : Fin s => true)) := by
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp [v]
        · refine Fin.cases ?_ (fun j => ?_) j
          · rw [Fin.append_right, Fin.cons_zero]
            exact ht.2.2 _ (by simp; omega)
          · rw [Fin.append_right, Fin.cons_succ]
            exact ht.2.1 _ (by simp; omega)
      refine ⟨E m v, ⟨v, hv, rfl⟩, ?_⟩
      rw [← he, hword, heval, hcons, hones]
      simp [pow_succ, mul_assoc]
    · rintro ⟨b, ⟨v, hv, rfl⟩, rfl⟩
      let w := Fin.append v (Fin.cons false (fun _ : Fin s => true))
      have hw : DBonacciAdmissible k (m + (s + 1)) w := by
        cases k with
        | zero => omega
        | succ M =>
          change runAdmissible M M _ w = true
          rw [hjoin]
          have hu := runAdmissible_eq_true_of_length_le M M s (fun _ => true) (by omega) le_rfl
          change runAdmissible M M m v = true at hv
          simp only [hv, hu, Bool.and_self]
      refine ⟨w, hw, ⟨by omega, ?_, ?_⟩, ?_⟩
      · intro i hi
        have hp : m + 1 ≤ i.val := by omega
        let j : Fin s := ⟨i.val - (m + 1), by have := i.isLt; omega⟩
        have he : i = Fin.natAdd m j.succ := by apply Fin.ext; simp [j]; omega
        rw [he]
        simp [w]
      · intro i hi
        have he : i = Fin.natAdd m 0 := by apply Fin.ext; simp; omega
        rw [he]
        simp [w]
      · dsimp only [w]
        rw [heval, hcons, hones]
        simp [pow_succ, mul_assoc]
  have hzero : ∀ m t, Z (m + (t + 1)) (t + 1) = I m := by
    intro m t
    ext y
    constructor
    · rintro ⟨w, hw, hz, he⟩
      let v : Fin m → Bool := fun i => w (Fin.castAdd (t + 1) i)
      have hv : DBonacciAdmissible k m v := hprefix m (t + 1) w hw
      have hword : w = Fin.append v (fun _ : Fin (t + 1) => false) := by
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp [v]
        · rw [Fin.append_right]
          exact hz.2 _ (by simp)
      refine ⟨v, hv, ?_⟩
      rw [← he, hword, heval, hfalse, mul_zero, add_zero]
    · rintro ⟨v, hv, rfl⟩
      let w := Fin.append v (Fin.cons false (fun _ : Fin t => false))
      have hall : Fin.cons false (fun _ : Fin t => false) = (fun _ => false) := by
        funext i; exact Fin.cases rfl (fun _ => rfl) i
      have hw : DBonacciAdmissible k (m + (t + 1)) w := by
        cases t with
        | zero =>
          simpa only [w, Fin.append_right_eq_snoc, Fin.cons_zero] using
            admissible_snoc_false k m v hv
        | succ t =>
          cases k with
          | zero => omega
          | succ M =>
            change runAdmissible M M _ w = true
            rw [hjoin, runAdmissible_all_false]
            change runAdmissible M M m v = true at hv
            simp only [hv, Bool.and_self]
      refine ⟨w, hw, ⟨by omega, ?_⟩, ?_⟩
      · intro i hi
        let j : Fin (t + 1) := ⟨i.val - m, by have := i.isLt; omega⟩
        have he : i = Fin.natAdd m j := by apply Fin.ext; simp [j]; omega
        rw [he]
        simp only [w, Fin.append_right, hall]
      · dsimp only [w]
        rw [heval, hall, hfalse, mul_zero, add_zero]
  intro n s z hs hz
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hn
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro y ⟨w, hw, ht, he⟩
    have := ht.1
    omega
  · intro hn
    subst n
    ext y
    constructor
    · rintro ⟨w, hw, ht, he⟩
      have hword : w = (fun _ => true) := by
        funext i; exact ht.2.1 i (by omega)
      simp only [Set.mem_singleton_iff, ← he, hword, hones]
    · intro hy
      have he : y = S s := Set.mem_singleton_iff.mp hy
      refine ⟨fun _ => true, hshort s _ hs, ⟨le_rfl, ?_, ?_⟩, ?_⟩
      · intro i hi; rfl
      · intro i hi; have := i.isLt; omega
      · rw [hones, he]
  · intro hn
    let m := n - s - 1
    have hlen : n = m + (s + 1) := by dsimp [m]; omega
    have he := htail m s hs
    simpa only [hlen, show m + (s + 1) - s = m + 1 by omega,
      show m + 1 - 1 = m by omega] using he
  · intro hn
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro y ⟨w, hw, ht, he⟩
    have := ht.1
    omega
  · intro hn
    obtain ⟨t, rfl⟩ : ∃ t, z = t + 1 := ⟨z - 1, by omega⟩
    let m := n - (t + 1)
    have hlen : n = m + (t + 1) := by dsimp [m]; omega
    simpa only [hlen, Nat.add_sub_cancel] using hzero m t

end D5.S1.Words.AdmissibleWords.KBonacciActualTailImages
