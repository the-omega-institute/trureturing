/- GID: D5/S0/Automata/FernauRystsovIntermediateReset
   generality: I
   mirror-B: D5/B/S0/Automata/FernauRystsovIntermediateReset
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Realizes every admissible finite reset threshold for a shared-letter DFA product. -/

import Mathlib.Computability.DFA
import OmegaBuild.Commands

compile_only_with_mathlib

/-! # Intermediate reset thresholds for products of deterministic automata -/

set_option autoImplicit false

namespace D5.S0.Automata.FernauRystsovIntermediateReset

/-- A singleton-image reset witness of observed length n, minimal among all reset words. -/
def Threshold (length : List Bool → ℕ) {σ : Type*} (A : DFA Bool σ) (n : ℕ) : Prop :=
  ∃ w : List Bool, length w = n ∧
    (∃ q, (fun p => A.evalFrom p w) '' Set.univ = {q}) ∧
    ∀ v : List Bool, (∃ q, (fun p => A.evalFrom p v) '' Set.univ = {q}) → n ≤ length v

/-- Advance one position if and only if the current state is below the cap. -/
private def advance {n : ℕ} (cap i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨max i.val (min (i.val + 1) cap.val), by
    have hi := i.isLt
    have hc := cap.isLt
    omega⟩

/-- First chain: a advances towards r, b advances only below t. -/
private def first (r t : ℕ) (htr : t ≤ r) : DFA Bool (Fin (r + 1)) where
  step i letter := if letter then advance ⟨t, by omega⟩ i else advance (Fin.last r) i
  start := 0
  accept := ∅

/-- Second chain: a fixes each state, b advances towards s. -/
private def second (s : ℕ) : DFA Bool (Fin (s + 1)) where
  step j letter := if letter then advance (Fin.last s) j else j
  start := 0
  accept := ∅

private theorem eval_replicate_advance {n : ℕ} (A : DFA Bool (Fin (n + 1)))
    (letter : Bool) (cap : Fin (n + 1))
    (hstep : ∀ i, A.step i letter = advance cap i)
    (k : ℕ) (i : Fin (n + 1)) :
    (A.evalFrom i (List.replicate k letter)).val = max i.val (min (i.val + k) cap.val) := by
  induction k generalizing i with
  | zero =>
      simp only [List.replicate_zero, DFA.evalFrom_nil, Nat.add_zero]
      omega
  | succ k ih =>
      rw [List.replicate_succ, DFA.evalFrom_cons, hstep, ih]
      simp only [advance]
      omega

private theorem first_a_eval (r t : ℕ) (htr : t ≤ r) (k : ℕ) (i : Fin (r + 1)) :
    ((first r t htr).evalFrom i (List.replicate k false)).val = min (i.val + k) r := by
  have h := eval_replicate_advance (first r t htr) false (Fin.last r) (fun _ => rfl) k i
  change _ = max i.val (min (i.val + k) r) at h
  have hi := i.isLt
  omega

private theorem first_b_eval (r t : ℕ) (htr : t ≤ r) (k : ℕ) (i : Fin (r + 1)) :
    ((first r t htr).evalFrom i (List.replicate k true)).val = max i.val (min (i.val + k) t) :=
  eval_replicate_advance (first r t htr) true ⟨t, by omega⟩ (fun _ => rfl) k i

private theorem second_b_eval (s k : ℕ) (j : Fin (s + 1)) :
    ((second s).evalFrom j (List.replicate k true)).val = min (j.val + k) s := by
  have h := eval_replicate_advance (second s) true (Fin.last s) (fun _ => rfl) k j
  change _ = max j.val (min (j.val + k) s) at h
  have hj := j.isLt
  omega

private theorem second_a_eval (s k : ℕ) (j : Fin (s + 1)) :
    (second s).evalFrom j (List.replicate k false) = j := by
  change List.foldl (second s).step j (List.replicate k false) = j
  have hmap : (List.replicate k false).map (fun _ : Bool => false) =
      List.replicate k false := List.map_replicate
  rw [← hmap, List.foldl_map]
  exact List.foldl_fixed (List.replicate k false)

private theorem first_top_fixed (r t : ℕ) (htr : t ≤ r) (letter : Bool) :
    (first r t htr).step (Fin.last r) letter = Fin.last r := by
  apply Fin.ext
  cases letter <;> simp [first, advance, Fin.val_last, htr]

private theorem second_top_fixed (s : ℕ) (letter : Bool) :
    (second s).step (Fin.last s) letter = Fin.last s := by
  apply Fin.ext
  cases letter <;> simp [second, advance, Fin.val_last]

private theorem first_step_le (r t : ℕ) (htr : t ≤ r) (i : Fin (r + 1)) (letter : Bool) :
    ((first r t htr).step i letter).val ≤ i.val + 1 := by
  cases letter <;> simp only [first, Bool.false_eq_true, ite_false, ite_true, advance] <;> omega

private theorem second_step_le (s : ℕ) (j : Fin (s + 1)) (letter : Bool) :
    ((second s).step j letter).val ≤ j.val + 1 := by
  cases letter <;> simp only [second, Bool.false_eq_true, ite_false, ite_true, advance] <;> omega

/-- The part of the first chain above t plus the full second coordinate. -/
private def potential {r s : ℕ} (t : ℕ) (p : Fin (r + 1) × Fin (s + 1)) : ℕ :=
  (p.1.val - t) + p.2.val

/-- Each shared letter can raise the product potential by at most one. -/
private theorem potential_step_le (r s t : ℕ) (htr : t ≤ r)
    (p : Fin (r + 1) × Fin (s + 1)) (letter : Bool) :
    potential t (((first r t htr).inter (second s)).step p letter) ≤ potential t p + 1 := by
  rcases p with ⟨i, j⟩
  cases letter <;>
    simp only [potential, DFA.inter, first, second, Bool.false_eq_true, ite_false, ite_true,
      advance, Fin.val_last] <;> omega

private theorem potential_eval_le {α σ : Type*} (A : DFA α σ) (P : σ → ℕ)
    (hstep : ∀ p letter, P (A.step p letter) ≤ P p + 1) (p : σ) (w : List α) :
    P (A.evalFrom p w) ≤ P p + w.length := by
  induction w generalizing p with
  | nil => simp
  | cons letter w ih =>
      rw [DFA.evalFrom_cons, List.length_cons]
      have h := ih (A.step p letter)
      have hs := hstep p letter
      omega

private theorem threshold_of_fixed {σ : Type*} (A : DFA Bool σ) (P : σ → ℕ)
    (hstep : ∀ p letter, P (A.step p letter) ≤ P p + 1)
    (bottom top : σ) (hfixed : ∀ letter, A.step top letter = top)
    (w : List Bool) (hw : ∀ p, A.evalFrom p w = top)
    (hlen : w.length = P top - P bottom) : Threshold List.length A w.length := by
  let : Nonempty σ := ⟨bottom⟩
  refine ⟨w, rfl, ⟨top, ?_⟩, ?_⟩
  · simpa only [Set.image_univ, Set.range_eq_singleton_iff] using hw
  · rintro v ⟨q, hq⟩
    simp only [Set.image_univ, Set.range_eq_singleton_iff] at hq
    have top_fixed : A.evalFrom top v = top := List.foldl_fixed' hfixed v
    have reach := (hq bottom).trans ((hq top).symm.trans top_fixed)
    have bound := potential_eval_le A P hstep bottom v
    rw [reach] at bound
    omega

private theorem first_threshold (r t : ℕ) (htr : t ≤ r) : Threshold List.length (first r t htr) r := by
  simpa only [List.length_replicate] using
    threshold_of_fixed (first r t htr) Fin.val (first_step_le r t htr)
      0 (Fin.last r) (first_top_fixed r t htr) (List.replicate r false)
      (fun p => Fin.ext (by rw [first_a_eval, Fin.val_last]; omega)) (by simp)

private theorem second_threshold (s : ℕ) : Threshold List.length (second s) s := by
  simpa only [List.length_replicate] using
    threshold_of_fixed (second s) Fin.val (second_step_le s)
      0 (Fin.last s) (second_top_fixed s) (List.replicate s true)
      (fun p => Fin.ext (by rw [second_b_eval, Fin.val_last]; omega)) (by simp)

private theorem product_threshold (r s t : ℕ) (htr : t ≤ r) (hts : t ≤ s) :
    Threshold List.length ((first r t htr).inter (second s)) (s + (r - t)) := by
  let A := first r t htr
  let B := second s
  let w := List.replicate s true ++ List.replicate (r - t) false
  have reach (p : Fin (r + 1) × Fin (s + 1)) :
      (A.inter B).evalFrom p w = (Fin.last r, Fin.last s) := by
    obtain ⟨i, j⟩ := p
    change List.foldl (A.inter B).step (i, j) w = _
    rw [List.foldl_hom₂ w Prod.mk A.step B.step (A.inter B).step i j (fun _ _ _ => rfl)]
    change (A.evalFrom i w, B.evalFrom j w) = _
    apply Prod.ext <;> apply Fin.ext
    · change (A.evalFrom i w).val = r
      rw [DFA.evalFrom_of_append, first_a_eval, first_b_eval]
      omega
    · change (B.evalFrom j w).val = s
      rw [DFA.evalFrom_of_append, second_a_eval, second_b_eval]
      omega
  have h := threshold_of_fixed (A.inter B) (potential t) (potential_step_le r s t htr)
    (0, 0) (Fin.last r, Fin.last s)
    (fun letter => Prod.ext (first_top_fixed r t htr letter) (second_top_fixed s letter))
    w reach (by simp [w, potential, Nat.add_comm])
  simpa only [w, List.length_append, List.length_replicate] using h

/-- Every integer between the maximum and sum of the factor thresholds occurs as
the threshold of a synchronous product over the shared two-letter alphabet. -/
theorem result (r s m : ℕ) (hlo : max r s ≤ m) (hhi : m ≤ r + s) :
    let length : List Bool → ℕ := List.length
    ∃ (A : DFA Bool (Fin (r + 1))) (B : DFA Bool (Fin (s + 1))),
      Threshold length A r ∧ Threshold length B s ∧ Threshold length (A.inter B) m := by
  let t := r + s - m
  have htr : t ≤ r := by dsimp [t]; omega
  have hts : t ≤ s := by dsimp [t]; omega
  have hlen : s + (r - t) = m := by dsimp [t]; omega
  exact ⟨first r t htr, second s, first_threshold r t htr, second_threshold s,
    hlen ▸ product_threshold r s t htr hts⟩

end D5.S0.Automata.FernauRystsovIntermediateReset
