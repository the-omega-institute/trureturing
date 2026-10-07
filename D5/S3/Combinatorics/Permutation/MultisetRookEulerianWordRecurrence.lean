/- GID: D5/S3/Combinatorics/Permutation/MultisetRookEulerianWordRecurrence
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/MultisetRookEulerianWordRecurrence
   mirror-E: none(waiver:exact-finite-certificate)
   anchors: []
   utility: none
   digest: The original strict-ascent word sum equals the residual-content recurrence. -/

import D5.S3.Combinatorics.Permutation.MultisetRookEulerianInterlacingRefutation
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.List.Permutation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.Permutation.MultisetRookEulerianWordRecurrence

open Polynomial
open D5.S3.Combinatorics.Permutation.MultisetRookEulerianInterlacingRefutation

def fits : List ℕ → List ℕ → Bool
  | [], [] => true
  | b :: bs, a :: ws => decide (0 < a ∧ a ≤ b) && fits bs ws
  | _, _ => false

def boundedWords (bounds letters : List ℕ) : Finset (List ℕ) :=
  letters.permutations'.toFinset.filter (fun w => fits bounds w)

theorem mem_boundedWords (bounds letters w : List ℕ) :
    w ∈ boundedWords bounds letters ↔ w.Perm letters ∧ fits bounds w = true := by
  simp [boundedWords]

theorem fits_eq_true_iff (bounds w : List ℕ) :
    fits bounds w = true ↔ w.length = bounds.length ∧
      ∀ i : ℕ, i < bounds.length → 0 < w.getD i 0 ∧ w.getD i 0 ≤ bounds.getD i 0 := by
  induction bounds generalizing w with
  | nil => cases w <;> simp [fits]
  | cons b bs ih =>
    cases w with
    | nil => simp [fits]
    | cons a ws =>
      simp only [fits, Bool.and_eq_true, decide_eq_true_eq, ih,
        List.length_cons, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨hab, hl, hf⟩
        refine ⟨hl, ?_⟩
        intro i hi
        cases i with
        | zero => simpa [List.getD] using hab
        | succ i => simpa [List.getD] using hf i (Nat.lt_of_succ_lt_succ hi)
      · rintro ⟨hl, hf⟩
        refine ⟨?_, hl, ?_⟩
        · simpa [List.getD] using hf 0 (Nat.zero_lt_succ _)
        · intro i hi
          simpa [List.getD] using hf (i + 1) (Nat.succ_lt_succ hi)


theorem boundedWords_cons (b : ℕ) (bs letters : List ℕ) :
    boundedWords (b :: bs) letters =
      (letters.toFinset.filter (fun a => 0 < a ∧ a ≤ b)).biUnion
        (fun a => (boundedWords bs (letters.erase a)).image (List.cons a)) := by
  ext w
  rw [mem_boundedWords]
  simp only [Finset.mem_biUnion, Finset.mem_filter, List.mem_toFinset,
    Finset.mem_image]
  constructor
  · rintro ⟨hp, hf⟩
    cases w with
    | nil => simp [fits] at hf
    | cons a w =>
      have ha : a ∈ letters := hp.mem_iff.mp (by simp)
      have hf' : (0 < a ∧ a ≤ b) ∧ fits bs w = true := by simpa [fits] using hf
      refine ⟨a, ⟨ha, hf'.1⟩, w, ?_, rfl⟩
      rw [mem_boundedWords]
      exact ⟨by simpa using hp.erase a, hf'.2⟩
  · rintro ⟨a, ⟨ha, hab⟩, v, hv, rfl⟩
    rw [mem_boundedWords] at hv
    refine ⟨?_, by simpa [fits] using And.intro hab hv.2⟩
    exact (hv.1.cons a).trans (List.perm_cons_erase ha).symm

def sourceLetters {k : ℕ} (α : Fin k → ℕ) : List ℕ :=
  (List.finRange k).flatMap (fun c => List.replicate (α c) (c.val + 1))

theorem length_sourceLetters {k : ℕ} (α : Fin k → ℕ) :
    (sourceLetters α).length = ∑ c, α c := by
  simp [sourceLetters, List.length_flatMap, List.finRange, List.map_ofFn, List.sum_ofFn]

theorem W_eq_boundedWords {n k : ℕ} (lam : Fin n → ℕ) (α : Fin k → ℕ)
    (hc : (∑ c, α c) = n) :
    W lam α = boundedWords (List.ofFn lam) (sourceLetters α) := by
  ext w
  rw [mem_boundedWords, fits_eq_true_iff]
  simp only [W, sourceLetters, Finset.mem_filter, List.mem_toFinset,
    List.mem_permutations', List.length_ofFn]
  constructor
  · rintro ⟨hp, hf⟩
    refine ⟨hp, ?_, ?_⟩
    · exact hp.length_eq.trans ((length_sourceLetters α).trans hc)
    · intro i hi
      simpa [List.getD, List.getElem?_ofFn, hi] using hf ⟨i, hi⟩
  · rintro ⟨hp, hl, hf⟩
    refine ⟨hp, ?_⟩
    intro i
    simpa [List.getD, List.getElem?_ofFn, i.isLt] using hf i.val i.isLt

theorem asc_cons_cons (a b : ℕ) (w : List ℕ) :
    asc (a :: b :: w) = (if a < b then 1 else 0) + asc (b :: w) := by
  simp only [asc, Finset.card_filter, List.length_cons, Nat.add_sub_cancel]
  rw [Finset.sum_range_succ']
  simp [List.getD, Nat.add_comm, Nat.add_left_comm, -Finset.sum_boole]
  rfl

/-! A recursive polynomial sum on the exact residual content. -/

noncomputable def weight : Option ℕ → List ℕ → ℝ[X]
  | _, [] => 1
  | none, a :: w => weight (some a) w
  | some p, a :: w => X ^ (if p < a then 1 else 0) * weight (some a) w

noncomputable def dp : List ℕ → List ℕ → Option ℕ → ℝ[X]
  | [], [], _ => 1
  | [], _ :: _, _ => 0
  | b :: bs, letters, prev =>
      ∑ a ∈ letters.toFinset.filter (fun a => 0 < a ∧ a ≤ b),
        X ^ (match prev with
          | none => 0
          | some p => if p < a then 1 else 0) *
          dp bs (letters.erase a) (some a)

/-- Replace the exact first-letter branches by their certified child polynomials. -/
theorem dp_cons_eq_sum_of_children (b : ℕ) (bs letters : List ℕ) (prev : Option ℕ)
    (allowed : Finset ℕ) (coefficients : ℕ → ℝ[X])
    (hallowed : letters.toFinset.filter (fun a => 0 < a ∧ a ≤ b) = allowed)
    (hchildren : ∀ a ∈ allowed, dp bs (letters.erase a) (some a) = coefficients a) :
    dp (b :: bs) letters prev =
      ∑ a ∈ allowed,
        X ^ (match prev with
          | none => 0
          | some p => if p < a then 1 else 0) * coefficients a := by
  rw [dp, hallowed]
  apply Finset.sum_congr rfl
  intro a ha
  rw [hchildren a ha]

theorem boundedWords_nil (letters : List ℕ) :
    boundedWords [] letters = if letters = [] then {[]} else ∅ := by
  ext w
  cases letters <;> cases w <;> simp [mem_boundedWords, fits]

theorem weight_some_eq (p : ℕ) (w : List ℕ) :
    weight (some p) w = X ^ asc (p :: w) := by
  induction w generalizing p with
  | nil => simp [weight, asc]
  | cons a w ih => rw [weight, ih, asc_cons_cons, pow_add]

theorem weight_none_eq (w : List ℕ) : weight none w = X ^ asc w := by
  cases w with
  | nil => simp [weight, asc]
  | cons a w => exact weight_some_eq a w

theorem sum_weight_eq_dp (bounds letters : List ℕ) (prev : Option ℕ) :
    (∑ w ∈ boundedWords bounds letters, weight prev w) = dp bounds letters prev := by
  induction bounds generalizing letters prev with
  | nil =>
    rw [boundedWords_nil]
    cases letters <;> simp [dp, weight]
  | cons b bs ih =>
    rw [boundedWords_cons]
    have hdisj : ((letters.toFinset.filter (fun a => 0 < a ∧ a ≤ b) : Finset ℕ) : Set ℕ).PairwiseDisjoint
        (fun a => (boundedWords bs (letters.erase a)).image (List.cons a)) := by
      intro a ha c hc hac
      change Disjoint ((boundedWords bs (letters.erase a)).image (List.cons a))
        ((boundedWords bs (letters.erase c)).image (List.cons c))
      refine Finset.disjoint_left.2 ?_
      intro w hwa hwc
      rcases Finset.mem_image.mp hwa with ⟨u, hu, rfl⟩
      rcases Finset.mem_image.mp hwc with ⟨v, hv, hhead⟩
      simp only [List.cons.injEq] at hhead
      exact hac hhead.1.symm
    rw [Finset.sum_biUnion hdisj, dp]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_image]
    · cases prev <;> simp [weight, ← Finset.mul_sum, ih]
    · intro u hu v hv huv
      exact (List.cons.inj huv).2

theorem W_sum_eq_dp {n k : ℕ} (lam : Fin n → ℕ) (α : Fin k → ℕ)
    (hsum : (∑ c, α c) = n) :
    R lam α = dp (List.ofFn lam) (sourceLetters α) none := by
  rw [R, W_eq_boundedWords lam α hsum]
  simpa only [weight_none_eq] using sum_weight_eq_dp (List.ofFn lam) (sourceLetters α) none

#print axioms W_eq_boundedWords
#print axioms sum_weight_eq_dp
#print axioms W_sum_eq_dp

end D5.S3.Combinatorics.Permutation.MultisetRookEulerianWordRecurrence
