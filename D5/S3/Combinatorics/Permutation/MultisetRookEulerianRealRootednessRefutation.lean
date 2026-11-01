/- GID: D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation
   mirror-E: none(waiver:exact-finite-certificate)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.claim; result=D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.result; claim=D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.claim
   digest: Remaining-content counting for the full multiset rook-Eulerian polynomial. -/

import D5.S3.Combinatorics.Permutation.MultisetRookEulerianInterlacingRefutation
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.List.Forall2

/-! Exact completion counts for the original full word polynomial. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Permutation.MultisetRookEulerianRealRootednessRefutation

open Polynomial
open MultisetRookEulerianInterlacingRefutation (W asc R)

/-- The first clause of Conjecture 28, with positive Ferrers row bounds. -/
noncomputable def claim : Prop :=
  ∀ (n k : ℕ) (lam : Fin n → ℕ) (α : Fin k → ℕ),
    0 < n → (∀ i, 0 < lam i) → Monotone lam → (∑ c, α c) = n →
      (R lam α).Splits

/-- The only new edge contributed by a next letter. There is no initial edge. -/
def edge (last : Option ℕ) (j : ℕ) : ℕ :=
  match last with
  | none => 0
  | some i => if i < j then 1 else 0

/-- Polynomial count of completions, choosing each available label once. -/
def count : List ℕ → Multiset ℕ → Option ℕ → ℕ[X]
  | [], m, _ => if m = 0 then 1 else 0
  | r :: rows, m, last =>
      ∑ j ∈ m.toFinset.filter (fun j => 0 < j ∧ j ≤ r),
        X ^ edge last j * count rows (m.erase j) (some j)

private def completions : List ℕ → Multiset ℕ → Finset (List ℕ)
  | [], m => if m = 0 then {[]} else ∅
  | r :: rows, m =>
      (m.toFinset.filter (fun j => 0 < j ∧ j ≤ r)).biUnion
        (fun j => (completions rows (m.erase j)).image (List.cons j))

private theorem mem_completions (rows : List ℕ) (m : Multiset ℕ) (w : List ℕ) :
    w ∈ completions rows m ↔
      (w : Multiset ℕ) = m ∧ List.Forall₂ (fun r j => 0 < j ∧ j ≤ r) rows w := by
  induction rows generalizing m w with
  | nil =>
      cases w <;> by_cases hm : m = 0 <;> simp [completions, hm, eq_comm]
  | cons r rows ih =>
      cases w with
      | nil => simp [completions]
      | cons j w =>
          simp only [completions, Finset.mem_biUnion, Finset.mem_filter,
            Multiset.mem_toFinset, Finset.mem_image, List.cons.injEq,
            List.forall₂_cons]
          constructor
          · rintro ⟨a, ⟨ha, hrow⟩, v, hv, he, hw⟩
            subst a
            subst v
            obtain ⟨hm, htail⟩ := (ih _ _).mp hv
            exact ⟨by change j ::ₘ (w : Multiset ℕ) = m; rw [hm, Multiset.cons_erase ha],
              hrow, htail⟩
          · rintro ⟨hm, hrow, htail⟩
            have hj : j ∈ m := hm ▸ (by simp)
            refine ⟨j, ⟨hj, hrow⟩, w, (ih _ _).mpr ⟨?_, htail⟩, rfl, rfl⟩
            change (w : Multiset ℕ) = m.erase j
            rw [← hm]
            exact (Multiset.erase_cons_head j (w : Multiset ℕ)).symm

private def weight : Option ℕ → List ℕ → ℕ[X]
  | _, [] => 1
  | last, j :: w => X ^ edge last j * weight (some j) w

private theorem count_eq_sum (rows : List ℕ) (m : Multiset ℕ) (last : Option ℕ) :
    count rows m last = ∑ w ∈ completions rows m, weight last w := by
  induction rows generalizing m last with
  | nil => by_cases hm : m = 0 <;> simp [count, completions, hm, weight]
  | cons r rows ih =>
      rw [count, completions, Finset.sum_biUnion]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_image]
        · simp only [weight, ← Finset.mul_sum, ← ih]
        · intro a _ b _ h
          exact List.cons.inj h |>.2
      · intro i _ j _ hij
        apply Finset.disjoint_left.mpr
        intro w hi hj
        obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hi
        obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hj
        exact hij (List.cons.inj (ha.trans hb.symm)).1

private theorem asc_cons_cons (i j : ℕ) (w : List ℕ) :
    asc (i :: j :: w) = (if i < j then 1 else 0) + asc (j :: w) := by
  simp only [asc, List.length_cons, Nat.add_sub_cancel, Finset.card_filter]
  rw [Finset.sum_range_succ']
  simp [List.getD_cons_succ, add_comm]

private theorem weight_cons (last : Option ℕ) (j : ℕ) (w : List ℕ) :
    weight last (j :: w) = X ^ edge last j * X ^ asc (j :: w) := by
  induction w generalizing last j with
  | nil => simp [weight, asc]
  | cons i w ih =>
      rw [weight, ih, asc_cons_cons, pow_add]
      rfl

private theorem weight_none (w : List ℕ) : weight none w = X ^ asc w := by
  cases w with
  | nil => simp [weight, asc]
  | cons j w => simp [weight_cons, edge]

private theorem content_length {k : ℕ} (α : Fin k → ℕ) :
    ((List.finRange k).flatMap (fun c => List.replicate (α c) (c.val + 1))).length =
      ∑ c, α c := by
  simp [List.length_flatMap, List.finRange, List.sum_ofFn]

private theorem completions_eq_W {n k : ℕ} (lam : Fin n → ℕ) (α : Fin k → ℕ)
    (htotal : (∑ c, α c) = n) :
    completions (List.ofFn lam)
      (((List.finRange k).flatMap
        (fun c => List.replicate (α c) (c.val + 1))) : Multiset ℕ) = W lam α := by
  ext w
  rw [mem_completions, W, Finset.mem_filter, List.mem_toFinset, List.mem_permutations',
    ← Multiset.coe_eq_coe]
  apply and_congr_right
  intro hm
  have hlen : w.length = n := by
    have := congrArg Multiset.card hm
    simpa only [Multiset.coe_card, content_length, htotal] using this
  rw [List.forall₂_iff_get]
  simp only [List.length_ofFn]
  constructor
  · rintro ⟨_, h⟩ i
    simpa only [List.get_ofFn, List.get_eq_getElem,
      List.getD_eq_getElem _ _ (by omega : i.val < w.length)] using
      h i.val i.isLt (by omega)
  · intro h
    refine ⟨hlen.symm, ?_⟩
    intro i hi hw
    simpa only [List.get_ofFn, List.get_eq_getElem,
      List.getD_eq_getElem _ _ hw] using h ⟨i, hi⟩

/-- Exact full-R counting, under the source's total-content hypothesis.
The recurrence also covers empty boards, zero content labels and impossible completions. -/
theorem count_eq_R {n k : ℕ} (lam : Fin n → ℕ) (α : Fin k → ℕ)
    (htotal : (∑ c, α c) = n) :
    (count (List.ofFn lam)
      (((List.finRange k).flatMap
        (fun c => List.replicate (α c) (c.val + 1))) : Multiset ℕ) none).map
          (Nat.castRingHom ℝ) = R lam α := by
  rw [count_eq_sum, completions_eq_W lam α htotal, R]
  simp only [Polynomial.map_sum, weight_none, Polynomial.map_pow, Polynomial.map_X]

#print axioms count_eq_R

end D5.S3.Combinatorics.Permutation.MultisetRookEulerianRealRootednessRefutation
