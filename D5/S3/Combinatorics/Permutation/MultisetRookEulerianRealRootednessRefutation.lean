/- GID: D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation
   mirror-E: none(waiver:exact-finite-certificate)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.claim; result=D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.result; claim=D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.claim
   digest: Remaining-content counting for the full multiset rook-Eulerian polynomial. -/

import D5.S3.Combinatorics.Permutation.MultisetRookEulerianInterlacingRefutation
import D5.S3.Zeros.Jensen.SourceJensenPositiveExtension
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD

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
  simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.zero_add]
  omega

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
    simpa only [List.get_eq_getElem, List.getElem_ofFn,
      List.getD_eq_getElem _ _ (by omega : i.val < w.length)] using
      h i.val i.isLt (by omega)
  · intro h
    refine ⟨hlen.symm, ?_⟩
    intro i hi hw
    simpa only [List.get_eq_getElem, List.getElem_ofFn,
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

private def board : Fin 120 → ℕ := fun i =>
  if i.val < 3 then 2 else if i.val < 7 then 3 else
    if i.val < 17 then 4 else if i.val < 19 then 5 else 6

private def content : Fin 6 → ℕ := ![6, 1, 4, 8, 1, 100]

private def rows : List ℕ :=
  List.replicate 3 2 ++ List.replicate 4 3 ++ List.replicate 10 4 ++
    List.replicate 2 5 ++ List.replicate 101 6

private def bag (a b c d e f : ℕ) : Multiset ℕ :=
  ((List.replicate a 1 ++ List.replicate b 2 ++ List.replicate c 3 ++
    List.replicate d 4 ++ List.replicate e 5 ++ List.replicate f 6) : List ℕ)

private theorem cert_0 : count (rows.drop 120) (bag 0 0 0 0 0 0) (some 6) =
    (1 : ℕ[X]) := by
  norm_num [count, rows, bag]

private theorem cert_1 : count (rows.drop 119) (bag 0 0 0 0 0 1) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 1).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 119 = 6 :: rows.drop 120 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 1).erase 6 = (bag 0 0 0 0 0 0) := by decide +kernel
  rw [hm6, cert_0]
  norm_num [edge]
  <;> ring

private theorem cert_2 : count (rows.drop 118) (bag 0 0 0 0 0 2) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 2).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 118 = 6 :: rows.drop 119 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 2).erase 6 = (bag 0 0 0 0 0 1) := by decide +kernel
  rw [hm6, cert_1]
  norm_num [edge]
  <;> ring

private theorem cert_3 : count (rows.drop 117) (bag 0 0 0 0 0 3) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 3).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 117 = 6 :: rows.drop 118 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 3).erase 6 = (bag 0 0 0 0 0 2) := by decide +kernel
  rw [hm6, cert_2]
  norm_num [edge]
  <;> ring

private theorem cert_4 : count (rows.drop 116) (bag 0 0 0 0 0 4) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 4).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 116 = 6 :: rows.drop 117 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 4).erase 6 = (bag 0 0 0 0 0 3) := by decide +kernel
  rw [hm6, cert_3]
  norm_num [edge]
  <;> ring

private theorem cert_5 : count (rows.drop 115) (bag 0 0 0 0 0 5) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 5).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 115 = 6 :: rows.drop 116 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 5).erase 6 = (bag 0 0 0 0 0 4) := by decide +kernel
  rw [hm6, cert_4]
  norm_num [edge]
  <;> ring

private theorem cert_6 : count (rows.drop 114) (bag 0 0 0 0 0 6) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 6).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 114 = 6 :: rows.drop 115 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 6).erase 6 = (bag 0 0 0 0 0 5) := by decide +kernel
  rw [hm6, cert_5]
  norm_num [edge]
  <;> ring

private theorem cert_7 : count (rows.drop 113) (bag 0 0 0 0 0 7) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 7).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 113 = 6 :: rows.drop 114 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 7).erase 6 = (bag 0 0 0 0 0 6) := by decide +kernel
  rw [hm6, cert_6]
  norm_num [edge]
  <;> ring

private theorem cert_8 : count (rows.drop 112) (bag 0 0 0 0 0 8) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 8).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 112 = 6 :: rows.drop 113 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 8).erase 6 = (bag 0 0 0 0 0 7) := by decide +kernel
  rw [hm6, cert_7]
  norm_num [edge]
  <;> ring

private theorem cert_9 : count (rows.drop 111) (bag 0 0 0 0 0 9) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 9).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 111 = 6 :: rows.drop 112 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 9).erase 6 = (bag 0 0 0 0 0 8) := by decide +kernel
  rw [hm6, cert_8]
  norm_num [edge]
  <;> ring

private theorem cert_10 : count (rows.drop 110) (bag 0 0 0 0 0 10) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 10).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 110 = 6 :: rows.drop 111 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 10).erase 6 = (bag 0 0 0 0 0 9) := by decide +kernel
  rw [hm6, cert_9]
  norm_num [edge]
  <;> ring

private theorem cert_11 : count (rows.drop 109) (bag 0 0 0 0 0 11) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 11).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 109 = 6 :: rows.drop 110 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 11).erase 6 = (bag 0 0 0 0 0 10) := by decide +kernel
  rw [hm6, cert_10]
  norm_num [edge]
  <;> ring

private theorem cert_12 : count (rows.drop 108) (bag 0 0 0 0 0 12) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 12).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 108 = 6 :: rows.drop 109 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 12).erase 6 = (bag 0 0 0 0 0 11) := by decide +kernel
  rw [hm6, cert_11]
  norm_num [edge]
  <;> ring

private theorem cert_13 : count (rows.drop 107) (bag 0 0 0 0 0 13) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 13).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 107 = 6 :: rows.drop 108 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 13).erase 6 = (bag 0 0 0 0 0 12) := by decide +kernel
  rw [hm6, cert_12]
  norm_num [edge]
  <;> ring

private theorem cert_14 : count (rows.drop 106) (bag 0 0 0 0 0 14) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 14).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 106 = 6 :: rows.drop 107 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 14).erase 6 = (bag 0 0 0 0 0 13) := by decide +kernel
  rw [hm6, cert_13]
  norm_num [edge]
  <;> ring

private theorem cert_15 : count (rows.drop 105) (bag 0 0 0 0 0 15) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 15).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 105 = 6 :: rows.drop 106 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 15).erase 6 = (bag 0 0 0 0 0 14) := by decide +kernel
  rw [hm6, cert_14]
  norm_num [edge]
  <;> ring

private theorem cert_16 : count (rows.drop 104) (bag 0 0 0 0 0 16) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 16).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 104 = 6 :: rows.drop 105 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 16).erase 6 = (bag 0 0 0 0 0 15) := by decide +kernel
  rw [hm6, cert_15]
  norm_num [edge]
  <;> ring

private theorem cert_17 : count (rows.drop 103) (bag 0 0 0 0 0 17) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 17).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 103 = 6 :: rows.drop 104 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 17).erase 6 = (bag 0 0 0 0 0 16) := by decide +kernel
  rw [hm6, cert_16]
  norm_num [edge]
  <;> ring

private theorem cert_18 : count (rows.drop 102) (bag 0 0 0 0 0 18) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 18).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 102 = 6 :: rows.drop 103 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 18).erase 6 = (bag 0 0 0 0 0 17) := by decide +kernel
  rw [hm6, cert_17]
  norm_num [edge]
  <;> ring

private theorem cert_19 : count (rows.drop 101) (bag 0 0 0 0 0 19) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 19).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 101 = 6 :: rows.drop 102 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 19).erase 6 = (bag 0 0 0 0 0 18) := by decide +kernel
  rw [hm6, cert_18]
  norm_num [edge]
  <;> ring

private theorem cert_20 : count (rows.drop 100) (bag 0 0 0 0 0 20) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 20).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 100 = 6 :: rows.drop 101 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 20).erase 6 = (bag 0 0 0 0 0 19) := by decide +kernel
  rw [hm6, cert_19]
  norm_num [edge]
  <;> ring

private theorem cert_21 : count (rows.drop 99) (bag 0 0 0 0 0 21) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 21).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 99 = 6 :: rows.drop 100 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 21).erase 6 = (bag 0 0 0 0 0 20) := by decide +kernel
  rw [hm6, cert_20]
  norm_num [edge]
  <;> ring

private theorem cert_22 : count (rows.drop 98) (bag 0 0 0 0 0 22) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 22).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 98 = 6 :: rows.drop 99 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 22).erase 6 = (bag 0 0 0 0 0 21) := by decide +kernel
  rw [hm6, cert_21]
  norm_num [edge]
  <;> ring

private theorem cert_23 : count (rows.drop 97) (bag 0 0 0 0 0 23) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 23).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 97 = 6 :: rows.drop 98 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 23).erase 6 = (bag 0 0 0 0 0 22) := by decide +kernel
  rw [hm6, cert_22]
  norm_num [edge]
  <;> ring

private theorem cert_24 : count (rows.drop 96) (bag 0 0 0 0 0 24) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 24).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 96 = 6 :: rows.drop 97 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 24).erase 6 = (bag 0 0 0 0 0 23) := by decide +kernel
  rw [hm6, cert_23]
  norm_num [edge]
  <;> ring

private theorem cert_25 : count (rows.drop 95) (bag 0 0 0 0 0 25) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 25).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 95 = 6 :: rows.drop 96 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 25).erase 6 = (bag 0 0 0 0 0 24) := by decide +kernel
  rw [hm6, cert_24]
  norm_num [edge]
  <;> ring

private theorem cert_26 : count (rows.drop 94) (bag 0 0 0 0 0 26) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 26).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 94 = 6 :: rows.drop 95 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 26).erase 6 = (bag 0 0 0 0 0 25) := by decide +kernel
  rw [hm6, cert_25]
  norm_num [edge]
  <;> ring

private theorem cert_27 : count (rows.drop 93) (bag 0 0 0 0 0 27) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 27).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 93 = 6 :: rows.drop 94 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 27).erase 6 = (bag 0 0 0 0 0 26) := by decide +kernel
  rw [hm6, cert_26]
  norm_num [edge]
  <;> ring

private theorem cert_28 : count (rows.drop 92) (bag 0 0 0 0 0 28) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 28).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 92 = 6 :: rows.drop 93 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 28).erase 6 = (bag 0 0 0 0 0 27) := by decide +kernel
  rw [hm6, cert_27]
  norm_num [edge]
  <;> ring

private theorem cert_29 : count (rows.drop 91) (bag 0 0 0 0 0 29) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 29).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 91 = 6 :: rows.drop 92 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 29).erase 6 = (bag 0 0 0 0 0 28) := by decide +kernel
  rw [hm6, cert_28]
  norm_num [edge]
  <;> ring

private theorem cert_30 : count (rows.drop 90) (bag 0 0 0 0 0 30) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 30).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 90 = 6 :: rows.drop 91 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 30).erase 6 = (bag 0 0 0 0 0 29) := by decide +kernel
  rw [hm6, cert_29]
  norm_num [edge]
  <;> ring

private theorem cert_31 : count (rows.drop 89) (bag 0 0 0 0 0 31) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 31).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 89 = 6 :: rows.drop 90 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 31).erase 6 = (bag 0 0 0 0 0 30) := by decide +kernel
  rw [hm6, cert_30]
  norm_num [edge]
  <;> ring

private theorem cert_32 : count (rows.drop 88) (bag 0 0 0 0 0 32) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 32).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 88 = 6 :: rows.drop 89 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 32).erase 6 = (bag 0 0 0 0 0 31) := by decide +kernel
  rw [hm6, cert_31]
  norm_num [edge]
  <;> ring

private theorem cert_33 : count (rows.drop 87) (bag 0 0 0 0 0 33) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 33).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 87 = 6 :: rows.drop 88 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 33).erase 6 = (bag 0 0 0 0 0 32) := by decide +kernel
  rw [hm6, cert_32]
  norm_num [edge]
  <;> ring

private theorem cert_34 : count (rows.drop 86) (bag 0 0 0 0 0 34) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 34).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 86 = 6 :: rows.drop 87 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 34).erase 6 = (bag 0 0 0 0 0 33) := by decide +kernel
  rw [hm6, cert_33]
  norm_num [edge]
  <;> ring

private theorem cert_35 : count (rows.drop 85) (bag 0 0 0 0 0 35) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 35).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 85 = 6 :: rows.drop 86 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 35).erase 6 = (bag 0 0 0 0 0 34) := by decide +kernel
  rw [hm6, cert_34]
  norm_num [edge]
  <;> ring

private theorem cert_36 : count (rows.drop 84) (bag 0 0 0 0 0 36) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 36).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 84 = 6 :: rows.drop 85 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 36).erase 6 = (bag 0 0 0 0 0 35) := by decide +kernel
  rw [hm6, cert_35]
  norm_num [edge]
  <;> ring

private theorem cert_37 : count (rows.drop 83) (bag 0 0 0 0 0 37) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 37).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 83 = 6 :: rows.drop 84 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 37).erase 6 = (bag 0 0 0 0 0 36) := by decide +kernel
  rw [hm6, cert_36]
  norm_num [edge]
  <;> ring

private theorem cert_38 : count (rows.drop 82) (bag 0 0 0 0 0 38) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 38).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 82 = 6 :: rows.drop 83 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 38).erase 6 = (bag 0 0 0 0 0 37) := by decide +kernel
  rw [hm6, cert_37]
  norm_num [edge]
  <;> ring

private theorem cert_39 : count (rows.drop 81) (bag 0 0 0 0 0 39) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 39).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 81 = 6 :: rows.drop 82 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 39).erase 6 = (bag 0 0 0 0 0 38) := by decide +kernel
  rw [hm6, cert_38]
  norm_num [edge]
  <;> ring

private theorem cert_40 : count (rows.drop 80) (bag 0 0 0 0 0 40) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 40).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 80 = 6 :: rows.drop 81 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 40).erase 6 = (bag 0 0 0 0 0 39) := by decide +kernel
  rw [hm6, cert_39]
  norm_num [edge]
  <;> ring

private theorem cert_41 : count (rows.drop 79) (bag 0 0 0 0 0 41) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 41).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 79 = 6 :: rows.drop 80 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 41).erase 6 = (bag 0 0 0 0 0 40) := by decide +kernel
  rw [hm6, cert_40]
  norm_num [edge]
  <;> ring

private theorem cert_42 : count (rows.drop 78) (bag 0 0 0 0 0 42) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 42).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 78 = 6 :: rows.drop 79 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 42).erase 6 = (bag 0 0 0 0 0 41) := by decide +kernel
  rw [hm6, cert_41]
  norm_num [edge]
  <;> ring

private theorem cert_43 : count (rows.drop 77) (bag 0 0 0 0 0 43) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 43).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 77 = 6 :: rows.drop 78 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 43).erase 6 = (bag 0 0 0 0 0 42) := by decide +kernel
  rw [hm6, cert_42]
  norm_num [edge]
  <;> ring

private theorem cert_44 : count (rows.drop 76) (bag 0 0 0 0 0 44) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 44).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 76 = 6 :: rows.drop 77 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 44).erase 6 = (bag 0 0 0 0 0 43) := by decide +kernel
  rw [hm6, cert_43]
  norm_num [edge]
  <;> ring

private theorem cert_45 : count (rows.drop 75) (bag 0 0 0 0 0 45) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 45).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 75 = 6 :: rows.drop 76 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 45).erase 6 = (bag 0 0 0 0 0 44) := by decide +kernel
  rw [hm6, cert_44]
  norm_num [edge]
  <;> ring

private theorem cert_46 : count (rows.drop 74) (bag 0 0 0 0 0 46) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 46).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 74 = 6 :: rows.drop 75 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 46).erase 6 = (bag 0 0 0 0 0 45) := by decide +kernel
  rw [hm6, cert_45]
  norm_num [edge]
  <;> ring

private theorem cert_47 : count (rows.drop 73) (bag 0 0 0 0 0 47) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 47).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 73 = 6 :: rows.drop 74 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 47).erase 6 = (bag 0 0 0 0 0 46) := by decide +kernel
  rw [hm6, cert_46]
  norm_num [edge]
  <;> ring

private theorem cert_48 : count (rows.drop 72) (bag 0 0 0 0 0 48) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 48).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 72 = 6 :: rows.drop 73 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 48).erase 6 = (bag 0 0 0 0 0 47) := by decide +kernel
  rw [hm6, cert_47]
  norm_num [edge]
  <;> ring

private theorem cert_49 : count (rows.drop 71) (bag 0 0 0 0 0 49) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 49).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 71 = 6 :: rows.drop 72 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 49).erase 6 = (bag 0 0 0 0 0 48) := by decide +kernel
  rw [hm6, cert_48]
  norm_num [edge]
  <;> ring

private theorem cert_50 : count (rows.drop 70) (bag 0 0 0 0 0 50) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 50).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 70 = 6 :: rows.drop 71 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 50).erase 6 = (bag 0 0 0 0 0 49) := by decide +kernel
  rw [hm6, cert_49]
  norm_num [edge]
  <;> ring

private theorem cert_51 : count (rows.drop 69) (bag 0 0 0 0 0 51) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 51).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 69 = 6 :: rows.drop 70 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 51).erase 6 = (bag 0 0 0 0 0 50) := by decide +kernel
  rw [hm6, cert_50]
  norm_num [edge]
  <;> ring

private theorem cert_52 : count (rows.drop 68) (bag 0 0 0 0 0 52) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 52).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 68 = 6 :: rows.drop 69 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 52).erase 6 = (bag 0 0 0 0 0 51) := by decide +kernel
  rw [hm6, cert_51]
  norm_num [edge]
  <;> ring

private theorem cert_53 : count (rows.drop 67) (bag 0 0 0 0 0 53) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 53).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 67 = 6 :: rows.drop 68 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 53).erase 6 = (bag 0 0 0 0 0 52) := by decide +kernel
  rw [hm6, cert_52]
  norm_num [edge]
  <;> ring

private theorem cert_54 : count (rows.drop 66) (bag 0 0 0 0 0 54) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 54).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 66 = 6 :: rows.drop 67 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 54).erase 6 = (bag 0 0 0 0 0 53) := by decide +kernel
  rw [hm6, cert_53]
  norm_num [edge]
  <;> ring

private theorem cert_55 : count (rows.drop 65) (bag 0 0 0 0 0 55) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 55).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 65 = 6 :: rows.drop 66 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 55).erase 6 = (bag 0 0 0 0 0 54) := by decide +kernel
  rw [hm6, cert_54]
  norm_num [edge]
  <;> ring

private theorem cert_56 : count (rows.drop 64) (bag 0 0 0 0 0 56) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 56).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 64 = 6 :: rows.drop 65 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 56).erase 6 = (bag 0 0 0 0 0 55) := by decide +kernel
  rw [hm6, cert_55]
  norm_num [edge]
  <;> ring

private theorem cert_57 : count (rows.drop 63) (bag 0 0 0 0 0 57) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 57).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 63 = 6 :: rows.drop 64 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 57).erase 6 = (bag 0 0 0 0 0 56) := by decide +kernel
  rw [hm6, cert_56]
  norm_num [edge]
  <;> ring

private theorem cert_58 : count (rows.drop 62) (bag 0 0 0 0 0 58) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 58).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 62 = 6 :: rows.drop 63 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 58).erase 6 = (bag 0 0 0 0 0 57) := by decide +kernel
  rw [hm6, cert_57]
  norm_num [edge]
  <;> ring

private theorem cert_59 : count (rows.drop 61) (bag 0 0 0 0 0 59) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 59).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 61 = 6 :: rows.drop 62 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 59).erase 6 = (bag 0 0 0 0 0 58) := by decide +kernel
  rw [hm6, cert_58]
  norm_num [edge]
  <;> ring

private theorem cert_60 : count (rows.drop 60) (bag 0 0 0 0 0 60) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 60).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 60 = 6 :: rows.drop 61 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 60).erase 6 = (bag 0 0 0 0 0 59) := by decide +kernel
  rw [hm6, cert_59]
  norm_num [edge]
  <;> ring

private theorem cert_61 : count (rows.drop 59) (bag 0 0 0 0 0 61) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 61).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 59 = 6 :: rows.drop 60 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 61).erase 6 = (bag 0 0 0 0 0 60) := by decide +kernel
  rw [hm6, cert_60]
  norm_num [edge]
  <;> ring

private theorem cert_62 : count (rows.drop 58) (bag 0 0 0 0 0 62) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 62).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 58 = 6 :: rows.drop 59 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 62).erase 6 = (bag 0 0 0 0 0 61) := by decide +kernel
  rw [hm6, cert_61]
  norm_num [edge]
  <;> ring

private theorem cert_63 : count (rows.drop 57) (bag 0 0 0 0 0 63) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 63).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 57 = 6 :: rows.drop 58 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 63).erase 6 = (bag 0 0 0 0 0 62) := by decide +kernel
  rw [hm6, cert_62]
  norm_num [edge]
  <;> ring

private theorem cert_64 : count (rows.drop 56) (bag 0 0 0 0 0 64) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 64).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 56 = 6 :: rows.drop 57 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 64).erase 6 = (bag 0 0 0 0 0 63) := by decide +kernel
  rw [hm6, cert_63]
  norm_num [edge]
  <;> ring

private theorem cert_65 : count (rows.drop 55) (bag 0 0 0 0 0 65) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 65).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 55 = 6 :: rows.drop 56 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 65).erase 6 = (bag 0 0 0 0 0 64) := by decide +kernel
  rw [hm6, cert_64]
  norm_num [edge]
  <;> ring

private theorem cert_66 : count (rows.drop 54) (bag 0 0 0 0 0 66) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 66).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 54 = 6 :: rows.drop 55 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 66).erase 6 = (bag 0 0 0 0 0 65) := by decide +kernel
  rw [hm6, cert_65]
  norm_num [edge]
  <;> ring

private theorem cert_67 : count (rows.drop 53) (bag 0 0 0 0 0 67) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 67).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 53 = 6 :: rows.drop 54 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 67).erase 6 = (bag 0 0 0 0 0 66) := by decide +kernel
  rw [hm6, cert_66]
  norm_num [edge]
  <;> ring

private theorem cert_68 : count (rows.drop 52) (bag 0 0 0 0 0 68) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 68).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 52 = 6 :: rows.drop 53 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 68).erase 6 = (bag 0 0 0 0 0 67) := by decide +kernel
  rw [hm6, cert_67]
  norm_num [edge]
  <;> ring

private theorem cert_69 : count (rows.drop 51) (bag 0 0 0 0 0 69) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 69).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 51 = 6 :: rows.drop 52 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 69).erase 6 = (bag 0 0 0 0 0 68) := by decide +kernel
  rw [hm6, cert_68]
  norm_num [edge]
  <;> ring

private theorem cert_70 : count (rows.drop 50) (bag 0 0 0 0 0 70) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 70).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 50 = 6 :: rows.drop 51 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 70).erase 6 = (bag 0 0 0 0 0 69) := by decide +kernel
  rw [hm6, cert_69]
  norm_num [edge]
  <;> ring

private theorem cert_71 : count (rows.drop 49) (bag 0 0 0 0 0 71) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 71).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 49 = 6 :: rows.drop 50 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 71).erase 6 = (bag 0 0 0 0 0 70) := by decide +kernel
  rw [hm6, cert_70]
  norm_num [edge]
  <;> ring

private theorem cert_72 : count (rows.drop 48) (bag 0 0 0 0 0 72) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 72).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 48 = 6 :: rows.drop 49 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 72).erase 6 = (bag 0 0 0 0 0 71) := by decide +kernel
  rw [hm6, cert_71]
  norm_num [edge]
  <;> ring

private theorem cert_73 : count (rows.drop 47) (bag 0 0 0 0 0 73) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 73).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 47 = 6 :: rows.drop 48 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 73).erase 6 = (bag 0 0 0 0 0 72) := by decide +kernel
  rw [hm6, cert_72]
  norm_num [edge]
  <;> ring

private theorem cert_74 : count (rows.drop 46) (bag 0 0 0 0 0 74) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 74).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 46 = 6 :: rows.drop 47 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 74).erase 6 = (bag 0 0 0 0 0 73) := by decide +kernel
  rw [hm6, cert_73]
  norm_num [edge]
  <;> ring

private theorem cert_75 : count (rows.drop 45) (bag 0 0 0 0 0 75) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 75).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 45 = 6 :: rows.drop 46 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 75).erase 6 = (bag 0 0 0 0 0 74) := by decide +kernel
  rw [hm6, cert_74]
  norm_num [edge]
  <;> ring

private theorem cert_76 : count (rows.drop 44) (bag 0 0 0 0 0 76) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 76).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 44 = 6 :: rows.drop 45 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 76).erase 6 = (bag 0 0 0 0 0 75) := by decide +kernel
  rw [hm6, cert_75]
  norm_num [edge]
  <;> ring

private theorem cert_77 : count (rows.drop 43) (bag 0 0 0 0 0 77) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 77).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 43 = 6 :: rows.drop 44 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 77).erase 6 = (bag 0 0 0 0 0 76) := by decide +kernel
  rw [hm6, cert_76]
  norm_num [edge]
  <;> ring

private theorem cert_78 : count (rows.drop 42) (bag 0 0 0 0 0 78) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 78).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 42 = 6 :: rows.drop 43 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 78).erase 6 = (bag 0 0 0 0 0 77) := by decide +kernel
  rw [hm6, cert_77]
  norm_num [edge]
  <;> ring

private theorem cert_79 : count (rows.drop 41) (bag 0 0 0 0 0 79) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 79).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 41 = 6 :: rows.drop 42 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 79).erase 6 = (bag 0 0 0 0 0 78) := by decide +kernel
  rw [hm6, cert_78]
  norm_num [edge]
  <;> ring

private theorem cert_80 : count (rows.drop 40) (bag 0 0 0 0 0 80) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 80).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 40 = 6 :: rows.drop 41 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 80).erase 6 = (bag 0 0 0 0 0 79) := by decide +kernel
  rw [hm6, cert_79]
  norm_num [edge]
  <;> ring

private theorem cert_81 : count (rows.drop 39) (bag 0 0 0 0 0 81) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 81).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 39 = 6 :: rows.drop 40 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 81).erase 6 = (bag 0 0 0 0 0 80) := by decide +kernel
  rw [hm6, cert_80]
  norm_num [edge]
  <;> ring

private theorem cert_82 : count (rows.drop 38) (bag 0 0 0 0 0 82) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 82).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 38 = 6 :: rows.drop 39 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 82).erase 6 = (bag 0 0 0 0 0 81) := by decide +kernel
  rw [hm6, cert_81]
  norm_num [edge]
  <;> ring

private theorem cert_83 : count (rows.drop 37) (bag 0 0 0 0 0 83) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 83).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 37 = 6 :: rows.drop 38 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 83).erase 6 = (bag 0 0 0 0 0 82) := by decide +kernel
  rw [hm6, cert_82]
  norm_num [edge]
  <;> ring

private theorem cert_84 : count (rows.drop 36) (bag 0 0 0 0 0 84) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 84).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 36 = 6 :: rows.drop 37 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 84).erase 6 = (bag 0 0 0 0 0 83) := by decide +kernel
  rw [hm6, cert_83]
  norm_num [edge]
  <;> ring

private theorem cert_85 : count (rows.drop 35) (bag 0 0 0 0 0 85) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 85).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 35 = 6 :: rows.drop 36 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 85).erase 6 = (bag 0 0 0 0 0 84) := by decide +kernel
  rw [hm6, cert_84]
  norm_num [edge]
  <;> ring

private theorem cert_86 : count (rows.drop 34) (bag 0 0 0 0 0 86) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 86).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 34 = 6 :: rows.drop 35 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 86).erase 6 = (bag 0 0 0 0 0 85) := by decide +kernel
  rw [hm6, cert_85]
  norm_num [edge]
  <;> ring

private theorem cert_87 : count (rows.drop 33) (bag 0 0 0 0 0 87) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 87).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 33 = 6 :: rows.drop 34 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 87).erase 6 = (bag 0 0 0 0 0 86) := by decide +kernel
  rw [hm6, cert_86]
  norm_num [edge]
  <;> ring

private theorem cert_88 : count (rows.drop 32) (bag 0 0 0 0 0 88) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 88).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 32 = 6 :: rows.drop 33 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 88).erase 6 = (bag 0 0 0 0 0 87) := by decide +kernel
  rw [hm6, cert_87]
  norm_num [edge]
  <;> ring

private theorem cert_89 : count (rows.drop 31) (bag 0 0 0 0 0 89) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 89).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 31 = 6 :: rows.drop 32 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 89).erase 6 = (bag 0 0 0 0 0 88) := by decide +kernel
  rw [hm6, cert_88]
  norm_num [edge]
  <;> ring

private theorem cert_90 : count (rows.drop 30) (bag 0 0 0 0 0 90) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 90).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 30 = 6 :: rows.drop 31 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 90).erase 6 = (bag 0 0 0 0 0 89) := by decide +kernel
  rw [hm6, cert_89]
  norm_num [edge]
  <;> ring

private theorem cert_91 : count (rows.drop 29) (bag 0 0 0 0 0 91) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 91).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 29 = 6 :: rows.drop 30 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 91).erase 6 = (bag 0 0 0 0 0 90) := by decide +kernel
  rw [hm6, cert_90]
  norm_num [edge]
  <;> ring

private theorem cert_92 : count (rows.drop 28) (bag 0 0 0 0 0 92) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 92).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 28 = 6 :: rows.drop 29 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 92).erase 6 = (bag 0 0 0 0 0 91) := by decide +kernel
  rw [hm6, cert_91]
  norm_num [edge]
  <;> ring

private theorem cert_93 : count (rows.drop 27) (bag 0 0 0 0 0 93) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 93).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 27 = 6 :: rows.drop 28 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 93).erase 6 = (bag 0 0 0 0 0 92) := by decide +kernel
  rw [hm6, cert_92]
  norm_num [edge]
  <;> ring

private theorem cert_94 : count (rows.drop 26) (bag 0 0 0 0 0 94) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 94).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 26 = 6 :: rows.drop 27 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 94).erase 6 = (bag 0 0 0 0 0 93) := by decide +kernel
  rw [hm6, cert_93]
  norm_num [edge]
  <;> ring

private theorem cert_95 : count (rows.drop 25) (bag 0 0 0 0 0 95) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 95).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 25 = 6 :: rows.drop 26 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 95).erase 6 = (bag 0 0 0 0 0 94) := by decide +kernel
  rw [hm6, cert_94]
  norm_num [edge]
  <;> ring

private theorem cert_96 : count (rows.drop 24) (bag 0 0 0 0 0 96) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 96).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 24 = 6 :: rows.drop 25 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 96).erase 6 = (bag 0 0 0 0 0 95) := by decide +kernel
  rw [hm6, cert_95]
  norm_num [edge]
  <;> ring

private theorem cert_97 : count (rows.drop 23) (bag 0 0 0 0 0 97) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 97).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 23 = 6 :: rows.drop 24 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 97).erase 6 = (bag 0 0 0 0 0 96) := by decide +kernel
  rw [hm6, cert_96]
  norm_num [edge]
  <;> ring

private theorem cert_98 : count (rows.drop 22) (bag 0 0 0 0 0 98) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 98).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 22 = 6 :: rows.drop 23 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 98).erase 6 = (bag 0 0 0 0 0 97) := by decide +kernel
  rw [hm6, cert_97]
  norm_num [edge]
  <;> ring

private theorem cert_99 : count (rows.drop 21) (bag 0 0 0 0 0 99) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 99).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 21 = 6 :: rows.drop 22 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 99).erase 6 = (bag 0 0 0 0 0 98) := by decide +kernel
  rw [hm6, cert_98]
  norm_num [edge]
  <;> ring

private theorem cert_100 : count (rows.drop 20) (bag 0 0 0 0 0 100) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 20 = 6 :: rows.drop 21 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 100).erase 6 = (bag 0 0 0 0 0 99) := by decide +kernel
  rw [hm6, cert_99]
  norm_num [edge]
  <;> ring

private theorem cert_101 : count (rows.drop 21) (bag 0 0 0 0 0 99) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 99).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 21 = 6 :: rows.drop 22 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 99).erase 6 = (bag 0 0 0 0 0 98) := by decide +kernel
  rw [hm6, cert_98]
  norm_num [edge]
  <;> ring

private theorem cert_102 : count (rows.drop 22) (bag 0 0 0 0 0 98) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 98).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 22 = 6 :: rows.drop 23 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 98).erase 6 = (bag 0 0 0 0 0 97) := by decide +kernel
  rw [hm6, cert_97]
  norm_num [edge]
  <;> ring

private theorem cert_103 : count (rows.drop 23) (bag 0 0 0 0 0 97) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 97).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 23 = 6 :: rows.drop 24 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 97).erase 6 = (bag 0 0 0 0 0 96) := by decide +kernel
  rw [hm6, cert_96]
  norm_num [edge]
  <;> ring

private theorem cert_104 : count (rows.drop 24) (bag 0 0 0 0 0 96) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 96).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 24 = 6 :: rows.drop 25 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 96).erase 6 = (bag 0 0 0 0 0 95) := by decide +kernel
  rw [hm6, cert_95]
  norm_num [edge]
  <;> ring

private theorem cert_105 : count (rows.drop 25) (bag 0 0 0 0 0 95) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 95).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 25 = 6 :: rows.drop 26 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 95).erase 6 = (bag 0 0 0 0 0 94) := by decide +kernel
  rw [hm6, cert_94]
  norm_num [edge]
  <;> ring

private theorem cert_106 : count (rows.drop 26) (bag 0 0 0 0 0 94) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 94).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 26 = 6 :: rows.drop 27 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 94).erase 6 = (bag 0 0 0 0 0 93) := by decide +kernel
  rw [hm6, cert_93]
  norm_num [edge]
  <;> ring

private theorem cert_107 : count (rows.drop 27) (bag 0 0 0 0 0 93) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 93).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 27 = 6 :: rows.drop 28 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 93).erase 6 = (bag 0 0 0 0 0 92) := by decide +kernel
  rw [hm6, cert_92]
  norm_num [edge]
  <;> ring

private theorem cert_108 : count (rows.drop 28) (bag 0 0 0 0 0 92) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 92).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 28 = 6 :: rows.drop 29 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 92).erase 6 = (bag 0 0 0 0 0 91) := by decide +kernel
  rw [hm6, cert_91]
  norm_num [edge]
  <;> ring

private theorem cert_109 : count (rows.drop 29) (bag 0 0 0 0 0 91) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 91).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 29 = 6 :: rows.drop 30 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 91).erase 6 = (bag 0 0 0 0 0 90) := by decide +kernel
  rw [hm6, cert_90]
  norm_num [edge]
  <;> ring

private theorem cert_110 : count (rows.drop 30) (bag 0 0 0 0 0 90) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 90).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 30 = 6 :: rows.drop 31 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 90).erase 6 = (bag 0 0 0 0 0 89) := by decide +kernel
  rw [hm6, cert_89]
  norm_num [edge]
  <;> ring

private theorem cert_111 : count (rows.drop 31) (bag 0 0 0 0 0 89) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 89).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 31 = 6 :: rows.drop 32 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 89).erase 6 = (bag 0 0 0 0 0 88) := by decide +kernel
  rw [hm6, cert_88]
  norm_num [edge]
  <;> ring

private theorem cert_112 : count (rows.drop 32) (bag 0 0 0 0 0 88) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 88).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 32 = 6 :: rows.drop 33 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 88).erase 6 = (bag 0 0 0 0 0 87) := by decide +kernel
  rw [hm6, cert_87]
  norm_num [edge]
  <;> ring

private theorem cert_113 : count (rows.drop 33) (bag 0 0 0 0 0 87) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 87).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 33 = 6 :: rows.drop 34 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 87).erase 6 = (bag 0 0 0 0 0 86) := by decide +kernel
  rw [hm6, cert_86]
  norm_num [edge]
  <;> ring

private theorem cert_114 : count (rows.drop 34) (bag 0 0 0 0 0 86) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 86).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 34 = 6 :: rows.drop 35 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 86).erase 6 = (bag 0 0 0 0 0 85) := by decide +kernel
  rw [hm6, cert_85]
  norm_num [edge]
  <;> ring

private theorem cert_115 : count (rows.drop 35) (bag 0 0 0 0 0 85) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 85).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 35 = 6 :: rows.drop 36 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 85).erase 6 = (bag 0 0 0 0 0 84) := by decide +kernel
  rw [hm6, cert_84]
  norm_num [edge]
  <;> ring

private theorem cert_116 : count (rows.drop 36) (bag 0 0 0 0 0 84) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 84).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 36 = 6 :: rows.drop 37 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 84).erase 6 = (bag 0 0 0 0 0 83) := by decide +kernel
  rw [hm6, cert_83]
  norm_num [edge]
  <;> ring

private theorem cert_117 : count (rows.drop 37) (bag 0 0 0 0 0 83) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 83).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 37 = 6 :: rows.drop 38 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 83).erase 6 = (bag 0 0 0 0 0 82) := by decide +kernel
  rw [hm6, cert_82]
  norm_num [edge]
  <;> ring

private theorem cert_118 : count (rows.drop 38) (bag 0 0 0 0 0 82) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 82).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 38 = 6 :: rows.drop 39 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 82).erase 6 = (bag 0 0 0 0 0 81) := by decide +kernel
  rw [hm6, cert_81]
  norm_num [edge]
  <;> ring

private theorem cert_119 : count (rows.drop 39) (bag 0 0 0 0 0 81) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 81).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 39 = 6 :: rows.drop 40 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 81).erase 6 = (bag 0 0 0 0 0 80) := by decide +kernel
  rw [hm6, cert_80]
  norm_num [edge]
  <;> ring

private theorem cert_120 : count (rows.drop 40) (bag 0 0 0 0 0 80) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 80).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 40 = 6 :: rows.drop 41 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 80).erase 6 = (bag 0 0 0 0 0 79) := by decide +kernel
  rw [hm6, cert_79]
  norm_num [edge]
  <;> ring

private theorem cert_121 : count (rows.drop 41) (bag 0 0 0 0 0 79) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 79).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 41 = 6 :: rows.drop 42 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 79).erase 6 = (bag 0 0 0 0 0 78) := by decide +kernel
  rw [hm6, cert_78]
  norm_num [edge]
  <;> ring

private theorem cert_122 : count (rows.drop 42) (bag 0 0 0 0 0 78) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 78).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 42 = 6 :: rows.drop 43 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 78).erase 6 = (bag 0 0 0 0 0 77) := by decide +kernel
  rw [hm6, cert_77]
  norm_num [edge]
  <;> ring

private theorem cert_123 : count (rows.drop 43) (bag 0 0 0 0 0 77) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 77).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 43 = 6 :: rows.drop 44 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 77).erase 6 = (bag 0 0 0 0 0 76) := by decide +kernel
  rw [hm6, cert_76]
  norm_num [edge]
  <;> ring

private theorem cert_124 : count (rows.drop 44) (bag 0 0 0 0 0 76) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 76).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 44 = 6 :: rows.drop 45 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 76).erase 6 = (bag 0 0 0 0 0 75) := by decide +kernel
  rw [hm6, cert_75]
  norm_num [edge]
  <;> ring

private theorem cert_125 : count (rows.drop 45) (bag 0 0 0 0 0 75) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 75).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 45 = 6 :: rows.drop 46 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 75).erase 6 = (bag 0 0 0 0 0 74) := by decide +kernel
  rw [hm6, cert_74]
  norm_num [edge]
  <;> ring

private theorem cert_126 : count (rows.drop 46) (bag 0 0 0 0 0 74) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 74).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 46 = 6 :: rows.drop 47 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 74).erase 6 = (bag 0 0 0 0 0 73) := by decide +kernel
  rw [hm6, cert_73]
  norm_num [edge]
  <;> ring

private theorem cert_127 : count (rows.drop 47) (bag 0 0 0 0 0 73) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 73).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 47 = 6 :: rows.drop 48 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 73).erase 6 = (bag 0 0 0 0 0 72) := by decide +kernel
  rw [hm6, cert_72]
  norm_num [edge]
  <;> ring

private theorem cert_128 : count (rows.drop 48) (bag 0 0 0 0 0 72) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 72).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 48 = 6 :: rows.drop 49 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 72).erase 6 = (bag 0 0 0 0 0 71) := by decide +kernel
  rw [hm6, cert_71]
  norm_num [edge]
  <;> ring

private theorem cert_129 : count (rows.drop 49) (bag 0 0 0 0 0 71) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 71).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 49 = 6 :: rows.drop 50 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 71).erase 6 = (bag 0 0 0 0 0 70) := by decide +kernel
  rw [hm6, cert_70]
  norm_num [edge]
  <;> ring

private theorem cert_130 : count (rows.drop 50) (bag 0 0 0 0 0 70) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 70).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 50 = 6 :: rows.drop 51 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 70).erase 6 = (bag 0 0 0 0 0 69) := by decide +kernel
  rw [hm6, cert_69]
  norm_num [edge]
  <;> ring

private theorem cert_131 : count (rows.drop 51) (bag 0 0 0 0 0 69) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 69).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 51 = 6 :: rows.drop 52 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 69).erase 6 = (bag 0 0 0 0 0 68) := by decide +kernel
  rw [hm6, cert_68]
  norm_num [edge]
  <;> ring

private theorem cert_132 : count (rows.drop 52) (bag 0 0 0 0 0 68) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 68).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 52 = 6 :: rows.drop 53 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 68).erase 6 = (bag 0 0 0 0 0 67) := by decide +kernel
  rw [hm6, cert_67]
  norm_num [edge]
  <;> ring

private theorem cert_133 : count (rows.drop 53) (bag 0 0 0 0 0 67) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 67).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 53 = 6 :: rows.drop 54 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 67).erase 6 = (bag 0 0 0 0 0 66) := by decide +kernel
  rw [hm6, cert_66]
  norm_num [edge]
  <;> ring

private theorem cert_134 : count (rows.drop 54) (bag 0 0 0 0 0 66) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 66).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 54 = 6 :: rows.drop 55 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 66).erase 6 = (bag 0 0 0 0 0 65) := by decide +kernel
  rw [hm6, cert_65]
  norm_num [edge]
  <;> ring

private theorem cert_135 : count (rows.drop 55) (bag 0 0 0 0 0 65) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 65).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 55 = 6 :: rows.drop 56 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 65).erase 6 = (bag 0 0 0 0 0 64) := by decide +kernel
  rw [hm6, cert_64]
  norm_num [edge]
  <;> ring

private theorem cert_136 : count (rows.drop 56) (bag 0 0 0 0 0 64) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 64).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 56 = 6 :: rows.drop 57 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 64).erase 6 = (bag 0 0 0 0 0 63) := by decide +kernel
  rw [hm6, cert_63]
  norm_num [edge]
  <;> ring

private theorem cert_137 : count (rows.drop 57) (bag 0 0 0 0 0 63) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 63).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 57 = 6 :: rows.drop 58 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 63).erase 6 = (bag 0 0 0 0 0 62) := by decide +kernel
  rw [hm6, cert_62]
  norm_num [edge]
  <;> ring

private theorem cert_138 : count (rows.drop 58) (bag 0 0 0 0 0 62) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 62).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 58 = 6 :: rows.drop 59 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 62).erase 6 = (bag 0 0 0 0 0 61) := by decide +kernel
  rw [hm6, cert_61]
  norm_num [edge]
  <;> ring

private theorem cert_139 : count (rows.drop 59) (bag 0 0 0 0 0 61) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 61).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 59 = 6 :: rows.drop 60 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 61).erase 6 = (bag 0 0 0 0 0 60) := by decide +kernel
  rw [hm6, cert_60]
  norm_num [edge]
  <;> ring

private theorem cert_140 : count (rows.drop 60) (bag 0 0 0 0 0 60) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 60).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 60 = 6 :: rows.drop 61 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 60).erase 6 = (bag 0 0 0 0 0 59) := by decide +kernel
  rw [hm6, cert_59]
  norm_num [edge]
  <;> ring

private theorem cert_141 : count (rows.drop 61) (bag 0 0 0 0 0 59) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 59).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 61 = 6 :: rows.drop 62 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 59).erase 6 = (bag 0 0 0 0 0 58) := by decide +kernel
  rw [hm6, cert_58]
  norm_num [edge]
  <;> ring

private theorem cert_142 : count (rows.drop 62) (bag 0 0 0 0 0 58) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 58).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 62 = 6 :: rows.drop 63 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 58).erase 6 = (bag 0 0 0 0 0 57) := by decide +kernel
  rw [hm6, cert_57]
  norm_num [edge]
  <;> ring

private theorem cert_143 : count (rows.drop 63) (bag 0 0 0 0 0 57) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 57).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 63 = 6 :: rows.drop 64 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 57).erase 6 = (bag 0 0 0 0 0 56) := by decide +kernel
  rw [hm6, cert_56]
  norm_num [edge]
  <;> ring

private theorem cert_144 : count (rows.drop 64) (bag 0 0 0 0 0 56) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 56).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 64 = 6 :: rows.drop 65 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 56).erase 6 = (bag 0 0 0 0 0 55) := by decide +kernel
  rw [hm6, cert_55]
  norm_num [edge]
  <;> ring

private theorem cert_145 : count (rows.drop 65) (bag 0 0 0 0 0 55) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 55).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 65 = 6 :: rows.drop 66 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 55).erase 6 = (bag 0 0 0 0 0 54) := by decide +kernel
  rw [hm6, cert_54]
  norm_num [edge]
  <;> ring

private theorem cert_146 : count (rows.drop 66) (bag 0 0 0 0 0 54) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 54).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 66 = 6 :: rows.drop 67 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 54).erase 6 = (bag 0 0 0 0 0 53) := by decide +kernel
  rw [hm6, cert_53]
  norm_num [edge]
  <;> ring

private theorem cert_147 : count (rows.drop 67) (bag 0 0 0 0 0 53) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 53).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 67 = 6 :: rows.drop 68 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 53).erase 6 = (bag 0 0 0 0 0 52) := by decide +kernel
  rw [hm6, cert_52]
  norm_num [edge]
  <;> ring

private theorem cert_148 : count (rows.drop 68) (bag 0 0 0 0 0 52) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 52).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 68 = 6 :: rows.drop 69 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 52).erase 6 = (bag 0 0 0 0 0 51) := by decide +kernel
  rw [hm6, cert_51]
  norm_num [edge]
  <;> ring

private theorem cert_149 : count (rows.drop 69) (bag 0 0 0 0 0 51) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 51).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 69 = 6 :: rows.drop 70 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 51).erase 6 = (bag 0 0 0 0 0 50) := by decide +kernel
  rw [hm6, cert_50]
  norm_num [edge]
  <;> ring

private theorem cert_150 : count (rows.drop 70) (bag 0 0 0 0 0 50) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 50).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 70 = 6 :: rows.drop 71 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 50).erase 6 = (bag 0 0 0 0 0 49) := by decide +kernel
  rw [hm6, cert_49]
  norm_num [edge]
  <;> ring

private theorem cert_151 : count (rows.drop 71) (bag 0 0 0 0 0 49) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 49).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 71 = 6 :: rows.drop 72 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 49).erase 6 = (bag 0 0 0 0 0 48) := by decide +kernel
  rw [hm6, cert_48]
  norm_num [edge]
  <;> ring

private theorem cert_152 : count (rows.drop 72) (bag 0 0 0 0 0 48) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 48).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 72 = 6 :: rows.drop 73 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 48).erase 6 = (bag 0 0 0 0 0 47) := by decide +kernel
  rw [hm6, cert_47]
  norm_num [edge]
  <;> ring

private theorem cert_153 : count (rows.drop 73) (bag 0 0 0 0 0 47) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 47).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 73 = 6 :: rows.drop 74 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 47).erase 6 = (bag 0 0 0 0 0 46) := by decide +kernel
  rw [hm6, cert_46]
  norm_num [edge]
  <;> ring

private theorem cert_154 : count (rows.drop 74) (bag 0 0 0 0 0 46) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 46).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 74 = 6 :: rows.drop 75 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 46).erase 6 = (bag 0 0 0 0 0 45) := by decide +kernel
  rw [hm6, cert_45]
  norm_num [edge]
  <;> ring

private theorem cert_155 : count (rows.drop 75) (bag 0 0 0 0 0 45) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 45).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 75 = 6 :: rows.drop 76 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 45).erase 6 = (bag 0 0 0 0 0 44) := by decide +kernel
  rw [hm6, cert_44]
  norm_num [edge]
  <;> ring

private theorem cert_156 : count (rows.drop 76) (bag 0 0 0 0 0 44) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 44).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 76 = 6 :: rows.drop 77 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 44).erase 6 = (bag 0 0 0 0 0 43) := by decide +kernel
  rw [hm6, cert_43]
  norm_num [edge]
  <;> ring

private theorem cert_157 : count (rows.drop 77) (bag 0 0 0 0 0 43) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 43).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 77 = 6 :: rows.drop 78 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 43).erase 6 = (bag 0 0 0 0 0 42) := by decide +kernel
  rw [hm6, cert_42]
  norm_num [edge]
  <;> ring

private theorem cert_158 : count (rows.drop 78) (bag 0 0 0 0 0 42) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 42).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 78 = 6 :: rows.drop 79 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 42).erase 6 = (bag 0 0 0 0 0 41) := by decide +kernel
  rw [hm6, cert_41]
  norm_num [edge]
  <;> ring

private theorem cert_159 : count (rows.drop 79) (bag 0 0 0 0 0 41) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 41).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 79 = 6 :: rows.drop 80 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 41).erase 6 = (bag 0 0 0 0 0 40) := by decide +kernel
  rw [hm6, cert_40]
  norm_num [edge]
  <;> ring

private theorem cert_160 : count (rows.drop 80) (bag 0 0 0 0 0 40) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 40).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 80 = 6 :: rows.drop 81 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 40).erase 6 = (bag 0 0 0 0 0 39) := by decide +kernel
  rw [hm6, cert_39]
  norm_num [edge]
  <;> ring

private theorem cert_161 : count (rows.drop 81) (bag 0 0 0 0 0 39) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 39).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 81 = 6 :: rows.drop 82 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 39).erase 6 = (bag 0 0 0 0 0 38) := by decide +kernel
  rw [hm6, cert_38]
  norm_num [edge]
  <;> ring

private theorem cert_162 : count (rows.drop 82) (bag 0 0 0 0 0 38) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 38).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 82 = 6 :: rows.drop 83 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 38).erase 6 = (bag 0 0 0 0 0 37) := by decide +kernel
  rw [hm6, cert_37]
  norm_num [edge]
  <;> ring

private theorem cert_163 : count (rows.drop 83) (bag 0 0 0 0 0 37) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 37).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 83 = 6 :: rows.drop 84 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 37).erase 6 = (bag 0 0 0 0 0 36) := by decide +kernel
  rw [hm6, cert_36]
  norm_num [edge]
  <;> ring

private theorem cert_164 : count (rows.drop 84) (bag 0 0 0 0 0 36) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 36).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 84 = 6 :: rows.drop 85 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 36).erase 6 = (bag 0 0 0 0 0 35) := by decide +kernel
  rw [hm6, cert_35]
  norm_num [edge]
  <;> ring

private theorem cert_165 : count (rows.drop 85) (bag 0 0 0 0 0 35) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 35).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 85 = 6 :: rows.drop 86 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 35).erase 6 = (bag 0 0 0 0 0 34) := by decide +kernel
  rw [hm6, cert_34]
  norm_num [edge]
  <;> ring

private theorem cert_166 : count (rows.drop 86) (bag 0 0 0 0 0 34) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 34).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 86 = 6 :: rows.drop 87 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 34).erase 6 = (bag 0 0 0 0 0 33) := by decide +kernel
  rw [hm6, cert_33]
  norm_num [edge]
  <;> ring

private theorem cert_167 : count (rows.drop 87) (bag 0 0 0 0 0 33) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 33).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 87 = 6 :: rows.drop 88 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 33).erase 6 = (bag 0 0 0 0 0 32) := by decide +kernel
  rw [hm6, cert_32]
  norm_num [edge]
  <;> ring

private theorem cert_168 : count (rows.drop 88) (bag 0 0 0 0 0 32) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 32).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 88 = 6 :: rows.drop 89 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 32).erase 6 = (bag 0 0 0 0 0 31) := by decide +kernel
  rw [hm6, cert_31]
  norm_num [edge]
  <;> ring

private theorem cert_169 : count (rows.drop 89) (bag 0 0 0 0 0 31) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 31).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 89 = 6 :: rows.drop 90 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 31).erase 6 = (bag 0 0 0 0 0 30) := by decide +kernel
  rw [hm6, cert_30]
  norm_num [edge]
  <;> ring

private theorem cert_170 : count (rows.drop 90) (bag 0 0 0 0 0 30) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 30).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 90 = 6 :: rows.drop 91 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 30).erase 6 = (bag 0 0 0 0 0 29) := by decide +kernel
  rw [hm6, cert_29]
  norm_num [edge]
  <;> ring

private theorem cert_171 : count (rows.drop 91) (bag 0 0 0 0 0 29) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 29).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 91 = 6 :: rows.drop 92 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 29).erase 6 = (bag 0 0 0 0 0 28) := by decide +kernel
  rw [hm6, cert_28]
  norm_num [edge]
  <;> ring

private theorem cert_172 : count (rows.drop 92) (bag 0 0 0 0 0 28) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 28).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 92 = 6 :: rows.drop 93 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 28).erase 6 = (bag 0 0 0 0 0 27) := by decide +kernel
  rw [hm6, cert_27]
  norm_num [edge]
  <;> ring

private theorem cert_173 : count (rows.drop 93) (bag 0 0 0 0 0 27) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 27).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 93 = 6 :: rows.drop 94 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 27).erase 6 = (bag 0 0 0 0 0 26) := by decide +kernel
  rw [hm6, cert_26]
  norm_num [edge]
  <;> ring

private theorem cert_174 : count (rows.drop 94) (bag 0 0 0 0 0 26) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 26).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 94 = 6 :: rows.drop 95 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 26).erase 6 = (bag 0 0 0 0 0 25) := by decide +kernel
  rw [hm6, cert_25]
  norm_num [edge]
  <;> ring

private theorem cert_175 : count (rows.drop 95) (bag 0 0 0 0 0 25) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 25).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 95 = 6 :: rows.drop 96 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 25).erase 6 = (bag 0 0 0 0 0 24) := by decide +kernel
  rw [hm6, cert_24]
  norm_num [edge]
  <;> ring

private theorem cert_176 : count (rows.drop 96) (bag 0 0 0 0 0 24) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 24).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 96 = 6 :: rows.drop 97 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 24).erase 6 = (bag 0 0 0 0 0 23) := by decide +kernel
  rw [hm6, cert_23]
  norm_num [edge]
  <;> ring

private theorem cert_177 : count (rows.drop 97) (bag 0 0 0 0 0 23) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 23).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 97 = 6 :: rows.drop 98 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 23).erase 6 = (bag 0 0 0 0 0 22) := by decide +kernel
  rw [hm6, cert_22]
  norm_num [edge]
  <;> ring

private theorem cert_178 : count (rows.drop 98) (bag 0 0 0 0 0 22) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 22).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 98 = 6 :: rows.drop 99 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 22).erase 6 = (bag 0 0 0 0 0 21) := by decide +kernel
  rw [hm6, cert_21]
  norm_num [edge]
  <;> ring

private theorem cert_179 : count (rows.drop 99) (bag 0 0 0 0 0 21) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 21).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 99 = 6 :: rows.drop 100 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 21).erase 6 = (bag 0 0 0 0 0 20) := by decide +kernel
  rw [hm6, cert_20]
  norm_num [edge]
  <;> ring

private theorem cert_180 : count (rows.drop 100) (bag 0 0 0 0 0 20) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 20).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 100 = 6 :: rows.drop 101 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 20).erase 6 = (bag 0 0 0 0 0 19) := by decide +kernel
  rw [hm6, cert_19]
  norm_num [edge]
  <;> ring

private theorem cert_181 : count (rows.drop 101) (bag 0 0 0 0 0 19) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 19).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 101 = 6 :: rows.drop 102 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 19).erase 6 = (bag 0 0 0 0 0 18) := by decide +kernel
  rw [hm6, cert_18]
  norm_num [edge]
  <;> ring

private theorem cert_182 : count (rows.drop 102) (bag 0 0 0 0 0 18) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 18).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 102 = 6 :: rows.drop 103 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 18).erase 6 = (bag 0 0 0 0 0 17) := by decide +kernel
  rw [hm6, cert_17]
  norm_num [edge]
  <;> ring

private theorem cert_183 : count (rows.drop 103) (bag 0 0 0 0 0 17) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 17).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 103 = 6 :: rows.drop 104 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 17).erase 6 = (bag 0 0 0 0 0 16) := by decide +kernel
  rw [hm6, cert_16]
  norm_num [edge]
  <;> ring

private theorem cert_184 : count (rows.drop 104) (bag 0 0 0 0 0 16) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 16).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 104 = 6 :: rows.drop 105 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 16).erase 6 = (bag 0 0 0 0 0 15) := by decide +kernel
  rw [hm6, cert_15]
  norm_num [edge]
  <;> ring

private theorem cert_185 : count (rows.drop 105) (bag 0 0 0 0 0 15) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 15).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 105 = 6 :: rows.drop 106 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 15).erase 6 = (bag 0 0 0 0 0 14) := by decide +kernel
  rw [hm6, cert_14]
  norm_num [edge]
  <;> ring

private theorem cert_186 : count (rows.drop 106) (bag 0 0 0 0 0 14) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 14).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 106 = 6 :: rows.drop 107 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 14).erase 6 = (bag 0 0 0 0 0 13) := by decide +kernel
  rw [hm6, cert_13]
  norm_num [edge]
  <;> ring

private theorem cert_187 : count (rows.drop 107) (bag 0 0 0 0 0 13) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 13).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 107 = 6 :: rows.drop 108 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 13).erase 6 = (bag 0 0 0 0 0 12) := by decide +kernel
  rw [hm6, cert_12]
  norm_num [edge]
  <;> ring

private theorem cert_188 : count (rows.drop 108) (bag 0 0 0 0 0 12) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 12).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 108 = 6 :: rows.drop 109 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 12).erase 6 = (bag 0 0 0 0 0 11) := by decide +kernel
  rw [hm6, cert_11]
  norm_num [edge]
  <;> ring

private theorem cert_189 : count (rows.drop 109) (bag 0 0 0 0 0 11) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 11).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 109 = 6 :: rows.drop 110 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 11).erase 6 = (bag 0 0 0 0 0 10) := by decide +kernel
  rw [hm6, cert_10]
  norm_num [edge]
  <;> ring

private theorem cert_190 : count (rows.drop 110) (bag 0 0 0 0 0 10) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 10).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 110 = 6 :: rows.drop 111 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 10).erase 6 = (bag 0 0 0 0 0 9) := by decide +kernel
  rw [hm6, cert_9]
  norm_num [edge]
  <;> ring

private theorem cert_191 : count (rows.drop 111) (bag 0 0 0 0 0 9) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 9).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 111 = 6 :: rows.drop 112 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 9).erase 6 = (bag 0 0 0 0 0 8) := by decide +kernel
  rw [hm6, cert_8]
  norm_num [edge]
  <;> ring

private theorem cert_192 : count (rows.drop 112) (bag 0 0 0 0 0 8) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 8).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 112 = 6 :: rows.drop 113 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 8).erase 6 = (bag 0 0 0 0 0 7) := by decide +kernel
  rw [hm6, cert_7]
  norm_num [edge]
  <;> ring

private theorem cert_193 : count (rows.drop 113) (bag 0 0 0 0 0 7) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 7).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 113 = 6 :: rows.drop 114 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 7).erase 6 = (bag 0 0 0 0 0 6) := by decide +kernel
  rw [hm6, cert_6]
  norm_num [edge]
  <;> ring

private theorem cert_194 : count (rows.drop 114) (bag 0 0 0 0 0 6) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 6).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 114 = 6 :: rows.drop 115 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 6).erase 6 = (bag 0 0 0 0 0 5) := by decide +kernel
  rw [hm6, cert_5]
  norm_num [edge]
  <;> ring

private theorem cert_195 : count (rows.drop 115) (bag 0 0 0 0 0 5) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 5).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 115 = 6 :: rows.drop 116 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 5).erase 6 = (bag 0 0 0 0 0 4) := by decide +kernel
  rw [hm6, cert_4]
  norm_num [edge]
  <;> ring

private theorem cert_196 : count (rows.drop 116) (bag 0 0 0 0 0 4) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 4).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 116 = 6 :: rows.drop 117 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 4).erase 6 = (bag 0 0 0 0 0 3) := by decide +kernel
  rw [hm6, cert_3]
  norm_num [edge]
  <;> ring

private theorem cert_197 : count (rows.drop 117) (bag 0 0 0 0 0 3) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 3).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 117 = 6 :: rows.drop 118 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 3).erase 6 = (bag 0 0 0 0 0 2) := by decide +kernel
  rw [hm6, cert_2]
  norm_num [edge]
  <;> ring

private theorem cert_198 : count (rows.drop 118) (bag 0 0 0 0 0 2) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 2).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 118 = 6 :: rows.drop 119 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 2).erase 6 = (bag 0 0 0 0 0 1) := by decide +kernel
  rw [hm6, cert_1]
  norm_num [edge]
  <;> ring

private theorem cert_199 : count (rows.drop 119) (bag 0 0 0 0 0 1) (some 5) =
    (X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 0 1).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {6} := by decide +kernel
  have hr : rows.drop 119 = 6 :: rows.drop 120 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm6 : (bag 0 0 0 0 0 1).erase 6 = (bag 0 0 0 0 0 0) := by decide +kernel
  rw [hm6, cert_0]
  norm_num [edge]
  <;> ring

private theorem cert_200 : count (rows.drop 120) (bag 0 0 0 0 0 0) (some 5) =
    (1 : ℕ[X]) := by
  norm_num [count, rows, bag]

private theorem cert_201 : count (rows.drop 119) (bag 0 0 0 0 1 0) (some 6) =
    (1 : ℕ[X]) := by
  have hs : (bag 0 0 0 0 1 0).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {5} := by decide +kernel
  have hr : rows.drop 119 = 6 :: rows.drop 120 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm5 : (bag 0 0 0 0 1 0).erase 5 = (bag 0 0 0 0 0 0) := by decide +kernel
  rw [hm5, cert_200]
  norm_num [edge]
  <;> ring

private theorem cert_202 : count (rows.drop 118) (bag 0 0 0 0 1 1) (some 6) =
    (1 + X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 1 1).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {5, 6} := by decide +kernel
  have hr : rows.drop 118 = 6 :: rows.drop 119 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm5 : (bag 0 0 0 0 1 1).erase 5 = (bag 0 0 0 0 0 1) := by decide +kernel
  have hm6 : (bag 0 0 0 0 1 1).erase 6 = (bag 0 0 0 0 1 0) := by decide +kernel
  rw [hm5, cert_199, hm6, cert_201]
  norm_num [edge]
  <;> ring

private theorem cert_203 : count (rows.drop 117) (bag 0 0 0 0 1 2) (some 6) =
    (1 + 2 * X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 1 2).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {5, 6} := by decide +kernel
  have hr : rows.drop 117 = 6 :: rows.drop 118 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm5 : (bag 0 0 0 0 1 2).erase 5 = (bag 0 0 0 0 0 2) := by decide +kernel
  have hm6 : (bag 0 0 0 0 1 2).erase 6 = (bag 0 0 0 0 1 1) := by decide +kernel
  rw [hm5, cert_198, hm6, cert_202]
  norm_num [edge]
  <;> ring

private theorem cert_204 : count (rows.drop 116) (bag 0 0 0 0 1 3) (some 6) =
    (1 + 3 * X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 1 3).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {5, 6} := by decide +kernel
  have hr : rows.drop 116 = 6 :: rows.drop 117 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm5 : (bag 0 0 0 0 1 3).erase 5 = (bag 0 0 0 0 0 3) := by decide +kernel
  have hm6 : (bag 0 0 0 0 1 3).erase 6 = (bag 0 0 0 0 1 2) := by decide +kernel
  rw [hm5, cert_197, hm6, cert_203]
  norm_num [edge]
  <;> ring

private theorem cert_205 : count (rows.drop 115) (bag 0 0 0 0 1 4) (some 6) =
    (1 + 4 * X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 1 4).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {5, 6} := by decide +kernel
  have hr : rows.drop 115 = 6 :: rows.drop 116 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm5 : (bag 0 0 0 0 1 4).erase 5 = (bag 0 0 0 0 0 4) := by decide +kernel
  have hm6 : (bag 0 0 0 0 1 4).erase 6 = (bag 0 0 0 0 1 3) := by decide +kernel
  rw [hm5, cert_196, hm6, cert_204]
  norm_num [edge]
  <;> ring

private theorem cert_206 : count (rows.drop 114) (bag 0 0 0 0 1 5) (some 6) =
    (1 + 5 * X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 1 5).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {5, 6} := by decide +kernel
  have hr : rows.drop 114 = 6 :: rows.drop 115 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm5 : (bag 0 0 0 0 1 5).erase 5 = (bag 0 0 0 0 0 5) := by decide +kernel
  have hm6 : (bag 0 0 0 0 1 5).erase 6 = (bag 0 0 0 0 1 4) := by decide +kernel
  rw [hm5, cert_195, hm6, cert_205]
  norm_num [edge]
  <;> ring

private theorem cert_207 : count (rows.drop 113) (bag 0 0 0 0 1 6) (some 6) =
    (1 + 6 * X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 1 6).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {5, 6} := by decide +kernel
  have hr : rows.drop 113 = 6 :: rows.drop 114 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm5 : (bag 0 0 0 0 1 6).erase 5 = (bag 0 0 0 0 0 6) := by decide +kernel
  have hm6 : (bag 0 0 0 0 1 6).erase 6 = (bag 0 0 0 0 1 5) := by decide +kernel
  rw [hm5, cert_194, hm6, cert_206]
  norm_num [edge]
  <;> ring

private theorem cert_208 : count (rows.drop 112) (bag 0 0 0 0 1 7) (some 6) =
    (1 + 7 * X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 1 7).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {5, 6} := by decide +kernel
  have hr : rows.drop 112 = 6 :: rows.drop 113 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm5 : (bag 0 0 0 0 1 7).erase 5 = (bag 0 0 0 0 0 7) := by decide +kernel
  have hm6 : (bag 0 0 0 0 1 7).erase 6 = (bag 0 0 0 0 1 6) := by decide +kernel
  rw [hm5, cert_193, hm6, cert_207]
  norm_num [edge]
  <;> ring

private theorem cert_209 : count (rows.drop 111) (bag 0 0 0 0 1 8) (some 6) =
    (1 + 8 * X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 1 8).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {5, 6} := by decide +kernel
  have hr : rows.drop 111 = 6 :: rows.drop 112 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm5 : (bag 0 0 0 0 1 8).erase 5 = (bag 0 0 0 0 0 8) := by decide +kernel
  have hm6 : (bag 0 0 0 0 1 8).erase 6 = (bag 0 0 0 0 1 7) := by decide +kernel
  rw [hm5, cert_192, hm6, cert_208]
  norm_num [edge]
  <;> ring

private theorem cert_210 : count (rows.drop 110) (bag 0 0 0 0 1 9) (some 6) =
    (1 + 9 * X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 1 9).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {5, 6} := by decide +kernel
  have hr : rows.drop 110 = 6 :: rows.drop 111 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm5 : (bag 0 0 0 0 1 9).erase 5 = (bag 0 0 0 0 0 9) := by decide +kernel
  have hm6 : (bag 0 0 0 0 1 9).erase 6 = (bag 0 0 0 0 1 8) := by decide +kernel
  rw [hm5, cert_191, hm6, cert_209]
  norm_num [edge]
  <;> ring

private theorem cert_211 : count (rows.drop 109) (bag 0 0 0 0 1 10) (some 6) =
    (1 + 10 * X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 1 10).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {5, 6} := by decide +kernel
  have hr : rows.drop 109 = 6 :: rows.drop 110 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm5 : (bag 0 0 0 0 1 10).erase 5 = (bag 0 0 0 0 0 10) := by decide +kernel
  have hm6 : (bag 0 0 0 0 1 10).erase 6 = (bag 0 0 0 0 1 9) := by decide +kernel
  rw [hm5, cert_190, hm6, cert_210]
  norm_num [edge]
  <;> ring

private theorem cert_212 : count (rows.drop 108) (bag 0 0 0 0 1 11) (some 6) =
    (1 + 11 * X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 1 11).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {5, 6} := by decide +kernel
  have hr : rows.drop 108 = 6 :: rows.drop 109 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm5 : (bag 0 0 0 0 1 11).erase 5 = (bag 0 0 0 0 0 11) := by decide +kernel
  have hm6 : (bag 0 0 0 0 1 11).erase 6 = (bag 0 0 0 0 1 10) := by decide +kernel
  rw [hm5, cert_189, hm6, cert_211]
  norm_num [edge]
  <;> ring

private theorem cert_213 : count (rows.drop 107) (bag 0 0 0 0 1 12) (some 6) =
    (1 + 12 * X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 1 12).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {5, 6} := by decide +kernel
  have hr : rows.drop 107 = 6 :: rows.drop 108 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm5 : (bag 0 0 0 0 1 12).erase 5 = (bag 0 0 0 0 0 12) := by decide +kernel
  have hm6 : (bag 0 0 0 0 1 12).erase 6 = (bag 0 0 0 0 1 11) := by decide +kernel
  rw [hm5, cert_188, hm6, cert_212]
  norm_num [edge]
  <;> ring

private theorem cert_214 : count (rows.drop 106) (bag 0 0 0 0 1 13) (some 6) =
    (1 + 13 * X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 1 13).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {5, 6} := by decide +kernel
  have hr : rows.drop 106 = 6 :: rows.drop 107 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm5 : (bag 0 0 0 0 1 13).erase 5 = (bag 0 0 0 0 0 13) := by decide +kernel
  have hm6 : (bag 0 0 0 0 1 13).erase 6 = (bag 0 0 0 0 1 12) := by decide +kernel
  rw [hm5, cert_187, hm6, cert_213]
  norm_num [edge]
  <;> ring

private theorem cert_215 : count (rows.drop 105) (bag 0 0 0 0 1 14) (some 6) =
    (1 + 14 * X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 1 14).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {5, 6} := by decide +kernel
  have hr : rows.drop 105 = 6 :: rows.drop 106 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm5 : (bag 0 0 0 0 1 14).erase 5 = (bag 0 0 0 0 0 14) := by decide +kernel
  have hm6 : (bag 0 0 0 0 1 14).erase 6 = (bag 0 0 0 0 1 13) := by decide +kernel
  rw [hm5, cert_186, hm6, cert_214]
  norm_num [edge]
  <;> ring

private theorem cert_216 : count (rows.drop 104) (bag 0 0 0 0 1 15) (some 6) =
    (1 + 15 * X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 1 15).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {5, 6} := by decide +kernel
  have hr : rows.drop 104 = 6 :: rows.drop 105 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm5 : (bag 0 0 0 0 1 15).erase 5 = (bag 0 0 0 0 0 15) := by decide +kernel
  have hm6 : (bag 0 0 0 0 1 15).erase 6 = (bag 0 0 0 0 1 14) := by decide +kernel
  rw [hm5, cert_185, hm6, cert_215]
  norm_num [edge]
  <;> ring

private theorem cert_217 : count (rows.drop 103) (bag 0 0 0 0 1 16) (some 6) =
    (1 + 16 * X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 1 16).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {5, 6} := by decide +kernel
  have hr : rows.drop 103 = 6 :: rows.drop 104 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm5 : (bag 0 0 0 0 1 16).erase 5 = (bag 0 0 0 0 0 16) := by decide +kernel
  have hm6 : (bag 0 0 0 0 1 16).erase 6 = (bag 0 0 0 0 1 15) := by decide +kernel
  rw [hm5, cert_184, hm6, cert_216]
  norm_num [edge]
  <;> ring

private theorem cert_218 : count (rows.drop 102) (bag 0 0 0 0 1 17) (some 6) =
    (1 + 17 * X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 1 17).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {5, 6} := by decide +kernel
  have hr : rows.drop 102 = 6 :: rows.drop 103 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm5 : (bag 0 0 0 0 1 17).erase 5 = (bag 0 0 0 0 0 17) := by decide +kernel
  have hm6 : (bag 0 0 0 0 1 17).erase 6 = (bag 0 0 0 0 1 16) := by decide +kernel
  rw [hm5, cert_183, hm6, cert_217]
  norm_num [edge]
  <;> ring

private theorem cert_219 : count (rows.drop 101) (bag 0 0 0 0 1 18) (some 6) =
    (1 + 18 * X : ℕ[X]) := by
  have hs : (bag 0 0 0 0 1 18).toFinset.filter (fun j => 0 < j ∧ j ≤ 6) = {5, 6} := by decide +kernel
  have hr : rows.drop 101 = 6 :: rows.drop 102 := by decide +kernel
  rw [hr, count, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  have hm5 : (bag 0 0 0 0 1 18).erase 5 = (bag 0 0 0 0 0 18) := by decide +kernel
  have hm6 : (bag 0 0 0 0 1 18).erase 6 = (bag 0 0 0 0 1 17) := by decide +kernel
  rw [hm5, cert_182, hm6, cert_218]
  norm_num [edge]
  <;> ring

end D5.S3.Combinatorics.Permutation.MultisetRookEulerianRealRootednessRefutation
