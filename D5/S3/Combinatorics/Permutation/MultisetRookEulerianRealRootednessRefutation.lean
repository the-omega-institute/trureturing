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

private theorem count_step (r : ℕ) (rows : List ℕ) (m : Multiset ℕ) (last : Option ℕ) :
    count (r :: rows) m last =
      ∑ j ∈ m.toFinset.filter (fun j => 0 < j ∧ j ≤ r),
        X ^ edge last j * count rows (m.erase j) (some j) := by rfl

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

set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

private theorem six_run (n : ℕ) (last : Option ℕ) :
    count (List.replicate n 6) (Multiset.replicate n 6) last =
      if n = 0 then 1 else X ^ edge last 6 := by
  induction n generalizing last with
  | zero => simp [count]
  | succ n ih =>
    rw [List.replicate_succ, count]
    simp only [Multiset.toFinset_replicate, Nat.succ_ne_zero, ite_false]
    norm_num only [Finset.filter_singleton, Finset.sum_singleton, Nat.reduceLT,
      Nat.le_refl, and_self, ite_true]
    rw [Multiset.replicate_succ, Multiset.erase_cons_head, ih]
    cases n <;> simp [edge]


private theorem six_mixed (n j : ℕ) (hj0 : 0 < j) (hj6 : j < 6) :
    count (List.replicate (n + 1) 6) (j ::ₘ Multiset.replicate n 6) (some 6) =
      1 + (n : ℕ[X]) * X := by
  induction n with
  | zero => simp [count, Finset.filter_singleton, edge, hj0, Nat.le_of_lt hj6, Nat.not_lt_of_ge hj6.le]
  | succ n ih =>
    have hs : ((j ::ₘ Multiset.replicate (n + 1) 6).toFinset.filter
        (fun a => 0 < a ∧ a ≤ 6)) = {j, 6} := by
      ext a
      simp only [Finset.mem_filter, Multiset.mem_toFinset, Multiset.mem_cons,
        Multiset.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
      omega
    have he : (j ::ₘ Multiset.replicate (n + 1) 6).erase 6 =
        j ::ₘ Multiset.replicate n 6 := by
      rw [Multiset.erase_cons_tail _ (by omega : j ≠ 6),
        Multiset.replicate_succ, Multiset.erase_cons_head]
    rw [List.replicate_succ, count, hs,
      Finset.sum_insert (by simp [show j ≠ 6 by omega]), Finset.sum_singleton,
      Multiset.erase_cons_head, he, six_run, ih]
    simp [edge, hj6, Nat.not_lt_of_ge hj6.le]
    ring

private theorem six_tail (n h j : ℕ) (hh : h < 6) (hj0 : 0 < j) (hj : j < 6) :
    count (List.replicate (n + 2) 6) (j ::ₘ Multiset.replicate (n + 1) 6) (some h) =
      X ^ (edge (some h) j + 1) + X + (n : ℕ[X]) * X ^ 2 := by
  have hs : ((j ::ₘ Multiset.replicate (n + 1) 6).toFinset.filter
      (fun a => 0 < a ∧ a ≤ 6)) = {j, 6} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, Multiset.mem_cons,
      Multiset.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have he : (j ::ₘ Multiset.replicate (n + 1) 6).erase 6 =
      j ::ₘ Multiset.replicate n 6 := by
    rw [Multiset.erase_cons_tail _ (by omega : j ≠ 6),
      Multiset.replicate_succ, Multiset.erase_cons_head]
  rw [show n + 2 = (n + 1) + 1 by omega, List.replicate_succ, count, hs,
    Finset.sum_insert (by simp [show j ≠ 6 by omega]), Finset.sum_singleton,
    Multiset.erase_cons_head, he, six_run, six_mixed n j hj0 hj]
  simp [edge, hj, hh, pow_succ]
  ring


private theorem count_one (rs qs : List ℕ) (m m1 : Multiset ℕ)
    (h : Option ℕ) (r j1 : ℕ) (hr : rs = r :: qs)
    (hs : m.toFinset.filter (fun j => 0 < j ∧ j ≤ r) = {j1})
    (hm1 : m.erase j1 = m1)
    (p1 : ℕ[X])
    (hp1 : count qs m1 (some j1) = p1) :
    count rs m h = X ^ edge h j1 * p1 := by
  rw [hr, count_step, hs, Finset.sum_singleton, hm1, hp1]

private theorem count_two (rs qs : List ℕ) (m m1 m2 : Multiset ℕ)
    (h : Option ℕ) (r j1 j2 : ℕ) (hr : rs = r :: qs)
    (hs : m.toFinset.filter (fun j => 0 < j ∧ j ≤ r) = {j1, j2}) (hn1 : j1 ≠ j2)
    (hm1 : m.erase j1 = m1) (hm2 : m.erase j2 = m2)
    (p1 p2 : ℕ[X])
    (hp1 : count qs m1 (some j1) = p1)
    (hp2 : count qs m2 (some j2) = p2) :
    count rs m h = X ^ edge h j1 * p1 + (X ^ edge h j2 * p2) := by
  rw [hr, count_step, hs, Finset.sum_insert (by simp [hn1]), Finset.sum_singleton, hm1, hp1, hm2, hp2]

private theorem count_three (rs qs : List ℕ) (m m1 m2 m3 : Multiset ℕ)
    (h : Option ℕ) (r j1 j2 j3 : ℕ) (hr : rs = r :: qs)
    (hs : m.toFinset.filter (fun j => 0 < j ∧ j ≤ r) = {j1, j2, j3}) (hn1 : j1 ∉ {j2, j3}) (hn2 : j2 ∉ {j3})
    (hm1 : m.erase j1 = m1) (hm2 : m.erase j2 = m2) (hm3 : m.erase j3 = m3)
    (p1 p2 p3 : ℕ[X])
    (hp1 : count qs m1 (some j1) = p1)
    (hp2 : count qs m2 (some j2) = p2)
    (hp3 : count qs m3 (some j3) = p3) :
    count rs m h = X ^ edge h j1 * p1 + (X ^ edge h j2 * p2 + (X ^ edge h j3 * p3)) := by
  rw [hr, count_step, hs, Finset.sum_insert hn1, Finset.sum_insert hn2, Finset.sum_singleton, hm1, hp1, hm2, hp2, hm3, hp3]

private theorem count_four (rs qs : List ℕ) (m m1 m2 m3 m4 : Multiset ℕ)
    (h : Option ℕ) (r j1 j2 j3 j4 : ℕ) (hr : rs = r :: qs)
    (hs : m.toFinset.filter (fun j => 0 < j ∧ j ≤ r) = {j1, j2, j3, j4}) (hn1 : j1 ∉ {j2, j3, j4}) (hn2 : j2 ∉ {j3, j4}) (hn3 : j3 ∉ {j4})
    (hm1 : m.erase j1 = m1) (hm2 : m.erase j2 = m2) (hm3 : m.erase j3 = m3) (hm4 : m.erase j4 = m4)
    (p1 p2 p3 p4 : ℕ[X])
    (hp1 : count qs m1 (some j1) = p1)
    (hp2 : count qs m2 (some j2) = p2)
    (hp3 : count qs m3 (some j3) = p3)
    (hp4 : count qs m4 (some j4) = p4) :
    count rs m h = X ^ edge h j1 * p1 + (X ^ edge h j2 * p2 + (X ^ edge h j3 * p3 + (X ^ edge h j4 * p4))) := by
  rw [hr, count_step, hs, Finset.sum_insert hn1, Finset.sum_insert hn2, Finset.sum_insert hn3, Finset.sum_singleton, hm1, hp1, hm2, hp2, hm3, hp3, hm4, hp4]

attribute [irreducible] count

private theorem cert_0 : count (rows.drop 19) (bag 0 0 0 0 1 100) (some 4) =
    (X + 100 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (5 ::ₘ Multiset.replicate 100 6) (some 4) = _
  rw [six_tail 99 4 5 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_1 : count (rows.drop 19) (bag 0 0 0 1 0 100) (some 5) =
    (2 * X + 99 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (4 ::ₘ Multiset.replicate 100 6) (some 5) = _
  rw [six_tail 99 5 4 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_2 : count (rows.drop 18) (bag 0 0 0 1 1 100) (some 4) =
    (X + 102 * X ^ 2 + 99 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 0 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {4, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm4 : (bag 0 0 0 1 1 100).erase 4 = (bag 0 0 0 0 1 100) := by rfl
  have hm5 : (bag 0 0 0 1 1 100).erase 5 = (bag 0 0 0 1 0 100) := by rfl
  have hc := count_two (rows.drop 18) (rows.drop 19) (bag 0 0 0 1 1 100) (bag 0 0 0 0 1 100) (bag 0 0 0 1 0 100) (some 4) 5 4 5 hr hs (by decide) hm4 hm5 _ _ cert_0 cert_1
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_3 : count (rows.drop 19) (bag 0 0 0 1 0 100) (some 4) =
    (2 * X + 99 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (4 ::ₘ Multiset.replicate 100 6) (some 4) = _
  rw [six_tail 99 4 4 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_4 : count (rows.drop 18) (bag 0 0 0 2 0 100) (some 5) =
    (2 * X + 99 * X ^ 2 : ℕ[X]) := by
  have hs : (bag 0 0 0 2 0 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm4 : (bag 0 0 0 2 0 100).erase 4 = (bag 0 0 0 1 0 100) := by rfl
  have hc := count_one (rows.drop 18) (rows.drop 19) (bag 0 0 0 2 0 100) (bag 0 0 0 1 0 100) (some 5) 5 4 hr hs hm4 _ cert_3
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_5 : count (rows.drop 17) (bag 0 0 0 2 1 100) (some 4) =
    (X + 104 * X ^ 2 + 198 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 0 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {4, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm4 : (bag 0 0 0 2 1 100).erase 4 = (bag 0 0 0 1 1 100) := by rfl
  have hm5 : (bag 0 0 0 2 1 100).erase 5 = (bag 0 0 0 2 0 100) := by rfl
  have hc := count_two (rows.drop 17) (rows.drop 18) (bag 0 0 0 2 1 100) (bag 0 0 0 1 1 100) (bag 0 0 0 2 0 100) (some 4) 5 4 5 hr hs (by decide) hm4 hm5 _ _ cert_2 cert_4
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_6 : count (rows.drop 16) (bag 0 0 0 3 1 100) (some 4) =
    (X + 104 * X ^ 2 + 198 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 0 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm4 : (bag 0 0 0 3 1 100).erase 4 = (bag 0 0 0 2 1 100) := by rfl
  have hc := count_one (rows.drop 16) (rows.drop 17) (bag 0 0 0 3 1 100) (bag 0 0 0 2 1 100) (some 4) 4 4 hr hs hm4 _ cert_5
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_7 : count (rows.drop 15) (bag 0 0 0 4 1 100) (some 4) =
    (X + 104 * X ^ 2 + 198 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 0 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm4 : (bag 0 0 0 4 1 100).erase 4 = (bag 0 0 0 3 1 100) := by rfl
  have hc := count_one (rows.drop 15) (rows.drop 16) (bag 0 0 0 4 1 100) (bag 0 0 0 3 1 100) (some 4) 4 4 hr hs hm4 _ cert_6
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_8 : count (rows.drop 14) (bag 0 0 0 5 1 100) (some 4) =
    (X + 104 * X ^ 2 + 198 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 0 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm4 : (bag 0 0 0 5 1 100).erase 4 = (bag 0 0 0 4 1 100) := by rfl
  have hc := count_one (rows.drop 14) (rows.drop 15) (bag 0 0 0 5 1 100) (bag 0 0 0 4 1 100) (some 4) 4 4 hr hs hm4 _ cert_7
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_9 : count (rows.drop 13) (bag 0 0 0 6 1 100) (some 4) =
    (X + 104 * X ^ 2 + 198 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 0 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm4 : (bag 0 0 0 6 1 100).erase 4 = (bag 0 0 0 5 1 100) := by rfl
  have hc := count_one (rows.drop 13) (rows.drop 14) (bag 0 0 0 6 1 100) (bag 0 0 0 5 1 100) (some 4) 4 4 hr hs hm4 _ cert_8
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_10 : count (rows.drop 12) (bag 0 0 0 7 1 100) (some 4) =
    (X + 104 * X ^ 2 + 198 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 0 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm4 : (bag 0 0 0 7 1 100).erase 4 = (bag 0 0 0 6 1 100) := by rfl
  have hc := count_one (rows.drop 12) (rows.drop 13) (bag 0 0 0 7 1 100) (bag 0 0 0 6 1 100) (some 4) 4 4 hr hs hm4 _ cert_9
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_11 : count (rows.drop 11) (bag 0 0 0 8 1 100) (some 3) =
    (X ^ 2 + 104 * X ^ 3 + 198 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 0 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm4 : (bag 0 0 0 8 1 100).erase 4 = (bag 0 0 0 7 1 100) := by rfl
  have hc := count_one (rows.drop 11) (rows.drop 12) (bag 0 0 0 8 1 100) (bag 0 0 0 7 1 100) (some 3) 4 4 hr hs hm4 _ cert_10
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_12 : count (rows.drop 12) (bag 0 0 0 7 1 100) (some 3) =
    (X ^ 2 + 104 * X ^ 3 + 198 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm4 : (bag 0 0 0 7 1 100).erase 4 = (bag 0 0 0 6 1 100) := by rfl
  have hc := count_one (rows.drop 12) (rows.drop 13) (bag 0 0 0 7 1 100) (bag 0 0 0 6 1 100) (some 3) 4 4 hr hs hm4 _ cert_9
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_13 : count (rows.drop 13) (bag 0 0 0 6 1 100) (some 3) =
    (X ^ 2 + 104 * X ^ 3 + 198 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm4 : (bag 0 0 0 6 1 100).erase 4 = (bag 0 0 0 5 1 100) := by rfl
  have hc := count_one (rows.drop 13) (rows.drop 14) (bag 0 0 0 6 1 100) (bag 0 0 0 5 1 100) (some 3) 4 4 hr hs hm4 _ cert_8
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_14 : count (rows.drop 14) (bag 0 0 0 5 1 100) (some 3) =
    (X ^ 2 + 104 * X ^ 3 + 198 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm4 : (bag 0 0 0 5 1 100).erase 4 = (bag 0 0 0 4 1 100) := by rfl
  have hc := count_one (rows.drop 14) (rows.drop 15) (bag 0 0 0 5 1 100) (bag 0 0 0 4 1 100) (some 3) 4 4 hr hs hm4 _ cert_7
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_15 : count (rows.drop 15) (bag 0 0 0 4 1 100) (some 3) =
    (X ^ 2 + 104 * X ^ 3 + 198 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm4 : (bag 0 0 0 4 1 100).erase 4 = (bag 0 0 0 3 1 100) := by rfl
  have hc := count_one (rows.drop 15) (rows.drop 16) (bag 0 0 0 4 1 100) (bag 0 0 0 3 1 100) (some 3) 4 4 hr hs hm4 _ cert_6
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_16 : count (rows.drop 16) (bag 0 0 0 3 1 100) (some 3) =
    (X ^ 2 + 104 * X ^ 3 + 198 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm4 : (bag 0 0 0 3 1 100).erase 4 = (bag 0 0 0 2 1 100) := by rfl
  have hc := count_one (rows.drop 16) (rows.drop 17) (bag 0 0 0 3 1 100) (bag 0 0 0 2 1 100) (some 3) 4 4 hr hs hm4 _ cert_5
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_17 : count (rows.drop 17) (bag 0 0 0 2 1 100) (some 3) =
    (3 * X ^ 2 + 201 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {4, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm4 : (bag 0 0 0 2 1 100).erase 4 = (bag 0 0 0 1 1 100) := by rfl
  have hm5 : (bag 0 0 0 2 1 100).erase 5 = (bag 0 0 0 2 0 100) := by rfl
  have hc := count_two (rows.drop 17) (rows.drop 18) (bag 0 0 0 2 1 100) (bag 0 0 0 1 1 100) (bag 0 0 0 2 0 100) (some 3) 5 4 5 hr hs (by decide) hm4 hm5 _ _ cert_2 cert_4
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_18 : count (rows.drop 18) (bag 0 0 0 1 1 100) (some 3) =
    (3 * X ^ 2 + 199 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 0 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {4, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm4 : (bag 0 0 0 1 1 100).erase 4 = (bag 0 0 0 0 1 100) := by rfl
  have hm5 : (bag 0 0 0 1 1 100).erase 5 = (bag 0 0 0 1 0 100) := by rfl
  have hc := count_two (rows.drop 18) (rows.drop 19) (bag 0 0 0 1 1 100) (bag 0 0 0 0 1 100) (bag 0 0 0 1 0 100) (some 3) 5 4 5 hr hs (by decide) hm4 hm5 _ _ cert_0 cert_1
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_19 : count (rows.drop 19) (bag 0 0 0 0 1 100) (some 3) =
    (X + 100 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (5 ::ₘ Multiset.replicate 100 6) (some 3) = _
  rw [six_tail 99 3 5 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_20 : count (rows.drop 19) (bag 0 0 1 0 0 100) (some 5) =
    (2 * X + 99 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (3 ::ₘ Multiset.replicate 100 6) (some 5) = _
  rw [six_tail 99 5 3 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_21 : count (rows.drop 18) (bag 0 0 1 0 1 100) (some 4) =
    (X + 102 * X ^ 2 + 99 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 0 1 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {3, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm3 : (bag 0 0 1 0 1 100).erase 3 = (bag 0 0 0 0 1 100) := by rfl
  have hm5 : (bag 0 0 1 0 1 100).erase 5 = (bag 0 0 1 0 0 100) := by rfl
  have hc := count_two (rows.drop 18) (rows.drop 19) (bag 0 0 1 0 1 100) (bag 0 0 0 0 1 100) (bag 0 0 1 0 0 100) (some 4) 5 3 5 hr hs (by decide) hm3 hm5 _ _ cert_19 cert_20
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_22 : count (rows.drop 19) (bag 0 0 0 1 0 100) (some 3) =
    (X + 100 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (4 ::ₘ Multiset.replicate 100 6) (some 3) = _
  rw [six_tail 99 3 4 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_23 : count (rows.drop 19) (bag 0 0 1 0 0 100) (some 4) =
    (2 * X + 99 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (3 ::ₘ Multiset.replicate 100 6) (some 4) = _
  rw [six_tail 99 4 3 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_24 : count (rows.drop 18) (bag 0 0 1 1 0 100) (some 5) =
    (3 * X + 199 * X ^ 2 : ℕ[X]) := by
  have hs : (bag 0 0 1 1 0 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm3 : (bag 0 0 1 1 0 100).erase 3 = (bag 0 0 0 1 0 100) := by rfl
  have hm4 : (bag 0 0 1 1 0 100).erase 4 = (bag 0 0 1 0 0 100) := by rfl
  have hc := count_two (rows.drop 18) (rows.drop 19) (bag 0 0 1 1 0 100) (bag 0 0 0 1 0 100) (bag 0 0 1 0 0 100) (some 5) 5 3 4 hr hs (by decide) hm3 hm4 _ _ cert_22 cert_23
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_25 : count (rows.drop 17) (bag 0 0 1 1 1 100) (some 4) =
    (X + 108 * X ^ 2 + 497 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 0 1 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {3, 4, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm3 : (bag 0 0 1 1 1 100).erase 3 = (bag 0 0 0 1 1 100) := by rfl
  have hm4 : (bag 0 0 1 1 1 100).erase 4 = (bag 0 0 1 0 1 100) := by rfl
  have hm5 : (bag 0 0 1 1 1 100).erase 5 = (bag 0 0 1 1 0 100) := by rfl
  have hc := count_three (rows.drop 17) (rows.drop 18) (bag 0 0 1 1 1 100) (bag 0 0 0 1 1 100) (bag 0 0 1 0 1 100) (bag 0 0 1 1 0 100) (some 4) 5 3 4 5 hr hs (by decide) (by decide) hm3 hm4 hm5 _ _ _ cert_18 cert_21 cert_24
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_26 : count (rows.drop 16) (bag 0 0 1 2 1 100) (some 4) =
    (X + 111 * X ^ 2 + 698 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 1 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm3 : (bag 0 0 1 2 1 100).erase 3 = (bag 0 0 0 2 1 100) := by rfl
  have hm4 : (bag 0 0 1 2 1 100).erase 4 = (bag 0 0 1 1 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 0 0 1 2 1 100) (bag 0 0 0 2 1 100) (bag 0 0 1 1 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_17 cert_25
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_27 : count (rows.drop 15) (bag 0 0 1 3 1 100) (some 4) =
    (X + 112 * X ^ 2 + 802 * X ^ 3 + 297 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 1 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm3 : (bag 0 0 1 3 1 100).erase 3 = (bag 0 0 0 3 1 100) := by rfl
  have hm4 : (bag 0 0 1 3 1 100).erase 4 = (bag 0 0 1 2 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 0 0 1 3 1 100) (bag 0 0 0 3 1 100) (bag 0 0 1 2 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_16 cert_26
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_28 : count (rows.drop 14) (bag 0 0 1 4 1 100) (some 4) =
    (X + 113 * X ^ 2 + 906 * X ^ 3 + 495 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 1 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm3 : (bag 0 0 1 4 1 100).erase 3 = (bag 0 0 0 4 1 100) := by rfl
  have hm4 : (bag 0 0 1 4 1 100).erase 4 = (bag 0 0 1 3 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 0 0 1 4 1 100) (bag 0 0 0 4 1 100) (bag 0 0 1 3 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_15 cert_27
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_29 : count (rows.drop 13) (bag 0 0 1 5 1 100) (some 4) =
    (X + 114 * X ^ 2 + 1010 * X ^ 3 + 693 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 1 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm3 : (bag 0 0 1 5 1 100).erase 3 = (bag 0 0 0 5 1 100) := by rfl
  have hm4 : (bag 0 0 1 5 1 100).erase 4 = (bag 0 0 1 4 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 0 0 1 5 1 100) (bag 0 0 0 5 1 100) (bag 0 0 1 4 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_14 cert_28
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_30 : count (rows.drop 12) (bag 0 0 1 6 1 100) (some 4) =
    (X + 115 * X ^ 2 + 1114 * X ^ 3 + 891 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 1 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm3 : (bag 0 0 1 6 1 100).erase 3 = (bag 0 0 0 6 1 100) := by rfl
  have hm4 : (bag 0 0 1 6 1 100).erase 4 = (bag 0 0 1 5 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 0 0 1 6 1 100) (bag 0 0 0 6 1 100) (bag 0 0 1 5 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_13 cert_29
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_31 : count (rows.drop 11) (bag 0 0 1 7 1 100) (some 4) =
    (X + 116 * X ^ 2 + 1218 * X ^ 3 + 1089 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 1 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm3 : (bag 0 0 1 7 1 100).erase 3 = (bag 0 0 0 7 1 100) := by rfl
  have hm4 : (bag 0 0 1 7 1 100).erase 4 = (bag 0 0 1 6 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 0 0 1 7 1 100) (bag 0 0 0 7 1 100) (bag 0 0 1 6 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_12 cert_30
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_32 : count (rows.drop 10) (bag 0 0 1 8 1 100) (some 3) =
    (2 * X ^ 2 + 220 * X ^ 3 + 1416 * X ^ 4 + 1089 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 1 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm3 : (bag 0 0 1 8 1 100).erase 3 = (bag 0 0 0 8 1 100) := by rfl
  have hm4 : (bag 0 0 1 8 1 100).erase 4 = (bag 0 0 1 7 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 0 0 1 8 1 100) (bag 0 0 0 8 1 100) (bag 0 0 1 7 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_11 cert_31
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_33 : count (rows.drop 11) (bag 0 0 1 7 1 100) (some 3) =
    (2 * X ^ 2 + 219 * X ^ 3 + 1312 * X ^ 4 + 891 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 1 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm3 : (bag 0 0 1 7 1 100).erase 3 = (bag 0 0 0 7 1 100) := by rfl
  have hm4 : (bag 0 0 1 7 1 100).erase 4 = (bag 0 0 1 6 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 0 0 1 7 1 100) (bag 0 0 0 7 1 100) (bag 0 0 1 6 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_12 cert_30
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_34 : count (rows.drop 12) (bag 0 0 1 6 1 100) (some 3) =
    (2 * X ^ 2 + 218 * X ^ 3 + 1208 * X ^ 4 + 693 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 1 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm3 : (bag 0 0 1 6 1 100).erase 3 = (bag 0 0 0 6 1 100) := by rfl
  have hm4 : (bag 0 0 1 6 1 100).erase 4 = (bag 0 0 1 5 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 0 0 1 6 1 100) (bag 0 0 0 6 1 100) (bag 0 0 1 5 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_13 cert_29
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_35 : count (rows.drop 13) (bag 0 0 1 5 1 100) (some 3) =
    (2 * X ^ 2 + 217 * X ^ 3 + 1104 * X ^ 4 + 495 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 1 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm3 : (bag 0 0 1 5 1 100).erase 3 = (bag 0 0 0 5 1 100) := by rfl
  have hm4 : (bag 0 0 1 5 1 100).erase 4 = (bag 0 0 1 4 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 0 0 1 5 1 100) (bag 0 0 0 5 1 100) (bag 0 0 1 4 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_14 cert_28
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_36 : count (rows.drop 14) (bag 0 0 1 4 1 100) (some 3) =
    (2 * X ^ 2 + 216 * X ^ 3 + 1000 * X ^ 4 + 297 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 1 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm3 : (bag 0 0 1 4 1 100).erase 3 = (bag 0 0 0 4 1 100) := by rfl
  have hm4 : (bag 0 0 1 4 1 100).erase 4 = (bag 0 0 1 3 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 0 0 1 4 1 100) (bag 0 0 0 4 1 100) (bag 0 0 1 3 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_15 cert_27
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_37 : count (rows.drop 15) (bag 0 0 1 3 1 100) (some 3) =
    (2 * X ^ 2 + 215 * X ^ 3 + 896 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 1 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm3 : (bag 0 0 1 3 1 100).erase 3 = (bag 0 0 0 3 1 100) := by rfl
  have hm4 : (bag 0 0 1 3 1 100).erase 4 = (bag 0 0 1 2 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 0 0 1 3 1 100) (bag 0 0 0 3 1 100) (bag 0 0 1 2 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_16 cert_26
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_38 : count (rows.drop 16) (bag 0 0 1 2 1 100) (some 3) =
    (4 * X ^ 2 + 309 * X ^ 3 + 596 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 1 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm3 : (bag 0 0 1 2 1 100).erase 3 = (bag 0 0 0 2 1 100) := by rfl
  have hm4 : (bag 0 0 1 2 1 100).erase 4 = (bag 0 0 1 1 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 0 0 1 2 1 100) (bag 0 0 0 2 1 100) (bag 0 0 1 1 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_17 cert_25
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_39 : count (rows.drop 17) (bag 0 0 1 1 1 100) (some 3) =
    (7 * X ^ 2 + 500 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 1 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {3, 4, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm3 : (bag 0 0 1 1 1 100).erase 3 = (bag 0 0 0 1 1 100) := by rfl
  have hm4 : (bag 0 0 1 1 1 100).erase 4 = (bag 0 0 1 0 1 100) := by rfl
  have hm5 : (bag 0 0 1 1 1 100).erase 5 = (bag 0 0 1 1 0 100) := by rfl
  have hc := count_three (rows.drop 17) (rows.drop 18) (bag 0 0 1 1 1 100) (bag 0 0 0 1 1 100) (bag 0 0 1 0 1 100) (bag 0 0 1 1 0 100) (some 3) 5 3 4 5 hr hs (by decide) (by decide) hm3 hm4 hm5 _ _ _ cert_18 cert_21 cert_24
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_40 : count (rows.drop 18) (bag 0 0 1 0 1 100) (some 3) =
    (X + 102 * X ^ 2 + 99 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 0 1 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {3, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm3 : (bag 0 0 1 0 1 100).erase 3 = (bag 0 0 0 0 1 100) := by rfl
  have hm5 : (bag 0 0 1 0 1 100).erase 5 = (bag 0 0 1 0 0 100) := by rfl
  have hc := count_two (rows.drop 18) (rows.drop 19) (bag 0 0 1 0 1 100) (bag 0 0 0 0 1 100) (bag 0 0 1 0 0 100) (some 3) 5 3 5 hr hs (by decide) hm3 hm5 _ _ cert_19 cert_20
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_41 : count (rows.drop 19) (bag 0 0 1 0 0 100) (some 3) =
    (2 * X + 99 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (3 ::ₘ Multiset.replicate 100 6) (some 3) = _
  rw [six_tail 99 3 3 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_42 : count (rows.drop 18) (bag 0 0 2 0 0 100) (some 5) =
    (2 * X + 99 * X ^ 2 : ℕ[X]) := by
  have hs : (bag 0 0 2 0 0 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm3 : (bag 0 0 2 0 0 100).erase 3 = (bag 0 0 1 0 0 100) := by rfl
  have hc := count_one (rows.drop 18) (rows.drop 19) (bag 0 0 2 0 0 100) (bag 0 0 1 0 0 100) (some 5) 5 3 hr hs hm3 _ cert_41
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_43 : count (rows.drop 17) (bag 0 0 2 0 1 100) (some 4) =
    (X + 104 * X ^ 2 + 198 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 0 2 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {3, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm3 : (bag 0 0 2 0 1 100).erase 3 = (bag 0 0 1 0 1 100) := by rfl
  have hm5 : (bag 0 0 2 0 1 100).erase 5 = (bag 0 0 2 0 0 100) := by rfl
  have hc := count_two (rows.drop 17) (rows.drop 18) (bag 0 0 2 0 1 100) (bag 0 0 1 0 1 100) (bag 0 0 2 0 0 100) (some 4) 5 3 5 hr hs (by decide) hm3 hm5 _ _ cert_40 cert_42
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_44 : count (rows.drop 16) (bag 0 0 2 1 1 100) (some 4) =
    (X + 111 * X ^ 2 + 698 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 2 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm3 : (bag 0 0 2 1 1 100).erase 3 = (bag 0 0 1 1 1 100) := by rfl
  have hm4 : (bag 0 0 2 1 1 100).erase 4 = (bag 0 0 2 0 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 0 0 2 1 1 100) (bag 0 0 1 1 1 100) (bag 0 0 2 0 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_39 cert_43
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_45 : count (rows.drop 15) (bag 0 0 2 2 1 100) (some 4) =
    (X + 115 * X ^ 2 + 1007 * X ^ 3 + 695 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 2 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm3 : (bag 0 0 2 2 1 100).erase 3 = (bag 0 0 1 2 1 100) := by rfl
  have hm4 : (bag 0 0 2 2 1 100).erase 4 = (bag 0 0 2 1 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 0 0 2 2 1 100) (bag 0 0 1 2 1 100) (bag 0 0 2 1 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_38 cert_44
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_46 : count (rows.drop 14) (bag 0 0 2 3 1 100) (some 4) =
    (X + 117 * X ^ 2 + 1222 * X ^ 3 + 1591 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 2 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm3 : (bag 0 0 2 3 1 100).erase 3 = (bag 0 0 1 3 1 100) := by rfl
  have hm4 : (bag 0 0 2 3 1 100).erase 4 = (bag 0 0 2 2 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 0 0 2 3 1 100) (bag 0 0 1 3 1 100) (bag 0 0 2 2 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_37 cert_45
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_47 : count (rows.drop 13) (bag 0 0 2 4 1 100) (some 4) =
    (X + 119 * X ^ 2 + 1438 * X ^ 3 + 2591 * X ^ 4 + 396 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 2 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm3 : (bag 0 0 2 4 1 100).erase 3 = (bag 0 0 1 4 1 100) := by rfl
  have hm4 : (bag 0 0 2 4 1 100).erase 4 = (bag 0 0 2 3 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 0 0 2 4 1 100) (bag 0 0 1 4 1 100) (bag 0 0 2 3 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_36 cert_46
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_48 : count (rows.drop 12) (bag 0 0 2 5 1 100) (some 4) =
    (X + 121 * X ^ 2 + 1655 * X ^ 3 + 3695 * X ^ 4 + 891 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 2 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm3 : (bag 0 0 2 5 1 100).erase 3 = (bag 0 0 1 5 1 100) := by rfl
  have hm4 : (bag 0 0 2 5 1 100).erase 4 = (bag 0 0 2 4 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 0 0 2 5 1 100) (bag 0 0 1 5 1 100) (bag 0 0 2 4 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_35 cert_47
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_49 : count (rows.drop 11) (bag 0 0 2 6 1 100) (some 4) =
    (X + 123 * X ^ 2 + 1873 * X ^ 3 + 4903 * X ^ 4 + 1584 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 2 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm3 : (bag 0 0 2 6 1 100).erase 3 = (bag 0 0 1 6 1 100) := by rfl
  have hm4 : (bag 0 0 2 6 1 100).erase 4 = (bag 0 0 2 5 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 0 0 2 6 1 100) (bag 0 0 1 6 1 100) (bag 0 0 2 5 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_34 cert_48
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_50 : count (rows.drop 10) (bag 0 0 2 7 1 100) (some 4) =
    (X + 125 * X ^ 2 + 2092 * X ^ 3 + 6215 * X ^ 4 + 2475 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 2 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm3 : (bag 0 0 2 7 1 100).erase 3 = (bag 0 0 1 7 1 100) := by rfl
  have hm4 : (bag 0 0 2 7 1 100).erase 4 = (bag 0 0 2 6 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 0 0 2 7 1 100) (bag 0 0 1 7 1 100) (bag 0 0 2 6 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_33 cert_49
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_51 : count (rows.drop 9) (bag 0 0 2 8 1 100) (some 3) =
    (3 * X ^ 2 + 345 * X ^ 3 + 3508 * X ^ 4 + 7304 * X ^ 5 + 2475 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 2 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm3 : (bag 0 0 2 8 1 100).erase 3 = (bag 0 0 1 8 1 100) := by rfl
  have hm4 : (bag 0 0 2 8 1 100).erase 4 = (bag 0 0 2 7 1 100) := by rfl
  have hc := count_two (rows.drop 9) (rows.drop 10) (bag 0 0 2 8 1 100) (bag 0 0 1 8 1 100) (bag 0 0 2 7 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_32 cert_50
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_52 : count (rows.drop 10) (bag 0 0 2 7 1 100) (some 3) =
    (3 * X ^ 2 + 342 * X ^ 3 + 3185 * X ^ 4 + 5794 * X ^ 5 + 1584 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 2 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm3 : (bag 0 0 2 7 1 100).erase 3 = (bag 0 0 1 7 1 100) := by rfl
  have hm4 : (bag 0 0 2 7 1 100).erase 4 = (bag 0 0 2 6 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 0 0 2 7 1 100) (bag 0 0 1 7 1 100) (bag 0 0 2 6 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_33 cert_49
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_53 : count (rows.drop 11) (bag 0 0 2 6 1 100) (some 3) =
    (3 * X ^ 2 + 339 * X ^ 3 + 2863 * X ^ 4 + 4388 * X ^ 5 + 891 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 2 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm3 : (bag 0 0 2 6 1 100).erase 3 = (bag 0 0 1 6 1 100) := by rfl
  have hm4 : (bag 0 0 2 6 1 100).erase 4 = (bag 0 0 2 5 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 0 0 2 6 1 100) (bag 0 0 1 6 1 100) (bag 0 0 2 5 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_34 cert_48
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_54 : count (rows.drop 12) (bag 0 0 2 5 1 100) (some 3) =
    (3 * X ^ 2 + 336 * X ^ 3 + 2542 * X ^ 4 + 3086 * X ^ 5 + 396 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 2 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm3 : (bag 0 0 2 5 1 100).erase 3 = (bag 0 0 1 5 1 100) := by rfl
  have hm4 : (bag 0 0 2 5 1 100).erase 4 = (bag 0 0 2 4 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 0 0 2 5 1 100) (bag 0 0 1 5 1 100) (bag 0 0 2 4 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_35 cert_47
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_55 : count (rows.drop 13) (bag 0 0 2 4 1 100) (some 3) =
    (3 * X ^ 2 + 333 * X ^ 3 + 2222 * X ^ 4 + 1888 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 2 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm3 : (bag 0 0 2 4 1 100).erase 3 = (bag 0 0 1 4 1 100) := by rfl
  have hm4 : (bag 0 0 2 4 1 100).erase 4 = (bag 0 0 2 3 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 0 0 2 4 1 100) (bag 0 0 1 4 1 100) (bag 0 0 2 3 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_36 cert_46
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_56 : count (rows.drop 14) (bag 0 0 2 3 1 100) (some 3) =
    (3 * X ^ 2 + 330 * X ^ 3 + 1903 * X ^ 4 + 794 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 2 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm3 : (bag 0 0 2 3 1 100).erase 3 = (bag 0 0 1 3 1 100) := by rfl
  have hm4 : (bag 0 0 2 3 1 100).erase 4 = (bag 0 0 2 2 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 0 0 2 3 1 100) (bag 0 0 1 3 1 100) (bag 0 0 2 2 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_37 cert_45
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_57 : count (rows.drop 15) (bag 0 0 2 2 1 100) (some 3) =
    (5 * X ^ 2 + 420 * X ^ 3 + 1294 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 2 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm3 : (bag 0 0 2 2 1 100).erase 3 = (bag 0 0 1 2 1 100) := by rfl
  have hm4 : (bag 0 0 2 2 1 100).erase 4 = (bag 0 0 2 1 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 0 0 2 2 1 100) (bag 0 0 1 2 1 100) (bag 0 0 2 1 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_38 cert_44
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_58 : count (rows.drop 16) (bag 0 0 2 1 1 100) (some 3) =
    (8 * X ^ 2 + 604 * X ^ 3 + 297 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 2 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm3 : (bag 0 0 2 1 1 100).erase 3 = (bag 0 0 1 1 1 100) := by rfl
  have hm4 : (bag 0 0 2 1 1 100).erase 4 = (bag 0 0 2 0 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 0 0 2 1 1 100) (bag 0 0 1 1 1 100) (bag 0 0 2 0 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_39 cert_43
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_59 : count (rows.drop 17) (bag 0 0 2 0 1 100) (some 3) =
    (X + 104 * X ^ 2 + 198 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 0 2 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {3, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm3 : (bag 0 0 2 0 1 100).erase 3 = (bag 0 0 1 0 1 100) := by rfl
  have hm5 : (bag 0 0 2 0 1 100).erase 5 = (bag 0 0 2 0 0 100) := by rfl
  have hc := count_two (rows.drop 17) (rows.drop 18) (bag 0 0 2 0 1 100) (bag 0 0 1 0 1 100) (bag 0 0 2 0 0 100) (some 3) 5 3 5 hr hs (by decide) hm3 hm5 _ _ cert_40 cert_42
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_60 : count (rows.drop 16) (bag 0 0 3 0 1 100) (some 4) =
    (X + 104 * X ^ 2 + 198 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 0 3 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm3 : (bag 0 0 3 0 1 100).erase 3 = (bag 0 0 2 0 1 100) := by rfl
  have hc := count_one (rows.drop 16) (rows.drop 17) (bag 0 0 3 0 1 100) (bag 0 0 2 0 1 100) (some 4) 4 3 hr hs hm3 _ cert_59
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_61 : count (rows.drop 15) (bag 0 0 3 1 1 100) (some 4) =
    (X + 112 * X ^ 2 + 802 * X ^ 3 + 297 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 3 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm3 : (bag 0 0 3 1 1 100).erase 3 = (bag 0 0 2 1 1 100) := by rfl
  have hm4 : (bag 0 0 3 1 1 100).erase 4 = (bag 0 0 3 0 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 0 0 3 1 1 100) (bag 0 0 2 1 1 100) (bag 0 0 3 0 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_58 cert_60
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_62 : count (rows.drop 14) (bag 0 0 3 2 1 100) (some 4) =
    (X + 117 * X ^ 2 + 1222 * X ^ 3 + 1591 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 3 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm3 : (bag 0 0 3 2 1 100).erase 3 = (bag 0 0 2 2 1 100) := by rfl
  have hm4 : (bag 0 0 3 2 1 100).erase 4 = (bag 0 0 3 1 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 0 0 3 2 1 100) (bag 0 0 2 2 1 100) (bag 0 0 3 1 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_57 cert_61
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_63 : count (rows.drop 13) (bag 0 0 3 3 1 100) (some 4) =
    (X + 120 * X ^ 2 + 1552 * X ^ 3 + 3494 * X ^ 4 + 893 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 3 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm3 : (bag 0 0 3 3 1 100).erase 3 = (bag 0 0 2 3 1 100) := by rfl
  have hm4 : (bag 0 0 3 3 1 100).erase 4 = (bag 0 0 3 2 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 0 0 3 3 1 100) (bag 0 0 2 3 1 100) (bag 0 0 3 2 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_56 cert_62
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_64 : count (rows.drop 12) (bag 0 0 3 4 1 100) (some 4) =
    (X + 123 * X ^ 2 + 1885 * X ^ 3 + 5716 * X ^ 4 + 2781 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 3 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm3 : (bag 0 0 3 4 1 100).erase 3 = (bag 0 0 2 4 1 100) := by rfl
  have hm4 : (bag 0 0 3 4 1 100).erase 4 = (bag 0 0 3 3 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 0 0 3 4 1 100) (bag 0 0 2 4 1 100) (bag 0 0 3 3 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_55 cert_63
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_65 : count (rows.drop 11) (bag 0 0 3 5 1 100) (some 4) =
    (X + 126 * X ^ 2 + 2221 * X ^ 3 + 8258 * X ^ 4 + 5867 * X ^ 5 + 495 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 3 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm3 : (bag 0 0 3 5 1 100).erase 3 = (bag 0 0 2 5 1 100) := by rfl
  have hm4 : (bag 0 0 3 5 1 100).erase 4 = (bag 0 0 3 4 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 0 0 3 5 1 100) (bag 0 0 2 5 1 100) (bag 0 0 3 4 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_54 cert_64
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_66 : count (rows.drop 10) (bag 0 0 3 6 1 100) (some 4) =
    (X + 129 * X ^ 2 + 2560 * X ^ 3 + 11121 * X ^ 4 + 10255 * X ^ 5 + 1386 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 3 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm3 : (bag 0 0 3 6 1 100).erase 3 = (bag 0 0 2 6 1 100) := by rfl
  have hm4 : (bag 0 0 3 6 1 100).erase 4 = (bag 0 0 3 5 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 0 0 3 6 1 100) (bag 0 0 2 6 1 100) (bag 0 0 3 5 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_53 cert_65
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_67 : count (rows.drop 9) (bag 0 0 3 7 1 100) (some 4) =
    (X + 132 * X ^ 2 + 2902 * X ^ 3 + 14306 * X ^ 4 + 16049 * X ^ 5 + 2970 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 3 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm3 : (bag 0 0 3 7 1 100).erase 3 = (bag 0 0 2 7 1 100) := by rfl
  have hm4 : (bag 0 0 3 7 1 100).erase 4 = (bag 0 0 3 6 1 100) := by rfl
  have hc := count_two (rows.drop 9) (rows.drop 10) (bag 0 0 3 7 1 100) (bag 0 0 2 7 1 100) (bag 0 0 3 6 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_52 cert_66
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_68 : count (rows.drop 8) (bag 0 0 3 8 1 100) (some 3) =
    (4 * X ^ 2 + 477 * X ^ 3 + 6410 * X ^ 4 + 21610 * X ^ 5 + 18524 * X ^ 6 + 2970 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 0 3 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm3 : (bag 0 0 3 8 1 100).erase 3 = (bag 0 0 2 8 1 100) := by rfl
  have hm4 : (bag 0 0 3 8 1 100).erase 4 = (bag 0 0 3 7 1 100) := by rfl
  have hc := count_two (rows.drop 8) (rows.drop 9) (bag 0 0 3 8 1 100) (bag 0 0 2 8 1 100) (bag 0 0 3 7 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_51 cert_67
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_69 : count (rows.drop 9) (bag 0 0 3 7 1 100) (some 3) =
    (4 * X ^ 2 + 471 * X ^ 3 + 5745 * X ^ 4 + 16915 * X ^ 5 + 11839 * X ^ 6 + 1386 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 0 3 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm3 : (bag 0 0 3 7 1 100).erase 3 = (bag 0 0 2 7 1 100) := by rfl
  have hm4 : (bag 0 0 3 7 1 100).erase 4 = (bag 0 0 3 6 1 100) := by rfl
  have hc := count_two (rows.drop 9) (rows.drop 10) (bag 0 0 3 7 1 100) (bag 0 0 2 7 1 100) (bag 0 0 3 6 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_52 cert_66
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_70 : count (rows.drop 10) (bag 0 0 3 6 1 100) (some 3) =
    (4 * X ^ 2 + 465 * X ^ 3 + 5084 * X ^ 4 + 12646 * X ^ 5 + 6758 * X ^ 6 + 495 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 0 3 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm3 : (bag 0 0 3 6 1 100).erase 3 = (bag 0 0 2 6 1 100) := by rfl
  have hm4 : (bag 0 0 3 6 1 100).erase 4 = (bag 0 0 3 5 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 0 0 3 6 1 100) (bag 0 0 2 6 1 100) (bag 0 0 3 5 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_53 cert_65
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_71 : count (rows.drop 11) (bag 0 0 3 5 1 100) (some 3) =
    (4 * X ^ 2 + 459 * X ^ 3 + 4427 * X ^ 4 + 8802 * X ^ 5 + 3177 * X ^ 6 + 99 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 0 3 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm3 : (bag 0 0 3 5 1 100).erase 3 = (bag 0 0 2 5 1 100) := by rfl
  have hm4 : (bag 0 0 3 5 1 100).erase 4 = (bag 0 0 3 4 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 0 0 3 5 1 100) (bag 0 0 2 5 1 100) (bag 0 0 3 4 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_54 cert_64
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_72 : count (rows.drop 12) (bag 0 0 3 4 1 100) (some 3) =
    (4 * X ^ 2 + 453 * X ^ 3 + 3774 * X ^ 4 + 5382 * X ^ 5 + 992 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 3 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm3 : (bag 0 0 3 4 1 100).erase 3 = (bag 0 0 2 4 1 100) := by rfl
  have hm4 : (bag 0 0 3 4 1 100).erase 4 = (bag 0 0 3 3 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 0 0 3 4 1 100) (bag 0 0 2 4 1 100) (bag 0 0 3 3 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_55 cert_63
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_73 : count (rows.drop 13) (bag 0 0 3 3 1 100) (some 3) =
    (4 * X ^ 2 + 447 * X ^ 3 + 3125 * X ^ 4 + 2385 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 3 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm3 : (bag 0 0 3 3 1 100).erase 3 = (bag 0 0 2 3 1 100) := by rfl
  have hm4 : (bag 0 0 3 3 1 100).erase 4 = (bag 0 0 3 2 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 0 0 3 3 1 100) (bag 0 0 2 3 1 100) (bag 0 0 3 2 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_56 cert_62
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_74 : count (rows.drop 14) (bag 0 0 3 2 1 100) (some 3) =
    (6 * X ^ 2 + 532 * X ^ 3 + 2096 * X ^ 4 + 396 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 3 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm3 : (bag 0 0 3 2 1 100).erase 3 = (bag 0 0 2 2 1 100) := by rfl
  have hm4 : (bag 0 0 3 2 1 100).erase 4 = (bag 0 0 3 1 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 0 0 3 2 1 100) (bag 0 0 2 2 1 100) (bag 0 0 3 1 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_57 cert_61
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_75 : count (rows.drop 15) (bag 0 0 3 1 1 100) (some 3) =
    (9 * X ^ 2 + 708 * X ^ 3 + 495 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 3 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm3 : (bag 0 0 3 1 1 100).erase 3 = (bag 0 0 2 1 1 100) := by rfl
  have hm4 : (bag 0 0 3 1 1 100).erase 4 = (bag 0 0 3 0 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 0 0 3 1 1 100) (bag 0 0 2 1 1 100) (bag 0 0 3 0 1 100) (some 3) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_58 cert_60
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_76 : count (rows.drop 16) (bag 0 0 3 0 1 100) (some 3) =
    (X + 104 * X ^ 2 + 198 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 0 3 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm3 : (bag 0 0 3 0 1 100).erase 3 = (bag 0 0 2 0 1 100) := by rfl
  have hc := count_one (rows.drop 16) (rows.drop 17) (bag 0 0 3 0 1 100) (bag 0 0 2 0 1 100) (some 3) 4 3 hr hs hm3 _ cert_59
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_77 : count (rows.drop 15) (bag 0 0 4 0 1 100) (some 4) =
    (X + 104 * X ^ 2 + 198 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 0 4 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm3 : (bag 0 0 4 0 1 100).erase 3 = (bag 0 0 3 0 1 100) := by rfl
  have hc := count_one (rows.drop 15) (rows.drop 16) (bag 0 0 4 0 1 100) (bag 0 0 3 0 1 100) (some 4) 4 3 hr hs hm3 _ cert_76
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_78 : count (rows.drop 14) (bag 0 0 4 1 1 100) (some 4) =
    (X + 113 * X ^ 2 + 906 * X ^ 3 + 495 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 4 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm3 : (bag 0 0 4 1 1 100).erase 3 = (bag 0 0 3 1 1 100) := by rfl
  have hm4 : (bag 0 0 4 1 1 100).erase 4 = (bag 0 0 4 0 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 0 0 4 1 1 100) (bag 0 0 3 1 1 100) (bag 0 0 4 0 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_75 cert_77
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_79 : count (rows.drop 13) (bag 0 0 4 2 1 100) (some 4) =
    (X + 119 * X ^ 2 + 1438 * X ^ 3 + 2591 * X ^ 4 + 396 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 4 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm3 : (bag 0 0 4 2 1 100).erase 3 = (bag 0 0 3 2 1 100) := by rfl
  have hm4 : (bag 0 0 4 2 1 100).erase 4 = (bag 0 0 4 1 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 0 0 4 2 1 100) (bag 0 0 3 2 1 100) (bag 0 0 4 1 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_74 cert_78
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_80 : count (rows.drop 12) (bag 0 0 4 3 1 100) (some 4) =
    (X + 123 * X ^ 2 + 1885 * X ^ 3 + 5716 * X ^ 4 + 2781 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 4 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm3 : (bag 0 0 4 3 1 100).erase 3 = (bag 0 0 3 3 1 100) := by rfl
  have hm4 : (bag 0 0 4 3 1 100).erase 4 = (bag 0 0 4 2 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 0 0 4 3 1 100) (bag 0 0 3 3 1 100) (bag 0 0 4 2 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_73 cert_79
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_81 : count (rows.drop 11) (bag 0 0 4 4 1 100) (some 4) =
    (X + 127 * X ^ 2 + 2338 * X ^ 3 + 9490 * X ^ 4 + 8163 * X ^ 5 + 1091 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 4 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm3 : (bag 0 0 4 4 1 100).erase 3 = (bag 0 0 3 4 1 100) := by rfl
  have hm4 : (bag 0 0 4 4 1 100).erase 4 = (bag 0 0 4 3 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 0 0 4 4 1 100) (bag 0 0 3 4 1 100) (bag 0 0 4 3 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_72 cert_80
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_82 : count (rows.drop 10) (bag 0 0 4 5 1 100) (some 4) =
    (X + 131 * X ^ 2 + 2797 * X ^ 3 + 13917 * X ^ 4 + 16965 * X ^ 5 + 4268 * X ^ 6 + 99 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 0 4 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm3 : (bag 0 0 4 5 1 100).erase 3 = (bag 0 0 3 5 1 100) := by rfl
  have hm4 : (bag 0 0 4 5 1 100).erase 4 = (bag 0 0 4 4 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 0 0 4 5 1 100) (bag 0 0 3 5 1 100) (bag 0 0 4 4 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_71 cert_81
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_83 : count (rows.drop 9) (bag 0 0 4 6 1 100) (some 4) =
    (X + 135 * X ^ 2 + 3262 * X ^ 3 + 19001 * X ^ 4 + 29611 * X ^ 5 + 11026 * X ^ 6 + 594 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 0 4 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm3 : (bag 0 0 4 6 1 100).erase 3 = (bag 0 0 3 6 1 100) := by rfl
  have hm4 : (bag 0 0 4 6 1 100).erase 4 = (bag 0 0 4 5 1 100) := by rfl
  have hc := count_two (rows.drop 9) (rows.drop 10) (bag 0 0 4 6 1 100) (bag 0 0 3 6 1 100) (bag 0 0 4 5 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_70 cert_82
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_84 : count (rows.drop 8) (bag 0 0 4 7 1 100) (some 4) =
    (X + 139 * X ^ 2 + 3733 * X ^ 3 + 24746 * X ^ 4 + 46526 * X ^ 5 + 22865 * X ^ 6 + 1980 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 0 4 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm3 : (bag 0 0 4 7 1 100).erase 3 = (bag 0 0 3 7 1 100) := by rfl
  have hm4 : (bag 0 0 4 7 1 100).erase 4 = (bag 0 0 4 6 1 100) := by rfl
  have hc := count_two (rows.drop 8) (rows.drop 9) (bag 0 0 4 7 1 100) (bag 0 0 3 7 1 100) (bag 0 0 4 6 1 100) (some 4) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_69 cert_83
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_85 : count (rows.drop 7) (bag 0 0 4 8 1 100) (some 2) =
    (X ^ 2 + 143 * X ^ 3 + 4210 * X ^ 4 + 31156 * X ^ 5 + 68136 * X ^ 6 + 41389 * X ^ 7 + 4950 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 0 0 4 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 7 = 4 :: rows.drop 8 := by rfl
  have hm3 : (bag 0 0 4 8 1 100).erase 3 = (bag 0 0 3 8 1 100) := by rfl
  have hm4 : (bag 0 0 4 8 1 100).erase 4 = (bag 0 0 4 7 1 100) := by rfl
  have hc := count_two (rows.drop 7) (rows.drop 8) (bag 0 0 4 8 1 100) (bag 0 0 3 8 1 100) (bag 0 0 4 7 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_68 cert_84
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_86 : count (rows.drop 8) (bag 0 0 3 8 1 100) (some 2) =
    (X ^ 2 + 135 * X ^ 3 + 3247 * X ^ 4 + 17814 * X ^ 5 + 23353 * X ^ 6 + 5445 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 0 3 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm3 : (bag 0 0 3 8 1 100).erase 3 = (bag 0 0 2 8 1 100) := by rfl
  have hm4 : (bag 0 0 3 8 1 100).erase 4 = (bag 0 0 3 7 1 100) := by rfl
  have hc := count_two (rows.drop 8) (rows.drop 9) (bag 0 0 3 8 1 100) (bag 0 0 2 8 1 100) (bag 0 0 3 7 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_51 cert_67
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_87 : count (rows.drop 9) (bag 0 0 2 8 1 100) (some 2) =
    (X ^ 2 + 127 * X ^ 3 + 2312 * X ^ 4 + 7631 * X ^ 5 + 3564 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 2 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm3 : (bag 0 0 2 8 1 100).erase 3 = (bag 0 0 1 8 1 100) := by rfl
  have hm4 : (bag 0 0 2 8 1 100).erase 4 = (bag 0 0 2 7 1 100) := by rfl
  have hc := count_two (rows.drop 9) (rows.drop 10) (bag 0 0 2 8 1 100) (bag 0 0 1 8 1 100) (bag 0 0 2 7 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_32 cert_50
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_88 : count (rows.drop 10) (bag 0 0 1 8 1 100) (some 2) =
    (X ^ 2 + 117 * X ^ 3 + 1322 * X ^ 4 + 1287 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 1 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm3 : (bag 0 0 1 8 1 100).erase 3 = (bag 0 0 0 8 1 100) := by rfl
  have hm4 : (bag 0 0 1 8 1 100).erase 4 = (bag 0 0 1 7 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 0 0 1 8 1 100) (bag 0 0 0 8 1 100) (bag 0 0 1 7 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_11 cert_31
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_89 : count (rows.drop 11) (bag 0 0 0 8 1 100) (some 2) =
    (X ^ 2 + 104 * X ^ 3 + 198 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 0 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm4 : (bag 0 0 0 8 1 100).erase 4 = (bag 0 0 0 7 1 100) := by rfl
  have hc := count_one (rows.drop 11) (rows.drop 12) (bag 0 0 0 8 1 100) (bag 0 0 0 7 1 100) (some 2) 4 4 hr hs hm4 _ cert_10
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_90 : count (rows.drop 12) (bag 0 0 0 7 1 100) (some 2) =
    (X ^ 2 + 104 * X ^ 3 + 198 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm4 : (bag 0 0 0 7 1 100).erase 4 = (bag 0 0 0 6 1 100) := by rfl
  have hc := count_one (rows.drop 12) (rows.drop 13) (bag 0 0 0 7 1 100) (bag 0 0 0 6 1 100) (some 2) 4 4 hr hs hm4 _ cert_9
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_91 : count (rows.drop 13) (bag 0 0 0 6 1 100) (some 2) =
    (X ^ 2 + 104 * X ^ 3 + 198 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm4 : (bag 0 0 0 6 1 100).erase 4 = (bag 0 0 0 5 1 100) := by rfl
  have hc := count_one (rows.drop 13) (rows.drop 14) (bag 0 0 0 6 1 100) (bag 0 0 0 5 1 100) (some 2) 4 4 hr hs hm4 _ cert_8
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_92 : count (rows.drop 14) (bag 0 0 0 5 1 100) (some 2) =
    (X ^ 2 + 104 * X ^ 3 + 198 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm4 : (bag 0 0 0 5 1 100).erase 4 = (bag 0 0 0 4 1 100) := by rfl
  have hc := count_one (rows.drop 14) (rows.drop 15) (bag 0 0 0 5 1 100) (bag 0 0 0 4 1 100) (some 2) 4 4 hr hs hm4 _ cert_7
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_93 : count (rows.drop 15) (bag 0 0 0 4 1 100) (some 2) =
    (X ^ 2 + 104 * X ^ 3 + 198 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm4 : (bag 0 0 0 4 1 100).erase 4 = (bag 0 0 0 3 1 100) := by rfl
  have hc := count_one (rows.drop 15) (rows.drop 16) (bag 0 0 0 4 1 100) (bag 0 0 0 3 1 100) (some 2) 4 4 hr hs hm4 _ cert_6
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_94 : count (rows.drop 16) (bag 0 0 0 3 1 100) (some 2) =
    (X ^ 2 + 104 * X ^ 3 + 198 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm4 : (bag 0 0 0 3 1 100).erase 4 = (bag 0 0 0 2 1 100) := by rfl
  have hc := count_one (rows.drop 16) (rows.drop 17) (bag 0 0 0 3 1 100) (bag 0 0 0 2 1 100) (some 2) 4 4 hr hs hm4 _ cert_5
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_95 : count (rows.drop 17) (bag 0 0 0 2 1 100) (some 2) =
    (3 * X ^ 2 + 201 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {4, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm4 : (bag 0 0 0 2 1 100).erase 4 = (bag 0 0 0 1 1 100) := by rfl
  have hm5 : (bag 0 0 0 2 1 100).erase 5 = (bag 0 0 0 2 0 100) := by rfl
  have hc := count_two (rows.drop 17) (rows.drop 18) (bag 0 0 0 2 1 100) (bag 0 0 0 1 1 100) (bag 0 0 0 2 0 100) (some 2) 5 4 5 hr hs (by decide) hm4 hm5 _ _ cert_2 cert_4
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_96 : count (rows.drop 18) (bag 0 0 0 1 1 100) (some 2) =
    (3 * X ^ 2 + 199 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 0 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {4, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm4 : (bag 0 0 0 1 1 100).erase 4 = (bag 0 0 0 0 1 100) := by rfl
  have hm5 : (bag 0 0 0 1 1 100).erase 5 = (bag 0 0 0 1 0 100) := by rfl
  have hc := count_two (rows.drop 18) (rows.drop 19) (bag 0 0 0 1 1 100) (bag 0 0 0 0 1 100) (bag 0 0 0 1 0 100) (some 2) 5 4 5 hr hs (by decide) hm4 hm5 _ _ cert_0 cert_1
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_97 : count (rows.drop 19) (bag 0 0 0 0 1 100) (some 2) =
    (X + 100 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (5 ::ₘ Multiset.replicate 100 6) (some 2) = _
  rw [six_tail 99 2 5 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_98 : count (rows.drop 19) (bag 0 1 0 0 0 100) (some 5) =
    (2 * X + 99 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (2 ::ₘ Multiset.replicate 100 6) (some 5) = _
  rw [six_tail 99 5 2 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_99 : count (rows.drop 18) (bag 0 1 0 0 1 100) (some 4) =
    (X + 102 * X ^ 2 + 99 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 1 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {2, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm2 : (bag 0 1 0 0 1 100).erase 2 = (bag 0 0 0 0 1 100) := by rfl
  have hm5 : (bag 0 1 0 0 1 100).erase 5 = (bag 0 1 0 0 0 100) := by rfl
  have hc := count_two (rows.drop 18) (rows.drop 19) (bag 0 1 0 0 1 100) (bag 0 0 0 0 1 100) (bag 0 1 0 0 0 100) (some 4) 5 2 5 hr hs (by decide) hm2 hm5 _ _ cert_97 cert_98
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_100 : count (rows.drop 19) (bag 0 0 0 1 0 100) (some 2) =
    (X + 100 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (4 ::ₘ Multiset.replicate 100 6) (some 2) = _
  rw [six_tail 99 2 4 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_101 : count (rows.drop 19) (bag 0 1 0 0 0 100) (some 4) =
    (2 * X + 99 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (2 ::ₘ Multiset.replicate 100 6) (some 4) = _
  rw [six_tail 99 4 2 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_102 : count (rows.drop 18) (bag 0 1 0 1 0 100) (some 5) =
    (3 * X + 199 * X ^ 2 : ℕ[X]) := by
  have hs : (bag 0 1 0 1 0 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm2 : (bag 0 1 0 1 0 100).erase 2 = (bag 0 0 0 1 0 100) := by rfl
  have hm4 : (bag 0 1 0 1 0 100).erase 4 = (bag 0 1 0 0 0 100) := by rfl
  have hc := count_two (rows.drop 18) (rows.drop 19) (bag 0 1 0 1 0 100) (bag 0 0 0 1 0 100) (bag 0 1 0 0 0 100) (some 5) 5 2 4 hr hs (by decide) hm2 hm4 _ _ cert_100 cert_101
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_103 : count (rows.drop 17) (bag 0 1 0 1 1 100) (some 4) =
    (X + 108 * X ^ 2 + 497 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 1 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {2, 4, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm2 : (bag 0 1 0 1 1 100).erase 2 = (bag 0 0 0 1 1 100) := by rfl
  have hm4 : (bag 0 1 0 1 1 100).erase 4 = (bag 0 1 0 0 1 100) := by rfl
  have hm5 : (bag 0 1 0 1 1 100).erase 5 = (bag 0 1 0 1 0 100) := by rfl
  have hc := count_three (rows.drop 17) (rows.drop 18) (bag 0 1 0 1 1 100) (bag 0 0 0 1 1 100) (bag 0 1 0 0 1 100) (bag 0 1 0 1 0 100) (some 4) 5 2 4 5 hr hs (by decide) (by decide) hm2 hm4 hm5 _ _ _ cert_96 cert_99 cert_102
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_104 : count (rows.drop 16) (bag 0 1 0 2 1 100) (some 4) =
    (X + 111 * X ^ 2 + 698 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 1 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm2 : (bag 0 1 0 2 1 100).erase 2 = (bag 0 0 0 2 1 100) := by rfl
  have hm4 : (bag 0 1 0 2 1 100).erase 4 = (bag 0 1 0 1 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 0 1 0 2 1 100) (bag 0 0 0 2 1 100) (bag 0 1 0 1 1 100) (some 4) 4 2 4 hr hs (by decide) hm2 hm4 _ _ cert_95 cert_103
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_105 : count (rows.drop 15) (bag 0 1 0 3 1 100) (some 4) =
    (X + 112 * X ^ 2 + 802 * X ^ 3 + 297 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 1 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm2 : (bag 0 1 0 3 1 100).erase 2 = (bag 0 0 0 3 1 100) := by rfl
  have hm4 : (bag 0 1 0 3 1 100).erase 4 = (bag 0 1 0 2 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 0 1 0 3 1 100) (bag 0 0 0 3 1 100) (bag 0 1 0 2 1 100) (some 4) 4 2 4 hr hs (by decide) hm2 hm4 _ _ cert_94 cert_104
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_106 : count (rows.drop 14) (bag 0 1 0 4 1 100) (some 4) =
    (X + 113 * X ^ 2 + 906 * X ^ 3 + 495 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 1 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm2 : (bag 0 1 0 4 1 100).erase 2 = (bag 0 0 0 4 1 100) := by rfl
  have hm4 : (bag 0 1 0 4 1 100).erase 4 = (bag 0 1 0 3 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 0 1 0 4 1 100) (bag 0 0 0 4 1 100) (bag 0 1 0 3 1 100) (some 4) 4 2 4 hr hs (by decide) hm2 hm4 _ _ cert_93 cert_105
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_107 : count (rows.drop 13) (bag 0 1 0 5 1 100) (some 4) =
    (X + 114 * X ^ 2 + 1010 * X ^ 3 + 693 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 1 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm2 : (bag 0 1 0 5 1 100).erase 2 = (bag 0 0 0 5 1 100) := by rfl
  have hm4 : (bag 0 1 0 5 1 100).erase 4 = (bag 0 1 0 4 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 0 1 0 5 1 100) (bag 0 0 0 5 1 100) (bag 0 1 0 4 1 100) (some 4) 4 2 4 hr hs (by decide) hm2 hm4 _ _ cert_92 cert_106
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_108 : count (rows.drop 12) (bag 0 1 0 6 1 100) (some 4) =
    (X + 115 * X ^ 2 + 1114 * X ^ 3 + 891 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 1 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm2 : (bag 0 1 0 6 1 100).erase 2 = (bag 0 0 0 6 1 100) := by rfl
  have hm4 : (bag 0 1 0 6 1 100).erase 4 = (bag 0 1 0 5 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 0 1 0 6 1 100) (bag 0 0 0 6 1 100) (bag 0 1 0 5 1 100) (some 4) 4 2 4 hr hs (by decide) hm2 hm4 _ _ cert_91 cert_107
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_109 : count (rows.drop 11) (bag 0 1 0 7 1 100) (some 4) =
    (X + 116 * X ^ 2 + 1218 * X ^ 3 + 1089 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 1 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm2 : (bag 0 1 0 7 1 100).erase 2 = (bag 0 0 0 7 1 100) := by rfl
  have hm4 : (bag 0 1 0 7 1 100).erase 4 = (bag 0 1 0 6 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 0 1 0 7 1 100) (bag 0 0 0 7 1 100) (bag 0 1 0 6 1 100) (some 4) 4 2 4 hr hs (by decide) hm2 hm4 _ _ cert_90 cert_108
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_110 : count (rows.drop 10) (bag 0 1 0 8 1 100) (some 3) =
    (2 * X ^ 2 + 220 * X ^ 3 + 1416 * X ^ 4 + 1089 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 0 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm2 : (bag 0 1 0 8 1 100).erase 2 = (bag 0 0 0 8 1 100) := by rfl
  have hm4 : (bag 0 1 0 8 1 100).erase 4 = (bag 0 1 0 7 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 0 1 0 8 1 100) (bag 0 0 0 8 1 100) (bag 0 1 0 7 1 100) (some 3) 4 2 4 hr hs (by decide) hm2 hm4 _ _ cert_89 cert_109
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_111 : count (rows.drop 11) (bag 0 0 1 7 1 100) (some 2) =
    (X ^ 2 + 116 * X ^ 3 + 1218 * X ^ 4 + 1089 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 1 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm3 : (bag 0 0 1 7 1 100).erase 3 = (bag 0 0 0 7 1 100) := by rfl
  have hm4 : (bag 0 0 1 7 1 100).erase 4 = (bag 0 0 1 6 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 0 0 1 7 1 100) (bag 0 0 0 7 1 100) (bag 0 0 1 6 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_12 cert_30
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_112 : count (rows.drop 11) (bag 0 1 0 7 1 100) (some 3) =
    (2 * X ^ 2 + 219 * X ^ 3 + 1312 * X ^ 4 + 891 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm2 : (bag 0 1 0 7 1 100).erase 2 = (bag 0 0 0 7 1 100) := by rfl
  have hm4 : (bag 0 1 0 7 1 100).erase 4 = (bag 0 1 0 6 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 0 1 0 7 1 100) (bag 0 0 0 7 1 100) (bag 0 1 0 6 1 100) (some 3) 4 2 4 hr hs (by decide) hm2 hm4 _ _ cert_90 cert_108
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_113 : count (rows.drop 12) (bag 0 0 1 6 1 100) (some 2) =
    (X ^ 2 + 115 * X ^ 3 + 1114 * X ^ 4 + 891 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 1 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm3 : (bag 0 0 1 6 1 100).erase 3 = (bag 0 0 0 6 1 100) := by rfl
  have hm4 : (bag 0 0 1 6 1 100).erase 4 = (bag 0 0 1 5 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 0 0 1 6 1 100) (bag 0 0 0 6 1 100) (bag 0 0 1 5 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_13 cert_29
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_114 : count (rows.drop 12) (bag 0 1 0 6 1 100) (some 3) =
    (2 * X ^ 2 + 218 * X ^ 3 + 1208 * X ^ 4 + 693 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm2 : (bag 0 1 0 6 1 100).erase 2 = (bag 0 0 0 6 1 100) := by rfl
  have hm4 : (bag 0 1 0 6 1 100).erase 4 = (bag 0 1 0 5 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 0 1 0 6 1 100) (bag 0 0 0 6 1 100) (bag 0 1 0 5 1 100) (some 3) 4 2 4 hr hs (by decide) hm2 hm4 _ _ cert_91 cert_107
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_115 : count (rows.drop 13) (bag 0 0 1 5 1 100) (some 2) =
    (X ^ 2 + 114 * X ^ 3 + 1010 * X ^ 4 + 693 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 1 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm3 : (bag 0 0 1 5 1 100).erase 3 = (bag 0 0 0 5 1 100) := by rfl
  have hm4 : (bag 0 0 1 5 1 100).erase 4 = (bag 0 0 1 4 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 0 0 1 5 1 100) (bag 0 0 0 5 1 100) (bag 0 0 1 4 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_14 cert_28
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_116 : count (rows.drop 13) (bag 0 1 0 5 1 100) (some 3) =
    (2 * X ^ 2 + 217 * X ^ 3 + 1104 * X ^ 4 + 495 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm2 : (bag 0 1 0 5 1 100).erase 2 = (bag 0 0 0 5 1 100) := by rfl
  have hm4 : (bag 0 1 0 5 1 100).erase 4 = (bag 0 1 0 4 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 0 1 0 5 1 100) (bag 0 0 0 5 1 100) (bag 0 1 0 4 1 100) (some 3) 4 2 4 hr hs (by decide) hm2 hm4 _ _ cert_92 cert_106
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_117 : count (rows.drop 14) (bag 0 0 1 4 1 100) (some 2) =
    (X ^ 2 + 113 * X ^ 3 + 906 * X ^ 4 + 495 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 1 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm3 : (bag 0 0 1 4 1 100).erase 3 = (bag 0 0 0 4 1 100) := by rfl
  have hm4 : (bag 0 0 1 4 1 100).erase 4 = (bag 0 0 1 3 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 0 0 1 4 1 100) (bag 0 0 0 4 1 100) (bag 0 0 1 3 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_15 cert_27
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_118 : count (rows.drop 14) (bag 0 1 0 4 1 100) (some 3) =
    (2 * X ^ 2 + 216 * X ^ 3 + 1000 * X ^ 4 + 297 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm2 : (bag 0 1 0 4 1 100).erase 2 = (bag 0 0 0 4 1 100) := by rfl
  have hm4 : (bag 0 1 0 4 1 100).erase 4 = (bag 0 1 0 3 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 0 1 0 4 1 100) (bag 0 0 0 4 1 100) (bag 0 1 0 3 1 100) (some 3) 4 2 4 hr hs (by decide) hm2 hm4 _ _ cert_93 cert_105
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_119 : count (rows.drop 15) (bag 0 0 1 3 1 100) (some 2) =
    (X ^ 2 + 112 * X ^ 3 + 802 * X ^ 4 + 297 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 1 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm3 : (bag 0 0 1 3 1 100).erase 3 = (bag 0 0 0 3 1 100) := by rfl
  have hm4 : (bag 0 0 1 3 1 100).erase 4 = (bag 0 0 1 2 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 0 0 1 3 1 100) (bag 0 0 0 3 1 100) (bag 0 0 1 2 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_16 cert_26
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_120 : count (rows.drop 15) (bag 0 1 0 3 1 100) (some 3) =
    (2 * X ^ 2 + 215 * X ^ 3 + 896 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm2 : (bag 0 1 0 3 1 100).erase 2 = (bag 0 0 0 3 1 100) := by rfl
  have hm4 : (bag 0 1 0 3 1 100).erase 4 = (bag 0 1 0 2 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 0 1 0 3 1 100) (bag 0 0 0 3 1 100) (bag 0 1 0 2 1 100) (some 3) 4 2 4 hr hs (by decide) hm2 hm4 _ _ cert_94 cert_104
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_121 : count (rows.drop 16) (bag 0 0 1 2 1 100) (some 2) =
    (X ^ 2 + 111 * X ^ 3 + 698 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 1 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm3 : (bag 0 0 1 2 1 100).erase 3 = (bag 0 0 0 2 1 100) := by rfl
  have hm4 : (bag 0 0 1 2 1 100).erase 4 = (bag 0 0 1 1 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 0 0 1 2 1 100) (bag 0 0 0 2 1 100) (bag 0 0 1 1 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_17 cert_25
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_122 : count (rows.drop 16) (bag 0 1 0 2 1 100) (some 3) =
    (4 * X ^ 2 + 309 * X ^ 3 + 596 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 1 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm2 : (bag 0 1 0 2 1 100).erase 2 = (bag 0 0 0 2 1 100) := by rfl
  have hm4 : (bag 0 1 0 2 1 100).erase 4 = (bag 0 1 0 1 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 0 1 0 2 1 100) (bag 0 0 0 2 1 100) (bag 0 1 0 1 1 100) (some 3) 4 2 4 hr hs (by decide) hm2 hm4 _ _ cert_95 cert_103
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_123 : count (rows.drop 17) (bag 0 0 1 1 1 100) (some 2) =
    (4 * X ^ 2 + 304 * X ^ 3 + 298 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 1 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {3, 4, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm3 : (bag 0 0 1 1 1 100).erase 3 = (bag 0 0 0 1 1 100) := by rfl
  have hm4 : (bag 0 0 1 1 1 100).erase 4 = (bag 0 0 1 0 1 100) := by rfl
  have hm5 : (bag 0 0 1 1 1 100).erase 5 = (bag 0 0 1 1 0 100) := by rfl
  have hc := count_three (rows.drop 17) (rows.drop 18) (bag 0 0 1 1 1 100) (bag 0 0 0 1 1 100) (bag 0 0 1 0 1 100) (bag 0 0 1 1 0 100) (some 2) 5 3 4 5 hr hs (by decide) (by decide) hm3 hm4 hm5 _ _ _ cert_18 cert_21 cert_24
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_124 : count (rows.drop 17) (bag 0 1 0 1 1 100) (some 3) =
    (7 * X ^ 2 + 500 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 1 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {2, 4, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm2 : (bag 0 1 0 1 1 100).erase 2 = (bag 0 0 0 1 1 100) := by rfl
  have hm4 : (bag 0 1 0 1 1 100).erase 4 = (bag 0 1 0 0 1 100) := by rfl
  have hm5 : (bag 0 1 0 1 1 100).erase 5 = (bag 0 1 0 1 0 100) := by rfl
  have hc := count_three (rows.drop 17) (rows.drop 18) (bag 0 1 0 1 1 100) (bag 0 0 0 1 1 100) (bag 0 1 0 0 1 100) (bag 0 1 0 1 0 100) (some 3) 5 2 4 5 hr hs (by decide) (by decide) hm2 hm4 hm5 _ _ _ cert_96 cert_99 cert_102
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_125 : count (rows.drop 18) (bag 0 0 1 0 1 100) (some 2) =
    (3 * X ^ 2 + 199 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 0 1 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {3, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm3 : (bag 0 0 1 0 1 100).erase 3 = (bag 0 0 0 0 1 100) := by rfl
  have hm5 : (bag 0 0 1 0 1 100).erase 5 = (bag 0 0 1 0 0 100) := by rfl
  have hc := count_two (rows.drop 18) (rows.drop 19) (bag 0 0 1 0 1 100) (bag 0 0 0 0 1 100) (bag 0 0 1 0 0 100) (some 2) 5 3 5 hr hs (by decide) hm3 hm5 _ _ cert_19 cert_20
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_126 : count (rows.drop 18) (bag 0 1 0 0 1 100) (some 3) =
    (X + 102 * X ^ 2 + 99 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 1 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {2, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm2 : (bag 0 1 0 0 1 100).erase 2 = (bag 0 0 0 0 1 100) := by rfl
  have hm5 : (bag 0 1 0 0 1 100).erase 5 = (bag 0 1 0 0 0 100) := by rfl
  have hc := count_two (rows.drop 18) (rows.drop 19) (bag 0 1 0 0 1 100) (bag 0 0 0 0 1 100) (bag 0 1 0 0 0 100) (some 3) 5 2 5 hr hs (by decide) hm2 hm5 _ _ cert_97 cert_98
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_127 : count (rows.drop 19) (bag 0 0 1 0 0 100) (some 2) =
    (X + 100 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (3 ::ₘ Multiset.replicate 100 6) (some 2) = _
  rw [six_tail 99 2 3 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_128 : count (rows.drop 19) (bag 0 1 0 0 0 100) (some 3) =
    (2 * X + 99 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (2 ::ₘ Multiset.replicate 100 6) (some 3) = _
  rw [six_tail 99 3 2 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_129 : count (rows.drop 18) (bag 0 1 1 0 0 100) (some 5) =
    (3 * X + 199 * X ^ 2 : ℕ[X]) := by
  have hs : (bag 0 1 1 0 0 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm2 : (bag 0 1 1 0 0 100).erase 2 = (bag 0 0 1 0 0 100) := by rfl
  have hm3 : (bag 0 1 1 0 0 100).erase 3 = (bag 0 1 0 0 0 100) := by rfl
  have hc := count_two (rows.drop 18) (rows.drop 19) (bag 0 1 1 0 0 100) (bag 0 0 1 0 0 100) (bag 0 1 0 0 0 100) (some 5) 5 2 3 hr hs (by decide) hm2 hm3 _ _ cert_127 cert_128
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_130 : count (rows.drop 17) (bag 0 1 1 0 1 100) (some 4) =
    (X + 108 * X ^ 2 + 497 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 1 1 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {2, 3, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm2 : (bag 0 1 1 0 1 100).erase 2 = (bag 0 0 1 0 1 100) := by rfl
  have hm3 : (bag 0 1 1 0 1 100).erase 3 = (bag 0 1 0 0 1 100) := by rfl
  have hm5 : (bag 0 1 1 0 1 100).erase 5 = (bag 0 1 1 0 0 100) := by rfl
  have hc := count_three (rows.drop 17) (rows.drop 18) (bag 0 1 1 0 1 100) (bag 0 0 1 0 1 100) (bag 0 1 0 0 1 100) (bag 0 1 1 0 0 100) (some 4) 5 2 3 5 hr hs (by decide) (by decide) hm2 hm3 hm5 _ _ _ cert_125 cert_126 cert_129
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_131 : count (rows.drop 16) (bag 0 1 1 1 1 100) (some 4) =
    (X + 119 * X ^ 2 + 1301 * X ^ 3 + 397 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 1 1 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm2 : (bag 0 1 1 1 1 100).erase 2 = (bag 0 0 1 1 1 100) := by rfl
  have hm3 : (bag 0 1 1 1 1 100).erase 3 = (bag 0 1 0 1 1 100) := by rfl
  have hm4 : (bag 0 1 1 1 1 100).erase 4 = (bag 0 1 1 0 1 100) := by rfl
  have hc := count_three (rows.drop 16) (rows.drop 17) (bag 0 1 1 1 1 100) (bag 0 0 1 1 1 100) (bag 0 1 0 1 1 100) (bag 0 1 1 0 1 100) (some 4) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_123 cert_124 cert_130
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_132 : count (rows.drop 15) (bag 0 1 1 2 1 100) (some 4) =
    (X + 124 * X ^ 2 + 1721 * X ^ 3 + 1691 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 1 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm2 : (bag 0 1 1 2 1 100).erase 2 = (bag 0 0 1 2 1 100) := by rfl
  have hm3 : (bag 0 1 1 2 1 100).erase 3 = (bag 0 1 0 2 1 100) := by rfl
  have hm4 : (bag 0 1 1 2 1 100).erase 4 = (bag 0 1 1 1 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 0 1 1 2 1 100) (bag 0 0 1 2 1 100) (bag 0 1 0 2 1 100) (bag 0 1 1 1 1 100) (some 4) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_121 cert_122 cert_131
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_133 : count (rows.drop 14) (bag 0 1 1 3 1 100) (some 4) =
    (X + 127 * X ^ 2 + 2048 * X ^ 3 + 3389 * X ^ 4 + 495 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 1 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm2 : (bag 0 1 1 3 1 100).erase 2 = (bag 0 0 1 3 1 100) := by rfl
  have hm3 : (bag 0 1 1 3 1 100).erase 3 = (bag 0 1 0 3 1 100) := by rfl
  have hm4 : (bag 0 1 1 3 1 100).erase 4 = (bag 0 1 1 2 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 0 1 1 3 1 100) (bag 0 0 1 3 1 100) (bag 0 1 0 3 1 100) (bag 0 1 1 2 1 100) (some 4) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_119 cert_120 cert_132
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_134 : count (rows.drop 13) (bag 0 1 1 4 1 100) (some 4) =
    (X + 130 * X ^ 2 + 2377 * X ^ 3 + 5295 * X ^ 4 + 1287 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 1 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm2 : (bag 0 1 1 4 1 100).erase 2 = (bag 0 0 1 4 1 100) := by rfl
  have hm3 : (bag 0 1 1 4 1 100).erase 3 = (bag 0 1 0 4 1 100) := by rfl
  have hm4 : (bag 0 1 1 4 1 100).erase 4 = (bag 0 1 1 3 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 0 1 1 4 1 100) (bag 0 0 1 4 1 100) (bag 0 1 0 4 1 100) (bag 0 1 1 3 1 100) (some 4) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_117 cert_118 cert_133
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_135 : count (rows.drop 12) (bag 0 1 1 5 1 100) (some 4) =
    (X + 133 * X ^ 2 + 2708 * X ^ 3 + 7409 * X ^ 4 + 2475 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 1 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm2 : (bag 0 1 1 5 1 100).erase 2 = (bag 0 0 1 5 1 100) := by rfl
  have hm3 : (bag 0 1 1 5 1 100).erase 3 = (bag 0 1 0 5 1 100) := by rfl
  have hm4 : (bag 0 1 1 5 1 100).erase 4 = (bag 0 1 1 4 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 0 1 1 5 1 100) (bag 0 0 1 5 1 100) (bag 0 1 0 5 1 100) (bag 0 1 1 4 1 100) (some 4) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_115 cert_116 cert_134
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_136 : count (rows.drop 11) (bag 0 1 1 6 1 100) (some 4) =
    (X + 136 * X ^ 2 + 3041 * X ^ 3 + 9731 * X ^ 4 + 4059 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 1 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm2 : (bag 0 1 1 6 1 100).erase 2 = (bag 0 0 1 6 1 100) := by rfl
  have hm3 : (bag 0 1 1 6 1 100).erase 3 = (bag 0 1 0 6 1 100) := by rfl
  have hm4 : (bag 0 1 1 6 1 100).erase 4 = (bag 0 1 1 5 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 0 1 1 6 1 100) (bag 0 0 1 6 1 100) (bag 0 1 0 6 1 100) (bag 0 1 1 5 1 100) (some 4) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_113 cert_114 cert_135
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_137 : count (rows.drop 10) (bag 0 1 1 7 1 100) (some 4) =
    (X + 139 * X ^ 2 + 3376 * X ^ 3 + 12261 * X ^ 4 + 6039 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 1 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm2 : (bag 0 1 1 7 1 100).erase 2 = (bag 0 0 1 7 1 100) := by rfl
  have hm3 : (bag 0 1 1 7 1 100).erase 3 = (bag 0 1 0 7 1 100) := by rfl
  have hm4 : (bag 0 1 1 7 1 100).erase 4 = (bag 0 1 1 6 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 0 1 1 7 1 100) (bag 0 0 1 7 1 100) (bag 0 1 0 7 1 100) (bag 0 1 1 6 1 100) (some 4) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_111 cert_112 cert_136
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_138 : count (rows.drop 9) (bag 0 1 1 8 1 100) (some 3) =
    (4 * X ^ 2 + 476 * X ^ 3 + 6114 * X ^ 4 + 14637 * X ^ 5 + 6039 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 1 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm2 : (bag 0 1 1 8 1 100).erase 2 = (bag 0 0 1 8 1 100) := by rfl
  have hm3 : (bag 0 1 1 8 1 100).erase 3 = (bag 0 1 0 8 1 100) := by rfl
  have hm4 : (bag 0 1 1 8 1 100).erase 4 = (bag 0 1 1 7 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 0 1 1 8 1 100) (bag 0 0 1 8 1 100) (bag 0 1 0 8 1 100) (bag 0 1 1 7 1 100) (some 3) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_88 cert_110 cert_137
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_139 : count (rows.drop 10) (bag 0 0 2 7 1 100) (some 2) =
    (X ^ 2 + 125 * X ^ 3 + 2092 * X ^ 4 + 6215 * X ^ 5 + 2475 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 2 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm3 : (bag 0 0 2 7 1 100).erase 3 = (bag 0 0 1 7 1 100) := by rfl
  have hm4 : (bag 0 0 2 7 1 100).erase 4 = (bag 0 0 2 6 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 0 0 2 7 1 100) (bag 0 0 1 7 1 100) (bag 0 0 2 6 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_33 cert_49
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_140 : count (rows.drop 10) (bag 0 1 1 7 1 100) (some 3) =
    (4 * X ^ 2 + 471 * X ^ 3 + 5571 * X ^ 4 + 11711 * X ^ 5 + 4059 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 1 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm2 : (bag 0 1 1 7 1 100).erase 2 = (bag 0 0 1 7 1 100) := by rfl
  have hm3 : (bag 0 1 1 7 1 100).erase 3 = (bag 0 1 0 7 1 100) := by rfl
  have hm4 : (bag 0 1 1 7 1 100).erase 4 = (bag 0 1 1 6 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 0 1 1 7 1 100) (bag 0 0 1 7 1 100) (bag 0 1 0 7 1 100) (bag 0 1 1 6 1 100) (some 3) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_111 cert_112 cert_136
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_141 : count (rows.drop 11) (bag 0 0 2 6 1 100) (some 2) =
    (X ^ 2 + 123 * X ^ 3 + 1873 * X ^ 4 + 4903 * X ^ 5 + 1584 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 2 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm3 : (bag 0 0 2 6 1 100).erase 3 = (bag 0 0 1 6 1 100) := by rfl
  have hm4 : (bag 0 0 2 6 1 100).erase 4 = (bag 0 0 2 5 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 0 0 2 6 1 100) (bag 0 0 1 6 1 100) (bag 0 0 2 5 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_34 cert_48
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_142 : count (rows.drop 11) (bag 0 1 1 6 1 100) (some 3) =
    (4 * X ^ 2 + 466 * X ^ 3 + 5030 * X ^ 4 + 8993 * X ^ 5 + 2475 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 1 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm2 : (bag 0 1 1 6 1 100).erase 2 = (bag 0 0 1 6 1 100) := by rfl
  have hm3 : (bag 0 1 1 6 1 100).erase 3 = (bag 0 1 0 6 1 100) := by rfl
  have hm4 : (bag 0 1 1 6 1 100).erase 4 = (bag 0 1 1 5 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 0 1 1 6 1 100) (bag 0 0 1 6 1 100) (bag 0 1 0 6 1 100) (bag 0 1 1 5 1 100) (some 3) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_113 cert_114 cert_135
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_143 : count (rows.drop 12) (bag 0 0 2 5 1 100) (some 2) =
    (X ^ 2 + 121 * X ^ 3 + 1655 * X ^ 4 + 3695 * X ^ 5 + 891 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 2 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm3 : (bag 0 0 2 5 1 100).erase 3 = (bag 0 0 1 5 1 100) := by rfl
  have hm4 : (bag 0 0 2 5 1 100).erase 4 = (bag 0 0 2 4 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 0 0 2 5 1 100) (bag 0 0 1 5 1 100) (bag 0 0 2 4 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_35 cert_47
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_144 : count (rows.drop 12) (bag 0 1 1 5 1 100) (some 3) =
    (4 * X ^ 2 + 461 * X ^ 3 + 4491 * X ^ 4 + 6483 * X ^ 5 + 1287 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 1 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm2 : (bag 0 1 1 5 1 100).erase 2 = (bag 0 0 1 5 1 100) := by rfl
  have hm3 : (bag 0 1 1 5 1 100).erase 3 = (bag 0 1 0 5 1 100) := by rfl
  have hm4 : (bag 0 1 1 5 1 100).erase 4 = (bag 0 1 1 4 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 0 1 1 5 1 100) (bag 0 0 1 5 1 100) (bag 0 1 0 5 1 100) (bag 0 1 1 4 1 100) (some 3) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_115 cert_116 cert_134
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_145 : count (rows.drop 13) (bag 0 0 2 4 1 100) (some 2) =
    (X ^ 2 + 119 * X ^ 3 + 1438 * X ^ 4 + 2591 * X ^ 5 + 396 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 2 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm3 : (bag 0 0 2 4 1 100).erase 3 = (bag 0 0 1 4 1 100) := by rfl
  have hm4 : (bag 0 0 2 4 1 100).erase 4 = (bag 0 0 2 3 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 0 0 2 4 1 100) (bag 0 0 1 4 1 100) (bag 0 0 2 3 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_36 cert_46
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_146 : count (rows.drop 13) (bag 0 1 1 4 1 100) (some 3) =
    (4 * X ^ 2 + 456 * X ^ 3 + 3954 * X ^ 4 + 4181 * X ^ 5 + 495 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 1 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm2 : (bag 0 1 1 4 1 100).erase 2 = (bag 0 0 1 4 1 100) := by rfl
  have hm3 : (bag 0 1 1 4 1 100).erase 3 = (bag 0 1 0 4 1 100) := by rfl
  have hm4 : (bag 0 1 1 4 1 100).erase 4 = (bag 0 1 1 3 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 0 1 1 4 1 100) (bag 0 0 1 4 1 100) (bag 0 1 0 4 1 100) (bag 0 1 1 3 1 100) (some 3) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_117 cert_118 cert_133
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_147 : count (rows.drop 14) (bag 0 0 2 3 1 100) (some 2) =
    (X ^ 2 + 117 * X ^ 3 + 1222 * X ^ 4 + 1591 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 2 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm3 : (bag 0 0 2 3 1 100).erase 3 = (bag 0 0 1 3 1 100) := by rfl
  have hm4 : (bag 0 0 2 3 1 100).erase 4 = (bag 0 0 2 2 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 0 0 2 3 1 100) (bag 0 0 1 3 1 100) (bag 0 0 2 2 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_37 cert_45
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_148 : count (rows.drop 14) (bag 0 1 1 3 1 100) (some 3) =
    (4 * X ^ 2 + 451 * X ^ 3 + 3419 * X ^ 4 + 2087 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 1 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm2 : (bag 0 1 1 3 1 100).erase 2 = (bag 0 0 1 3 1 100) := by rfl
  have hm3 : (bag 0 1 1 3 1 100).erase 3 = (bag 0 1 0 3 1 100) := by rfl
  have hm4 : (bag 0 1 1 3 1 100).erase 4 = (bag 0 1 1 2 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 0 1 1 3 1 100) (bag 0 0 1 3 1 100) (bag 0 1 0 3 1 100) (bag 0 1 1 2 1 100) (some 3) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_119 cert_120 cert_132
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_149 : count (rows.drop 15) (bag 0 0 2 2 1 100) (some 2) =
    (X ^ 2 + 115 * X ^ 3 + 1007 * X ^ 4 + 695 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 2 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm3 : (bag 0 0 2 2 1 100).erase 3 = (bag 0 0 1 2 1 100) := by rfl
  have hm4 : (bag 0 0 2 2 1 100).erase 4 = (bag 0 0 2 1 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 0 0 2 2 1 100) (bag 0 0 1 2 1 100) (bag 0 0 2 1 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_38 cert_44
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_150 : count (rows.drop 15) (bag 0 1 1 2 1 100) (some 3) =
    (6 * X ^ 2 + 539 * X ^ 3 + 2595 * X ^ 4 + 496 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 1 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm2 : (bag 0 1 1 2 1 100).erase 2 = (bag 0 0 1 2 1 100) := by rfl
  have hm3 : (bag 0 1 1 2 1 100).erase 3 = (bag 0 1 0 2 1 100) := by rfl
  have hm4 : (bag 0 1 1 2 1 100).erase 4 = (bag 0 1 1 1 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 0 1 1 2 1 100) (bag 0 0 1 2 1 100) (bag 0 1 0 2 1 100) (bag 0 1 1 1 1 100) (some 3) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_121 cert_122 cert_131
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_151 : count (rows.drop 16) (bag 0 0 2 1 1 100) (some 2) =
    (X ^ 2 + 111 * X ^ 3 + 698 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 2 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm3 : (bag 0 0 2 1 1 100).erase 3 = (bag 0 0 1 1 1 100) := by rfl
  have hm4 : (bag 0 0 2 1 1 100).erase 4 = (bag 0 0 2 0 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 0 0 2 1 1 100) (bag 0 0 1 1 1 100) (bag 0 0 2 0 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_39 cert_43
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_152 : count (rows.drop 16) (bag 0 1 1 1 1 100) (some 3) =
    (12 * X ^ 2 + 912 * X ^ 3 + 894 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 1 1 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm2 : (bag 0 1 1 1 1 100).erase 2 = (bag 0 0 1 1 1 100) := by rfl
  have hm3 : (bag 0 1 1 1 1 100).erase 3 = (bag 0 1 0 1 1 100) := by rfl
  have hm4 : (bag 0 1 1 1 1 100).erase 4 = (bag 0 1 1 0 1 100) := by rfl
  have hc := count_three (rows.drop 16) (rows.drop 17) (bag 0 1 1 1 1 100) (bag 0 0 1 1 1 100) (bag 0 1 0 1 1 100) (bag 0 1 1 0 1 100) (some 3) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_123 cert_124 cert_130
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_153 : count (rows.drop 17) (bag 0 0 2 0 1 100) (some 2) =
    (3 * X ^ 2 + 201 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 2 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {3, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm3 : (bag 0 0 2 0 1 100).erase 3 = (bag 0 0 1 0 1 100) := by rfl
  have hm5 : (bag 0 0 2 0 1 100).erase 5 = (bag 0 0 2 0 0 100) := by rfl
  have hc := count_two (rows.drop 17) (rows.drop 18) (bag 0 0 2 0 1 100) (bag 0 0 1 0 1 100) (bag 0 0 2 0 0 100) (some 2) 5 3 5 hr hs (by decide) hm3 hm5 _ _ cert_40 cert_42
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_154 : count (rows.drop 17) (bag 0 1 1 0 1 100) (some 3) =
    (X + 108 * X ^ 2 + 497 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 1 1 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {2, 3, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm2 : (bag 0 1 1 0 1 100).erase 2 = (bag 0 0 1 0 1 100) := by rfl
  have hm3 : (bag 0 1 1 0 1 100).erase 3 = (bag 0 1 0 0 1 100) := by rfl
  have hm5 : (bag 0 1 1 0 1 100).erase 5 = (bag 0 1 1 0 0 100) := by rfl
  have hc := count_three (rows.drop 17) (rows.drop 18) (bag 0 1 1 0 1 100) (bag 0 0 1 0 1 100) (bag 0 1 0 0 1 100) (bag 0 1 1 0 0 100) (some 3) 5 2 3 5 hr hs (by decide) (by decide) hm2 hm3 hm5 _ _ _ cert_125 cert_126 cert_129
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_155 : count (rows.drop 16) (bag 0 1 2 0 1 100) (some 4) =
    (X + 111 * X ^ 2 + 698 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 1 2 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm2 : (bag 0 1 2 0 1 100).erase 2 = (bag 0 0 2 0 1 100) := by rfl
  have hm3 : (bag 0 1 2 0 1 100).erase 3 = (bag 0 1 1 0 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 0 1 2 0 1 100) (bag 0 0 2 0 1 100) (bag 0 1 1 0 1 100) (some 4) 4 2 3 hr hs (by decide) hm2 hm3 _ _ cert_153 cert_154
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_156 : count (rows.drop 15) (bag 0 1 2 1 1 100) (some 4) =
    (X + 124 * X ^ 2 + 1721 * X ^ 3 + 1691 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 2 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm2 : (bag 0 1 2 1 1 100).erase 2 = (bag 0 0 2 1 1 100) := by rfl
  have hm3 : (bag 0 1 2 1 1 100).erase 3 = (bag 0 1 1 1 1 100) := by rfl
  have hm4 : (bag 0 1 2 1 1 100).erase 4 = (bag 0 1 2 0 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 0 1 2 1 1 100) (bag 0 0 2 1 1 100) (bag 0 1 1 1 1 100) (bag 0 1 2 0 1 100) (some 4) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_151 cert_152 cert_155
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_157 : count (rows.drop 14) (bag 0 1 2 2 1 100) (some 4) =
    (X + 131 * X ^ 2 + 2375 * X ^ 3 + 5293 * X ^ 4 + 1290 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 2 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm2 : (bag 0 1 2 2 1 100).erase 2 = (bag 0 0 2 2 1 100) := by rfl
  have hm3 : (bag 0 1 2 2 1 100).erase 3 = (bag 0 1 1 2 1 100) := by rfl
  have hm4 : (bag 0 1 2 2 1 100).erase 4 = (bag 0 1 2 1 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 0 1 2 2 1 100) (bag 0 0 2 2 1 100) (bag 0 1 1 2 1 100) (bag 0 1 2 1 1 100) (some 4) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_149 cert_150 cert_156
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_158 : count (rows.drop 13) (bag 0 1 2 3 1 100) (some 4) =
    (X + 136 * X ^ 2 + 2943 * X ^ 3 + 9934 * X ^ 4 + 4968 * X ^ 5 + 198 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 2 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm2 : (bag 0 1 2 3 1 100).erase 2 = (bag 0 0 2 3 1 100) := by rfl
  have hm3 : (bag 0 1 2 3 1 100).erase 3 = (bag 0 1 1 3 1 100) := by rfl
  have hm4 : (bag 0 1 2 3 1 100).erase 4 = (bag 0 1 2 2 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 0 1 2 3 1 100) (bag 0 0 2 3 1 100) (bag 0 1 1 3 1 100) (bag 0 1 2 2 1 100) (some 4) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_147 cert_148 cert_157
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_159 : count (rows.drop 12) (bag 0 1 2 4 1 100) (some 4) =
    (X + 141 * X ^ 2 + 3518 * X ^ 3 + 15326 * X ^ 4 + 11740 * X ^ 5 + 1089 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 2 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm2 : (bag 0 1 2 4 1 100).erase 2 = (bag 0 0 2 4 1 100) := by rfl
  have hm3 : (bag 0 1 2 4 1 100).erase 3 = (bag 0 1 1 4 1 100) := by rfl
  have hm4 : (bag 0 1 2 4 1 100).erase 4 = (bag 0 1 2 3 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 0 1 2 4 1 100) (bag 0 0 2 4 1 100) (bag 0 1 1 4 1 100) (bag 0 1 2 3 1 100) (some 4) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_145 cert_146 cert_158
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_160 : count (rows.drop 11) (bag 0 1 2 5 1 100) (some 4) =
    (X + 146 * X ^ 2 + 4100 * X ^ 3 + 21472 * X ^ 4 + 21918 * X ^ 5 + 3267 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 2 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm2 : (bag 0 1 2 5 1 100).erase 2 = (bag 0 0 2 5 1 100) := by rfl
  have hm3 : (bag 0 1 2 5 1 100).erase 3 = (bag 0 1 1 5 1 100) := by rfl
  have hm4 : (bag 0 1 2 5 1 100).erase 4 = (bag 0 1 2 4 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 0 1 2 5 1 100) (bag 0 0 2 5 1 100) (bag 0 1 1 5 1 100) (bag 0 1 2 4 1 100) (some 4) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_143 cert_144 cert_159
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_161 : count (rows.drop 10) (bag 0 1 2 6 1 100) (some 4) =
    (X + 151 * X ^ 2 + 4689 * X ^ 3 + 28375 * X ^ 4 + 35814 * X ^ 5 + 7326 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 2 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm2 : (bag 0 1 2 6 1 100).erase 2 = (bag 0 0 2 6 1 100) := by rfl
  have hm3 : (bag 0 1 2 6 1 100).erase 3 = (bag 0 1 1 6 1 100) := by rfl
  have hm4 : (bag 0 1 2 6 1 100).erase 4 = (bag 0 1 2 5 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 0 1 2 6 1 100) (bag 0 0 2 6 1 100) (bag 0 1 1 6 1 100) (bag 0 1 2 5 1 100) (some 4) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_141 cert_142 cert_160
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_162 : count (rows.drop 9) (bag 0 1 2 7 1 100) (some 4) =
    (X + 156 * X ^ 2 + 5285 * X ^ 3 + 36038 * X ^ 4 + 53740 * X ^ 5 + 13860 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 2 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm2 : (bag 0 1 2 7 1 100).erase 2 = (bag 0 0 2 7 1 100) := by rfl
  have hm3 : (bag 0 1 2 7 1 100).erase 3 = (bag 0 1 1 7 1 100) := by rfl
  have hm4 : (bag 0 1 2 7 1 100).erase 4 = (bag 0 1 2 6 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 0 1 2 7 1 100) (bag 0 0 2 7 1 100) (bag 0 1 1 7 1 100) (bag 0 1 2 6 1 100) (some 4) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_139 cert_140 cert_161
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_163 : count (rows.drop 8) (bag 0 1 2 8 1 100) (some 3) =
    (6 * X ^ 2 + 759 * X ^ 3 + 13711 * X ^ 4 + 58306 * X ^ 5 + 63343 * X ^ 6 + 13860 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 1 2 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm2 : (bag 0 1 2 8 1 100).erase 2 = (bag 0 0 2 8 1 100) := by rfl
  have hm3 : (bag 0 1 2 8 1 100).erase 3 = (bag 0 1 1 8 1 100) := by rfl
  have hm4 : (bag 0 1 2 8 1 100).erase 4 = (bag 0 1 2 7 1 100) := by rfl
  have hc := count_three (rows.drop 8) (rows.drop 9) (bag 0 1 2 8 1 100) (bag 0 0 2 8 1 100) (bag 0 1 1 8 1 100) (bag 0 1 2 7 1 100) (some 3) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_87 cert_138 cert_162
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_164 : count (rows.drop 9) (bag 0 0 3 7 1 100) (some 2) =
    (X ^ 2 + 132 * X ^ 3 + 2902 * X ^ 4 + 14306 * X ^ 5 + 16049 * X ^ 6 + 2970 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 0 3 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm3 : (bag 0 0 3 7 1 100).erase 3 = (bag 0 0 2 7 1 100) := by rfl
  have hm4 : (bag 0 0 3 7 1 100).erase 4 = (bag 0 0 3 6 1 100) := by rfl
  have hc := count_two (rows.drop 9) (rows.drop 10) (bag 0 0 3 7 1 100) (bag 0 0 2 7 1 100) (bag 0 0 3 6 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_52 cert_66
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_165 : count (rows.drop 9) (bag 0 1 2 7 1 100) (some 3) =
    (6 * X ^ 2 + 747 * X ^ 3 + 12352 * X ^ 4 + 46301 * X ^ 5 + 42348 * X ^ 6 + 7326 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 1 2 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm2 : (bag 0 1 2 7 1 100).erase 2 = (bag 0 0 2 7 1 100) := by rfl
  have hm3 : (bag 0 1 2 7 1 100).erase 3 = (bag 0 1 1 7 1 100) := by rfl
  have hm4 : (bag 0 1 2 7 1 100).erase 4 = (bag 0 1 2 6 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 0 1 2 7 1 100) (bag 0 0 2 7 1 100) (bag 0 1 1 7 1 100) (bag 0 1 2 6 1 100) (some 3) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_139 cert_140 cert_161
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_166 : count (rows.drop 10) (bag 0 0 3 6 1 100) (some 2) =
    (X ^ 2 + 129 * X ^ 3 + 2560 * X ^ 4 + 11121 * X ^ 5 + 10255 * X ^ 6 + 1386 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 0 3 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm3 : (bag 0 0 3 6 1 100).erase 3 = (bag 0 0 2 6 1 100) := by rfl
  have hm4 : (bag 0 0 3 6 1 100).erase 4 = (bag 0 0 3 5 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 0 0 3 6 1 100) (bag 0 0 2 6 1 100) (bag 0 0 3 5 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_53 cert_65
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_167 : count (rows.drop 10) (bag 0 1 2 6 1 100) (some 3) =
    (6 * X ^ 2 + 735 * X ^ 3 + 11003 * X ^ 4 + 35368 * X ^ 5 + 25977 * X ^ 6 + 3267 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 1 2 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm2 : (bag 0 1 2 6 1 100).erase 2 = (bag 0 0 2 6 1 100) := by rfl
  have hm3 : (bag 0 1 2 6 1 100).erase 3 = (bag 0 1 1 6 1 100) := by rfl
  have hm4 : (bag 0 1 2 6 1 100).erase 4 = (bag 0 1 2 5 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 0 1 2 6 1 100) (bag 0 0 2 6 1 100) (bag 0 1 1 6 1 100) (bag 0 1 2 5 1 100) (some 3) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_141 cert_142 cert_160
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_168 : count (rows.drop 11) (bag 0 0 3 5 1 100) (some 2) =
    (X ^ 2 + 126 * X ^ 3 + 2221 * X ^ 4 + 8258 * X ^ 5 + 5867 * X ^ 6 + 495 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 0 3 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm3 : (bag 0 0 3 5 1 100).erase 3 = (bag 0 0 2 5 1 100) := by rfl
  have hm4 : (bag 0 0 3 5 1 100).erase 4 = (bag 0 0 3 4 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 0 0 3 5 1 100) (bag 0 0 2 5 1 100) (bag 0 0 3 4 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_54 cert_64
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_169 : count (rows.drop 11) (bag 0 1 2 5 1 100) (some 3) =
    (6 * X ^ 2 + 723 * X ^ 3 + 9664 * X ^ 4 + 25504 * X ^ 5 + 13918 * X ^ 6 + 1089 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 1 2 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm2 : (bag 0 1 2 5 1 100).erase 2 = (bag 0 0 2 5 1 100) := by rfl
  have hm3 : (bag 0 1 2 5 1 100).erase 3 = (bag 0 1 1 5 1 100) := by rfl
  have hm4 : (bag 0 1 2 5 1 100).erase 4 = (bag 0 1 2 4 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 0 1 2 5 1 100) (bag 0 0 2 5 1 100) (bag 0 1 1 5 1 100) (bag 0 1 2 4 1 100) (some 3) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_143 cert_144 cert_159
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_170 : count (rows.drop 12) (bag 0 0 3 4 1 100) (some 2) =
    (X ^ 2 + 123 * X ^ 3 + 1885 * X ^ 4 + 5716 * X ^ 5 + 2781 * X ^ 6 + 99 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 0 3 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm3 : (bag 0 0 3 4 1 100).erase 3 = (bag 0 0 2 4 1 100) := by rfl
  have hm4 : (bag 0 0 3 4 1 100).erase 4 = (bag 0 0 3 3 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 0 0 3 4 1 100) (bag 0 0 2 4 1 100) (bag 0 0 3 3 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_55 cert_63
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_171 : count (rows.drop 12) (bag 0 1 2 4 1 100) (some 3) =
    (6 * X ^ 2 + 711 * X ^ 3 + 8335 * X ^ 4 + 16706 * X ^ 5 + 5859 * X ^ 6 + 198 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 1 2 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm2 : (bag 0 1 2 4 1 100).erase 2 = (bag 0 0 2 4 1 100) := by rfl
  have hm3 : (bag 0 1 2 4 1 100).erase 3 = (bag 0 1 1 4 1 100) := by rfl
  have hm4 : (bag 0 1 2 4 1 100).erase 4 = (bag 0 1 2 3 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 0 1 2 4 1 100) (bag 0 0 2 4 1 100) (bag 0 1 1 4 1 100) (bag 0 1 2 3 1 100) (some 3) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_145 cert_146 cert_158
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_172 : count (rows.drop 13) (bag 0 0 3 3 1 100) (some 2) =
    (X ^ 2 + 120 * X ^ 3 + 1552 * X ^ 4 + 3494 * X ^ 5 + 893 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 3 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm3 : (bag 0 0 3 3 1 100).erase 3 = (bag 0 0 2 3 1 100) := by rfl
  have hm4 : (bag 0 0 3 3 1 100).erase 4 = (bag 0 0 3 2 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 0 0 3 3 1 100) (bag 0 0 2 3 1 100) (bag 0 0 3 2 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_56 cert_62
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_173 : count (rows.drop 13) (bag 0 1 2 3 1 100) (some 3) =
    (6 * X ^ 2 + 699 * X ^ 3 + 7016 * X ^ 4 + 8971 * X ^ 5 + 1488 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 2 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm2 : (bag 0 1 2 3 1 100).erase 2 = (bag 0 0 2 3 1 100) := by rfl
  have hm3 : (bag 0 1 2 3 1 100).erase 3 = (bag 0 1 1 3 1 100) := by rfl
  have hm4 : (bag 0 1 2 3 1 100).erase 4 = (bag 0 1 2 2 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 0 1 2 3 1 100) (bag 0 0 2 3 1 100) (bag 0 1 1 3 1 100) (bag 0 1 2 2 1 100) (some 3) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_147 cert_148 cert_157
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_174 : count (rows.drop 14) (bag 0 0 3 2 1 100) (some 2) =
    (X ^ 2 + 117 * X ^ 3 + 1222 * X ^ 4 + 1591 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 3 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm3 : (bag 0 0 3 2 1 100).erase 3 = (bag 0 0 2 2 1 100) := by rfl
  have hm4 : (bag 0 0 3 2 1 100).erase 4 = (bag 0 0 3 1 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 0 0 3 2 1 100) (bag 0 0 2 2 1 100) (bag 0 0 3 1 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_57 cert_61
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_175 : count (rows.drop 14) (bag 0 1 2 2 1 100) (some 3) =
    (8 * X ^ 2 + 778 * X ^ 3 + 5323 * X ^ 4 + 2882 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 2 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm2 : (bag 0 1 2 2 1 100).erase 2 = (bag 0 0 2 2 1 100) := by rfl
  have hm3 : (bag 0 1 2 2 1 100).erase 3 = (bag 0 1 1 2 1 100) := by rfl
  have hm4 : (bag 0 1 2 2 1 100).erase 4 = (bag 0 1 2 1 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 0 1 2 2 1 100) (bag 0 0 2 2 1 100) (bag 0 1 1 2 1 100) (bag 0 1 2 1 1 100) (some 3) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_149 cert_150 cert_156
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_176 : count (rows.drop 15) (bag 0 0 3 1 1 100) (some 2) =
    (X ^ 2 + 112 * X ^ 3 + 802 * X ^ 4 + 297 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 3 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm3 : (bag 0 0 3 1 1 100).erase 3 = (bag 0 0 2 1 1 100) := by rfl
  have hm4 : (bag 0 0 3 1 1 100).erase 4 = (bag 0 0 3 0 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 0 0 3 1 1 100) (bag 0 0 2 1 1 100) (bag 0 0 3 0 1 100) (some 2) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_58 cert_60
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_177 : count (rows.drop 15) (bag 0 1 2 1 1 100) (some 3) =
    (14 * X ^ 2 + 1134 * X ^ 3 + 2290 * X ^ 4 + 198 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 2 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm2 : (bag 0 1 2 1 1 100).erase 2 = (bag 0 0 2 1 1 100) := by rfl
  have hm3 : (bag 0 1 2 1 1 100).erase 3 = (bag 0 1 1 1 1 100) := by rfl
  have hm4 : (bag 0 1 2 1 1 100).erase 4 = (bag 0 1 2 0 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 0 1 2 1 1 100) (bag 0 0 2 1 1 100) (bag 0 1 1 1 1 100) (bag 0 1 2 0 1 100) (some 3) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_151 cert_152 cert_155
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_178 : count (rows.drop 16) (bag 0 0 3 0 1 100) (some 2) =
    (X ^ 2 + 104 * X ^ 3 + 198 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 3 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm3 : (bag 0 0 3 0 1 100).erase 3 = (bag 0 0 2 0 1 100) := by rfl
  have hc := count_one (rows.drop 16) (rows.drop 17) (bag 0 0 3 0 1 100) (bag 0 0 2 0 1 100) (some 2) 4 3 hr hs hm3 _ cert_59
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_179 : count (rows.drop 16) (bag 0 1 2 0 1 100) (some 3) =
    (X + 111 * X ^ 2 + 698 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 1 2 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm2 : (bag 0 1 2 0 1 100).erase 2 = (bag 0 0 2 0 1 100) := by rfl
  have hm3 : (bag 0 1 2 0 1 100).erase 3 = (bag 0 1 1 0 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 0 1 2 0 1 100) (bag 0 0 2 0 1 100) (bag 0 1 1 0 1 100) (some 3) 4 2 3 hr hs (by decide) hm2 hm3 _ _ cert_153 cert_154
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_180 : count (rows.drop 15) (bag 0 1 3 0 1 100) (some 4) =
    (X + 112 * X ^ 2 + 802 * X ^ 3 + 297 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 1 3 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm2 : (bag 0 1 3 0 1 100).erase 2 = (bag 0 0 3 0 1 100) := by rfl
  have hm3 : (bag 0 1 3 0 1 100).erase 3 = (bag 0 1 2 0 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 0 1 3 0 1 100) (bag 0 0 3 0 1 100) (bag 0 1 2 0 1 100) (some 4) 4 2 3 hr hs (by decide) hm2 hm3 _ _ cert_178 cert_179
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_181 : count (rows.drop 14) (bag 0 1 3 1 1 100) (some 4) =
    (X + 127 * X ^ 2 + 2048 * X ^ 3 + 3389 * X ^ 4 + 495 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 3 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm2 : (bag 0 1 3 1 1 100).erase 2 = (bag 0 0 3 1 1 100) := by rfl
  have hm3 : (bag 0 1 3 1 1 100).erase 3 = (bag 0 1 2 1 1 100) := by rfl
  have hm4 : (bag 0 1 3 1 1 100).erase 4 = (bag 0 1 3 0 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 0 1 3 1 1 100) (bag 0 0 3 1 1 100) (bag 0 1 2 1 1 100) (bag 0 1 3 0 1 100) (some 4) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_176 cert_177 cert_180
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_182 : count (rows.drop 13) (bag 0 1 3 2 1 100) (some 4) =
    (X + 136 * X ^ 2 + 2943 * X ^ 3 + 9934 * X ^ 4 + 4968 * X ^ 5 + 198 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 3 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm2 : (bag 0 1 3 2 1 100).erase 2 = (bag 0 0 3 2 1 100) := by rfl
  have hm3 : (bag 0 1 3 2 1 100).erase 3 = (bag 0 1 2 2 1 100) := by rfl
  have hm4 : (bag 0 1 3 2 1 100).erase 4 = (bag 0 1 3 1 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 0 1 3 2 1 100) (bag 0 0 3 2 1 100) (bag 0 1 2 2 1 100) (bag 0 1 3 1 1 100) (some 4) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_174 cert_175 cert_181
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_183 : count (rows.drop 12) (bag 0 1 3 3 1 100) (some 4) =
    (X + 143 * X ^ 2 + 3762 * X ^ 3 + 18502 * X ^ 4 + 17433 * X ^ 5 + 2579 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 3 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm2 : (bag 0 1 3 3 1 100).erase 2 = (bag 0 0 3 3 1 100) := by rfl
  have hm3 : (bag 0 1 3 3 1 100).erase 3 = (bag 0 1 2 3 1 100) := by rfl
  have hm4 : (bag 0 1 3 3 1 100).erase 4 = (bag 0 1 3 2 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 0 1 3 3 1 100) (bag 0 0 3 3 1 100) (bag 0 1 2 3 1 100) (bag 0 1 3 2 1 100) (some 4) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_172 cert_173 cert_182
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_184 : count (rows.drop 11) (bag 0 1 3 4 1 100) (some 4) =
    (X + 150 * X ^ 2 + 4596 * X ^ 3 + 28722 * X ^ 4 + 39855 * X ^ 5 + 11219 * X ^ 6 + 297 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 1 3 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm2 : (bag 0 1 3 4 1 100).erase 2 = (bag 0 0 3 4 1 100) := by rfl
  have hm3 : (bag 0 1 3 4 1 100).erase 3 = (bag 0 1 2 4 1 100) := by rfl
  have hm4 : (bag 0 1 3 4 1 100).erase 4 = (bag 0 1 3 3 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 0 1 3 4 1 100) (bag 0 0 3 4 1 100) (bag 0 1 2 4 1 100) (bag 0 1 3 3 1 100) (some 4) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_170 cert_171 cert_183
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_185 : count (rows.drop 10) (bag 0 1 3 5 1 100) (some 4) =
    (X + 157 * X ^ 2 + 5445 * X ^ 3 + 40607 * X ^ 4 + 73617 * X ^ 5 + 31004 * X ^ 6 + 1881 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 1 3 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm2 : (bag 0 1 3 5 1 100).erase 2 = (bag 0 0 3 5 1 100) := by rfl
  have hm3 : (bag 0 1 3 5 1 100).erase 3 = (bag 0 1 2 5 1 100) := by rfl
  have hm4 : (bag 0 1 3 5 1 100).erase 4 = (bag 0 1 3 4 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 0 1 3 5 1 100) (bag 0 0 3 5 1 100) (bag 0 1 2 5 1 100) (bag 0 1 3 4 1 100) (some 4) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_168 cert_169 cert_184
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_186 : count (rows.drop 9) (bag 0 1 3 6 1 100) (some 4) =
    (X + 164 * X ^ 2 + 6309 * X ^ 3 + 54170 * X ^ 4 + 120106 * X ^ 5 + 67236 * X ^ 6 + 6534 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 1 3 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm2 : (bag 0 1 3 6 1 100).erase 2 = (bag 0 0 3 6 1 100) := by rfl
  have hm3 : (bag 0 1 3 6 1 100).erase 3 = (bag 0 1 2 6 1 100) := by rfl
  have hm4 : (bag 0 1 3 6 1 100).erase 4 = (bag 0 1 3 5 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 0 1 3 6 1 100) (bag 0 0 3 6 1 100) (bag 0 1 2 6 1 100) (bag 0 1 3 5 1 100) (some 4) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_166 cert_167 cert_185
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_187 : count (rows.drop 8) (bag 0 1 3 7 1 100) (some 4) =
    (X + 171 * X ^ 2 + 7188 * X ^ 3 + 69424 * X ^ 4 + 180713 * X ^ 5 + 125633 * X ^ 6 + 16830 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 1 3 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm2 : (bag 0 1 3 7 1 100).erase 2 = (bag 0 0 3 7 1 100) := by rfl
  have hm3 : (bag 0 1 3 7 1 100).erase 3 = (bag 0 1 2 7 1 100) := by rfl
  have hm4 : (bag 0 1 3 7 1 100).erase 4 = (bag 0 1 3 6 1 100) := by rfl
  have hc := count_three (rows.drop 8) (rows.drop 9) (bag 0 1 3 7 1 100) (bag 0 0 3 7 1 100) (bag 0 1 2 7 1 100) (bag 0 1 3 6 1 100) (some 4) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_164 cert_165 cert_186
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_188 : count (rows.drop 7) (bag 0 1 3 8 1 100) (some 3) =
    (8 * X ^ 2 + 1065 * X ^ 3 + 24146 * X ^ 4 + 145544 * X ^ 5 + 267409 * X ^ 6 + 144938 * X ^ 7 + 16830 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 0 1 3 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 7 = 4 :: rows.drop 8 := by rfl
  have hm2 : (bag 0 1 3 8 1 100).erase 2 = (bag 0 0 3 8 1 100) := by rfl
  have hm3 : (bag 0 1 3 8 1 100).erase 3 = (bag 0 1 2 8 1 100) := by rfl
  have hm4 : (bag 0 1 3 8 1 100).erase 4 = (bag 0 1 3 7 1 100) := by rfl
  have hc := count_three (rows.drop 7) (rows.drop 8) (bag 0 1 3 8 1 100) (bag 0 0 3 8 1 100) (bag 0 1 2 8 1 100) (bag 0 1 3 7 1 100) (some 3) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_86 cert_163 cert_187
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_189 : count (rows.drop 6) (bag 0 1 4 8 1 100) (some 1) =
    (9 * X ^ 3 + 1208 * X ^ 4 + 28356 * X ^ 5 + 176700 * X ^ 6 + 335545 * X ^ 7 + 186327 * X ^ 8 + 21780 * X ^ 9 : ℕ[X]) := by
  have hs : (bag 0 1 4 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 6 = 3 :: rows.drop 7 := by rfl
  have hm2 : (bag 0 1 4 8 1 100).erase 2 = (bag 0 0 4 8 1 100) := by rfl
  have hm3 : (bag 0 1 4 8 1 100).erase 3 = (bag 0 1 3 8 1 100) := by rfl
  have hc := count_two (rows.drop 6) (rows.drop 7) (bag 0 1 4 8 1 100) (bag 0 0 4 8 1 100) (bag 0 1 3 8 1 100) (some 1) 3 2 3 hr hs (by decide) hm2 hm3 _ _ cert_85 cert_188
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_190 : count (rows.drop 7) (bag 0 0 4 8 1 100) (some 1) =
    (X ^ 2 + 143 * X ^ 3 + 4210 * X ^ 4 + 31156 * X ^ 5 + 68136 * X ^ 6 + 41389 * X ^ 7 + 4950 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 0 0 4 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 7 = 4 :: rows.drop 8 := by rfl
  have hm3 : (bag 0 0 4 8 1 100).erase 3 = (bag 0 0 3 8 1 100) := by rfl
  have hm4 : (bag 0 0 4 8 1 100).erase 4 = (bag 0 0 4 7 1 100) := by rfl
  have hc := count_two (rows.drop 7) (rows.drop 8) (bag 0 0 4 8 1 100) (bag 0 0 3 8 1 100) (bag 0 0 4 7 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_68 cert_84
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_191 : count (rows.drop 8) (bag 0 0 3 8 1 100) (some 1) =
    (X ^ 2 + 135 * X ^ 3 + 3247 * X ^ 4 + 17814 * X ^ 5 + 23353 * X ^ 6 + 5445 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 0 3 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm3 : (bag 0 0 3 8 1 100).erase 3 = (bag 0 0 2 8 1 100) := by rfl
  have hm4 : (bag 0 0 3 8 1 100).erase 4 = (bag 0 0 3 7 1 100) := by rfl
  have hc := count_two (rows.drop 8) (rows.drop 9) (bag 0 0 3 8 1 100) (bag 0 0 2 8 1 100) (bag 0 0 3 7 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_51 cert_67
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_192 : count (rows.drop 9) (bag 0 0 2 8 1 100) (some 1) =
    (X ^ 2 + 127 * X ^ 3 + 2312 * X ^ 4 + 7631 * X ^ 5 + 3564 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 2 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm3 : (bag 0 0 2 8 1 100).erase 3 = (bag 0 0 1 8 1 100) := by rfl
  have hm4 : (bag 0 0 2 8 1 100).erase 4 = (bag 0 0 2 7 1 100) := by rfl
  have hc := count_two (rows.drop 9) (rows.drop 10) (bag 0 0 2 8 1 100) (bag 0 0 1 8 1 100) (bag 0 0 2 7 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_32 cert_50
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_193 : count (rows.drop 10) (bag 0 0 1 8 1 100) (some 1) =
    (X ^ 2 + 117 * X ^ 3 + 1322 * X ^ 4 + 1287 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 1 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm3 : (bag 0 0 1 8 1 100).erase 3 = (bag 0 0 0 8 1 100) := by rfl
  have hm4 : (bag 0 0 1 8 1 100).erase 4 = (bag 0 0 1 7 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 0 0 1 8 1 100) (bag 0 0 0 8 1 100) (bag 0 0 1 7 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_11 cert_31
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_194 : count (rows.drop 11) (bag 0 0 0 8 1 100) (some 1) =
    (X ^ 2 + 104 * X ^ 3 + 198 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 0 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm4 : (bag 0 0 0 8 1 100).erase 4 = (bag 0 0 0 7 1 100) := by rfl
  have hc := count_one (rows.drop 11) (rows.drop 12) (bag 0 0 0 8 1 100) (bag 0 0 0 7 1 100) (some 1) 4 4 hr hs hm4 _ cert_10
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_195 : count (rows.drop 12) (bag 0 0 0 7 1 100) (some 1) =
    (X ^ 2 + 104 * X ^ 3 + 198 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm4 : (bag 0 0 0 7 1 100).erase 4 = (bag 0 0 0 6 1 100) := by rfl
  have hc := count_one (rows.drop 12) (rows.drop 13) (bag 0 0 0 7 1 100) (bag 0 0 0 6 1 100) (some 1) 4 4 hr hs hm4 _ cert_9
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_196 : count (rows.drop 13) (bag 0 0 0 6 1 100) (some 1) =
    (X ^ 2 + 104 * X ^ 3 + 198 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm4 : (bag 0 0 0 6 1 100).erase 4 = (bag 0 0 0 5 1 100) := by rfl
  have hc := count_one (rows.drop 13) (rows.drop 14) (bag 0 0 0 6 1 100) (bag 0 0 0 5 1 100) (some 1) 4 4 hr hs hm4 _ cert_8
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_197 : count (rows.drop 14) (bag 0 0 0 5 1 100) (some 1) =
    (X ^ 2 + 104 * X ^ 3 + 198 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm4 : (bag 0 0 0 5 1 100).erase 4 = (bag 0 0 0 4 1 100) := by rfl
  have hc := count_one (rows.drop 14) (rows.drop 15) (bag 0 0 0 5 1 100) (bag 0 0 0 4 1 100) (some 1) 4 4 hr hs hm4 _ cert_7
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_198 : count (rows.drop 15) (bag 0 0 0 4 1 100) (some 1) =
    (X ^ 2 + 104 * X ^ 3 + 198 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm4 : (bag 0 0 0 4 1 100).erase 4 = (bag 0 0 0 3 1 100) := by rfl
  have hc := count_one (rows.drop 15) (rows.drop 16) (bag 0 0 0 4 1 100) (bag 0 0 0 3 1 100) (some 1) 4 4 hr hs hm4 _ cert_6
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_199 : count (rows.drop 16) (bag 0 0 0 3 1 100) (some 1) =
    (X ^ 2 + 104 * X ^ 3 + 198 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm4 : (bag 0 0 0 3 1 100).erase 4 = (bag 0 0 0 2 1 100) := by rfl
  have hc := count_one (rows.drop 16) (rows.drop 17) (bag 0 0 0 3 1 100) (bag 0 0 0 2 1 100) (some 1) 4 4 hr hs hm4 _ cert_5
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_200 : count (rows.drop 17) (bag 0 0 0 2 1 100) (some 1) =
    (3 * X ^ 2 + 201 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {4, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm4 : (bag 0 0 0 2 1 100).erase 4 = (bag 0 0 0 1 1 100) := by rfl
  have hm5 : (bag 0 0 0 2 1 100).erase 5 = (bag 0 0 0 2 0 100) := by rfl
  have hc := count_two (rows.drop 17) (rows.drop 18) (bag 0 0 0 2 1 100) (bag 0 0 0 1 1 100) (bag 0 0 0 2 0 100) (some 1) 5 4 5 hr hs (by decide) hm4 hm5 _ _ cert_2 cert_4
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_201 : count (rows.drop 18) (bag 0 0 0 1 1 100) (some 1) =
    (3 * X ^ 2 + 199 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 0 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {4, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm4 : (bag 0 0 0 1 1 100).erase 4 = (bag 0 0 0 0 1 100) := by rfl
  have hm5 : (bag 0 0 0 1 1 100).erase 5 = (bag 0 0 0 1 0 100) := by rfl
  have hc := count_two (rows.drop 18) (rows.drop 19) (bag 0 0 0 1 1 100) (bag 0 0 0 0 1 100) (bag 0 0 0 1 0 100) (some 1) 5 4 5 hr hs (by decide) hm4 hm5 _ _ cert_0 cert_1
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_202 : count (rows.drop 19) (bag 0 0 0 0 1 100) (some 1) =
    (X + 100 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (5 ::ₘ Multiset.replicate 100 6) (some 1) = _
  rw [six_tail 99 1 5 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_203 : count (rows.drop 19) (bag 1 0 0 0 0 100) (some 5) =
    (2 * X + 99 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (1 ::ₘ Multiset.replicate 100 6) (some 5) = _
  rw [six_tail 99 5 1 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_204 : count (rows.drop 18) (bag 1 0 0 0 1 100) (some 4) =
    (X + 102 * X ^ 2 + 99 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 1 0 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm1 : (bag 1 0 0 0 1 100).erase 1 = (bag 0 0 0 0 1 100) := by rfl
  have hm5 : (bag 1 0 0 0 1 100).erase 5 = (bag 1 0 0 0 0 100) := by rfl
  have hc := count_two (rows.drop 18) (rows.drop 19) (bag 1 0 0 0 1 100) (bag 0 0 0 0 1 100) (bag 1 0 0 0 0 100) (some 4) 5 1 5 hr hs (by decide) hm1 hm5 _ _ cert_202 cert_203
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_205 : count (rows.drop 19) (bag 0 0 0 1 0 100) (some 1) =
    (X + 100 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (4 ::ₘ Multiset.replicate 100 6) (some 1) = _
  rw [six_tail 99 1 4 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_206 : count (rows.drop 19) (bag 1 0 0 0 0 100) (some 4) =
    (2 * X + 99 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (1 ::ₘ Multiset.replicate 100 6) (some 4) = _
  rw [six_tail 99 4 1 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_207 : count (rows.drop 18) (bag 1 0 0 1 0 100) (some 5) =
    (3 * X + 199 * X ^ 2 : ℕ[X]) := by
  have hs : (bag 1 0 0 1 0 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm1 : (bag 1 0 0 1 0 100).erase 1 = (bag 0 0 0 1 0 100) := by rfl
  have hm4 : (bag 1 0 0 1 0 100).erase 4 = (bag 1 0 0 0 0 100) := by rfl
  have hc := count_two (rows.drop 18) (rows.drop 19) (bag 1 0 0 1 0 100) (bag 0 0 0 1 0 100) (bag 1 0 0 0 0 100) (some 5) 5 1 4 hr hs (by decide) hm1 hm4 _ _ cert_205 cert_206
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_208 : count (rows.drop 17) (bag 1 0 0 1 1 100) (some 4) =
    (X + 108 * X ^ 2 + 497 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 1 0 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1, 4, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm1 : (bag 1 0 0 1 1 100).erase 1 = (bag 0 0 0 1 1 100) := by rfl
  have hm4 : (bag 1 0 0 1 1 100).erase 4 = (bag 1 0 0 0 1 100) := by rfl
  have hm5 : (bag 1 0 0 1 1 100).erase 5 = (bag 1 0 0 1 0 100) := by rfl
  have hc := count_three (rows.drop 17) (rows.drop 18) (bag 1 0 0 1 1 100) (bag 0 0 0 1 1 100) (bag 1 0 0 0 1 100) (bag 1 0 0 1 0 100) (some 4) 5 1 4 5 hr hs (by decide) (by decide) hm1 hm4 hm5 _ _ _ cert_201 cert_204 cert_207
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_209 : count (rows.drop 16) (bag 1 0 0 2 1 100) (some 4) =
    (X + 111 * X ^ 2 + 698 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 0 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 1 0 0 2 1 100).erase 1 = (bag 0 0 0 2 1 100) := by rfl
  have hm4 : (bag 1 0 0 2 1 100).erase 4 = (bag 1 0 0 1 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 1 0 0 2 1 100) (bag 0 0 0 2 1 100) (bag 1 0 0 1 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_200 cert_208
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_210 : count (rows.drop 15) (bag 1 0 0 3 1 100) (some 4) =
    (X + 112 * X ^ 2 + 802 * X ^ 3 + 297 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 0 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 1 0 0 3 1 100).erase 1 = (bag 0 0 0 3 1 100) := by rfl
  have hm4 : (bag 1 0 0 3 1 100).erase 4 = (bag 1 0 0 2 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 1 0 0 3 1 100) (bag 0 0 0 3 1 100) (bag 1 0 0 2 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_199 cert_209
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_211 : count (rows.drop 14) (bag 1 0 0 4 1 100) (some 4) =
    (X + 113 * X ^ 2 + 906 * X ^ 3 + 495 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 0 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 1 0 0 4 1 100).erase 1 = (bag 0 0 0 4 1 100) := by rfl
  have hm4 : (bag 1 0 0 4 1 100).erase 4 = (bag 1 0 0 3 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 1 0 0 4 1 100) (bag 0 0 0 4 1 100) (bag 1 0 0 3 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_198 cert_210
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_212 : count (rows.drop 13) (bag 1 0 0 5 1 100) (some 4) =
    (X + 114 * X ^ 2 + 1010 * X ^ 3 + 693 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 0 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 1 0 0 5 1 100).erase 1 = (bag 0 0 0 5 1 100) := by rfl
  have hm4 : (bag 1 0 0 5 1 100).erase 4 = (bag 1 0 0 4 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 1 0 0 5 1 100) (bag 0 0 0 5 1 100) (bag 1 0 0 4 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_197 cert_211
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_213 : count (rows.drop 12) (bag 1 0 0 6 1 100) (some 4) =
    (X + 115 * X ^ 2 + 1114 * X ^ 3 + 891 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 0 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 1 0 0 6 1 100).erase 1 = (bag 0 0 0 6 1 100) := by rfl
  have hm4 : (bag 1 0 0 6 1 100).erase 4 = (bag 1 0 0 5 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 1 0 0 6 1 100) (bag 0 0 0 6 1 100) (bag 1 0 0 5 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_196 cert_212
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_214 : count (rows.drop 11) (bag 1 0 0 7 1 100) (some 4) =
    (X + 116 * X ^ 2 + 1218 * X ^ 3 + 1089 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 0 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 1 0 0 7 1 100).erase 1 = (bag 0 0 0 7 1 100) := by rfl
  have hm4 : (bag 1 0 0 7 1 100).erase 4 = (bag 1 0 0 6 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 1 0 0 7 1 100) (bag 0 0 0 7 1 100) (bag 1 0 0 6 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_195 cert_213
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_215 : count (rows.drop 10) (bag 1 0 0 8 1 100) (some 3) =
    (2 * X ^ 2 + 220 * X ^ 3 + 1416 * X ^ 4 + 1089 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 0 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 1 0 0 8 1 100).erase 1 = (bag 0 0 0 8 1 100) := by rfl
  have hm4 : (bag 1 0 0 8 1 100).erase 4 = (bag 1 0 0 7 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 1 0 0 8 1 100) (bag 0 0 0 8 1 100) (bag 1 0 0 7 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_194 cert_214
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_216 : count (rows.drop 11) (bag 0 0 1 7 1 100) (some 1) =
    (X ^ 2 + 116 * X ^ 3 + 1218 * X ^ 4 + 1089 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 1 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm3 : (bag 0 0 1 7 1 100).erase 3 = (bag 0 0 0 7 1 100) := by rfl
  have hm4 : (bag 0 0 1 7 1 100).erase 4 = (bag 0 0 1 6 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 0 0 1 7 1 100) (bag 0 0 0 7 1 100) (bag 0 0 1 6 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_12 cert_30
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_217 : count (rows.drop 11) (bag 1 0 0 7 1 100) (some 3) =
    (2 * X ^ 2 + 219 * X ^ 3 + 1312 * X ^ 4 + 891 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 1 0 0 7 1 100).erase 1 = (bag 0 0 0 7 1 100) := by rfl
  have hm4 : (bag 1 0 0 7 1 100).erase 4 = (bag 1 0 0 6 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 1 0 0 7 1 100) (bag 0 0 0 7 1 100) (bag 1 0 0 6 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_195 cert_213
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_218 : count (rows.drop 12) (bag 0 0 1 6 1 100) (some 1) =
    (X ^ 2 + 115 * X ^ 3 + 1114 * X ^ 4 + 891 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 1 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm3 : (bag 0 0 1 6 1 100).erase 3 = (bag 0 0 0 6 1 100) := by rfl
  have hm4 : (bag 0 0 1 6 1 100).erase 4 = (bag 0 0 1 5 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 0 0 1 6 1 100) (bag 0 0 0 6 1 100) (bag 0 0 1 5 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_13 cert_29
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_219 : count (rows.drop 12) (bag 1 0 0 6 1 100) (some 3) =
    (2 * X ^ 2 + 218 * X ^ 3 + 1208 * X ^ 4 + 693 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 1 0 0 6 1 100).erase 1 = (bag 0 0 0 6 1 100) := by rfl
  have hm4 : (bag 1 0 0 6 1 100).erase 4 = (bag 1 0 0 5 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 1 0 0 6 1 100) (bag 0 0 0 6 1 100) (bag 1 0 0 5 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_196 cert_212
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_220 : count (rows.drop 13) (bag 0 0 1 5 1 100) (some 1) =
    (X ^ 2 + 114 * X ^ 3 + 1010 * X ^ 4 + 693 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 1 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm3 : (bag 0 0 1 5 1 100).erase 3 = (bag 0 0 0 5 1 100) := by rfl
  have hm4 : (bag 0 0 1 5 1 100).erase 4 = (bag 0 0 1 4 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 0 0 1 5 1 100) (bag 0 0 0 5 1 100) (bag 0 0 1 4 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_14 cert_28
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_221 : count (rows.drop 13) (bag 1 0 0 5 1 100) (some 3) =
    (2 * X ^ 2 + 217 * X ^ 3 + 1104 * X ^ 4 + 495 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 1 0 0 5 1 100).erase 1 = (bag 0 0 0 5 1 100) := by rfl
  have hm4 : (bag 1 0 0 5 1 100).erase 4 = (bag 1 0 0 4 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 1 0 0 5 1 100) (bag 0 0 0 5 1 100) (bag 1 0 0 4 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_197 cert_211
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_222 : count (rows.drop 14) (bag 0 0 1 4 1 100) (some 1) =
    (X ^ 2 + 113 * X ^ 3 + 906 * X ^ 4 + 495 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 1 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm3 : (bag 0 0 1 4 1 100).erase 3 = (bag 0 0 0 4 1 100) := by rfl
  have hm4 : (bag 0 0 1 4 1 100).erase 4 = (bag 0 0 1 3 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 0 0 1 4 1 100) (bag 0 0 0 4 1 100) (bag 0 0 1 3 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_15 cert_27
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_223 : count (rows.drop 14) (bag 1 0 0 4 1 100) (some 3) =
    (2 * X ^ 2 + 216 * X ^ 3 + 1000 * X ^ 4 + 297 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 1 0 0 4 1 100).erase 1 = (bag 0 0 0 4 1 100) := by rfl
  have hm4 : (bag 1 0 0 4 1 100).erase 4 = (bag 1 0 0 3 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 1 0 0 4 1 100) (bag 0 0 0 4 1 100) (bag 1 0 0 3 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_198 cert_210
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_224 : count (rows.drop 15) (bag 0 0 1 3 1 100) (some 1) =
    (X ^ 2 + 112 * X ^ 3 + 802 * X ^ 4 + 297 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 1 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm3 : (bag 0 0 1 3 1 100).erase 3 = (bag 0 0 0 3 1 100) := by rfl
  have hm4 : (bag 0 0 1 3 1 100).erase 4 = (bag 0 0 1 2 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 0 0 1 3 1 100) (bag 0 0 0 3 1 100) (bag 0 0 1 2 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_16 cert_26
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_225 : count (rows.drop 15) (bag 1 0 0 3 1 100) (some 3) =
    (2 * X ^ 2 + 215 * X ^ 3 + 896 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 1 0 0 3 1 100).erase 1 = (bag 0 0 0 3 1 100) := by rfl
  have hm4 : (bag 1 0 0 3 1 100).erase 4 = (bag 1 0 0 2 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 1 0 0 3 1 100) (bag 0 0 0 3 1 100) (bag 1 0 0 2 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_199 cert_209
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_226 : count (rows.drop 16) (bag 0 0 1 2 1 100) (some 1) =
    (X ^ 2 + 111 * X ^ 3 + 698 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 1 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm3 : (bag 0 0 1 2 1 100).erase 3 = (bag 0 0 0 2 1 100) := by rfl
  have hm4 : (bag 0 0 1 2 1 100).erase 4 = (bag 0 0 1 1 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 0 0 1 2 1 100) (bag 0 0 0 2 1 100) (bag 0 0 1 1 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_17 cert_25
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_227 : count (rows.drop 16) (bag 1 0 0 2 1 100) (some 3) =
    (4 * X ^ 2 + 309 * X ^ 3 + 596 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 0 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 1 0 0 2 1 100).erase 1 = (bag 0 0 0 2 1 100) := by rfl
  have hm4 : (bag 1 0 0 2 1 100).erase 4 = (bag 1 0 0 1 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 1 0 0 2 1 100) (bag 0 0 0 2 1 100) (bag 1 0 0 1 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_200 cert_208
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_228 : count (rows.drop 17) (bag 0 0 1 1 1 100) (some 1) =
    (4 * X ^ 2 + 304 * X ^ 3 + 298 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 1 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {3, 4, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm3 : (bag 0 0 1 1 1 100).erase 3 = (bag 0 0 0 1 1 100) := by rfl
  have hm4 : (bag 0 0 1 1 1 100).erase 4 = (bag 0 0 1 0 1 100) := by rfl
  have hm5 : (bag 0 0 1 1 1 100).erase 5 = (bag 0 0 1 1 0 100) := by rfl
  have hc := count_three (rows.drop 17) (rows.drop 18) (bag 0 0 1 1 1 100) (bag 0 0 0 1 1 100) (bag 0 0 1 0 1 100) (bag 0 0 1 1 0 100) (some 1) 5 3 4 5 hr hs (by decide) (by decide) hm3 hm4 hm5 _ _ _ cert_18 cert_21 cert_24
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_229 : count (rows.drop 17) (bag 1 0 0 1 1 100) (some 3) =
    (7 * X ^ 2 + 500 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 0 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1, 4, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm1 : (bag 1 0 0 1 1 100).erase 1 = (bag 0 0 0 1 1 100) := by rfl
  have hm4 : (bag 1 0 0 1 1 100).erase 4 = (bag 1 0 0 0 1 100) := by rfl
  have hm5 : (bag 1 0 0 1 1 100).erase 5 = (bag 1 0 0 1 0 100) := by rfl
  have hc := count_three (rows.drop 17) (rows.drop 18) (bag 1 0 0 1 1 100) (bag 0 0 0 1 1 100) (bag 1 0 0 0 1 100) (bag 1 0 0 1 0 100) (some 3) 5 1 4 5 hr hs (by decide) (by decide) hm1 hm4 hm5 _ _ _ cert_201 cert_204 cert_207
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_230 : count (rows.drop 18) (bag 0 0 1 0 1 100) (some 1) =
    (3 * X ^ 2 + 199 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 0 1 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {3, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm3 : (bag 0 0 1 0 1 100).erase 3 = (bag 0 0 0 0 1 100) := by rfl
  have hm5 : (bag 0 0 1 0 1 100).erase 5 = (bag 0 0 1 0 0 100) := by rfl
  have hc := count_two (rows.drop 18) (rows.drop 19) (bag 0 0 1 0 1 100) (bag 0 0 0 0 1 100) (bag 0 0 1 0 0 100) (some 1) 5 3 5 hr hs (by decide) hm3 hm5 _ _ cert_19 cert_20
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_231 : count (rows.drop 18) (bag 1 0 0 0 1 100) (some 3) =
    (X + 102 * X ^ 2 + 99 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 1 0 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm1 : (bag 1 0 0 0 1 100).erase 1 = (bag 0 0 0 0 1 100) := by rfl
  have hm5 : (bag 1 0 0 0 1 100).erase 5 = (bag 1 0 0 0 0 100) := by rfl
  have hc := count_two (rows.drop 18) (rows.drop 19) (bag 1 0 0 0 1 100) (bag 0 0 0 0 1 100) (bag 1 0 0 0 0 100) (some 3) 5 1 5 hr hs (by decide) hm1 hm5 _ _ cert_202 cert_203
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_232 : count (rows.drop 19) (bag 0 0 1 0 0 100) (some 1) =
    (X + 100 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (3 ::ₘ Multiset.replicate 100 6) (some 1) = _
  rw [six_tail 99 1 3 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_233 : count (rows.drop 19) (bag 1 0 0 0 0 100) (some 3) =
    (2 * X + 99 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (1 ::ₘ Multiset.replicate 100 6) (some 3) = _
  rw [six_tail 99 3 1 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_234 : count (rows.drop 18) (bag 1 0 1 0 0 100) (some 5) =
    (3 * X + 199 * X ^ 2 : ℕ[X]) := by
  have hs : (bag 1 0 1 0 0 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm1 : (bag 1 0 1 0 0 100).erase 1 = (bag 0 0 1 0 0 100) := by rfl
  have hm3 : (bag 1 0 1 0 0 100).erase 3 = (bag 1 0 0 0 0 100) := by rfl
  have hc := count_two (rows.drop 18) (rows.drop 19) (bag 1 0 1 0 0 100) (bag 0 0 1 0 0 100) (bag 1 0 0 0 0 100) (some 5) 5 1 3 hr hs (by decide) hm1 hm3 _ _ cert_232 cert_233
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_235 : count (rows.drop 17) (bag 1 0 1 0 1 100) (some 4) =
    (X + 108 * X ^ 2 + 497 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 1 0 1 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1, 3, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm1 : (bag 1 0 1 0 1 100).erase 1 = (bag 0 0 1 0 1 100) := by rfl
  have hm3 : (bag 1 0 1 0 1 100).erase 3 = (bag 1 0 0 0 1 100) := by rfl
  have hm5 : (bag 1 0 1 0 1 100).erase 5 = (bag 1 0 1 0 0 100) := by rfl
  have hc := count_three (rows.drop 17) (rows.drop 18) (bag 1 0 1 0 1 100) (bag 0 0 1 0 1 100) (bag 1 0 0 0 1 100) (bag 1 0 1 0 0 100) (some 4) 5 1 3 5 hr hs (by decide) (by decide) hm1 hm3 hm5 _ _ _ cert_230 cert_231 cert_234
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_236 : count (rows.drop 16) (bag 1 0 1 1 1 100) (some 4) =
    (X + 119 * X ^ 2 + 1301 * X ^ 3 + 397 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 0 1 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 1 0 1 1 1 100).erase 1 = (bag 0 0 1 1 1 100) := by rfl
  have hm3 : (bag 1 0 1 1 1 100).erase 3 = (bag 1 0 0 1 1 100) := by rfl
  have hm4 : (bag 1 0 1 1 1 100).erase 4 = (bag 1 0 1 0 1 100) := by rfl
  have hc := count_three (rows.drop 16) (rows.drop 17) (bag 1 0 1 1 1 100) (bag 0 0 1 1 1 100) (bag 1 0 0 1 1 100) (bag 1 0 1 0 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_228 cert_229 cert_235
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_237 : count (rows.drop 15) (bag 1 0 1 2 1 100) (some 4) =
    (X + 124 * X ^ 2 + 1721 * X ^ 3 + 1691 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 1 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 1 0 1 2 1 100).erase 1 = (bag 0 0 1 2 1 100) := by rfl
  have hm3 : (bag 1 0 1 2 1 100).erase 3 = (bag 1 0 0 2 1 100) := by rfl
  have hm4 : (bag 1 0 1 2 1 100).erase 4 = (bag 1 0 1 1 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 1 0 1 2 1 100) (bag 0 0 1 2 1 100) (bag 1 0 0 2 1 100) (bag 1 0 1 1 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_226 cert_227 cert_236
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_238 : count (rows.drop 14) (bag 1 0 1 3 1 100) (some 4) =
    (X + 127 * X ^ 2 + 2048 * X ^ 3 + 3389 * X ^ 4 + 495 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 1 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 1 0 1 3 1 100).erase 1 = (bag 0 0 1 3 1 100) := by rfl
  have hm3 : (bag 1 0 1 3 1 100).erase 3 = (bag 1 0 0 3 1 100) := by rfl
  have hm4 : (bag 1 0 1 3 1 100).erase 4 = (bag 1 0 1 2 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 1 0 1 3 1 100) (bag 0 0 1 3 1 100) (bag 1 0 0 3 1 100) (bag 1 0 1 2 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_224 cert_225 cert_237
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_239 : count (rows.drop 13) (bag 1 0 1 4 1 100) (some 4) =
    (X + 130 * X ^ 2 + 2377 * X ^ 3 + 5295 * X ^ 4 + 1287 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 1 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 1 0 1 4 1 100).erase 1 = (bag 0 0 1 4 1 100) := by rfl
  have hm3 : (bag 1 0 1 4 1 100).erase 3 = (bag 1 0 0 4 1 100) := by rfl
  have hm4 : (bag 1 0 1 4 1 100).erase 4 = (bag 1 0 1 3 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 1 0 1 4 1 100) (bag 0 0 1 4 1 100) (bag 1 0 0 4 1 100) (bag 1 0 1 3 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_222 cert_223 cert_238
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_240 : count (rows.drop 12) (bag 1 0 1 5 1 100) (some 4) =
    (X + 133 * X ^ 2 + 2708 * X ^ 3 + 7409 * X ^ 4 + 2475 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 1 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 1 0 1 5 1 100).erase 1 = (bag 0 0 1 5 1 100) := by rfl
  have hm3 : (bag 1 0 1 5 1 100).erase 3 = (bag 1 0 0 5 1 100) := by rfl
  have hm4 : (bag 1 0 1 5 1 100).erase 4 = (bag 1 0 1 4 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 1 0 1 5 1 100) (bag 0 0 1 5 1 100) (bag 1 0 0 5 1 100) (bag 1 0 1 4 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_220 cert_221 cert_239
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_241 : count (rows.drop 11) (bag 1 0 1 6 1 100) (some 4) =
    (X + 136 * X ^ 2 + 3041 * X ^ 3 + 9731 * X ^ 4 + 4059 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 1 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 1 0 1 6 1 100).erase 1 = (bag 0 0 1 6 1 100) := by rfl
  have hm3 : (bag 1 0 1 6 1 100).erase 3 = (bag 1 0 0 6 1 100) := by rfl
  have hm4 : (bag 1 0 1 6 1 100).erase 4 = (bag 1 0 1 5 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 1 0 1 6 1 100) (bag 0 0 1 6 1 100) (bag 1 0 0 6 1 100) (bag 1 0 1 5 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_218 cert_219 cert_240
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_242 : count (rows.drop 10) (bag 1 0 1 7 1 100) (some 4) =
    (X + 139 * X ^ 2 + 3376 * X ^ 3 + 12261 * X ^ 4 + 6039 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 1 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 1 0 1 7 1 100).erase 1 = (bag 0 0 1 7 1 100) := by rfl
  have hm3 : (bag 1 0 1 7 1 100).erase 3 = (bag 1 0 0 7 1 100) := by rfl
  have hm4 : (bag 1 0 1 7 1 100).erase 4 = (bag 1 0 1 6 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 1 0 1 7 1 100) (bag 0 0 1 7 1 100) (bag 1 0 0 7 1 100) (bag 1 0 1 6 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_216 cert_217 cert_241
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_243 : count (rows.drop 9) (bag 1 0 1 8 1 100) (some 3) =
    (4 * X ^ 2 + 476 * X ^ 3 + 6114 * X ^ 4 + 14637 * X ^ 5 + 6039 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 1 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 1 0 1 8 1 100).erase 1 = (bag 0 0 1 8 1 100) := by rfl
  have hm3 : (bag 1 0 1 8 1 100).erase 3 = (bag 1 0 0 8 1 100) := by rfl
  have hm4 : (bag 1 0 1 8 1 100).erase 4 = (bag 1 0 1 7 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 1 0 1 8 1 100) (bag 0 0 1 8 1 100) (bag 1 0 0 8 1 100) (bag 1 0 1 7 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_193 cert_215 cert_242
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_244 : count (rows.drop 10) (bag 0 0 2 7 1 100) (some 1) =
    (X ^ 2 + 125 * X ^ 3 + 2092 * X ^ 4 + 6215 * X ^ 5 + 2475 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 2 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm3 : (bag 0 0 2 7 1 100).erase 3 = (bag 0 0 1 7 1 100) := by rfl
  have hm4 : (bag 0 0 2 7 1 100).erase 4 = (bag 0 0 2 6 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 0 0 2 7 1 100) (bag 0 0 1 7 1 100) (bag 0 0 2 6 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_33 cert_49
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_245 : count (rows.drop 10) (bag 1 0 1 7 1 100) (some 3) =
    (4 * X ^ 2 + 471 * X ^ 3 + 5571 * X ^ 4 + 11711 * X ^ 5 + 4059 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 1 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 1 0 1 7 1 100).erase 1 = (bag 0 0 1 7 1 100) := by rfl
  have hm3 : (bag 1 0 1 7 1 100).erase 3 = (bag 1 0 0 7 1 100) := by rfl
  have hm4 : (bag 1 0 1 7 1 100).erase 4 = (bag 1 0 1 6 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 1 0 1 7 1 100) (bag 0 0 1 7 1 100) (bag 1 0 0 7 1 100) (bag 1 0 1 6 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_216 cert_217 cert_241
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_246 : count (rows.drop 11) (bag 0 0 2 6 1 100) (some 1) =
    (X ^ 2 + 123 * X ^ 3 + 1873 * X ^ 4 + 4903 * X ^ 5 + 1584 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 2 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm3 : (bag 0 0 2 6 1 100).erase 3 = (bag 0 0 1 6 1 100) := by rfl
  have hm4 : (bag 0 0 2 6 1 100).erase 4 = (bag 0 0 2 5 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 0 0 2 6 1 100) (bag 0 0 1 6 1 100) (bag 0 0 2 5 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_34 cert_48
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_247 : count (rows.drop 11) (bag 1 0 1 6 1 100) (some 3) =
    (4 * X ^ 2 + 466 * X ^ 3 + 5030 * X ^ 4 + 8993 * X ^ 5 + 2475 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 1 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 1 0 1 6 1 100).erase 1 = (bag 0 0 1 6 1 100) := by rfl
  have hm3 : (bag 1 0 1 6 1 100).erase 3 = (bag 1 0 0 6 1 100) := by rfl
  have hm4 : (bag 1 0 1 6 1 100).erase 4 = (bag 1 0 1 5 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 1 0 1 6 1 100) (bag 0 0 1 6 1 100) (bag 1 0 0 6 1 100) (bag 1 0 1 5 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_218 cert_219 cert_240
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_248 : count (rows.drop 12) (bag 0 0 2 5 1 100) (some 1) =
    (X ^ 2 + 121 * X ^ 3 + 1655 * X ^ 4 + 3695 * X ^ 5 + 891 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 2 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm3 : (bag 0 0 2 5 1 100).erase 3 = (bag 0 0 1 5 1 100) := by rfl
  have hm4 : (bag 0 0 2 5 1 100).erase 4 = (bag 0 0 2 4 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 0 0 2 5 1 100) (bag 0 0 1 5 1 100) (bag 0 0 2 4 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_35 cert_47
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_249 : count (rows.drop 12) (bag 1 0 1 5 1 100) (some 3) =
    (4 * X ^ 2 + 461 * X ^ 3 + 4491 * X ^ 4 + 6483 * X ^ 5 + 1287 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 1 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 1 0 1 5 1 100).erase 1 = (bag 0 0 1 5 1 100) := by rfl
  have hm3 : (bag 1 0 1 5 1 100).erase 3 = (bag 1 0 0 5 1 100) := by rfl
  have hm4 : (bag 1 0 1 5 1 100).erase 4 = (bag 1 0 1 4 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 1 0 1 5 1 100) (bag 0 0 1 5 1 100) (bag 1 0 0 5 1 100) (bag 1 0 1 4 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_220 cert_221 cert_239
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_250 : count (rows.drop 13) (bag 0 0 2 4 1 100) (some 1) =
    (X ^ 2 + 119 * X ^ 3 + 1438 * X ^ 4 + 2591 * X ^ 5 + 396 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 2 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm3 : (bag 0 0 2 4 1 100).erase 3 = (bag 0 0 1 4 1 100) := by rfl
  have hm4 : (bag 0 0 2 4 1 100).erase 4 = (bag 0 0 2 3 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 0 0 2 4 1 100) (bag 0 0 1 4 1 100) (bag 0 0 2 3 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_36 cert_46
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_251 : count (rows.drop 13) (bag 1 0 1 4 1 100) (some 3) =
    (4 * X ^ 2 + 456 * X ^ 3 + 3954 * X ^ 4 + 4181 * X ^ 5 + 495 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 1 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 1 0 1 4 1 100).erase 1 = (bag 0 0 1 4 1 100) := by rfl
  have hm3 : (bag 1 0 1 4 1 100).erase 3 = (bag 1 0 0 4 1 100) := by rfl
  have hm4 : (bag 1 0 1 4 1 100).erase 4 = (bag 1 0 1 3 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 1 0 1 4 1 100) (bag 0 0 1 4 1 100) (bag 1 0 0 4 1 100) (bag 1 0 1 3 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_222 cert_223 cert_238
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_252 : count (rows.drop 14) (bag 0 0 2 3 1 100) (some 1) =
    (X ^ 2 + 117 * X ^ 3 + 1222 * X ^ 4 + 1591 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 2 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm3 : (bag 0 0 2 3 1 100).erase 3 = (bag 0 0 1 3 1 100) := by rfl
  have hm4 : (bag 0 0 2 3 1 100).erase 4 = (bag 0 0 2 2 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 0 0 2 3 1 100) (bag 0 0 1 3 1 100) (bag 0 0 2 2 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_37 cert_45
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_253 : count (rows.drop 14) (bag 1 0 1 3 1 100) (some 3) =
    (4 * X ^ 2 + 451 * X ^ 3 + 3419 * X ^ 4 + 2087 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 1 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 1 0 1 3 1 100).erase 1 = (bag 0 0 1 3 1 100) := by rfl
  have hm3 : (bag 1 0 1 3 1 100).erase 3 = (bag 1 0 0 3 1 100) := by rfl
  have hm4 : (bag 1 0 1 3 1 100).erase 4 = (bag 1 0 1 2 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 1 0 1 3 1 100) (bag 0 0 1 3 1 100) (bag 1 0 0 3 1 100) (bag 1 0 1 2 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_224 cert_225 cert_237
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_254 : count (rows.drop 15) (bag 0 0 2 2 1 100) (some 1) =
    (X ^ 2 + 115 * X ^ 3 + 1007 * X ^ 4 + 695 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 2 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm3 : (bag 0 0 2 2 1 100).erase 3 = (bag 0 0 1 2 1 100) := by rfl
  have hm4 : (bag 0 0 2 2 1 100).erase 4 = (bag 0 0 2 1 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 0 0 2 2 1 100) (bag 0 0 1 2 1 100) (bag 0 0 2 1 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_38 cert_44
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_255 : count (rows.drop 15) (bag 1 0 1 2 1 100) (some 3) =
    (6 * X ^ 2 + 539 * X ^ 3 + 2595 * X ^ 4 + 496 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 1 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 1 0 1 2 1 100).erase 1 = (bag 0 0 1 2 1 100) := by rfl
  have hm3 : (bag 1 0 1 2 1 100).erase 3 = (bag 1 0 0 2 1 100) := by rfl
  have hm4 : (bag 1 0 1 2 1 100).erase 4 = (bag 1 0 1 1 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 1 0 1 2 1 100) (bag 0 0 1 2 1 100) (bag 1 0 0 2 1 100) (bag 1 0 1 1 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_226 cert_227 cert_236
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_256 : count (rows.drop 16) (bag 0 0 2 1 1 100) (some 1) =
    (X ^ 2 + 111 * X ^ 3 + 698 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 2 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm3 : (bag 0 0 2 1 1 100).erase 3 = (bag 0 0 1 1 1 100) := by rfl
  have hm4 : (bag 0 0 2 1 1 100).erase 4 = (bag 0 0 2 0 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 0 0 2 1 1 100) (bag 0 0 1 1 1 100) (bag 0 0 2 0 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_39 cert_43
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_257 : count (rows.drop 16) (bag 1 0 1 1 1 100) (some 3) =
    (12 * X ^ 2 + 912 * X ^ 3 + 894 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 0 1 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 1 0 1 1 1 100).erase 1 = (bag 0 0 1 1 1 100) := by rfl
  have hm3 : (bag 1 0 1 1 1 100).erase 3 = (bag 1 0 0 1 1 100) := by rfl
  have hm4 : (bag 1 0 1 1 1 100).erase 4 = (bag 1 0 1 0 1 100) := by rfl
  have hc := count_three (rows.drop 16) (rows.drop 17) (bag 1 0 1 1 1 100) (bag 0 0 1 1 1 100) (bag 1 0 0 1 1 100) (bag 1 0 1 0 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_228 cert_229 cert_235
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_258 : count (rows.drop 17) (bag 0 0 2 0 1 100) (some 1) =
    (3 * X ^ 2 + 201 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 2 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {3, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm3 : (bag 0 0 2 0 1 100).erase 3 = (bag 0 0 1 0 1 100) := by rfl
  have hm5 : (bag 0 0 2 0 1 100).erase 5 = (bag 0 0 2 0 0 100) := by rfl
  have hc := count_two (rows.drop 17) (rows.drop 18) (bag 0 0 2 0 1 100) (bag 0 0 1 0 1 100) (bag 0 0 2 0 0 100) (some 1) 5 3 5 hr hs (by decide) hm3 hm5 _ _ cert_40 cert_42
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_259 : count (rows.drop 17) (bag 1 0 1 0 1 100) (some 3) =
    (X + 108 * X ^ 2 + 497 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 1 0 1 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1, 3, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm1 : (bag 1 0 1 0 1 100).erase 1 = (bag 0 0 1 0 1 100) := by rfl
  have hm3 : (bag 1 0 1 0 1 100).erase 3 = (bag 1 0 0 0 1 100) := by rfl
  have hm5 : (bag 1 0 1 0 1 100).erase 5 = (bag 1 0 1 0 0 100) := by rfl
  have hc := count_three (rows.drop 17) (rows.drop 18) (bag 1 0 1 0 1 100) (bag 0 0 1 0 1 100) (bag 1 0 0 0 1 100) (bag 1 0 1 0 0 100) (some 3) 5 1 3 5 hr hs (by decide) (by decide) hm1 hm3 hm5 _ _ _ cert_230 cert_231 cert_234
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_260 : count (rows.drop 16) (bag 1 0 2 0 1 100) (some 4) =
    (X + 111 * X ^ 2 + 698 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 0 2 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 1 0 2 0 1 100).erase 1 = (bag 0 0 2 0 1 100) := by rfl
  have hm3 : (bag 1 0 2 0 1 100).erase 3 = (bag 1 0 1 0 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 1 0 2 0 1 100) (bag 0 0 2 0 1 100) (bag 1 0 1 0 1 100) (some 4) 4 1 3 hr hs (by decide) hm1 hm3 _ _ cert_258 cert_259
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_261 : count (rows.drop 15) (bag 1 0 2 1 1 100) (some 4) =
    (X + 124 * X ^ 2 + 1721 * X ^ 3 + 1691 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 2 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 1 0 2 1 1 100).erase 1 = (bag 0 0 2 1 1 100) := by rfl
  have hm3 : (bag 1 0 2 1 1 100).erase 3 = (bag 1 0 1 1 1 100) := by rfl
  have hm4 : (bag 1 0 2 1 1 100).erase 4 = (bag 1 0 2 0 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 1 0 2 1 1 100) (bag 0 0 2 1 1 100) (bag 1 0 1 1 1 100) (bag 1 0 2 0 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_256 cert_257 cert_260
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_262 : count (rows.drop 14) (bag 1 0 2 2 1 100) (some 4) =
    (X + 131 * X ^ 2 + 2375 * X ^ 3 + 5293 * X ^ 4 + 1290 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 2 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 1 0 2 2 1 100).erase 1 = (bag 0 0 2 2 1 100) := by rfl
  have hm3 : (bag 1 0 2 2 1 100).erase 3 = (bag 1 0 1 2 1 100) := by rfl
  have hm4 : (bag 1 0 2 2 1 100).erase 4 = (bag 1 0 2 1 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 1 0 2 2 1 100) (bag 0 0 2 2 1 100) (bag 1 0 1 2 1 100) (bag 1 0 2 1 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_254 cert_255 cert_261
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_263 : count (rows.drop 13) (bag 1 0 2 3 1 100) (some 4) =
    (X + 136 * X ^ 2 + 2943 * X ^ 3 + 9934 * X ^ 4 + 4968 * X ^ 5 + 198 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 2 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 1 0 2 3 1 100).erase 1 = (bag 0 0 2 3 1 100) := by rfl
  have hm3 : (bag 1 0 2 3 1 100).erase 3 = (bag 1 0 1 3 1 100) := by rfl
  have hm4 : (bag 1 0 2 3 1 100).erase 4 = (bag 1 0 2 2 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 1 0 2 3 1 100) (bag 0 0 2 3 1 100) (bag 1 0 1 3 1 100) (bag 1 0 2 2 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_252 cert_253 cert_262
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_264 : count (rows.drop 12) (bag 1 0 2 4 1 100) (some 4) =
    (X + 141 * X ^ 2 + 3518 * X ^ 3 + 15326 * X ^ 4 + 11740 * X ^ 5 + 1089 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 2 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 1 0 2 4 1 100).erase 1 = (bag 0 0 2 4 1 100) := by rfl
  have hm3 : (bag 1 0 2 4 1 100).erase 3 = (bag 1 0 1 4 1 100) := by rfl
  have hm4 : (bag 1 0 2 4 1 100).erase 4 = (bag 1 0 2 3 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 1 0 2 4 1 100) (bag 0 0 2 4 1 100) (bag 1 0 1 4 1 100) (bag 1 0 2 3 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_250 cert_251 cert_263
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_265 : count (rows.drop 11) (bag 1 0 2 5 1 100) (some 4) =
    (X + 146 * X ^ 2 + 4100 * X ^ 3 + 21472 * X ^ 4 + 21918 * X ^ 5 + 3267 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 2 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 1 0 2 5 1 100).erase 1 = (bag 0 0 2 5 1 100) := by rfl
  have hm3 : (bag 1 0 2 5 1 100).erase 3 = (bag 1 0 1 5 1 100) := by rfl
  have hm4 : (bag 1 0 2 5 1 100).erase 4 = (bag 1 0 2 4 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 1 0 2 5 1 100) (bag 0 0 2 5 1 100) (bag 1 0 1 5 1 100) (bag 1 0 2 4 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_248 cert_249 cert_264
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_266 : count (rows.drop 10) (bag 1 0 2 6 1 100) (some 4) =
    (X + 151 * X ^ 2 + 4689 * X ^ 3 + 28375 * X ^ 4 + 35814 * X ^ 5 + 7326 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 2 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 1 0 2 6 1 100).erase 1 = (bag 0 0 2 6 1 100) := by rfl
  have hm3 : (bag 1 0 2 6 1 100).erase 3 = (bag 1 0 1 6 1 100) := by rfl
  have hm4 : (bag 1 0 2 6 1 100).erase 4 = (bag 1 0 2 5 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 1 0 2 6 1 100) (bag 0 0 2 6 1 100) (bag 1 0 1 6 1 100) (bag 1 0 2 5 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_246 cert_247 cert_265
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_267 : count (rows.drop 9) (bag 1 0 2 7 1 100) (some 4) =
    (X + 156 * X ^ 2 + 5285 * X ^ 3 + 36038 * X ^ 4 + 53740 * X ^ 5 + 13860 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 2 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 1 0 2 7 1 100).erase 1 = (bag 0 0 2 7 1 100) := by rfl
  have hm3 : (bag 1 0 2 7 1 100).erase 3 = (bag 1 0 1 7 1 100) := by rfl
  have hm4 : (bag 1 0 2 7 1 100).erase 4 = (bag 1 0 2 6 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 1 0 2 7 1 100) (bag 0 0 2 7 1 100) (bag 1 0 1 7 1 100) (bag 1 0 2 6 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_244 cert_245 cert_266
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_268 : count (rows.drop 8) (bag 1 0 2 8 1 100) (some 3) =
    (6 * X ^ 2 + 759 * X ^ 3 + 13711 * X ^ 4 + 58306 * X ^ 5 + 63343 * X ^ 6 + 13860 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 0 2 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm1 : (bag 1 0 2 8 1 100).erase 1 = (bag 0 0 2 8 1 100) := by rfl
  have hm3 : (bag 1 0 2 8 1 100).erase 3 = (bag 1 0 1 8 1 100) := by rfl
  have hm4 : (bag 1 0 2 8 1 100).erase 4 = (bag 1 0 2 7 1 100) := by rfl
  have hc := count_three (rows.drop 8) (rows.drop 9) (bag 1 0 2 8 1 100) (bag 0 0 2 8 1 100) (bag 1 0 1 8 1 100) (bag 1 0 2 7 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_192 cert_243 cert_267
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_269 : count (rows.drop 9) (bag 0 0 3 7 1 100) (some 1) =
    (X ^ 2 + 132 * X ^ 3 + 2902 * X ^ 4 + 14306 * X ^ 5 + 16049 * X ^ 6 + 2970 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 0 3 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm3 : (bag 0 0 3 7 1 100).erase 3 = (bag 0 0 2 7 1 100) := by rfl
  have hm4 : (bag 0 0 3 7 1 100).erase 4 = (bag 0 0 3 6 1 100) := by rfl
  have hc := count_two (rows.drop 9) (rows.drop 10) (bag 0 0 3 7 1 100) (bag 0 0 2 7 1 100) (bag 0 0 3 6 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_52 cert_66
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_270 : count (rows.drop 9) (bag 1 0 2 7 1 100) (some 3) =
    (6 * X ^ 2 + 747 * X ^ 3 + 12352 * X ^ 4 + 46301 * X ^ 5 + 42348 * X ^ 6 + 7326 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 0 2 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 1 0 2 7 1 100).erase 1 = (bag 0 0 2 7 1 100) := by rfl
  have hm3 : (bag 1 0 2 7 1 100).erase 3 = (bag 1 0 1 7 1 100) := by rfl
  have hm4 : (bag 1 0 2 7 1 100).erase 4 = (bag 1 0 2 6 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 1 0 2 7 1 100) (bag 0 0 2 7 1 100) (bag 1 0 1 7 1 100) (bag 1 0 2 6 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_244 cert_245 cert_266
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_271 : count (rows.drop 10) (bag 0 0 3 6 1 100) (some 1) =
    (X ^ 2 + 129 * X ^ 3 + 2560 * X ^ 4 + 11121 * X ^ 5 + 10255 * X ^ 6 + 1386 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 0 3 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm3 : (bag 0 0 3 6 1 100).erase 3 = (bag 0 0 2 6 1 100) := by rfl
  have hm4 : (bag 0 0 3 6 1 100).erase 4 = (bag 0 0 3 5 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 0 0 3 6 1 100) (bag 0 0 2 6 1 100) (bag 0 0 3 5 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_53 cert_65
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_272 : count (rows.drop 10) (bag 1 0 2 6 1 100) (some 3) =
    (6 * X ^ 2 + 735 * X ^ 3 + 11003 * X ^ 4 + 35368 * X ^ 5 + 25977 * X ^ 6 + 3267 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 0 2 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 1 0 2 6 1 100).erase 1 = (bag 0 0 2 6 1 100) := by rfl
  have hm3 : (bag 1 0 2 6 1 100).erase 3 = (bag 1 0 1 6 1 100) := by rfl
  have hm4 : (bag 1 0 2 6 1 100).erase 4 = (bag 1 0 2 5 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 1 0 2 6 1 100) (bag 0 0 2 6 1 100) (bag 1 0 1 6 1 100) (bag 1 0 2 5 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_246 cert_247 cert_265
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_273 : count (rows.drop 11) (bag 0 0 3 5 1 100) (some 1) =
    (X ^ 2 + 126 * X ^ 3 + 2221 * X ^ 4 + 8258 * X ^ 5 + 5867 * X ^ 6 + 495 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 0 3 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm3 : (bag 0 0 3 5 1 100).erase 3 = (bag 0 0 2 5 1 100) := by rfl
  have hm4 : (bag 0 0 3 5 1 100).erase 4 = (bag 0 0 3 4 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 0 0 3 5 1 100) (bag 0 0 2 5 1 100) (bag 0 0 3 4 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_54 cert_64
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_274 : count (rows.drop 11) (bag 1 0 2 5 1 100) (some 3) =
    (6 * X ^ 2 + 723 * X ^ 3 + 9664 * X ^ 4 + 25504 * X ^ 5 + 13918 * X ^ 6 + 1089 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 0 2 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 1 0 2 5 1 100).erase 1 = (bag 0 0 2 5 1 100) := by rfl
  have hm3 : (bag 1 0 2 5 1 100).erase 3 = (bag 1 0 1 5 1 100) := by rfl
  have hm4 : (bag 1 0 2 5 1 100).erase 4 = (bag 1 0 2 4 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 1 0 2 5 1 100) (bag 0 0 2 5 1 100) (bag 1 0 1 5 1 100) (bag 1 0 2 4 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_248 cert_249 cert_264
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_275 : count (rows.drop 12) (bag 0 0 3 4 1 100) (some 1) =
    (X ^ 2 + 123 * X ^ 3 + 1885 * X ^ 4 + 5716 * X ^ 5 + 2781 * X ^ 6 + 99 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 0 3 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm3 : (bag 0 0 3 4 1 100).erase 3 = (bag 0 0 2 4 1 100) := by rfl
  have hm4 : (bag 0 0 3 4 1 100).erase 4 = (bag 0 0 3 3 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 0 0 3 4 1 100) (bag 0 0 2 4 1 100) (bag 0 0 3 3 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_55 cert_63
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_276 : count (rows.drop 12) (bag 1 0 2 4 1 100) (some 3) =
    (6 * X ^ 2 + 711 * X ^ 3 + 8335 * X ^ 4 + 16706 * X ^ 5 + 5859 * X ^ 6 + 198 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 0 2 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 1 0 2 4 1 100).erase 1 = (bag 0 0 2 4 1 100) := by rfl
  have hm3 : (bag 1 0 2 4 1 100).erase 3 = (bag 1 0 1 4 1 100) := by rfl
  have hm4 : (bag 1 0 2 4 1 100).erase 4 = (bag 1 0 2 3 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 1 0 2 4 1 100) (bag 0 0 2 4 1 100) (bag 1 0 1 4 1 100) (bag 1 0 2 3 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_250 cert_251 cert_263
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_277 : count (rows.drop 13) (bag 0 0 3 3 1 100) (some 1) =
    (X ^ 2 + 120 * X ^ 3 + 1552 * X ^ 4 + 3494 * X ^ 5 + 893 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 3 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm3 : (bag 0 0 3 3 1 100).erase 3 = (bag 0 0 2 3 1 100) := by rfl
  have hm4 : (bag 0 0 3 3 1 100).erase 4 = (bag 0 0 3 2 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 0 0 3 3 1 100) (bag 0 0 2 3 1 100) (bag 0 0 3 2 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_56 cert_62
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_278 : count (rows.drop 13) (bag 1 0 2 3 1 100) (some 3) =
    (6 * X ^ 2 + 699 * X ^ 3 + 7016 * X ^ 4 + 8971 * X ^ 5 + 1488 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 2 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 1 0 2 3 1 100).erase 1 = (bag 0 0 2 3 1 100) := by rfl
  have hm3 : (bag 1 0 2 3 1 100).erase 3 = (bag 1 0 1 3 1 100) := by rfl
  have hm4 : (bag 1 0 2 3 1 100).erase 4 = (bag 1 0 2 2 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 1 0 2 3 1 100) (bag 0 0 2 3 1 100) (bag 1 0 1 3 1 100) (bag 1 0 2 2 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_252 cert_253 cert_262
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_279 : count (rows.drop 14) (bag 0 0 3 2 1 100) (some 1) =
    (X ^ 2 + 117 * X ^ 3 + 1222 * X ^ 4 + 1591 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 0 3 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm3 : (bag 0 0 3 2 1 100).erase 3 = (bag 0 0 2 2 1 100) := by rfl
  have hm4 : (bag 0 0 3 2 1 100).erase 4 = (bag 0 0 3 1 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 0 0 3 2 1 100) (bag 0 0 2 2 1 100) (bag 0 0 3 1 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_57 cert_61
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_280 : count (rows.drop 14) (bag 1 0 2 2 1 100) (some 3) =
    (8 * X ^ 2 + 778 * X ^ 3 + 5323 * X ^ 4 + 2882 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 2 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 1 0 2 2 1 100).erase 1 = (bag 0 0 2 2 1 100) := by rfl
  have hm3 : (bag 1 0 2 2 1 100).erase 3 = (bag 1 0 1 2 1 100) := by rfl
  have hm4 : (bag 1 0 2 2 1 100).erase 4 = (bag 1 0 2 1 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 1 0 2 2 1 100) (bag 0 0 2 2 1 100) (bag 1 0 1 2 1 100) (bag 1 0 2 1 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_254 cert_255 cert_261
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_281 : count (rows.drop 15) (bag 0 0 3 1 1 100) (some 1) =
    (X ^ 2 + 112 * X ^ 3 + 802 * X ^ 4 + 297 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 0 3 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm3 : (bag 0 0 3 1 1 100).erase 3 = (bag 0 0 2 1 1 100) := by rfl
  have hm4 : (bag 0 0 3 1 1 100).erase 4 = (bag 0 0 3 0 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 0 0 3 1 1 100) (bag 0 0 2 1 1 100) (bag 0 0 3 0 1 100) (some 1) 4 3 4 hr hs (by decide) hm3 hm4 _ _ cert_58 cert_60
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_282 : count (rows.drop 15) (bag 1 0 2 1 1 100) (some 3) =
    (14 * X ^ 2 + 1134 * X ^ 3 + 2290 * X ^ 4 + 198 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 2 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 1 0 2 1 1 100).erase 1 = (bag 0 0 2 1 1 100) := by rfl
  have hm3 : (bag 1 0 2 1 1 100).erase 3 = (bag 1 0 1 1 1 100) := by rfl
  have hm4 : (bag 1 0 2 1 1 100).erase 4 = (bag 1 0 2 0 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 1 0 2 1 1 100) (bag 0 0 2 1 1 100) (bag 1 0 1 1 1 100) (bag 1 0 2 0 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_256 cert_257 cert_260
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_283 : count (rows.drop 16) (bag 0 0 3 0 1 100) (some 1) =
    (X ^ 2 + 104 * X ^ 3 + 198 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 0 3 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm3 : (bag 0 0 3 0 1 100).erase 3 = (bag 0 0 2 0 1 100) := by rfl
  have hc := count_one (rows.drop 16) (rows.drop 17) (bag 0 0 3 0 1 100) (bag 0 0 2 0 1 100) (some 1) 4 3 hr hs hm3 _ cert_59
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_284 : count (rows.drop 16) (bag 1 0 2 0 1 100) (some 3) =
    (X + 111 * X ^ 2 + 698 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 0 2 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 1 0 2 0 1 100).erase 1 = (bag 0 0 2 0 1 100) := by rfl
  have hm3 : (bag 1 0 2 0 1 100).erase 3 = (bag 1 0 1 0 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 1 0 2 0 1 100) (bag 0 0 2 0 1 100) (bag 1 0 1 0 1 100) (some 3) 4 1 3 hr hs (by decide) hm1 hm3 _ _ cert_258 cert_259
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_285 : count (rows.drop 15) (bag 1 0 3 0 1 100) (some 4) =
    (X + 112 * X ^ 2 + 802 * X ^ 3 + 297 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 0 3 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 1 0 3 0 1 100).erase 1 = (bag 0 0 3 0 1 100) := by rfl
  have hm3 : (bag 1 0 3 0 1 100).erase 3 = (bag 1 0 2 0 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 1 0 3 0 1 100) (bag 0 0 3 0 1 100) (bag 1 0 2 0 1 100) (some 4) 4 1 3 hr hs (by decide) hm1 hm3 _ _ cert_283 cert_284
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_286 : count (rows.drop 14) (bag 1 0 3 1 1 100) (some 4) =
    (X + 127 * X ^ 2 + 2048 * X ^ 3 + 3389 * X ^ 4 + 495 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 3 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 1 0 3 1 1 100).erase 1 = (bag 0 0 3 1 1 100) := by rfl
  have hm3 : (bag 1 0 3 1 1 100).erase 3 = (bag 1 0 2 1 1 100) := by rfl
  have hm4 : (bag 1 0 3 1 1 100).erase 4 = (bag 1 0 3 0 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 1 0 3 1 1 100) (bag 0 0 3 1 1 100) (bag 1 0 2 1 1 100) (bag 1 0 3 0 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_281 cert_282 cert_285
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_287 : count (rows.drop 13) (bag 1 0 3 2 1 100) (some 4) =
    (X + 136 * X ^ 2 + 2943 * X ^ 3 + 9934 * X ^ 4 + 4968 * X ^ 5 + 198 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 3 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 1 0 3 2 1 100).erase 1 = (bag 0 0 3 2 1 100) := by rfl
  have hm3 : (bag 1 0 3 2 1 100).erase 3 = (bag 1 0 2 2 1 100) := by rfl
  have hm4 : (bag 1 0 3 2 1 100).erase 4 = (bag 1 0 3 1 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 1 0 3 2 1 100) (bag 0 0 3 2 1 100) (bag 1 0 2 2 1 100) (bag 1 0 3 1 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_279 cert_280 cert_286
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_288 : count (rows.drop 12) (bag 1 0 3 3 1 100) (some 4) =
    (X + 143 * X ^ 2 + 3762 * X ^ 3 + 18502 * X ^ 4 + 17433 * X ^ 5 + 2579 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 3 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 1 0 3 3 1 100).erase 1 = (bag 0 0 3 3 1 100) := by rfl
  have hm3 : (bag 1 0 3 3 1 100).erase 3 = (bag 1 0 2 3 1 100) := by rfl
  have hm4 : (bag 1 0 3 3 1 100).erase 4 = (bag 1 0 3 2 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 1 0 3 3 1 100) (bag 0 0 3 3 1 100) (bag 1 0 2 3 1 100) (bag 1 0 3 2 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_277 cert_278 cert_287
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_289 : count (rows.drop 11) (bag 1 0 3 4 1 100) (some 4) =
    (X + 150 * X ^ 2 + 4596 * X ^ 3 + 28722 * X ^ 4 + 39855 * X ^ 5 + 11219 * X ^ 6 + 297 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 0 3 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 1 0 3 4 1 100).erase 1 = (bag 0 0 3 4 1 100) := by rfl
  have hm3 : (bag 1 0 3 4 1 100).erase 3 = (bag 1 0 2 4 1 100) := by rfl
  have hm4 : (bag 1 0 3 4 1 100).erase 4 = (bag 1 0 3 3 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 1 0 3 4 1 100) (bag 0 0 3 4 1 100) (bag 1 0 2 4 1 100) (bag 1 0 3 3 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_275 cert_276 cert_288
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_290 : count (rows.drop 10) (bag 1 0 3 5 1 100) (some 4) =
    (X + 157 * X ^ 2 + 5445 * X ^ 3 + 40607 * X ^ 4 + 73617 * X ^ 5 + 31004 * X ^ 6 + 1881 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 0 3 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 1 0 3 5 1 100).erase 1 = (bag 0 0 3 5 1 100) := by rfl
  have hm3 : (bag 1 0 3 5 1 100).erase 3 = (bag 1 0 2 5 1 100) := by rfl
  have hm4 : (bag 1 0 3 5 1 100).erase 4 = (bag 1 0 3 4 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 1 0 3 5 1 100) (bag 0 0 3 5 1 100) (bag 1 0 2 5 1 100) (bag 1 0 3 4 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_273 cert_274 cert_289
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_291 : count (rows.drop 9) (bag 1 0 3 6 1 100) (some 4) =
    (X + 164 * X ^ 2 + 6309 * X ^ 3 + 54170 * X ^ 4 + 120106 * X ^ 5 + 67236 * X ^ 6 + 6534 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 0 3 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 1 0 3 6 1 100).erase 1 = (bag 0 0 3 6 1 100) := by rfl
  have hm3 : (bag 1 0 3 6 1 100).erase 3 = (bag 1 0 2 6 1 100) := by rfl
  have hm4 : (bag 1 0 3 6 1 100).erase 4 = (bag 1 0 3 5 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 1 0 3 6 1 100) (bag 0 0 3 6 1 100) (bag 1 0 2 6 1 100) (bag 1 0 3 5 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_271 cert_272 cert_290
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_292 : count (rows.drop 8) (bag 1 0 3 7 1 100) (some 4) =
    (X + 171 * X ^ 2 + 7188 * X ^ 3 + 69424 * X ^ 4 + 180713 * X ^ 5 + 125633 * X ^ 6 + 16830 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 0 3 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm1 : (bag 1 0 3 7 1 100).erase 1 = (bag 0 0 3 7 1 100) := by rfl
  have hm3 : (bag 1 0 3 7 1 100).erase 3 = (bag 1 0 2 7 1 100) := by rfl
  have hm4 : (bag 1 0 3 7 1 100).erase 4 = (bag 1 0 3 6 1 100) := by rfl
  have hc := count_three (rows.drop 8) (rows.drop 9) (bag 1 0 3 7 1 100) (bag 0 0 3 7 1 100) (bag 1 0 2 7 1 100) (bag 1 0 3 6 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_269 cert_270 cert_291
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_293 : count (rows.drop 7) (bag 1 0 3 8 1 100) (some 3) =
    (8 * X ^ 2 + 1065 * X ^ 3 + 24146 * X ^ 4 + 145544 * X ^ 5 + 267409 * X ^ 6 + 144938 * X ^ 7 + 16830 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 1 0 3 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 7 = 4 :: rows.drop 8 := by rfl
  have hm1 : (bag 1 0 3 8 1 100).erase 1 = (bag 0 0 3 8 1 100) := by rfl
  have hm3 : (bag 1 0 3 8 1 100).erase 3 = (bag 1 0 2 8 1 100) := by rfl
  have hm4 : (bag 1 0 3 8 1 100).erase 4 = (bag 1 0 3 7 1 100) := by rfl
  have hc := count_three (rows.drop 7) (rows.drop 8) (bag 1 0 3 8 1 100) (bag 0 0 3 8 1 100) (bag 1 0 2 8 1 100) (bag 1 0 3 7 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_191 cert_268 cert_292
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_294 : count (rows.drop 6) (bag 1 0 4 8 1 100) (some 2) =
    (X ^ 2 + 151 * X ^ 3 + 5275 * X ^ 4 + 55302 * X ^ 5 + 213680 * X ^ 6 + 308798 * X ^ 7 + 149888 * X ^ 8 + 16830 * X ^ 9 : ℕ[X]) := by
  have hs : (bag 1 0 4 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 6 = 3 :: rows.drop 7 := by rfl
  have hm1 : (bag 1 0 4 8 1 100).erase 1 = (bag 0 0 4 8 1 100) := by rfl
  have hm3 : (bag 1 0 4 8 1 100).erase 3 = (bag 1 0 3 8 1 100) := by rfl
  have hc := count_two (rows.drop 6) (rows.drop 7) (bag 1 0 4 8 1 100) (bag 0 0 4 8 1 100) (bag 1 0 3 8 1 100) (some 2) 3 1 3 hr hs (by decide) hm1 hm3 _ _ cert_190 cert_293
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_295 : count (rows.drop 7) (bag 0 1 3 8 1 100) (some 1) =
    (X ^ 2 + 178 * X ^ 3 + 8082 * X ^ 4 + 86382 * X ^ 5 + 256833 * X ^ 6 + 212329 * X ^ 7 + 36135 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 0 1 3 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 7 = 4 :: rows.drop 8 := by rfl
  have hm2 : (bag 0 1 3 8 1 100).erase 2 = (bag 0 0 3 8 1 100) := by rfl
  have hm3 : (bag 0 1 3 8 1 100).erase 3 = (bag 0 1 2 8 1 100) := by rfl
  have hm4 : (bag 0 1 3 8 1 100).erase 4 = (bag 0 1 3 7 1 100) := by rfl
  have hc := count_three (rows.drop 7) (rows.drop 8) (bag 0 1 3 8 1 100) (bag 0 0 3 8 1 100) (bag 0 1 2 8 1 100) (bag 0 1 3 7 1 100) (some 1) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_86 cert_163 cert_187
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_296 : count (rows.drop 7) (bag 1 0 3 8 1 100) (some 2) =
    (2 * X ^ 2 + 312 * X ^ 3 + 11194 * X ^ 4 + 100949 * X ^ 5 + 262372 * X ^ 6 + 194421 * X ^ 7 + 30690 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 1 0 3 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 7 = 4 :: rows.drop 8 := by rfl
  have hm1 : (bag 1 0 3 8 1 100).erase 1 = (bag 0 0 3 8 1 100) := by rfl
  have hm3 : (bag 1 0 3 8 1 100).erase 3 = (bag 1 0 2 8 1 100) := by rfl
  have hm4 : (bag 1 0 3 8 1 100).erase 4 = (bag 1 0 3 7 1 100) := by rfl
  have hc := count_three (rows.drop 7) (rows.drop 8) (bag 1 0 3 8 1 100) (bag 0 0 3 8 1 100) (bag 1 0 2 8 1 100) (bag 1 0 3 7 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_191 cert_268 cert_292
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_297 : count (rows.drop 8) (bag 0 1 2 8 1 100) (some 1) =
    (X ^ 2 + 161 * X ^ 3 + 5888 * X ^ 4 + 44464 * X ^ 5 + 76008 * X ^ 6 + 23463 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 1 2 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm2 : (bag 0 1 2 8 1 100).erase 2 = (bag 0 0 2 8 1 100) := by rfl
  have hm3 : (bag 0 1 2 8 1 100).erase 3 = (bag 0 1 1 8 1 100) := by rfl
  have hm4 : (bag 0 1 2 8 1 100).erase 4 = (bag 0 1 2 7 1 100) := by rfl
  have hc := count_three (rows.drop 8) (rows.drop 9) (bag 0 1 2 8 1 100) (bag 0 0 2 8 1 100) (bag 0 1 1 8 1 100) (bag 0 1 2 7 1 100) (some 1) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_87 cert_138 cert_162
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_298 : count (rows.drop 8) (bag 1 0 2 8 1 100) (some 2) =
    (2 * X ^ 2 + 287 * X ^ 3 + 8073 * X ^ 4 + 49783 * X ^ 5 + 71941 * X ^ 6 + 19899 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 0 2 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm1 : (bag 1 0 2 8 1 100).erase 1 = (bag 0 0 2 8 1 100) := by rfl
  have hm3 : (bag 1 0 2 8 1 100).erase 3 = (bag 1 0 1 8 1 100) := by rfl
  have hm4 : (bag 1 0 2 8 1 100).erase 4 = (bag 1 0 2 7 1 100) := by rfl
  have hc := count_three (rows.drop 8) (rows.drop 9) (bag 1 0 2 8 1 100) (bag 0 0 2 8 1 100) (bag 1 0 1 8 1 100) (bag 1 0 2 7 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_192 cert_243 cert_267
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_299 : count (rows.drop 9) (bag 0 1 1 8 1 100) (some 1) =
    (X ^ 2 + 142 * X ^ 3 + 3713 * X ^ 4 + 14999 * X ^ 5 + 8415 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 1 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm2 : (bag 0 1 1 8 1 100).erase 2 = (bag 0 0 1 8 1 100) := by rfl
  have hm3 : (bag 0 1 1 8 1 100).erase 3 = (bag 0 1 0 8 1 100) := by rfl
  have hm4 : (bag 0 1 1 8 1 100).erase 4 = (bag 0 1 1 7 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 0 1 1 8 1 100) (bag 0 0 1 8 1 100) (bag 0 1 0 8 1 100) (bag 0 1 1 7 1 100) (some 1) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_88 cert_110 cert_137
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_300 : count (rows.drop 9) (bag 1 0 1 8 1 100) (some 2) =
    (2 * X ^ 2 + 258 * X ^ 3 + 4918 * X ^ 4 + 14964 * X ^ 5 + 7128 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 1 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 1 0 1 8 1 100).erase 1 = (bag 0 0 1 8 1 100) := by rfl
  have hm3 : (bag 1 0 1 8 1 100).erase 3 = (bag 1 0 0 8 1 100) := by rfl
  have hm4 : (bag 1 0 1 8 1 100).erase 4 = (bag 1 0 1 7 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 1 0 1 8 1 100) (bag 0 0 1 8 1 100) (bag 1 0 0 8 1 100) (bag 1 0 1 7 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_193 cert_215 cert_242
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_301 : count (rows.drop 10) (bag 0 1 0 8 1 100) (some 1) =
    (X ^ 2 + 117 * X ^ 3 + 1322 * X ^ 4 + 1287 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 0 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm2 : (bag 0 1 0 8 1 100).erase 2 = (bag 0 0 0 8 1 100) := by rfl
  have hm4 : (bag 0 1 0 8 1 100).erase 4 = (bag 0 1 0 7 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 0 1 0 8 1 100) (bag 0 0 0 8 1 100) (bag 0 1 0 7 1 100) (some 1) 4 2 4 hr hs (by decide) hm2 hm4 _ _ cert_89 cert_109
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_302 : count (rows.drop 10) (bag 1 0 0 8 1 100) (some 2) =
    (2 * X ^ 2 + 220 * X ^ 3 + 1416 * X ^ 4 + 1089 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 0 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 1 0 0 8 1 100).erase 1 = (bag 0 0 0 8 1 100) := by rfl
  have hm4 : (bag 1 0 0 8 1 100).erase 4 = (bag 1 0 0 7 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 1 0 0 8 1 100) (bag 0 0 0 8 1 100) (bag 1 0 0 7 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_194 cert_214
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_303 : count (rows.drop 11) (bag 0 1 0 7 1 100) (some 1) =
    (X ^ 2 + 116 * X ^ 3 + 1218 * X ^ 4 + 1089 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm2 : (bag 0 1 0 7 1 100).erase 2 = (bag 0 0 0 7 1 100) := by rfl
  have hm4 : (bag 0 1 0 7 1 100).erase 4 = (bag 0 1 0 6 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 0 1 0 7 1 100) (bag 0 0 0 7 1 100) (bag 0 1 0 6 1 100) (some 1) 4 2 4 hr hs (by decide) hm2 hm4 _ _ cert_90 cert_108
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_304 : count (rows.drop 11) (bag 1 0 0 7 1 100) (some 2) =
    (2 * X ^ 2 + 219 * X ^ 3 + 1312 * X ^ 4 + 891 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 1 0 0 7 1 100).erase 1 = (bag 0 0 0 7 1 100) := by rfl
  have hm4 : (bag 1 0 0 7 1 100).erase 4 = (bag 1 0 0 6 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 1 0 0 7 1 100) (bag 0 0 0 7 1 100) (bag 1 0 0 6 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_195 cert_213
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_305 : count (rows.drop 12) (bag 0 1 0 6 1 100) (some 1) =
    (X ^ 2 + 115 * X ^ 3 + 1114 * X ^ 4 + 891 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm2 : (bag 0 1 0 6 1 100).erase 2 = (bag 0 0 0 6 1 100) := by rfl
  have hm4 : (bag 0 1 0 6 1 100).erase 4 = (bag 0 1 0 5 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 0 1 0 6 1 100) (bag 0 0 0 6 1 100) (bag 0 1 0 5 1 100) (some 1) 4 2 4 hr hs (by decide) hm2 hm4 _ _ cert_91 cert_107
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_306 : count (rows.drop 12) (bag 1 0 0 6 1 100) (some 2) =
    (2 * X ^ 2 + 218 * X ^ 3 + 1208 * X ^ 4 + 693 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 1 0 0 6 1 100).erase 1 = (bag 0 0 0 6 1 100) := by rfl
  have hm4 : (bag 1 0 0 6 1 100).erase 4 = (bag 1 0 0 5 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 1 0 0 6 1 100) (bag 0 0 0 6 1 100) (bag 1 0 0 5 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_196 cert_212
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_307 : count (rows.drop 13) (bag 0 1 0 5 1 100) (some 1) =
    (X ^ 2 + 114 * X ^ 3 + 1010 * X ^ 4 + 693 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm2 : (bag 0 1 0 5 1 100).erase 2 = (bag 0 0 0 5 1 100) := by rfl
  have hm4 : (bag 0 1 0 5 1 100).erase 4 = (bag 0 1 0 4 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 0 1 0 5 1 100) (bag 0 0 0 5 1 100) (bag 0 1 0 4 1 100) (some 1) 4 2 4 hr hs (by decide) hm2 hm4 _ _ cert_92 cert_106
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_308 : count (rows.drop 13) (bag 1 0 0 5 1 100) (some 2) =
    (2 * X ^ 2 + 217 * X ^ 3 + 1104 * X ^ 4 + 495 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 1 0 0 5 1 100).erase 1 = (bag 0 0 0 5 1 100) := by rfl
  have hm4 : (bag 1 0 0 5 1 100).erase 4 = (bag 1 0 0 4 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 1 0 0 5 1 100) (bag 0 0 0 5 1 100) (bag 1 0 0 4 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_197 cert_211
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_309 : count (rows.drop 14) (bag 0 1 0 4 1 100) (some 1) =
    (X ^ 2 + 113 * X ^ 3 + 906 * X ^ 4 + 495 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm2 : (bag 0 1 0 4 1 100).erase 2 = (bag 0 0 0 4 1 100) := by rfl
  have hm4 : (bag 0 1 0 4 1 100).erase 4 = (bag 0 1 0 3 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 0 1 0 4 1 100) (bag 0 0 0 4 1 100) (bag 0 1 0 3 1 100) (some 1) 4 2 4 hr hs (by decide) hm2 hm4 _ _ cert_93 cert_105
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_310 : count (rows.drop 14) (bag 1 0 0 4 1 100) (some 2) =
    (2 * X ^ 2 + 216 * X ^ 3 + 1000 * X ^ 4 + 297 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 1 0 0 4 1 100).erase 1 = (bag 0 0 0 4 1 100) := by rfl
  have hm4 : (bag 1 0 0 4 1 100).erase 4 = (bag 1 0 0 3 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 1 0 0 4 1 100) (bag 0 0 0 4 1 100) (bag 1 0 0 3 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_198 cert_210
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_311 : count (rows.drop 15) (bag 0 1 0 3 1 100) (some 1) =
    (X ^ 2 + 112 * X ^ 3 + 802 * X ^ 4 + 297 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm2 : (bag 0 1 0 3 1 100).erase 2 = (bag 0 0 0 3 1 100) := by rfl
  have hm4 : (bag 0 1 0 3 1 100).erase 4 = (bag 0 1 0 2 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 0 1 0 3 1 100) (bag 0 0 0 3 1 100) (bag 0 1 0 2 1 100) (some 1) 4 2 4 hr hs (by decide) hm2 hm4 _ _ cert_94 cert_104
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_312 : count (rows.drop 15) (bag 1 0 0 3 1 100) (some 2) =
    (2 * X ^ 2 + 215 * X ^ 3 + 896 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 1 0 0 3 1 100).erase 1 = (bag 0 0 0 3 1 100) := by rfl
  have hm4 : (bag 1 0 0 3 1 100).erase 4 = (bag 1 0 0 2 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 1 0 0 3 1 100) (bag 0 0 0 3 1 100) (bag 1 0 0 2 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_199 cert_209
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_313 : count (rows.drop 16) (bag 0 1 0 2 1 100) (some 1) =
    (X ^ 2 + 111 * X ^ 3 + 698 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm2 : (bag 0 1 0 2 1 100).erase 2 = (bag 0 0 0 2 1 100) := by rfl
  have hm4 : (bag 0 1 0 2 1 100).erase 4 = (bag 0 1 0 1 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 0 1 0 2 1 100) (bag 0 0 0 2 1 100) (bag 0 1 0 1 1 100) (some 1) 4 2 4 hr hs (by decide) hm2 hm4 _ _ cert_95 cert_103
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_314 : count (rows.drop 16) (bag 1 0 0 2 1 100) (some 2) =
    (4 * X ^ 2 + 309 * X ^ 3 + 596 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 0 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 1 0 0 2 1 100).erase 1 = (bag 0 0 0 2 1 100) := by rfl
  have hm4 : (bag 1 0 0 2 1 100).erase 4 = (bag 1 0 0 1 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 1 0 0 2 1 100) (bag 0 0 0 2 1 100) (bag 1 0 0 1 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_200 cert_208
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_315 : count (rows.drop 17) (bag 0 1 0 1 1 100) (some 1) =
    (4 * X ^ 2 + 304 * X ^ 3 + 298 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 1 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {2, 4, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm2 : (bag 0 1 0 1 1 100).erase 2 = (bag 0 0 0 1 1 100) := by rfl
  have hm4 : (bag 0 1 0 1 1 100).erase 4 = (bag 0 1 0 0 1 100) := by rfl
  have hm5 : (bag 0 1 0 1 1 100).erase 5 = (bag 0 1 0 1 0 100) := by rfl
  have hc := count_three (rows.drop 17) (rows.drop 18) (bag 0 1 0 1 1 100) (bag 0 0 0 1 1 100) (bag 0 1 0 0 1 100) (bag 0 1 0 1 0 100) (some 1) 5 2 4 5 hr hs (by decide) (by decide) hm2 hm4 hm5 _ _ _ cert_96 cert_99 cert_102
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_316 : count (rows.drop 17) (bag 1 0 0 1 1 100) (some 2) =
    (7 * X ^ 2 + 500 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 0 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1, 4, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm1 : (bag 1 0 0 1 1 100).erase 1 = (bag 0 0 0 1 1 100) := by rfl
  have hm4 : (bag 1 0 0 1 1 100).erase 4 = (bag 1 0 0 0 1 100) := by rfl
  have hm5 : (bag 1 0 0 1 1 100).erase 5 = (bag 1 0 0 1 0 100) := by rfl
  have hc := count_three (rows.drop 17) (rows.drop 18) (bag 1 0 0 1 1 100) (bag 0 0 0 1 1 100) (bag 1 0 0 0 1 100) (bag 1 0 0 1 0 100) (some 2) 5 1 4 5 hr hs (by decide) (by decide) hm1 hm4 hm5 _ _ _ cert_201 cert_204 cert_207
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_317 : count (rows.drop 18) (bag 0 1 0 0 1 100) (some 1) =
    (3 * X ^ 2 + 199 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 0 1 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {2, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm2 : (bag 0 1 0 0 1 100).erase 2 = (bag 0 0 0 0 1 100) := by rfl
  have hm5 : (bag 0 1 0 0 1 100).erase 5 = (bag 0 1 0 0 0 100) := by rfl
  have hc := count_two (rows.drop 18) (rows.drop 19) (bag 0 1 0 0 1 100) (bag 0 0 0 0 1 100) (bag 0 1 0 0 0 100) (some 1) 5 2 5 hr hs (by decide) hm2 hm5 _ _ cert_97 cert_98
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_318 : count (rows.drop 18) (bag 1 0 0 0 1 100) (some 2) =
    (X + 102 * X ^ 2 + 99 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 1 0 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm1 : (bag 1 0 0 0 1 100).erase 1 = (bag 0 0 0 0 1 100) := by rfl
  have hm5 : (bag 1 0 0 0 1 100).erase 5 = (bag 1 0 0 0 0 100) := by rfl
  have hc := count_two (rows.drop 18) (rows.drop 19) (bag 1 0 0 0 1 100) (bag 0 0 0 0 1 100) (bag 1 0 0 0 0 100) (some 2) 5 1 5 hr hs (by decide) hm1 hm5 _ _ cert_202 cert_203
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_319 : count (rows.drop 19) (bag 0 1 0 0 0 100) (some 1) =
    (X + 100 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (2 ::ₘ Multiset.replicate 100 6) (some 1) = _
  rw [six_tail 99 1 2 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_320 : count (rows.drop 19) (bag 1 0 0 0 0 100) (some 2) =
    (2 * X + 99 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (1 ::ₘ Multiset.replicate 100 6) (some 2) = _
  rw [six_tail 99 2 1 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_321 : count (rows.drop 18) (bag 1 1 0 0 0 100) (some 5) =
    (3 * X + 199 * X ^ 2 : ℕ[X]) := by
  have hs : (bag 1 1 0 0 0 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1, 2} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm1 : (bag 1 1 0 0 0 100).erase 1 = (bag 0 1 0 0 0 100) := by rfl
  have hm2 : (bag 1 1 0 0 0 100).erase 2 = (bag 1 0 0 0 0 100) := by rfl
  have hc := count_two (rows.drop 18) (rows.drop 19) (bag 1 1 0 0 0 100) (bag 0 1 0 0 0 100) (bag 1 0 0 0 0 100) (some 5) 5 1 2 hr hs (by decide) hm1 hm2 _ _ cert_319 cert_320
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_322 : count (rows.drop 17) (bag 1 1 0 0 1 100) (some 4) =
    (X + 108 * X ^ 2 + 497 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 1 1 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1, 2, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm1 : (bag 1 1 0 0 1 100).erase 1 = (bag 0 1 0 0 1 100) := by rfl
  have hm2 : (bag 1 1 0 0 1 100).erase 2 = (bag 1 0 0 0 1 100) := by rfl
  have hm5 : (bag 1 1 0 0 1 100).erase 5 = (bag 1 1 0 0 0 100) := by rfl
  have hc := count_three (rows.drop 17) (rows.drop 18) (bag 1 1 0 0 1 100) (bag 0 1 0 0 1 100) (bag 1 0 0 0 1 100) (bag 1 1 0 0 0 100) (some 4) 5 1 2 5 hr hs (by decide) (by decide) hm1 hm2 hm5 _ _ _ cert_317 cert_318 cert_321
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_323 : count (rows.drop 16) (bag 1 1 0 1 1 100) (some 4) =
    (X + 119 * X ^ 2 + 1301 * X ^ 3 + 397 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 1 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 1 1 0 1 1 100).erase 1 = (bag 0 1 0 1 1 100) := by rfl
  have hm2 : (bag 1 1 0 1 1 100).erase 2 = (bag 1 0 0 1 1 100) := by rfl
  have hm4 : (bag 1 1 0 1 1 100).erase 4 = (bag 1 1 0 0 1 100) := by rfl
  have hc := count_three (rows.drop 16) (rows.drop 17) (bag 1 1 0 1 1 100) (bag 0 1 0 1 1 100) (bag 1 0 0 1 1 100) (bag 1 1 0 0 1 100) (some 4) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_315 cert_316 cert_322
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_324 : count (rows.drop 15) (bag 1 1 0 2 1 100) (some 4) =
    (X + 124 * X ^ 2 + 1721 * X ^ 3 + 1691 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 1 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 1 1 0 2 1 100).erase 1 = (bag 0 1 0 2 1 100) := by rfl
  have hm2 : (bag 1 1 0 2 1 100).erase 2 = (bag 1 0 0 2 1 100) := by rfl
  have hm4 : (bag 1 1 0 2 1 100).erase 4 = (bag 1 1 0 1 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 1 1 0 2 1 100) (bag 0 1 0 2 1 100) (bag 1 0 0 2 1 100) (bag 1 1 0 1 1 100) (some 4) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_313 cert_314 cert_323
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_325 : count (rows.drop 14) (bag 1 1 0 3 1 100) (some 4) =
    (X + 127 * X ^ 2 + 2048 * X ^ 3 + 3389 * X ^ 4 + 495 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 1 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 1 1 0 3 1 100).erase 1 = (bag 0 1 0 3 1 100) := by rfl
  have hm2 : (bag 1 1 0 3 1 100).erase 2 = (bag 1 0 0 3 1 100) := by rfl
  have hm4 : (bag 1 1 0 3 1 100).erase 4 = (bag 1 1 0 2 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 1 1 0 3 1 100) (bag 0 1 0 3 1 100) (bag 1 0 0 3 1 100) (bag 1 1 0 2 1 100) (some 4) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_311 cert_312 cert_324
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_326 : count (rows.drop 13) (bag 1 1 0 4 1 100) (some 4) =
    (X + 130 * X ^ 2 + 2377 * X ^ 3 + 5295 * X ^ 4 + 1287 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 1 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 1 1 0 4 1 100).erase 1 = (bag 0 1 0 4 1 100) := by rfl
  have hm2 : (bag 1 1 0 4 1 100).erase 2 = (bag 1 0 0 4 1 100) := by rfl
  have hm4 : (bag 1 1 0 4 1 100).erase 4 = (bag 1 1 0 3 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 1 1 0 4 1 100) (bag 0 1 0 4 1 100) (bag 1 0 0 4 1 100) (bag 1 1 0 3 1 100) (some 4) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_309 cert_310 cert_325
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_327 : count (rows.drop 12) (bag 1 1 0 5 1 100) (some 4) =
    (X + 133 * X ^ 2 + 2708 * X ^ 3 + 7409 * X ^ 4 + 2475 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 1 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 1 1 0 5 1 100).erase 1 = (bag 0 1 0 5 1 100) := by rfl
  have hm2 : (bag 1 1 0 5 1 100).erase 2 = (bag 1 0 0 5 1 100) := by rfl
  have hm4 : (bag 1 1 0 5 1 100).erase 4 = (bag 1 1 0 4 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 1 1 0 5 1 100) (bag 0 1 0 5 1 100) (bag 1 0 0 5 1 100) (bag 1 1 0 4 1 100) (some 4) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_307 cert_308 cert_326
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_328 : count (rows.drop 11) (bag 1 1 0 6 1 100) (some 4) =
    (X + 136 * X ^ 2 + 3041 * X ^ 3 + 9731 * X ^ 4 + 4059 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 1 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 1 1 0 6 1 100).erase 1 = (bag 0 1 0 6 1 100) := by rfl
  have hm2 : (bag 1 1 0 6 1 100).erase 2 = (bag 1 0 0 6 1 100) := by rfl
  have hm4 : (bag 1 1 0 6 1 100).erase 4 = (bag 1 1 0 5 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 1 1 0 6 1 100) (bag 0 1 0 6 1 100) (bag 1 0 0 6 1 100) (bag 1 1 0 5 1 100) (some 4) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_305 cert_306 cert_327
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_329 : count (rows.drop 10) (bag 1 1 0 7 1 100) (some 4) =
    (X + 139 * X ^ 2 + 3376 * X ^ 3 + 12261 * X ^ 4 + 6039 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 1 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 1 1 0 7 1 100).erase 1 = (bag 0 1 0 7 1 100) := by rfl
  have hm2 : (bag 1 1 0 7 1 100).erase 2 = (bag 1 0 0 7 1 100) := by rfl
  have hm4 : (bag 1 1 0 7 1 100).erase 4 = (bag 1 1 0 6 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 1 1 0 7 1 100) (bag 0 1 0 7 1 100) (bag 1 0 0 7 1 100) (bag 1 1 0 6 1 100) (some 4) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_303 cert_304 cert_328
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_330 : count (rows.drop 9) (bag 1 1 0 8 1 100) (some 3) =
    (4 * X ^ 2 + 476 * X ^ 3 + 6114 * X ^ 4 + 14637 * X ^ 5 + 6039 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 0 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 1 1 0 8 1 100).erase 1 = (bag 0 1 0 8 1 100) := by rfl
  have hm2 : (bag 1 1 0 8 1 100).erase 2 = (bag 1 0 0 8 1 100) := by rfl
  have hm4 : (bag 1 1 0 8 1 100).erase 4 = (bag 1 1 0 7 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 1 1 0 8 1 100) (bag 0 1 0 8 1 100) (bag 1 0 0 8 1 100) (bag 1 1 0 7 1 100) (some 3) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_301 cert_302 cert_329
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_331 : count (rows.drop 10) (bag 0 1 1 7 1 100) (some 1) =
    (X ^ 2 + 139 * X ^ 3 + 3376 * X ^ 4 + 12261 * X ^ 5 + 6039 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 1 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm2 : (bag 0 1 1 7 1 100).erase 2 = (bag 0 0 1 7 1 100) := by rfl
  have hm3 : (bag 0 1 1 7 1 100).erase 3 = (bag 0 1 0 7 1 100) := by rfl
  have hm4 : (bag 0 1 1 7 1 100).erase 4 = (bag 0 1 1 6 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 0 1 1 7 1 100) (bag 0 0 1 7 1 100) (bag 0 1 0 7 1 100) (bag 0 1 1 6 1 100) (some 1) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_111 cert_112 cert_136
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_332 : count (rows.drop 10) (bag 1 0 1 7 1 100) (some 2) =
    (2 * X ^ 2 + 254 * X ^ 3 + 4478 * X ^ 4 + 12132 * X ^ 5 + 4950 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 1 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 1 0 1 7 1 100).erase 1 = (bag 0 0 1 7 1 100) := by rfl
  have hm3 : (bag 1 0 1 7 1 100).erase 3 = (bag 1 0 0 7 1 100) := by rfl
  have hm4 : (bag 1 0 1 7 1 100).erase 4 = (bag 1 0 1 6 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 1 0 1 7 1 100) (bag 0 0 1 7 1 100) (bag 1 0 0 7 1 100) (bag 1 0 1 6 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_216 cert_217 cert_241
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_333 : count (rows.drop 10) (bag 1 1 0 7 1 100) (some 3) =
    (4 * X ^ 2 + 471 * X ^ 3 + 5571 * X ^ 4 + 11711 * X ^ 5 + 4059 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 1 1 0 7 1 100).erase 1 = (bag 0 1 0 7 1 100) := by rfl
  have hm2 : (bag 1 1 0 7 1 100).erase 2 = (bag 1 0 0 7 1 100) := by rfl
  have hm4 : (bag 1 1 0 7 1 100).erase 4 = (bag 1 1 0 6 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 1 1 0 7 1 100) (bag 0 1 0 7 1 100) (bag 1 0 0 7 1 100) (bag 1 1 0 6 1 100) (some 3) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_303 cert_304 cert_328
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_334 : count (rows.drop 11) (bag 0 1 1 6 1 100) (some 1) =
    (X ^ 2 + 136 * X ^ 3 + 3041 * X ^ 4 + 9731 * X ^ 5 + 4059 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 1 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm2 : (bag 0 1 1 6 1 100).erase 2 = (bag 0 0 1 6 1 100) := by rfl
  have hm3 : (bag 0 1 1 6 1 100).erase 3 = (bag 0 1 0 6 1 100) := by rfl
  have hm4 : (bag 0 1 1 6 1 100).erase 4 = (bag 0 1 1 5 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 0 1 1 6 1 100) (bag 0 0 1 6 1 100) (bag 0 1 0 6 1 100) (bag 0 1 1 5 1 100) (some 1) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_113 cert_114 cert_135
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_335 : count (rows.drop 11) (bag 1 0 1 6 1 100) (some 2) =
    (2 * X ^ 2 + 250 * X ^ 3 + 4040 * X ^ 4 + 9508 * X ^ 5 + 3168 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 1 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 1 0 1 6 1 100).erase 1 = (bag 0 0 1 6 1 100) := by rfl
  have hm3 : (bag 1 0 1 6 1 100).erase 3 = (bag 1 0 0 6 1 100) := by rfl
  have hm4 : (bag 1 0 1 6 1 100).erase 4 = (bag 1 0 1 5 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 1 0 1 6 1 100) (bag 0 0 1 6 1 100) (bag 1 0 0 6 1 100) (bag 1 0 1 5 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_218 cert_219 cert_240
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_336 : count (rows.drop 11) (bag 1 1 0 6 1 100) (some 3) =
    (4 * X ^ 2 + 466 * X ^ 3 + 5030 * X ^ 4 + 8993 * X ^ 5 + 2475 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 1 1 0 6 1 100).erase 1 = (bag 0 1 0 6 1 100) := by rfl
  have hm2 : (bag 1 1 0 6 1 100).erase 2 = (bag 1 0 0 6 1 100) := by rfl
  have hm4 : (bag 1 1 0 6 1 100).erase 4 = (bag 1 1 0 5 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 1 1 0 6 1 100) (bag 0 1 0 6 1 100) (bag 1 0 0 6 1 100) (bag 1 1 0 5 1 100) (some 3) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_305 cert_306 cert_327
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_337 : count (rows.drop 12) (bag 0 1 1 5 1 100) (some 1) =
    (X ^ 2 + 133 * X ^ 3 + 2708 * X ^ 4 + 7409 * X ^ 5 + 2475 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 1 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm2 : (bag 0 1 1 5 1 100).erase 2 = (bag 0 0 1 5 1 100) := by rfl
  have hm3 : (bag 0 1 1 5 1 100).erase 3 = (bag 0 1 0 5 1 100) := by rfl
  have hm4 : (bag 0 1 1 5 1 100).erase 4 = (bag 0 1 1 4 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 0 1 1 5 1 100) (bag 0 0 1 5 1 100) (bag 0 1 0 5 1 100) (bag 0 1 1 4 1 100) (some 1) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_115 cert_116 cert_134
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_338 : count (rows.drop 12) (bag 1 0 1 5 1 100) (some 2) =
    (2 * X ^ 2 + 246 * X ^ 3 + 3604 * X ^ 4 + 7092 * X ^ 5 + 1782 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 1 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 1 0 1 5 1 100).erase 1 = (bag 0 0 1 5 1 100) := by rfl
  have hm3 : (bag 1 0 1 5 1 100).erase 3 = (bag 1 0 0 5 1 100) := by rfl
  have hm4 : (bag 1 0 1 5 1 100).erase 4 = (bag 1 0 1 4 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 1 0 1 5 1 100) (bag 0 0 1 5 1 100) (bag 1 0 0 5 1 100) (bag 1 0 1 4 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_220 cert_221 cert_239
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_339 : count (rows.drop 12) (bag 1 1 0 5 1 100) (some 3) =
    (4 * X ^ 2 + 461 * X ^ 3 + 4491 * X ^ 4 + 6483 * X ^ 5 + 1287 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 1 1 0 5 1 100).erase 1 = (bag 0 1 0 5 1 100) := by rfl
  have hm2 : (bag 1 1 0 5 1 100).erase 2 = (bag 1 0 0 5 1 100) := by rfl
  have hm4 : (bag 1 1 0 5 1 100).erase 4 = (bag 1 1 0 4 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 1 1 0 5 1 100) (bag 0 1 0 5 1 100) (bag 1 0 0 5 1 100) (bag 1 1 0 4 1 100) (some 3) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_307 cert_308 cert_326
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_340 : count (rows.drop 13) (bag 0 1 1 4 1 100) (some 1) =
    (X ^ 2 + 130 * X ^ 3 + 2377 * X ^ 4 + 5295 * X ^ 5 + 1287 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 1 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm2 : (bag 0 1 1 4 1 100).erase 2 = (bag 0 0 1 4 1 100) := by rfl
  have hm3 : (bag 0 1 1 4 1 100).erase 3 = (bag 0 1 0 4 1 100) := by rfl
  have hm4 : (bag 0 1 1 4 1 100).erase 4 = (bag 0 1 1 3 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 0 1 1 4 1 100) (bag 0 0 1 4 1 100) (bag 0 1 0 4 1 100) (bag 0 1 1 3 1 100) (some 1) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_117 cert_118 cert_133
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_341 : count (rows.drop 13) (bag 1 0 1 4 1 100) (some 2) =
    (2 * X ^ 2 + 242 * X ^ 3 + 3170 * X ^ 4 + 4884 * X ^ 5 + 792 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 1 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 1 0 1 4 1 100).erase 1 = (bag 0 0 1 4 1 100) := by rfl
  have hm3 : (bag 1 0 1 4 1 100).erase 3 = (bag 1 0 0 4 1 100) := by rfl
  have hm4 : (bag 1 0 1 4 1 100).erase 4 = (bag 1 0 1 3 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 1 0 1 4 1 100) (bag 0 0 1 4 1 100) (bag 1 0 0 4 1 100) (bag 1 0 1 3 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_222 cert_223 cert_238
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_342 : count (rows.drop 13) (bag 1 1 0 4 1 100) (some 3) =
    (4 * X ^ 2 + 456 * X ^ 3 + 3954 * X ^ 4 + 4181 * X ^ 5 + 495 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 1 1 0 4 1 100).erase 1 = (bag 0 1 0 4 1 100) := by rfl
  have hm2 : (bag 1 1 0 4 1 100).erase 2 = (bag 1 0 0 4 1 100) := by rfl
  have hm4 : (bag 1 1 0 4 1 100).erase 4 = (bag 1 1 0 3 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 1 1 0 4 1 100) (bag 0 1 0 4 1 100) (bag 1 0 0 4 1 100) (bag 1 1 0 3 1 100) (some 3) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_309 cert_310 cert_325
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_343 : count (rows.drop 14) (bag 0 1 1 3 1 100) (some 1) =
    (X ^ 2 + 127 * X ^ 3 + 2048 * X ^ 4 + 3389 * X ^ 5 + 495 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 1 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm2 : (bag 0 1 1 3 1 100).erase 2 = (bag 0 0 1 3 1 100) := by rfl
  have hm3 : (bag 0 1 1 3 1 100).erase 3 = (bag 0 1 0 3 1 100) := by rfl
  have hm4 : (bag 0 1 1 3 1 100).erase 4 = (bag 0 1 1 2 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 0 1 1 3 1 100) (bag 0 0 1 3 1 100) (bag 0 1 0 3 1 100) (bag 0 1 1 2 1 100) (some 1) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_119 cert_120 cert_132
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_344 : count (rows.drop 14) (bag 1 0 1 3 1 100) (some 2) =
    (2 * X ^ 2 + 238 * X ^ 3 + 2738 * X ^ 4 + 2884 * X ^ 5 + 198 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 1 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 1 0 1 3 1 100).erase 1 = (bag 0 0 1 3 1 100) := by rfl
  have hm3 : (bag 1 0 1 3 1 100).erase 3 = (bag 1 0 0 3 1 100) := by rfl
  have hm4 : (bag 1 0 1 3 1 100).erase 4 = (bag 1 0 1 2 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 1 0 1 3 1 100) (bag 0 0 1 3 1 100) (bag 1 0 0 3 1 100) (bag 1 0 1 2 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_224 cert_225 cert_237
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_345 : count (rows.drop 14) (bag 1 1 0 3 1 100) (some 3) =
    (4 * X ^ 2 + 451 * X ^ 3 + 3419 * X ^ 4 + 2087 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 1 1 0 3 1 100).erase 1 = (bag 0 1 0 3 1 100) := by rfl
  have hm2 : (bag 1 1 0 3 1 100).erase 2 = (bag 1 0 0 3 1 100) := by rfl
  have hm4 : (bag 1 1 0 3 1 100).erase 4 = (bag 1 1 0 2 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 1 1 0 3 1 100) (bag 0 1 0 3 1 100) (bag 1 0 0 3 1 100) (bag 1 1 0 2 1 100) (some 3) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_311 cert_312 cert_324
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_346 : count (rows.drop 15) (bag 0 1 1 2 1 100) (some 1) =
    (X ^ 2 + 124 * X ^ 3 + 1721 * X ^ 4 + 1691 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 1 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm2 : (bag 0 1 1 2 1 100).erase 2 = (bag 0 0 1 2 1 100) := by rfl
  have hm3 : (bag 0 1 1 2 1 100).erase 3 = (bag 0 1 0 2 1 100) := by rfl
  have hm4 : (bag 0 1 1 2 1 100).erase 4 = (bag 0 1 1 1 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 0 1 1 2 1 100) (bag 0 0 1 2 1 100) (bag 0 1 0 2 1 100) (bag 0 1 1 1 1 100) (some 1) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_121 cert_122 cert_131
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_347 : count (rows.drop 15) (bag 1 0 1 2 1 100) (some 2) =
    (2 * X ^ 2 + 234 * X ^ 3 + 2308 * X ^ 4 + 1092 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 1 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 1 0 1 2 1 100).erase 1 = (bag 0 0 1 2 1 100) := by rfl
  have hm3 : (bag 1 0 1 2 1 100).erase 3 = (bag 1 0 0 2 1 100) := by rfl
  have hm4 : (bag 1 0 1 2 1 100).erase 4 = (bag 1 0 1 1 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 1 0 1 2 1 100) (bag 0 0 1 2 1 100) (bag 1 0 0 2 1 100) (bag 1 0 1 1 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_226 cert_227 cert_236
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_348 : count (rows.drop 15) (bag 1 1 0 2 1 100) (some 3) =
    (6 * X ^ 2 + 539 * X ^ 3 + 2595 * X ^ 4 + 496 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 1 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 1 1 0 2 1 100).erase 1 = (bag 0 1 0 2 1 100) := by rfl
  have hm2 : (bag 1 1 0 2 1 100).erase 2 = (bag 1 0 0 2 1 100) := by rfl
  have hm4 : (bag 1 1 0 2 1 100).erase 4 = (bag 1 1 0 1 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 1 1 0 2 1 100) (bag 0 1 0 2 1 100) (bag 1 0 0 2 1 100) (bag 1 1 0 1 1 100) (some 3) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_313 cert_314 cert_323
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_349 : count (rows.drop 16) (bag 0 1 1 1 1 100) (some 1) =
    (X ^ 2 + 119 * X ^ 3 + 1301 * X ^ 4 + 397 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 1 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm2 : (bag 0 1 1 1 1 100).erase 2 = (bag 0 0 1 1 1 100) := by rfl
  have hm3 : (bag 0 1 1 1 1 100).erase 3 = (bag 0 1 0 1 1 100) := by rfl
  have hm4 : (bag 0 1 1 1 1 100).erase 4 = (bag 0 1 1 0 1 100) := by rfl
  have hc := count_three (rows.drop 16) (rows.drop 17) (bag 0 1 1 1 1 100) (bag 0 0 1 1 1 100) (bag 0 1 0 1 1 100) (bag 0 1 1 0 1 100) (some 1) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_123 cert_124 cert_130
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_350 : count (rows.drop 16) (bag 1 0 1 1 1 100) (some 2) =
    (5 * X ^ 2 + 419 * X ^ 3 + 1295 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 1 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 1 0 1 1 1 100).erase 1 = (bag 0 0 1 1 1 100) := by rfl
  have hm3 : (bag 1 0 1 1 1 100).erase 3 = (bag 1 0 0 1 1 100) := by rfl
  have hm4 : (bag 1 0 1 1 1 100).erase 4 = (bag 1 0 1 0 1 100) := by rfl
  have hc := count_three (rows.drop 16) (rows.drop 17) (bag 1 0 1 1 1 100) (bag 0 0 1 1 1 100) (bag 1 0 0 1 1 100) (bag 1 0 1 0 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_228 cert_229 cert_235
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_351 : count (rows.drop 16) (bag 1 1 0 1 1 100) (some 3) =
    (12 * X ^ 2 + 912 * X ^ 3 + 894 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 1 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 1 1 0 1 1 100).erase 1 = (bag 0 1 0 1 1 100) := by rfl
  have hm2 : (bag 1 1 0 1 1 100).erase 2 = (bag 1 0 0 1 1 100) := by rfl
  have hm4 : (bag 1 1 0 1 1 100).erase 4 = (bag 1 1 0 0 1 100) := by rfl
  have hc := count_three (rows.drop 16) (rows.drop 17) (bag 1 1 0 1 1 100) (bag 0 1 0 1 1 100) (bag 1 0 0 1 1 100) (bag 1 1 0 0 1 100) (some 3) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_315 cert_316 cert_322
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_352 : count (rows.drop 17) (bag 0 1 1 0 1 100) (some 1) =
    (4 * X ^ 2 + 304 * X ^ 3 + 298 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 0 1 1 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {2, 3, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm2 : (bag 0 1 1 0 1 100).erase 2 = (bag 0 0 1 0 1 100) := by rfl
  have hm3 : (bag 0 1 1 0 1 100).erase 3 = (bag 0 1 0 0 1 100) := by rfl
  have hm5 : (bag 0 1 1 0 1 100).erase 5 = (bag 0 1 1 0 0 100) := by rfl
  have hc := count_three (rows.drop 17) (rows.drop 18) (bag 0 1 1 0 1 100) (bag 0 0 1 0 1 100) (bag 0 1 0 0 1 100) (bag 0 1 1 0 0 100) (some 1) 5 2 3 5 hr hs (by decide) (by decide) hm2 hm3 hm5 _ _ _ cert_125 cert_126 cert_129
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_353 : count (rows.drop 17) (bag 1 0 1 0 1 100) (some 2) =
    (7 * X ^ 2 + 500 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 0 1 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1, 3, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm1 : (bag 1 0 1 0 1 100).erase 1 = (bag 0 0 1 0 1 100) := by rfl
  have hm3 : (bag 1 0 1 0 1 100).erase 3 = (bag 1 0 0 0 1 100) := by rfl
  have hm5 : (bag 1 0 1 0 1 100).erase 5 = (bag 1 0 1 0 0 100) := by rfl
  have hc := count_three (rows.drop 17) (rows.drop 18) (bag 1 0 1 0 1 100) (bag 0 0 1 0 1 100) (bag 1 0 0 0 1 100) (bag 1 0 1 0 0 100) (some 2) 5 1 3 5 hr hs (by decide) (by decide) hm1 hm3 hm5 _ _ _ cert_230 cert_231 cert_234
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_354 : count (rows.drop 17) (bag 1 1 0 0 1 100) (some 3) =
    (X + 108 * X ^ 2 + 497 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 1 1 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1, 2, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm1 : (bag 1 1 0 0 1 100).erase 1 = (bag 0 1 0 0 1 100) := by rfl
  have hm2 : (bag 1 1 0 0 1 100).erase 2 = (bag 1 0 0 0 1 100) := by rfl
  have hm5 : (bag 1 1 0 0 1 100).erase 5 = (bag 1 1 0 0 0 100) := by rfl
  have hc := count_three (rows.drop 17) (rows.drop 18) (bag 1 1 0 0 1 100) (bag 0 1 0 0 1 100) (bag 1 0 0 0 1 100) (bag 1 1 0 0 0 100) (some 3) 5 1 2 5 hr hs (by decide) (by decide) hm1 hm2 hm5 _ _ _ cert_317 cert_318 cert_321
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_355 : count (rows.drop 16) (bag 1 1 1 0 1 100) (some 4) =
    (X + 119 * X ^ 2 + 1301 * X ^ 3 + 397 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 1 1 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 1 1 1 0 1 100).erase 1 = (bag 0 1 1 0 1 100) := by rfl
  have hm2 : (bag 1 1 1 0 1 100).erase 2 = (bag 1 0 1 0 1 100) := by rfl
  have hm3 : (bag 1 1 1 0 1 100).erase 3 = (bag 1 1 0 0 1 100) := by rfl
  have hc := count_three (rows.drop 16) (rows.drop 17) (bag 1 1 1 0 1 100) (bag 0 1 1 0 1 100) (bag 1 0 1 0 1 100) (bag 1 1 0 0 1 100) (some 4) 4 1 2 3 hr hs (by decide) (by decide) hm1 hm2 hm3 _ _ _ cert_352 cert_353 cert_354
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_356 : count (rows.drop 15) (bag 1 1 1 1 1 100) (some 4) =
    (X + 137 * X ^ 2 + 2751 * X ^ 3 + 3887 * X ^ 4 + 496 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 1 1 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 1 1 1 1 1 100).erase 1 = (bag 0 1 1 1 1 100) := by rfl
  have hm2 : (bag 1 1 1 1 1 100).erase 2 = (bag 1 0 1 1 1 100) := by rfl
  have hm3 : (bag 1 1 1 1 1 100).erase 3 = (bag 1 1 0 1 1 100) := by rfl
  have hm4 : (bag 1 1 1 1 1 100).erase 4 = (bag 1 1 1 0 1 100) := by rfl
  have hc := count_four (rows.drop 15) (rows.drop 16) (bag 1 1 1 1 1 100) (bag 0 1 1 1 1 100) (bag 1 0 1 1 1 100) (bag 1 1 0 1 1 100) (bag 1 1 1 0 1 100) (some 4) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_349 cert_350 cert_351 cert_355
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_357 : count (rows.drop 14) (bag 1 1 1 2 1 100) (some 4) =
    (X + 146 * X ^ 2 + 3648 * X ^ 3 + 10511 * X ^ 4 + 3775 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 1 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 1 1 1 2 1 100).erase 1 = (bag 0 1 1 2 1 100) := by rfl
  have hm2 : (bag 1 1 1 2 1 100).erase 2 = (bag 1 0 1 2 1 100) := by rfl
  have hm3 : (bag 1 1 1 2 1 100).erase 3 = (bag 1 1 0 2 1 100) := by rfl
  have hm4 : (bag 1 1 1 2 1 100).erase 4 = (bag 1 1 1 1 1 100) := by rfl
  have hc := count_four (rows.drop 14) (rows.drop 15) (bag 1 1 1 2 1 100) (bag 0 1 1 2 1 100) (bag 1 0 1 2 1 100) (bag 1 1 0 2 1 100) (bag 1 1 1 1 1 100) (some 4) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_346 cert_347 cert_348 cert_356
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_358 : count (rows.drop 13) (bag 1 1 1 3 1 100) (some 4) =
    (X + 153 * X ^ 2 + 4464 * X ^ 3 + 18716 * X ^ 4 + 12135 * X ^ 5 + 891 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 1 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 1 1 1 3 1 100).erase 1 = (bag 0 1 1 3 1 100) := by rfl
  have hm2 : (bag 1 1 1 3 1 100).erase 2 = (bag 1 0 1 3 1 100) := by rfl
  have hm3 : (bag 1 1 1 3 1 100).erase 3 = (bag 1 1 0 3 1 100) := by rfl
  have hm4 : (bag 1 1 1 3 1 100).erase 4 = (bag 1 1 1 2 1 100) := by rfl
  have hc := count_four (rows.drop 13) (rows.drop 14) (bag 1 1 1 3 1 100) (bag 0 1 1 3 1 100) (bag 1 0 1 3 1 100) (bag 1 1 0 3 1 100) (bag 1 1 1 2 1 100) (some 4) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_343 cert_344 cert_345 cert_357
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_359 : count (rows.drop 12) (bag 1 1 1 4 1 100) (some 4) =
    (X + 160 * X ^ 2 + 5292 * X ^ 3 + 28217 * X ^ 4 + 26495 * X ^ 5 + 3465 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 1 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 1 1 1 4 1 100).erase 1 = (bag 0 1 1 4 1 100) := by rfl
  have hm2 : (bag 1 1 1 4 1 100).erase 2 = (bag 1 0 1 4 1 100) := by rfl
  have hm3 : (bag 1 1 1 4 1 100).erase 3 = (bag 1 1 0 4 1 100) := by rfl
  have hm4 : (bag 1 1 1 4 1 100).erase 4 = (bag 1 1 1 3 1 100) := by rfl
  have hc := count_four (rows.drop 12) (rows.drop 13) (bag 1 1 1 4 1 100) (bag 0 1 1 4 1 100) (bag 1 0 1 4 1 100) (bag 1 1 0 4 1 100) (bag 1 1 1 3 1 100) (some 4) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_340 cert_341 cert_342 cert_358
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_360 : count (rows.drop 11) (bag 1 1 1 5 1 100) (some 4) =
    (X + 167 * X ^ 2 + 6132 * X ^ 3 + 39020 * X ^ 4 + 47479 * X ^ 5 + 9009 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 1 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 1 1 1 5 1 100).erase 1 = (bag 0 1 1 5 1 100) := by rfl
  have hm2 : (bag 1 1 1 5 1 100).erase 2 = (bag 1 0 1 5 1 100) := by rfl
  have hm3 : (bag 1 1 1 5 1 100).erase 3 = (bag 1 1 0 5 1 100) := by rfl
  have hm4 : (bag 1 1 1 5 1 100).erase 4 = (bag 1 1 1 4 1 100) := by rfl
  have hc := count_four (rows.drop 11) (rows.drop 12) (bag 1 1 1 5 1 100) (bag 0 1 1 5 1 100) (bag 1 0 1 5 1 100) (bag 1 1 0 5 1 100) (bag 1 1 1 4 1 100) (some 4) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_337 cert_338 cert_339 cert_359
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_361 : count (rows.drop 10) (bag 1 1 1 6 1 100) (some 4) =
    (X + 174 * X ^ 2 + 6984 * X ^ 3 + 51131 * X ^ 4 + 75711 * X ^ 5 + 18711 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 1 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 1 1 1 6 1 100).erase 1 = (bag 0 1 1 6 1 100) := by rfl
  have hm2 : (bag 1 1 1 6 1 100).erase 2 = (bag 1 0 1 6 1 100) := by rfl
  have hm3 : (bag 1 1 1 6 1 100).erase 3 = (bag 1 1 0 6 1 100) := by rfl
  have hm4 : (bag 1 1 1 6 1 100).erase 4 = (bag 1 1 1 5 1 100) := by rfl
  have hc := count_four (rows.drop 10) (rows.drop 11) (bag 1 1 1 6 1 100) (bag 0 1 1 6 1 100) (bag 1 0 1 6 1 100) (bag 1 1 0 6 1 100) (bag 1 1 1 5 1 100) (some 4) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_334 cert_335 cert_336 cert_360
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_362 : count (rows.drop 9) (bag 1 1 1 7 1 100) (some 4) =
    (X + 181 * X ^ 2 + 7848 * X ^ 3 + 64556 * X ^ 4 + 111815 * X ^ 5 + 33759 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 1 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 1 1 1 7 1 100).erase 1 = (bag 0 1 1 7 1 100) := by rfl
  have hm2 : (bag 1 1 1 7 1 100).erase 2 = (bag 1 0 1 7 1 100) := by rfl
  have hm3 : (bag 1 1 1 7 1 100).erase 3 = (bag 1 1 0 7 1 100) := by rfl
  have hm4 : (bag 1 1 1 7 1 100).erase 4 = (bag 1 1 1 6 1 100) := by rfl
  have hc := count_four (rows.drop 9) (rows.drop 10) (bag 1 1 1 7 1 100) (bag 0 1 1 7 1 100) (bag 1 0 1 7 1 100) (bag 1 1 0 7 1 100) (bag 1 1 1 6 1 100) (some 4) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_331 cert_332 cert_333 cert_361
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_363 : count (rows.drop 8) (bag 1 1 1 8 1 100) (some 3) =
    (8 * X ^ 2 + 1057 * X ^ 3 + 22593 * X ^ 4 + 109156 * X ^ 5 + 133397 * X ^ 6 + 33759 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 1 1 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm1 : (bag 1 1 1 8 1 100).erase 1 = (bag 0 1 1 8 1 100) := by rfl
  have hm2 : (bag 1 1 1 8 1 100).erase 2 = (bag 1 0 1 8 1 100) := by rfl
  have hm3 : (bag 1 1 1 8 1 100).erase 3 = (bag 1 1 0 8 1 100) := by rfl
  have hm4 : (bag 1 1 1 8 1 100).erase 4 = (bag 1 1 1 7 1 100) := by rfl
  have hc := count_four (rows.drop 8) (rows.drop 9) (bag 1 1 1 8 1 100) (bag 0 1 1 8 1 100) (bag 1 0 1 8 1 100) (bag 1 1 0 8 1 100) (bag 1 1 1 7 1 100) (some 3) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_299 cert_300 cert_330 cert_362
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_364 : count (rows.drop 9) (bag 0 1 2 7 1 100) (some 1) =
    (X ^ 2 + 156 * X ^ 3 + 5285 * X ^ 4 + 36038 * X ^ 5 + 53740 * X ^ 6 + 13860 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 1 2 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm2 : (bag 0 1 2 7 1 100).erase 2 = (bag 0 0 2 7 1 100) := by rfl
  have hm3 : (bag 0 1 2 7 1 100).erase 3 = (bag 0 1 1 7 1 100) := by rfl
  have hm4 : (bag 0 1 2 7 1 100).erase 4 = (bag 0 1 2 6 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 0 1 2 7 1 100) (bag 0 0 2 7 1 100) (bag 0 1 1 7 1 100) (bag 0 1 2 6 1 100) (some 1) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_139 cert_140 cert_161
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_365 : count (rows.drop 9) (bag 1 0 2 7 1 100) (some 2) =
    (2 * X ^ 2 + 280 * X ^ 3 + 7252 * X ^ 4 + 40161 * X ^ 5 + 50000 * X ^ 6 + 11385 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 0 2 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 1 0 2 7 1 100).erase 1 = (bag 0 0 2 7 1 100) := by rfl
  have hm3 : (bag 1 0 2 7 1 100).erase 3 = (bag 1 0 1 7 1 100) := by rfl
  have hm4 : (bag 1 0 2 7 1 100).erase 4 = (bag 1 0 2 6 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 1 0 2 7 1 100) (bag 0 0 2 7 1 100) (bag 1 0 1 7 1 100) (bag 1 0 2 6 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_244 cert_245 cert_266
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_366 : count (rows.drop 9) (bag 1 1 1 7 1 100) (some 3) =
    (8 * X ^ 2 + 1038 * X ^ 3 + 20409 * X ^ 4 + 87235 * X ^ 5 + 90759 * X ^ 6 + 18711 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 1 1 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 1 1 1 7 1 100).erase 1 = (bag 0 1 1 7 1 100) := by rfl
  have hm2 : (bag 1 1 1 7 1 100).erase 2 = (bag 1 0 1 7 1 100) := by rfl
  have hm3 : (bag 1 1 1 7 1 100).erase 3 = (bag 1 1 0 7 1 100) := by rfl
  have hm4 : (bag 1 1 1 7 1 100).erase 4 = (bag 1 1 1 6 1 100) := by rfl
  have hc := count_four (rows.drop 9) (rows.drop 10) (bag 1 1 1 7 1 100) (bag 0 1 1 7 1 100) (bag 1 0 1 7 1 100) (bag 1 1 0 7 1 100) (bag 1 1 1 6 1 100) (some 3) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_331 cert_332 cert_333 cert_361
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_367 : count (rows.drop 10) (bag 0 1 2 6 1 100) (some 1) =
    (X ^ 2 + 151 * X ^ 3 + 4689 * X ^ 4 + 28375 * X ^ 5 + 35814 * X ^ 6 + 7326 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 1 2 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm2 : (bag 0 1 2 6 1 100).erase 2 = (bag 0 0 2 6 1 100) := by rfl
  have hm3 : (bag 0 1 2 6 1 100).erase 3 = (bag 0 1 1 6 1 100) := by rfl
  have hm4 : (bag 0 1 2 6 1 100).erase 4 = (bag 0 1 2 5 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 0 1 2 6 1 100) (bag 0 0 2 6 1 100) (bag 0 1 1 6 1 100) (bag 0 1 2 5 1 100) (some 1) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_141 cert_142 cert_160
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_368 : count (rows.drop 10) (bag 1 0 2 6 1 100) (some 2) =
    (2 * X ^ 2 + 273 * X ^ 3 + 6439 * X ^ 4 + 31405 * X ^ 5 + 32495 * X ^ 6 + 5742 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 0 2 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 1 0 2 6 1 100).erase 1 = (bag 0 0 2 6 1 100) := by rfl
  have hm3 : (bag 1 0 2 6 1 100).erase 3 = (bag 1 0 1 6 1 100) := by rfl
  have hm4 : (bag 1 0 2 6 1 100).erase 4 = (bag 1 0 2 5 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 1 0 2 6 1 100) (bag 0 0 2 6 1 100) (bag 1 0 1 6 1 100) (bag 1 0 2 5 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_246 cert_247 cert_265
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_369 : count (rows.drop 10) (bag 1 1 1 6 1 100) (some 3) =
    (8 * X ^ 2 + 1019 * X ^ 3 + 18243 * X ^ 4 + 67252 * X ^ 5 + 57181 * X ^ 6 + 9009 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 1 1 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 1 1 1 6 1 100).erase 1 = (bag 0 1 1 6 1 100) := by rfl
  have hm2 : (bag 1 1 1 6 1 100).erase 2 = (bag 1 0 1 6 1 100) := by rfl
  have hm3 : (bag 1 1 1 6 1 100).erase 3 = (bag 1 1 0 6 1 100) := by rfl
  have hm4 : (bag 1 1 1 6 1 100).erase 4 = (bag 1 1 1 5 1 100) := by rfl
  have hc := count_four (rows.drop 10) (rows.drop 11) (bag 1 1 1 6 1 100) (bag 0 1 1 6 1 100) (bag 1 0 1 6 1 100) (bag 1 1 0 6 1 100) (bag 1 1 1 5 1 100) (some 3) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_334 cert_335 cert_336 cert_360
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_370 : count (rows.drop 11) (bag 0 1 2 5 1 100) (some 1) =
    (X ^ 2 + 146 * X ^ 3 + 4100 * X ^ 4 + 21472 * X ^ 5 + 21918 * X ^ 6 + 3267 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 1 2 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm2 : (bag 0 1 2 5 1 100).erase 2 = (bag 0 0 2 5 1 100) := by rfl
  have hm3 : (bag 0 1 2 5 1 100).erase 3 = (bag 0 1 1 5 1 100) := by rfl
  have hm4 : (bag 0 1 2 5 1 100).erase 4 = (bag 0 1 2 4 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 0 1 2 5 1 100) (bag 0 0 2 5 1 100) (bag 0 1 1 5 1 100) (bag 0 1 2 4 1 100) (some 1) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_143 cert_144 cert_159
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_371 : count (rows.drop 11) (bag 1 0 2 5 1 100) (some 2) =
    (2 * X ^ 2 + 266 * X ^ 3 + 5634 * X ^ 4 + 23512 * X ^ 5 + 19114 * X ^ 6 + 2376 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 0 2 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 1 0 2 5 1 100).erase 1 = (bag 0 0 2 5 1 100) := by rfl
  have hm3 : (bag 1 0 2 5 1 100).erase 3 = (bag 1 0 1 5 1 100) := by rfl
  have hm4 : (bag 1 0 2 5 1 100).erase 4 = (bag 1 0 2 4 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 1 0 2 5 1 100) (bag 0 0 2 5 1 100) (bag 1 0 1 5 1 100) (bag 1 0 2 4 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_248 cert_249 cert_264
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_372 : count (rows.drop 11) (bag 1 1 1 5 1 100) (some 3) =
    (8 * X ^ 2 + 1000 * X ^ 3 + 16095 * X ^ 4 + 49201 * X ^ 5 + 32039 * X ^ 6 + 3465 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 1 1 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 1 1 1 5 1 100).erase 1 = (bag 0 1 1 5 1 100) := by rfl
  have hm2 : (bag 1 1 1 5 1 100).erase 2 = (bag 1 0 1 5 1 100) := by rfl
  have hm3 : (bag 1 1 1 5 1 100).erase 3 = (bag 1 1 0 5 1 100) := by rfl
  have hm4 : (bag 1 1 1 5 1 100).erase 4 = (bag 1 1 1 4 1 100) := by rfl
  have hc := count_four (rows.drop 11) (rows.drop 12) (bag 1 1 1 5 1 100) (bag 0 1 1 5 1 100) (bag 1 0 1 5 1 100) (bag 1 1 0 5 1 100) (bag 1 1 1 4 1 100) (some 3) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_337 cert_338 cert_339 cert_359
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_373 : count (rows.drop 12) (bag 0 1 2 4 1 100) (some 1) =
    (X ^ 2 + 141 * X ^ 3 + 3518 * X ^ 4 + 15326 * X ^ 5 + 11740 * X ^ 6 + 1089 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 1 2 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm2 : (bag 0 1 2 4 1 100).erase 2 = (bag 0 0 2 4 1 100) := by rfl
  have hm3 : (bag 0 1 2 4 1 100).erase 3 = (bag 0 1 1 4 1 100) := by rfl
  have hm4 : (bag 0 1 2 4 1 100).erase 4 = (bag 0 1 2 3 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 0 1 2 4 1 100) (bag 0 0 2 4 1 100) (bag 0 1 1 4 1 100) (bag 0 1 2 3 1 100) (some 1) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_145 cert_146 cert_158
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_374 : count (rows.drop 12) (bag 1 0 2 4 1 100) (some 2) =
    (2 * X ^ 2 + 259 * X ^ 3 + 4837 * X ^ 4 + 16479 * X ^ 5 + 9545 * X ^ 6 + 693 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 0 2 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 1 0 2 4 1 100).erase 1 = (bag 0 0 2 4 1 100) := by rfl
  have hm3 : (bag 1 0 2 4 1 100).erase 3 = (bag 1 0 1 4 1 100) := by rfl
  have hm4 : (bag 1 0 2 4 1 100).erase 4 = (bag 1 0 2 3 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 1 0 2 4 1 100) (bag 0 0 2 4 1 100) (bag 1 0 1 4 1 100) (bag 1 0 2 3 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_250 cert_251 cert_263
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_375 : count (rows.drop 12) (bag 1 1 1 4 1 100) (some 3) =
    (8 * X ^ 2 + 981 * X ^ 3 + 13965 * X ^ 4 + 33076 * X ^ 5 + 14709 * X ^ 6 + 891 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 1 1 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 1 1 1 4 1 100).erase 1 = (bag 0 1 1 4 1 100) := by rfl
  have hm2 : (bag 1 1 1 4 1 100).erase 2 = (bag 1 0 1 4 1 100) := by rfl
  have hm3 : (bag 1 1 1 4 1 100).erase 3 = (bag 1 1 0 4 1 100) := by rfl
  have hm4 : (bag 1 1 1 4 1 100).erase 4 = (bag 1 1 1 3 1 100) := by rfl
  have hc := count_four (rows.drop 12) (rows.drop 13) (bag 1 1 1 4 1 100) (bag 0 1 1 4 1 100) (bag 1 0 1 4 1 100) (bag 1 1 0 4 1 100) (bag 1 1 1 3 1 100) (some 3) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_340 cert_341 cert_342 cert_358
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_376 : count (rows.drop 13) (bag 0 1 2 3 1 100) (some 1) =
    (X ^ 2 + 136 * X ^ 3 + 2943 * X ^ 4 + 9934 * X ^ 5 + 4968 * X ^ 6 + 198 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 0 1 2 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm2 : (bag 0 1 2 3 1 100).erase 2 = (bag 0 0 2 3 1 100) := by rfl
  have hm3 : (bag 0 1 2 3 1 100).erase 3 = (bag 0 1 1 3 1 100) := by rfl
  have hm4 : (bag 0 1 2 3 1 100).erase 4 = (bag 0 1 2 2 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 0 1 2 3 1 100) (bag 0 0 2 3 1 100) (bag 0 1 1 3 1 100) (bag 0 1 2 2 1 100) (some 1) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_147 cert_148 cert_157
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_377 : count (rows.drop 13) (bag 1 0 2 3 1 100) (some 2) =
    (2 * X ^ 2 + 252 * X ^ 3 + 4048 * X ^ 4 + 10303 * X ^ 5 + 3476 * X ^ 6 + 99 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 0 2 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 1 0 2 3 1 100).erase 1 = (bag 0 0 2 3 1 100) := by rfl
  have hm3 : (bag 1 0 2 3 1 100).erase 3 = (bag 1 0 1 3 1 100) := by rfl
  have hm4 : (bag 1 0 2 3 1 100).erase 4 = (bag 1 0 2 2 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 1 0 2 3 1 100) (bag 0 0 2 3 1 100) (bag 1 0 1 3 1 100) (bag 1 0 2 2 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_252 cert_253 cert_262
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_378 : count (rows.drop 13) (bag 1 1 1 3 1 100) (some 3) =
    (8 * X ^ 2 + 962 * X ^ 3 + 11853 * X ^ 4 + 18871 * X ^ 5 + 4567 * X ^ 6 + 99 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 1 1 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 1 1 1 3 1 100).erase 1 = (bag 0 1 1 3 1 100) := by rfl
  have hm2 : (bag 1 1 1 3 1 100).erase 2 = (bag 1 0 1 3 1 100) := by rfl
  have hm3 : (bag 1 1 1 3 1 100).erase 3 = (bag 1 1 0 3 1 100) := by rfl
  have hm4 : (bag 1 1 1 3 1 100).erase 4 = (bag 1 1 1 2 1 100) := by rfl
  have hc := count_four (rows.drop 13) (rows.drop 14) (bag 1 1 1 3 1 100) (bag 0 1 1 3 1 100) (bag 1 0 1 3 1 100) (bag 1 1 0 3 1 100) (bag 1 1 1 2 1 100) (some 3) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_343 cert_344 cert_345 cert_357
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_379 : count (rows.drop 14) (bag 0 1 2 2 1 100) (some 1) =
    (X ^ 2 + 131 * X ^ 3 + 2375 * X ^ 4 + 5293 * X ^ 5 + 1290 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 2 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm2 : (bag 0 1 2 2 1 100).erase 2 = (bag 0 0 2 2 1 100) := by rfl
  have hm3 : (bag 0 1 2 2 1 100).erase 3 = (bag 0 1 1 2 1 100) := by rfl
  have hm4 : (bag 0 1 2 2 1 100).erase 4 = (bag 0 1 2 1 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 0 1 2 2 1 100) (bag 0 0 2 2 1 100) (bag 0 1 1 2 1 100) (bag 0 1 2 1 1 100) (some 1) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_149 cert_150 cert_156
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_380 : count (rows.drop 14) (bag 1 0 2 2 1 100) (some 2) =
    (2 * X ^ 2 + 245 * X ^ 3 + 3267 * X ^ 4 + 4981 * X ^ 5 + 595 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 2 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 1 0 2 2 1 100).erase 1 = (bag 0 0 2 2 1 100) := by rfl
  have hm3 : (bag 1 0 2 2 1 100).erase 3 = (bag 1 0 1 2 1 100) := by rfl
  have hm4 : (bag 1 0 2 2 1 100).erase 4 = (bag 1 0 2 1 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 1 0 2 2 1 100) (bag 0 0 2 2 1 100) (bag 1 0 1 2 1 100) (bag 1 0 2 1 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_254 cert_255 cert_261
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_381 : count (rows.drop 14) (bag 1 1 1 2 1 100) (some 3) =
    (10 * X ^ 2 + 1034 * X ^ 3 + 9375 * X ^ 4 + 7166 * X ^ 5 + 595 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 1 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 1 1 1 2 1 100).erase 1 = (bag 0 1 1 2 1 100) := by rfl
  have hm2 : (bag 1 1 1 2 1 100).erase 2 = (bag 1 0 1 2 1 100) := by rfl
  have hm3 : (bag 1 1 1 2 1 100).erase 3 = (bag 1 1 0 2 1 100) := by rfl
  have hm4 : (bag 1 1 1 2 1 100).erase 4 = (bag 1 1 1 1 1 100) := by rfl
  have hc := count_four (rows.drop 14) (rows.drop 15) (bag 1 1 1 2 1 100) (bag 0 1 1 2 1 100) (bag 1 0 1 2 1 100) (bag 1 1 0 2 1 100) (bag 1 1 1 1 1 100) (some 3) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_346 cert_347 cert_348 cert_356
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_382 : count (rows.drop 15) (bag 0 1 2 1 1 100) (some 1) =
    (X ^ 2 + 124 * X ^ 3 + 1721 * X ^ 4 + 1691 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 0 1 2 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm2 : (bag 0 1 2 1 1 100).erase 2 = (bag 0 0 2 1 1 100) := by rfl
  have hm3 : (bag 0 1 2 1 1 100).erase 3 = (bag 0 1 1 1 1 100) := by rfl
  have hm4 : (bag 0 1 2 1 1 100).erase 4 = (bag 0 1 2 0 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 0 1 2 1 1 100) (bag 0 0 2 1 1 100) (bag 0 1 1 1 1 100) (bag 0 1 2 0 1 100) (some 1) 4 2 3 4 hr hs (by decide) (by decide) hm2 hm3 hm4 _ _ _ cert_151 cert_152 cert_155
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_383 : count (rows.drop 15) (bag 1 0 2 1 1 100) (some 2) =
    (2 * X ^ 2 + 234 * X ^ 3 + 2308 * X ^ 4 + 1092 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 2 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 1 0 2 1 1 100).erase 1 = (bag 0 0 2 1 1 100) := by rfl
  have hm3 : (bag 1 0 2 1 1 100).erase 3 = (bag 1 0 1 1 1 100) := by rfl
  have hm4 : (bag 1 0 2 1 1 100).erase 4 = (bag 1 0 2 0 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 1 0 2 1 1 100) (bag 0 0 2 1 1 100) (bag 1 0 1 1 1 100) (bag 1 0 2 0 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_256 cert_257 cert_260
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_384 : count (rows.drop 15) (bag 1 1 1 1 1 100) (some 3) =
    (19 * X ^ 2 + 1569 * X ^ 3 + 4791 * X ^ 4 + 893 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 1 1 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 1 1 1 1 1 100).erase 1 = (bag 0 1 1 1 1 100) := by rfl
  have hm2 : (bag 1 1 1 1 1 100).erase 2 = (bag 1 0 1 1 1 100) := by rfl
  have hm3 : (bag 1 1 1 1 1 100).erase 3 = (bag 1 1 0 1 1 100) := by rfl
  have hm4 : (bag 1 1 1 1 1 100).erase 4 = (bag 1 1 1 0 1 100) := by rfl
  have hc := count_four (rows.drop 15) (rows.drop 16) (bag 1 1 1 1 1 100) (bag 0 1 1 1 1 100) (bag 1 0 1 1 1 100) (bag 1 1 0 1 1 100) (bag 1 1 1 0 1 100) (some 3) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_349 cert_350 cert_351 cert_355
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_385 : count (rows.drop 16) (bag 0 1 2 0 1 100) (some 1) =
    (X ^ 2 + 111 * X ^ 3 + 698 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 0 1 2 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm2 : (bag 0 1 2 0 1 100).erase 2 = (bag 0 0 2 0 1 100) := by rfl
  have hm3 : (bag 0 1 2 0 1 100).erase 3 = (bag 0 1 1 0 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 0 1 2 0 1 100) (bag 0 0 2 0 1 100) (bag 0 1 1 0 1 100) (some 1) 4 2 3 hr hs (by decide) hm2 hm3 _ _ cert_153 cert_154
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_386 : count (rows.drop 16) (bag 1 0 2 0 1 100) (some 2) =
    (4 * X ^ 2 + 309 * X ^ 3 + 596 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 0 2 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 1 0 2 0 1 100).erase 1 = (bag 0 0 2 0 1 100) := by rfl
  have hm3 : (bag 1 0 2 0 1 100).erase 3 = (bag 1 0 1 0 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 1 0 2 0 1 100) (bag 0 0 2 0 1 100) (bag 1 0 1 0 1 100) (some 2) 4 1 3 hr hs (by decide) hm1 hm3 _ _ cert_258 cert_259
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_387 : count (rows.drop 16) (bag 1 1 1 0 1 100) (some 3) =
    (X + 119 * X ^ 2 + 1301 * X ^ 3 + 397 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 1 1 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 1 1 1 0 1 100).erase 1 = (bag 0 1 1 0 1 100) := by rfl
  have hm2 : (bag 1 1 1 0 1 100).erase 2 = (bag 1 0 1 0 1 100) := by rfl
  have hm3 : (bag 1 1 1 0 1 100).erase 3 = (bag 1 1 0 0 1 100) := by rfl
  have hc := count_three (rows.drop 16) (rows.drop 17) (bag 1 1 1 0 1 100) (bag 0 1 1 0 1 100) (bag 1 0 1 0 1 100) (bag 1 1 0 0 1 100) (some 3) 4 1 2 3 hr hs (by decide) (by decide) hm1 hm2 hm3 _ _ _ cert_352 cert_353 cert_354
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_388 : count (rows.drop 15) (bag 1 1 2 0 1 100) (some 4) =
    (X + 124 * X ^ 2 + 1721 * X ^ 3 + 1691 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 1 2 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 1 1 2 0 1 100).erase 1 = (bag 0 1 2 0 1 100) := by rfl
  have hm2 : (bag 1 1 2 0 1 100).erase 2 = (bag 1 0 2 0 1 100) := by rfl
  have hm3 : (bag 1 1 2 0 1 100).erase 3 = (bag 1 1 1 0 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 1 1 2 0 1 100) (bag 0 1 2 0 1 100) (bag 1 0 2 0 1 100) (bag 1 1 1 0 1 100) (some 4) 4 1 2 3 hr hs (by decide) (by decide) hm1 hm2 hm3 _ _ _ cert_385 cert_386 cert_387
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_389 : count (rows.drop 14) (bag 1 1 2 1 1 100) (some 4) =
    (X + 146 * X ^ 2 + 3648 * X ^ 3 + 10511 * X ^ 4 + 3775 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 2 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 1 1 2 1 1 100).erase 1 = (bag 0 1 2 1 1 100) := by rfl
  have hm2 : (bag 1 1 2 1 1 100).erase 2 = (bag 1 0 2 1 1 100) := by rfl
  have hm3 : (bag 1 1 2 1 1 100).erase 3 = (bag 1 1 1 1 1 100) := by rfl
  have hm4 : (bag 1 1 2 1 1 100).erase 4 = (bag 1 1 2 0 1 100) := by rfl
  have hc := count_four (rows.drop 14) (rows.drop 15) (bag 1 1 2 1 1 100) (bag 0 1 2 1 1 100) (bag 1 0 2 1 1 100) (bag 1 1 1 1 1 100) (bag 1 1 2 0 1 100) (some 4) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_382 cert_383 cert_384 cert_388
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_390 : count (rows.drop 13) (bag 1 1 2 2 1 100) (some 4) =
    (X + 159 * X ^ 2 + 5058 * X ^ 3 + 25528 * X ^ 4 + 21215 * X ^ 5 + 2579 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 2 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 1 1 2 2 1 100).erase 1 = (bag 0 1 2 2 1 100) := by rfl
  have hm2 : (bag 1 1 2 2 1 100).erase 2 = (bag 1 0 2 2 1 100) := by rfl
  have hm3 : (bag 1 1 2 2 1 100).erase 3 = (bag 1 1 1 2 1 100) := by rfl
  have hm4 : (bag 1 1 2 2 1 100).erase 4 = (bag 1 1 2 1 1 100) := by rfl
  have hc := count_four (rows.drop 13) (rows.drop 14) (bag 1 1 2 2 1 100) (bag 0 1 2 2 1 100) (bag 1 0 2 2 1 100) (bag 1 1 1 2 1 100) (bag 1 1 2 1 1 100) (some 4) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_379 cert_380 cert_381 cert_389
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_391 : count (rows.drop 12) (bag 1 1 2 3 1 100) (some 4) =
    (X + 170 * X ^ 2 + 6408 * X ^ 3 + 44372 * X ^ 4 + 60323 * X ^ 5 + 15590 * X ^ 6 + 396 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 1 2 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 1 1 2 3 1 100).erase 1 = (bag 0 1 2 3 1 100) := by rfl
  have hm2 : (bag 1 1 2 3 1 100).erase 2 = (bag 1 0 2 3 1 100) := by rfl
  have hm3 : (bag 1 1 2 3 1 100).erase 3 = (bag 1 1 1 3 1 100) := by rfl
  have hm4 : (bag 1 1 2 3 1 100).erase 4 = (bag 1 1 2 2 1 100) := by rfl
  have hc := count_four (rows.drop 12) (rows.drop 13) (bag 1 1 2 3 1 100) (bag 0 1 2 3 1 100) (bag 1 0 2 3 1 100) (bag 1 1 1 3 1 100) (bag 1 1 2 2 1 100) (some 4) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_376 cert_377 cert_378 cert_390
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_392 : count (rows.drop 11) (bag 1 1 2 4 1 100) (some 4) =
    (X + 181 * X ^ 2 + 7789 * X ^ 3 + 66692 * X ^ 4 + 125204 * X ^ 5 + 51584 * X ^ 6 + 3069 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 1 2 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 1 1 2 4 1 100).erase 1 = (bag 0 1 2 4 1 100) := by rfl
  have hm2 : (bag 1 1 2 4 1 100).erase 2 = (bag 1 0 2 4 1 100) := by rfl
  have hm3 : (bag 1 1 2 4 1 100).erase 3 = (bag 1 1 1 4 1 100) := by rfl
  have hm4 : (bag 1 1 2 4 1 100).erase 4 = (bag 1 1 2 3 1 100) := by rfl
  have hc := count_four (rows.drop 11) (rows.drop 12) (bag 1 1 2 4 1 100) (bag 0 1 2 4 1 100) (bag 1 0 2 4 1 100) (bag 1 1 1 4 1 100) (bag 1 1 2 3 1 100) (some 4) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_373 cert_374 cert_375 cert_391
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_393 : count (rows.drop 10) (bag 1 1 2 5 1 100) (some 4) =
    (X + 192 * X ^ 2 + 9201 * X ^ 3 + 92521 * X ^ 4 + 219389 * X ^ 5 + 124655 * X ^ 6 + 12177 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 1 2 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 1 1 2 5 1 100).erase 1 = (bag 0 1 2 5 1 100) := by rfl
  have hm2 : (bag 1 1 2 5 1 100).erase 2 = (bag 1 0 2 5 1 100) := by rfl
  have hm3 : (bag 1 1 2 5 1 100).erase 3 = (bag 1 1 1 5 1 100) := by rfl
  have hm4 : (bag 1 1 2 5 1 100).erase 4 = (bag 1 1 2 4 1 100) := by rfl
  have hc := count_four (rows.drop 10) (rows.drop 11) (bag 1 1 2 5 1 100) (bag 0 1 2 5 1 100) (bag 1 0 2 5 1 100) (bag 1 1 1 5 1 100) (bag 1 1 2 4 1 100) (some 4) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_370 cert_371 cert_372 cert_392
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_394 : count (rows.drop 9) (bag 1 1 2 6 1 100) (some 4) =
    (X + 203 * X ^ 2 + 10644 * X ^ 3 + 121892 * X ^ 4 + 346421 * X ^ 5 + 250145 * X ^ 6 + 34254 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 1 2 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 1 1 2 6 1 100).erase 1 = (bag 0 1 2 6 1 100) := by rfl
  have hm2 : (bag 1 1 2 6 1 100).erase 2 = (bag 1 0 2 6 1 100) := by rfl
  have hm3 : (bag 1 1 2 6 1 100).erase 3 = (bag 1 1 1 6 1 100) := by rfl
  have hm4 : (bag 1 1 2 6 1 100).erase 4 = (bag 1 1 2 5 1 100) := by rfl
  have hc := count_four (rows.drop 9) (rows.drop 10) (bag 1 1 2 6 1 100) (bag 0 1 2 6 1 100) (bag 1 0 2 6 1 100) (bag 1 1 1 6 1 100) (bag 1 1 2 5 1 100) (some 4) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_367 cert_368 cert_369 cert_393
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_395 : count (rows.drop 8) (bag 1 1 2 7 1 100) (some 4) =
    (X + 214 * X ^ 2 + 12118 * X ^ 3 + 154838 * X ^ 4 + 509855 * X ^ 5 + 444644 * X ^ 6 + 78210 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 1 2 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm1 : (bag 1 1 2 7 1 100).erase 1 = (bag 0 1 2 7 1 100) := by rfl
  have hm2 : (bag 1 1 2 7 1 100).erase 2 = (bag 1 0 2 7 1 100) := by rfl
  have hm3 : (bag 1 1 2 7 1 100).erase 3 = (bag 1 1 1 7 1 100) := by rfl
  have hm4 : (bag 1 1 2 7 1 100).erase 4 = (bag 1 1 2 6 1 100) := by rfl
  have hc := count_four (rows.drop 8) (rows.drop 9) (bag 1 1 2 7 1 100) (bag 0 1 2 7 1 100) (bag 1 0 2 7 1 100) (bag 1 1 1 7 1 100) (bag 1 1 2 6 1 100) (some 4) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_364 cert_365 cert_366 cert_394
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_396 : count (rows.drop 7) (bag 1 1 2 8 1 100) (some 3) =
    (12 * X ^ 2 + 1719 * X ^ 3 + 48672 * X ^ 4 + 358241 * X ^ 5 + 791201 * X ^ 6 + 521765 * X ^ 7 + 78210 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 1 1 2 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 7 = 4 :: rows.drop 8 := by rfl
  have hm1 : (bag 1 1 2 8 1 100).erase 1 = (bag 0 1 2 8 1 100) := by rfl
  have hm2 : (bag 1 1 2 8 1 100).erase 2 = (bag 1 0 2 8 1 100) := by rfl
  have hm3 : (bag 1 1 2 8 1 100).erase 3 = (bag 1 1 1 8 1 100) := by rfl
  have hm4 : (bag 1 1 2 8 1 100).erase 4 = (bag 1 1 2 7 1 100) := by rfl
  have hc := count_four (rows.drop 7) (rows.drop 8) (bag 1 1 2 8 1 100) (bag 0 1 2 8 1 100) (bag 1 0 2 8 1 100) (bag 1 1 1 8 1 100) (bag 1 1 2 7 1 100) (some 3) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_297 cert_298 cert_363 cert_395
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_397 : count (rows.drop 6) (bag 1 1 3 8 1 100) (some 3) =
    (15 * X ^ 2 + 2209 * X ^ 3 + 67948 * X ^ 4 + 545572 * X ^ 5 + 1310406 * X ^ 6 + 928515 * X ^ 7 + 145035 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 1 1 3 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 6 = 3 :: rows.drop 7 := by rfl
  have hm1 : (bag 1 1 3 8 1 100).erase 1 = (bag 0 1 3 8 1 100) := by rfl
  have hm2 : (bag 1 1 3 8 1 100).erase 2 = (bag 1 0 3 8 1 100) := by rfl
  have hm3 : (bag 1 1 3 8 1 100).erase 3 = (bag 1 1 2 8 1 100) := by rfl
  have hc := count_three (rows.drop 6) (rows.drop 7) (bag 1 1 3 8 1 100) (bag 0 1 3 8 1 100) (bag 1 0 3 8 1 100) (bag 1 1 2 8 1 100) (some 3) 3 1 2 3 hr hs (by decide) (by decide) hm1 hm2 hm3 _ _ _ cert_295 cert_296 cert_396
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_398 : count (rows.drop 5) (bag 1 1 4 8 1 100) (some 1) =
    (25 * X ^ 3 + 3568 * X ^ 4 + 101579 * X ^ 5 + 777574 * X ^ 6 + 1859631 * X ^ 7 + 1423640 * X ^ 8 + 316703 * X ^ 9 + 16830 * X ^ 10 : ℕ[X]) := by
  have hs : (bag 1 1 4 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 5 = 3 :: rows.drop 6 := by rfl
  have hm1 : (bag 1 1 4 8 1 100).erase 1 = (bag 0 1 4 8 1 100) := by rfl
  have hm2 : (bag 1 1 4 8 1 100).erase 2 = (bag 1 0 4 8 1 100) := by rfl
  have hm3 : (bag 1 1 4 8 1 100).erase 3 = (bag 1 1 3 8 1 100) := by rfl
  have hc := count_three (rows.drop 5) (rows.drop 6) (bag 1 1 4 8 1 100) (bag 0 1 4 8 1 100) (bag 1 0 4 8 1 100) (bag 1 1 3 8 1 100) (some 1) 3 1 2 3 hr hs (by decide) (by decide) hm1 hm2 hm3 _ _ _ cert_189 cert_294 cert_397
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_399 : count (rows.drop 6) (bag 1 0 4 8 1 100) (some 1) =
    (X ^ 2 + 151 * X ^ 3 + 5275 * X ^ 4 + 55302 * X ^ 5 + 213680 * X ^ 6 + 308798 * X ^ 7 + 149888 * X ^ 8 + 16830 * X ^ 9 : ℕ[X]) := by
  have hs : (bag 1 0 4 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 6 = 3 :: rows.drop 7 := by rfl
  have hm1 : (bag 1 0 4 8 1 100).erase 1 = (bag 0 0 4 8 1 100) := by rfl
  have hm3 : (bag 1 0 4 8 1 100).erase 3 = (bag 1 0 3 8 1 100) := by rfl
  have hc := count_two (rows.drop 6) (rows.drop 7) (bag 1 0 4 8 1 100) (bag 0 0 4 8 1 100) (bag 1 0 3 8 1 100) (some 1) 3 1 3 hr hs (by decide) hm1 hm3 _ _ cert_190 cert_293
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_400 : count (rows.drop 7) (bag 1 0 3 8 1 100) (some 1) =
    (2 * X ^ 2 + 312 * X ^ 3 + 11194 * X ^ 4 + 100949 * X ^ 5 + 262372 * X ^ 6 + 194421 * X ^ 7 + 30690 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 1 0 3 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 7 = 4 :: rows.drop 8 := by rfl
  have hm1 : (bag 1 0 3 8 1 100).erase 1 = (bag 0 0 3 8 1 100) := by rfl
  have hm3 : (bag 1 0 3 8 1 100).erase 3 = (bag 1 0 2 8 1 100) := by rfl
  have hm4 : (bag 1 0 3 8 1 100).erase 4 = (bag 1 0 3 7 1 100) := by rfl
  have hc := count_three (rows.drop 7) (rows.drop 8) (bag 1 0 3 8 1 100) (bag 0 0 3 8 1 100) (bag 1 0 2 8 1 100) (bag 1 0 3 7 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_191 cert_268 cert_292
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_401 : count (rows.drop 8) (bag 1 0 2 8 1 100) (some 1) =
    (2 * X ^ 2 + 287 * X ^ 3 + 8073 * X ^ 4 + 49783 * X ^ 5 + 71941 * X ^ 6 + 19899 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 0 2 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm1 : (bag 1 0 2 8 1 100).erase 1 = (bag 0 0 2 8 1 100) := by rfl
  have hm3 : (bag 1 0 2 8 1 100).erase 3 = (bag 1 0 1 8 1 100) := by rfl
  have hm4 : (bag 1 0 2 8 1 100).erase 4 = (bag 1 0 2 7 1 100) := by rfl
  have hc := count_three (rows.drop 8) (rows.drop 9) (bag 1 0 2 8 1 100) (bag 0 0 2 8 1 100) (bag 1 0 1 8 1 100) (bag 1 0 2 7 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_192 cert_243 cert_267
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_402 : count (rows.drop 9) (bag 1 0 1 8 1 100) (some 1) =
    (2 * X ^ 2 + 258 * X ^ 3 + 4918 * X ^ 4 + 14964 * X ^ 5 + 7128 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 1 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 1 0 1 8 1 100).erase 1 = (bag 0 0 1 8 1 100) := by rfl
  have hm3 : (bag 1 0 1 8 1 100).erase 3 = (bag 1 0 0 8 1 100) := by rfl
  have hm4 : (bag 1 0 1 8 1 100).erase 4 = (bag 1 0 1 7 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 1 0 1 8 1 100) (bag 0 0 1 8 1 100) (bag 1 0 0 8 1 100) (bag 1 0 1 7 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_193 cert_215 cert_242
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_403 : count (rows.drop 10) (bag 1 0 0 8 1 100) (some 1) =
    (2 * X ^ 2 + 220 * X ^ 3 + 1416 * X ^ 4 + 1089 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 0 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 1 0 0 8 1 100).erase 1 = (bag 0 0 0 8 1 100) := by rfl
  have hm4 : (bag 1 0 0 8 1 100).erase 4 = (bag 1 0 0 7 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 1 0 0 8 1 100) (bag 0 0 0 8 1 100) (bag 1 0 0 7 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_194 cert_214
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_404 : count (rows.drop 11) (bag 1 0 0 7 1 100) (some 1) =
    (2 * X ^ 2 + 219 * X ^ 3 + 1312 * X ^ 4 + 891 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 1 0 0 7 1 100).erase 1 = (bag 0 0 0 7 1 100) := by rfl
  have hm4 : (bag 1 0 0 7 1 100).erase 4 = (bag 1 0 0 6 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 1 0 0 7 1 100) (bag 0 0 0 7 1 100) (bag 1 0 0 6 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_195 cert_213
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_405 : count (rows.drop 12) (bag 1 0 0 6 1 100) (some 1) =
    (2 * X ^ 2 + 218 * X ^ 3 + 1208 * X ^ 4 + 693 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 1 0 0 6 1 100).erase 1 = (bag 0 0 0 6 1 100) := by rfl
  have hm4 : (bag 1 0 0 6 1 100).erase 4 = (bag 1 0 0 5 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 1 0 0 6 1 100) (bag 0 0 0 6 1 100) (bag 1 0 0 5 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_196 cert_212
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_406 : count (rows.drop 13) (bag 1 0 0 5 1 100) (some 1) =
    (2 * X ^ 2 + 217 * X ^ 3 + 1104 * X ^ 4 + 495 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 1 0 0 5 1 100).erase 1 = (bag 0 0 0 5 1 100) := by rfl
  have hm4 : (bag 1 0 0 5 1 100).erase 4 = (bag 1 0 0 4 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 1 0 0 5 1 100) (bag 0 0 0 5 1 100) (bag 1 0 0 4 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_197 cert_211
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_407 : count (rows.drop 14) (bag 1 0 0 4 1 100) (some 1) =
    (2 * X ^ 2 + 216 * X ^ 3 + 1000 * X ^ 4 + 297 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 1 0 0 4 1 100).erase 1 = (bag 0 0 0 4 1 100) := by rfl
  have hm4 : (bag 1 0 0 4 1 100).erase 4 = (bag 1 0 0 3 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 1 0 0 4 1 100) (bag 0 0 0 4 1 100) (bag 1 0 0 3 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_198 cert_210
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_408 : count (rows.drop 15) (bag 1 0 0 3 1 100) (some 1) =
    (2 * X ^ 2 + 215 * X ^ 3 + 896 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 1 0 0 3 1 100).erase 1 = (bag 0 0 0 3 1 100) := by rfl
  have hm4 : (bag 1 0 0 3 1 100).erase 4 = (bag 1 0 0 2 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 1 0 0 3 1 100) (bag 0 0 0 3 1 100) (bag 1 0 0 2 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_199 cert_209
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_409 : count (rows.drop 16) (bag 1 0 0 2 1 100) (some 1) =
    (4 * X ^ 2 + 309 * X ^ 3 + 596 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 0 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 1 0 0 2 1 100).erase 1 = (bag 0 0 0 2 1 100) := by rfl
  have hm4 : (bag 1 0 0 2 1 100).erase 4 = (bag 1 0 0 1 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 1 0 0 2 1 100) (bag 0 0 0 2 1 100) (bag 1 0 0 1 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_200 cert_208
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_410 : count (rows.drop 17) (bag 1 0 0 1 1 100) (some 1) =
    (7 * X ^ 2 + 500 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 0 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1, 4, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm1 : (bag 1 0 0 1 1 100).erase 1 = (bag 0 0 0 1 1 100) := by rfl
  have hm4 : (bag 1 0 0 1 1 100).erase 4 = (bag 1 0 0 0 1 100) := by rfl
  have hm5 : (bag 1 0 0 1 1 100).erase 5 = (bag 1 0 0 1 0 100) := by rfl
  have hc := count_three (rows.drop 17) (rows.drop 18) (bag 1 0 0 1 1 100) (bag 0 0 0 1 1 100) (bag 1 0 0 0 1 100) (bag 1 0 0 1 0 100) (some 1) 5 1 4 5 hr hs (by decide) (by decide) hm1 hm4 hm5 _ _ _ cert_201 cert_204 cert_207
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_411 : count (rows.drop 18) (bag 1 0 0 0 1 100) (some 1) =
    (X + 102 * X ^ 2 + 99 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 1 0 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm1 : (bag 1 0 0 0 1 100).erase 1 = (bag 0 0 0 0 1 100) := by rfl
  have hm5 : (bag 1 0 0 0 1 100).erase 5 = (bag 1 0 0 0 0 100) := by rfl
  have hc := count_two (rows.drop 18) (rows.drop 19) (bag 1 0 0 0 1 100) (bag 0 0 0 0 1 100) (bag 1 0 0 0 0 100) (some 1) 5 1 5 hr hs (by decide) hm1 hm5 _ _ cert_202 cert_203
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_412 : count (rows.drop 19) (bag 1 0 0 0 0 100) (some 1) =
    (2 * X + 99 * X ^ 2 : ℕ[X]) := by
  change count (List.replicate 101 6) (1 ::ₘ Multiset.replicate 100 6) (some 1) = _
  rw [six_tail 99 1 1 (by decide) (by decide) (by decide)]
  simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
  ring

private theorem cert_413 : count (rows.drop 18) (bag 2 0 0 0 0 100) (some 5) =
    (2 * X + 99 * X ^ 2 : ℕ[X]) := by
  have hs : (bag 2 0 0 0 0 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 18 = 5 :: rows.drop 19 := by rfl
  have hm1 : (bag 2 0 0 0 0 100).erase 1 = (bag 1 0 0 0 0 100) := by rfl
  have hc := count_one (rows.drop 18) (rows.drop 19) (bag 2 0 0 0 0 100) (bag 1 0 0 0 0 100) (some 5) 5 1 hr hs hm1 _ cert_412
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_414 : count (rows.drop 17) (bag 2 0 0 0 1 100) (some 4) =
    (X + 104 * X ^ 2 + 198 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 2 0 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm1 : (bag 2 0 0 0 1 100).erase 1 = (bag 1 0 0 0 1 100) := by rfl
  have hm5 : (bag 2 0 0 0 1 100).erase 5 = (bag 2 0 0 0 0 100) := by rfl
  have hc := count_two (rows.drop 17) (rows.drop 18) (bag 2 0 0 0 1 100) (bag 1 0 0 0 1 100) (bag 2 0 0 0 0 100) (some 4) 5 1 5 hr hs (by decide) hm1 hm5 _ _ cert_411 cert_413
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_415 : count (rows.drop 16) (bag 2 0 0 1 1 100) (some 4) =
    (X + 111 * X ^ 2 + 698 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 2 0 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 2 0 0 1 1 100).erase 1 = (bag 1 0 0 1 1 100) := by rfl
  have hm4 : (bag 2 0 0 1 1 100).erase 4 = (bag 2 0 0 0 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 2 0 0 1 1 100) (bag 1 0 0 1 1 100) (bag 2 0 0 0 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_410 cert_414
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_416 : count (rows.drop 15) (bag 2 0 0 2 1 100) (some 4) =
    (X + 115 * X ^ 2 + 1007 * X ^ 3 + 695 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 2 0 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 2 0 0 2 1 100).erase 1 = (bag 1 0 0 2 1 100) := by rfl
  have hm4 : (bag 2 0 0 2 1 100).erase 4 = (bag 2 0 0 1 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 2 0 0 2 1 100) (bag 1 0 0 2 1 100) (bag 2 0 0 1 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_409 cert_415
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_417 : count (rows.drop 14) (bag 2 0 0 3 1 100) (some 4) =
    (X + 117 * X ^ 2 + 1222 * X ^ 3 + 1591 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 2 0 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 2 0 0 3 1 100).erase 1 = (bag 1 0 0 3 1 100) := by rfl
  have hm4 : (bag 2 0 0 3 1 100).erase 4 = (bag 2 0 0 2 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 2 0 0 3 1 100) (bag 1 0 0 3 1 100) (bag 2 0 0 2 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_408 cert_416
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_418 : count (rows.drop 13) (bag 2 0 0 4 1 100) (some 4) =
    (X + 119 * X ^ 2 + 1438 * X ^ 3 + 2591 * X ^ 4 + 396 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 2 0 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 2 0 0 4 1 100).erase 1 = (bag 1 0 0 4 1 100) := by rfl
  have hm4 : (bag 2 0 0 4 1 100).erase 4 = (bag 2 0 0 3 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 2 0 0 4 1 100) (bag 1 0 0 4 1 100) (bag 2 0 0 3 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_407 cert_417
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_419 : count (rows.drop 12) (bag 2 0 0 5 1 100) (some 4) =
    (X + 121 * X ^ 2 + 1655 * X ^ 3 + 3695 * X ^ 4 + 891 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 2 0 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 2 0 0 5 1 100).erase 1 = (bag 1 0 0 5 1 100) := by rfl
  have hm4 : (bag 2 0 0 5 1 100).erase 4 = (bag 2 0 0 4 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 2 0 0 5 1 100) (bag 1 0 0 5 1 100) (bag 2 0 0 4 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_406 cert_418
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_420 : count (rows.drop 11) (bag 2 0 0 6 1 100) (some 4) =
    (X + 123 * X ^ 2 + 1873 * X ^ 3 + 4903 * X ^ 4 + 1584 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 2 0 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 2 0 0 6 1 100).erase 1 = (bag 1 0 0 6 1 100) := by rfl
  have hm4 : (bag 2 0 0 6 1 100).erase 4 = (bag 2 0 0 5 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 2 0 0 6 1 100) (bag 1 0 0 6 1 100) (bag 2 0 0 5 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_405 cert_419
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_421 : count (rows.drop 10) (bag 2 0 0 7 1 100) (some 4) =
    (X + 125 * X ^ 2 + 2092 * X ^ 3 + 6215 * X ^ 4 + 2475 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 2 0 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 2 0 0 7 1 100).erase 1 = (bag 1 0 0 7 1 100) := by rfl
  have hm4 : (bag 2 0 0 7 1 100).erase 4 = (bag 2 0 0 6 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 2 0 0 7 1 100) (bag 1 0 0 7 1 100) (bag 2 0 0 6 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_404 cert_420
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_422 : count (rows.drop 9) (bag 2 0 0 8 1 100) (some 3) =
    (3 * X ^ 2 + 345 * X ^ 3 + 3508 * X ^ 4 + 7304 * X ^ 5 + 2475 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 0 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 2 0 0 8 1 100).erase 1 = (bag 1 0 0 8 1 100) := by rfl
  have hm4 : (bag 2 0 0 8 1 100).erase 4 = (bag 2 0 0 7 1 100) := by rfl
  have hc := count_two (rows.drop 9) (rows.drop 10) (bag 2 0 0 8 1 100) (bag 1 0 0 8 1 100) (bag 2 0 0 7 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_403 cert_421
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_423 : count (rows.drop 10) (bag 1 0 1 7 1 100) (some 1) =
    (2 * X ^ 2 + 254 * X ^ 3 + 4478 * X ^ 4 + 12132 * X ^ 5 + 4950 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 1 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 1 0 1 7 1 100).erase 1 = (bag 0 0 1 7 1 100) := by rfl
  have hm3 : (bag 1 0 1 7 1 100).erase 3 = (bag 1 0 0 7 1 100) := by rfl
  have hm4 : (bag 1 0 1 7 1 100).erase 4 = (bag 1 0 1 6 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 1 0 1 7 1 100) (bag 0 0 1 7 1 100) (bag 1 0 0 7 1 100) (bag 1 0 1 6 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_216 cert_217 cert_241
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_424 : count (rows.drop 10) (bag 2 0 0 7 1 100) (some 3) =
    (3 * X ^ 2 + 342 * X ^ 3 + 3185 * X ^ 4 + 5794 * X ^ 5 + 1584 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 2 0 0 7 1 100).erase 1 = (bag 1 0 0 7 1 100) := by rfl
  have hm4 : (bag 2 0 0 7 1 100).erase 4 = (bag 2 0 0 6 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 2 0 0 7 1 100) (bag 1 0 0 7 1 100) (bag 2 0 0 6 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_404 cert_420
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_425 : count (rows.drop 11) (bag 1 0 1 6 1 100) (some 1) =
    (2 * X ^ 2 + 250 * X ^ 3 + 4040 * X ^ 4 + 9508 * X ^ 5 + 3168 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 1 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 1 0 1 6 1 100).erase 1 = (bag 0 0 1 6 1 100) := by rfl
  have hm3 : (bag 1 0 1 6 1 100).erase 3 = (bag 1 0 0 6 1 100) := by rfl
  have hm4 : (bag 1 0 1 6 1 100).erase 4 = (bag 1 0 1 5 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 1 0 1 6 1 100) (bag 0 0 1 6 1 100) (bag 1 0 0 6 1 100) (bag 1 0 1 5 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_218 cert_219 cert_240
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_426 : count (rows.drop 11) (bag 2 0 0 6 1 100) (some 3) =
    (3 * X ^ 2 + 339 * X ^ 3 + 2863 * X ^ 4 + 4388 * X ^ 5 + 891 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 2 0 0 6 1 100).erase 1 = (bag 1 0 0 6 1 100) := by rfl
  have hm4 : (bag 2 0 0 6 1 100).erase 4 = (bag 2 0 0 5 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 2 0 0 6 1 100) (bag 1 0 0 6 1 100) (bag 2 0 0 5 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_405 cert_419
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_427 : count (rows.drop 12) (bag 1 0 1 5 1 100) (some 1) =
    (2 * X ^ 2 + 246 * X ^ 3 + 3604 * X ^ 4 + 7092 * X ^ 5 + 1782 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 1 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 1 0 1 5 1 100).erase 1 = (bag 0 0 1 5 1 100) := by rfl
  have hm3 : (bag 1 0 1 5 1 100).erase 3 = (bag 1 0 0 5 1 100) := by rfl
  have hm4 : (bag 1 0 1 5 1 100).erase 4 = (bag 1 0 1 4 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 1 0 1 5 1 100) (bag 0 0 1 5 1 100) (bag 1 0 0 5 1 100) (bag 1 0 1 4 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_220 cert_221 cert_239
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_428 : count (rows.drop 12) (bag 2 0 0 5 1 100) (some 3) =
    (3 * X ^ 2 + 336 * X ^ 3 + 2542 * X ^ 4 + 3086 * X ^ 5 + 396 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 2 0 0 5 1 100).erase 1 = (bag 1 0 0 5 1 100) := by rfl
  have hm4 : (bag 2 0 0 5 1 100).erase 4 = (bag 2 0 0 4 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 2 0 0 5 1 100) (bag 1 0 0 5 1 100) (bag 2 0 0 4 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_406 cert_418
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_429 : count (rows.drop 13) (bag 1 0 1 4 1 100) (some 1) =
    (2 * X ^ 2 + 242 * X ^ 3 + 3170 * X ^ 4 + 4884 * X ^ 5 + 792 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 1 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 1 0 1 4 1 100).erase 1 = (bag 0 0 1 4 1 100) := by rfl
  have hm3 : (bag 1 0 1 4 1 100).erase 3 = (bag 1 0 0 4 1 100) := by rfl
  have hm4 : (bag 1 0 1 4 1 100).erase 4 = (bag 1 0 1 3 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 1 0 1 4 1 100) (bag 0 0 1 4 1 100) (bag 1 0 0 4 1 100) (bag 1 0 1 3 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_222 cert_223 cert_238
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_430 : count (rows.drop 13) (bag 2 0 0 4 1 100) (some 3) =
    (3 * X ^ 2 + 333 * X ^ 3 + 2222 * X ^ 4 + 1888 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 2 0 0 4 1 100).erase 1 = (bag 1 0 0 4 1 100) := by rfl
  have hm4 : (bag 2 0 0 4 1 100).erase 4 = (bag 2 0 0 3 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 2 0 0 4 1 100) (bag 1 0 0 4 1 100) (bag 2 0 0 3 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_407 cert_417
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_431 : count (rows.drop 14) (bag 1 0 1 3 1 100) (some 1) =
    (2 * X ^ 2 + 238 * X ^ 3 + 2738 * X ^ 4 + 2884 * X ^ 5 + 198 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 1 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 1 0 1 3 1 100).erase 1 = (bag 0 0 1 3 1 100) := by rfl
  have hm3 : (bag 1 0 1 3 1 100).erase 3 = (bag 1 0 0 3 1 100) := by rfl
  have hm4 : (bag 1 0 1 3 1 100).erase 4 = (bag 1 0 1 2 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 1 0 1 3 1 100) (bag 0 0 1 3 1 100) (bag 1 0 0 3 1 100) (bag 1 0 1 2 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_224 cert_225 cert_237
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_432 : count (rows.drop 14) (bag 2 0 0 3 1 100) (some 3) =
    (3 * X ^ 2 + 330 * X ^ 3 + 1903 * X ^ 4 + 794 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 2 0 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 2 0 0 3 1 100).erase 1 = (bag 1 0 0 3 1 100) := by rfl
  have hm4 : (bag 2 0 0 3 1 100).erase 4 = (bag 2 0 0 2 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 2 0 0 3 1 100) (bag 1 0 0 3 1 100) (bag 2 0 0 2 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_408 cert_416
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_433 : count (rows.drop 15) (bag 1 0 1 2 1 100) (some 1) =
    (2 * X ^ 2 + 234 * X ^ 3 + 2308 * X ^ 4 + 1092 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 1 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 1 0 1 2 1 100).erase 1 = (bag 0 0 1 2 1 100) := by rfl
  have hm3 : (bag 1 0 1 2 1 100).erase 3 = (bag 1 0 0 2 1 100) := by rfl
  have hm4 : (bag 1 0 1 2 1 100).erase 4 = (bag 1 0 1 1 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 1 0 1 2 1 100) (bag 0 0 1 2 1 100) (bag 1 0 0 2 1 100) (bag 1 0 1 1 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_226 cert_227 cert_236
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_434 : count (rows.drop 15) (bag 2 0 0 2 1 100) (some 3) =
    (5 * X ^ 2 + 420 * X ^ 3 + 1294 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 2 0 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 2 0 0 2 1 100).erase 1 = (bag 1 0 0 2 1 100) := by rfl
  have hm4 : (bag 2 0 0 2 1 100).erase 4 = (bag 2 0 0 1 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 2 0 0 2 1 100) (bag 1 0 0 2 1 100) (bag 2 0 0 1 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_409 cert_415
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_435 : count (rows.drop 16) (bag 1 0 1 1 1 100) (some 1) =
    (5 * X ^ 2 + 419 * X ^ 3 + 1295 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 1 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 1 0 1 1 1 100).erase 1 = (bag 0 0 1 1 1 100) := by rfl
  have hm3 : (bag 1 0 1 1 1 100).erase 3 = (bag 1 0 0 1 1 100) := by rfl
  have hm4 : (bag 1 0 1 1 1 100).erase 4 = (bag 1 0 1 0 1 100) := by rfl
  have hc := count_three (rows.drop 16) (rows.drop 17) (bag 1 0 1 1 1 100) (bag 0 0 1 1 1 100) (bag 1 0 0 1 1 100) (bag 1 0 1 0 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_228 cert_229 cert_235
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_436 : count (rows.drop 16) (bag 2 0 0 1 1 100) (some 3) =
    (8 * X ^ 2 + 604 * X ^ 3 + 297 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 2 0 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 2 0 0 1 1 100).erase 1 = (bag 1 0 0 1 1 100) := by rfl
  have hm4 : (bag 2 0 0 1 1 100).erase 4 = (bag 2 0 0 0 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 2 0 0 1 1 100) (bag 1 0 0 1 1 100) (bag 2 0 0 0 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_410 cert_414
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_437 : count (rows.drop 17) (bag 1 0 1 0 1 100) (some 1) =
    (7 * X ^ 2 + 500 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 0 1 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1, 3, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm1 : (bag 1 0 1 0 1 100).erase 1 = (bag 0 0 1 0 1 100) := by rfl
  have hm3 : (bag 1 0 1 0 1 100).erase 3 = (bag 1 0 0 0 1 100) := by rfl
  have hm5 : (bag 1 0 1 0 1 100).erase 5 = (bag 1 0 1 0 0 100) := by rfl
  have hc := count_three (rows.drop 17) (rows.drop 18) (bag 1 0 1 0 1 100) (bag 0 0 1 0 1 100) (bag 1 0 0 0 1 100) (bag 1 0 1 0 0 100) (some 1) 5 1 3 5 hr hs (by decide) (by decide) hm1 hm3 hm5 _ _ _ cert_230 cert_231 cert_234
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_438 : count (rows.drop 17) (bag 2 0 0 0 1 100) (some 3) =
    (X + 104 * X ^ 2 + 198 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 2 0 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm1 : (bag 2 0 0 0 1 100).erase 1 = (bag 1 0 0 0 1 100) := by rfl
  have hm5 : (bag 2 0 0 0 1 100).erase 5 = (bag 2 0 0 0 0 100) := by rfl
  have hc := count_two (rows.drop 17) (rows.drop 18) (bag 2 0 0 0 1 100) (bag 1 0 0 0 1 100) (bag 2 0 0 0 0 100) (some 3) 5 1 5 hr hs (by decide) hm1 hm5 _ _ cert_411 cert_413
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_439 : count (rows.drop 16) (bag 2 0 1 0 1 100) (some 4) =
    (X + 111 * X ^ 2 + 698 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 2 0 1 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 2 0 1 0 1 100).erase 1 = (bag 1 0 1 0 1 100) := by rfl
  have hm3 : (bag 2 0 1 0 1 100).erase 3 = (bag 2 0 0 0 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 2 0 1 0 1 100) (bag 1 0 1 0 1 100) (bag 2 0 0 0 1 100) (some 4) 4 1 3 hr hs (by decide) hm1 hm3 _ _ cert_437 cert_438
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_440 : count (rows.drop 15) (bag 2 0 1 1 1 100) (some 4) =
    (X + 124 * X ^ 2 + 1721 * X ^ 3 + 1691 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 2 0 1 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 2 0 1 1 1 100).erase 1 = (bag 1 0 1 1 1 100) := by rfl
  have hm3 : (bag 2 0 1 1 1 100).erase 3 = (bag 2 0 0 1 1 100) := by rfl
  have hm4 : (bag 2 0 1 1 1 100).erase 4 = (bag 2 0 1 0 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 2 0 1 1 1 100) (bag 1 0 1 1 1 100) (bag 2 0 0 1 1 100) (bag 2 0 1 0 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_435 cert_436 cert_439
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_441 : count (rows.drop 14) (bag 2 0 1 2 1 100) (some 4) =
    (X + 131 * X ^ 2 + 2375 * X ^ 3 + 5293 * X ^ 4 + 1290 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 2 0 1 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 2 0 1 2 1 100).erase 1 = (bag 1 0 1 2 1 100) := by rfl
  have hm3 : (bag 2 0 1 2 1 100).erase 3 = (bag 2 0 0 2 1 100) := by rfl
  have hm4 : (bag 2 0 1 2 1 100).erase 4 = (bag 2 0 1 1 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 2 0 1 2 1 100) (bag 1 0 1 2 1 100) (bag 2 0 0 2 1 100) (bag 2 0 1 1 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_433 cert_434 cert_440
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_442 : count (rows.drop 13) (bag 2 0 1 3 1 100) (some 4) =
    (X + 136 * X ^ 2 + 2943 * X ^ 3 + 9934 * X ^ 4 + 4968 * X ^ 5 + 198 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 1 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 2 0 1 3 1 100).erase 1 = (bag 1 0 1 3 1 100) := by rfl
  have hm3 : (bag 2 0 1 3 1 100).erase 3 = (bag 2 0 0 3 1 100) := by rfl
  have hm4 : (bag 2 0 1 3 1 100).erase 4 = (bag 2 0 1 2 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 2 0 1 3 1 100) (bag 1 0 1 3 1 100) (bag 2 0 0 3 1 100) (bag 2 0 1 2 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_431 cert_432 cert_441
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_443 : count (rows.drop 12) (bag 2 0 1 4 1 100) (some 4) =
    (X + 141 * X ^ 2 + 3518 * X ^ 3 + 15326 * X ^ 4 + 11740 * X ^ 5 + 1089 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 1 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 2 0 1 4 1 100).erase 1 = (bag 1 0 1 4 1 100) := by rfl
  have hm3 : (bag 2 0 1 4 1 100).erase 3 = (bag 2 0 0 4 1 100) := by rfl
  have hm4 : (bag 2 0 1 4 1 100).erase 4 = (bag 2 0 1 3 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 2 0 1 4 1 100) (bag 1 0 1 4 1 100) (bag 2 0 0 4 1 100) (bag 2 0 1 3 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_429 cert_430 cert_442
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_444 : count (rows.drop 11) (bag 2 0 1 5 1 100) (some 4) =
    (X + 146 * X ^ 2 + 4100 * X ^ 3 + 21472 * X ^ 4 + 21918 * X ^ 5 + 3267 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 1 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 2 0 1 5 1 100).erase 1 = (bag 1 0 1 5 1 100) := by rfl
  have hm3 : (bag 2 0 1 5 1 100).erase 3 = (bag 2 0 0 5 1 100) := by rfl
  have hm4 : (bag 2 0 1 5 1 100).erase 4 = (bag 2 0 1 4 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 2 0 1 5 1 100) (bag 1 0 1 5 1 100) (bag 2 0 0 5 1 100) (bag 2 0 1 4 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_427 cert_428 cert_443
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_445 : count (rows.drop 10) (bag 2 0 1 6 1 100) (some 4) =
    (X + 151 * X ^ 2 + 4689 * X ^ 3 + 28375 * X ^ 4 + 35814 * X ^ 5 + 7326 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 1 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 2 0 1 6 1 100).erase 1 = (bag 1 0 1 6 1 100) := by rfl
  have hm3 : (bag 2 0 1 6 1 100).erase 3 = (bag 2 0 0 6 1 100) := by rfl
  have hm4 : (bag 2 0 1 6 1 100).erase 4 = (bag 2 0 1 5 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 2 0 1 6 1 100) (bag 1 0 1 6 1 100) (bag 2 0 0 6 1 100) (bag 2 0 1 5 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_425 cert_426 cert_444
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_446 : count (rows.drop 9) (bag 2 0 1 7 1 100) (some 4) =
    (X + 156 * X ^ 2 + 5285 * X ^ 3 + 36038 * X ^ 4 + 53740 * X ^ 5 + 13860 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 1 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 2 0 1 7 1 100).erase 1 = (bag 1 0 1 7 1 100) := by rfl
  have hm3 : (bag 2 0 1 7 1 100).erase 3 = (bag 2 0 0 7 1 100) := by rfl
  have hm4 : (bag 2 0 1 7 1 100).erase 4 = (bag 2 0 1 6 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 2 0 1 7 1 100) (bag 1 0 1 7 1 100) (bag 2 0 0 7 1 100) (bag 2 0 1 6 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_423 cert_424 cert_445
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_447 : count (rows.drop 8) (bag 2 0 1 8 1 100) (some 3) =
    (6 * X ^ 2 + 759 * X ^ 3 + 13711 * X ^ 4 + 58306 * X ^ 5 + 63343 * X ^ 6 + 13860 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 0 1 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm1 : (bag 2 0 1 8 1 100).erase 1 = (bag 1 0 1 8 1 100) := by rfl
  have hm3 : (bag 2 0 1 8 1 100).erase 3 = (bag 2 0 0 8 1 100) := by rfl
  have hm4 : (bag 2 0 1 8 1 100).erase 4 = (bag 2 0 1 7 1 100) := by rfl
  have hc := count_three (rows.drop 8) (rows.drop 9) (bag 2 0 1 8 1 100) (bag 1 0 1 8 1 100) (bag 2 0 0 8 1 100) (bag 2 0 1 7 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_402 cert_422 cert_446
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_448 : count (rows.drop 9) (bag 1 0 2 7 1 100) (some 1) =
    (2 * X ^ 2 + 280 * X ^ 3 + 7252 * X ^ 4 + 40161 * X ^ 5 + 50000 * X ^ 6 + 11385 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 0 2 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 1 0 2 7 1 100).erase 1 = (bag 0 0 2 7 1 100) := by rfl
  have hm3 : (bag 1 0 2 7 1 100).erase 3 = (bag 1 0 1 7 1 100) := by rfl
  have hm4 : (bag 1 0 2 7 1 100).erase 4 = (bag 1 0 2 6 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 1 0 2 7 1 100) (bag 0 0 2 7 1 100) (bag 1 0 1 7 1 100) (bag 1 0 2 6 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_244 cert_245 cert_266
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_449 : count (rows.drop 9) (bag 2 0 1 7 1 100) (some 3) =
    (6 * X ^ 2 + 747 * X ^ 3 + 12352 * X ^ 4 + 46301 * X ^ 5 + 42348 * X ^ 6 + 7326 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 0 1 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 2 0 1 7 1 100).erase 1 = (bag 1 0 1 7 1 100) := by rfl
  have hm3 : (bag 2 0 1 7 1 100).erase 3 = (bag 2 0 0 7 1 100) := by rfl
  have hm4 : (bag 2 0 1 7 1 100).erase 4 = (bag 2 0 1 6 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 2 0 1 7 1 100) (bag 1 0 1 7 1 100) (bag 2 0 0 7 1 100) (bag 2 0 1 6 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_423 cert_424 cert_445
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_450 : count (rows.drop 10) (bag 1 0 2 6 1 100) (some 1) =
    (2 * X ^ 2 + 273 * X ^ 3 + 6439 * X ^ 4 + 31405 * X ^ 5 + 32495 * X ^ 6 + 5742 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 0 2 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 1 0 2 6 1 100).erase 1 = (bag 0 0 2 6 1 100) := by rfl
  have hm3 : (bag 1 0 2 6 1 100).erase 3 = (bag 1 0 1 6 1 100) := by rfl
  have hm4 : (bag 1 0 2 6 1 100).erase 4 = (bag 1 0 2 5 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 1 0 2 6 1 100) (bag 0 0 2 6 1 100) (bag 1 0 1 6 1 100) (bag 1 0 2 5 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_246 cert_247 cert_265
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_451 : count (rows.drop 10) (bag 2 0 1 6 1 100) (some 3) =
    (6 * X ^ 2 + 735 * X ^ 3 + 11003 * X ^ 4 + 35368 * X ^ 5 + 25977 * X ^ 6 + 3267 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 0 1 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 2 0 1 6 1 100).erase 1 = (bag 1 0 1 6 1 100) := by rfl
  have hm3 : (bag 2 0 1 6 1 100).erase 3 = (bag 2 0 0 6 1 100) := by rfl
  have hm4 : (bag 2 0 1 6 1 100).erase 4 = (bag 2 0 1 5 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 2 0 1 6 1 100) (bag 1 0 1 6 1 100) (bag 2 0 0 6 1 100) (bag 2 0 1 5 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_425 cert_426 cert_444
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_452 : count (rows.drop 11) (bag 1 0 2 5 1 100) (some 1) =
    (2 * X ^ 2 + 266 * X ^ 3 + 5634 * X ^ 4 + 23512 * X ^ 5 + 19114 * X ^ 6 + 2376 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 0 2 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 1 0 2 5 1 100).erase 1 = (bag 0 0 2 5 1 100) := by rfl
  have hm3 : (bag 1 0 2 5 1 100).erase 3 = (bag 1 0 1 5 1 100) := by rfl
  have hm4 : (bag 1 0 2 5 1 100).erase 4 = (bag 1 0 2 4 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 1 0 2 5 1 100) (bag 0 0 2 5 1 100) (bag 1 0 1 5 1 100) (bag 1 0 2 4 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_248 cert_249 cert_264
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_453 : count (rows.drop 11) (bag 2 0 1 5 1 100) (some 3) =
    (6 * X ^ 2 + 723 * X ^ 3 + 9664 * X ^ 4 + 25504 * X ^ 5 + 13918 * X ^ 6 + 1089 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 0 1 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 2 0 1 5 1 100).erase 1 = (bag 1 0 1 5 1 100) := by rfl
  have hm3 : (bag 2 0 1 5 1 100).erase 3 = (bag 2 0 0 5 1 100) := by rfl
  have hm4 : (bag 2 0 1 5 1 100).erase 4 = (bag 2 0 1 4 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 2 0 1 5 1 100) (bag 1 0 1 5 1 100) (bag 2 0 0 5 1 100) (bag 2 0 1 4 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_427 cert_428 cert_443
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_454 : count (rows.drop 12) (bag 1 0 2 4 1 100) (some 1) =
    (2 * X ^ 2 + 259 * X ^ 3 + 4837 * X ^ 4 + 16479 * X ^ 5 + 9545 * X ^ 6 + 693 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 0 2 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 1 0 2 4 1 100).erase 1 = (bag 0 0 2 4 1 100) := by rfl
  have hm3 : (bag 1 0 2 4 1 100).erase 3 = (bag 1 0 1 4 1 100) := by rfl
  have hm4 : (bag 1 0 2 4 1 100).erase 4 = (bag 1 0 2 3 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 1 0 2 4 1 100) (bag 0 0 2 4 1 100) (bag 1 0 1 4 1 100) (bag 1 0 2 3 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_250 cert_251 cert_263
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_455 : count (rows.drop 12) (bag 2 0 1 4 1 100) (some 3) =
    (6 * X ^ 2 + 711 * X ^ 3 + 8335 * X ^ 4 + 16706 * X ^ 5 + 5859 * X ^ 6 + 198 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 0 1 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 2 0 1 4 1 100).erase 1 = (bag 1 0 1 4 1 100) := by rfl
  have hm3 : (bag 2 0 1 4 1 100).erase 3 = (bag 2 0 0 4 1 100) := by rfl
  have hm4 : (bag 2 0 1 4 1 100).erase 4 = (bag 2 0 1 3 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 2 0 1 4 1 100) (bag 1 0 1 4 1 100) (bag 2 0 0 4 1 100) (bag 2 0 1 3 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_429 cert_430 cert_442
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_456 : count (rows.drop 13) (bag 1 0 2 3 1 100) (some 1) =
    (2 * X ^ 2 + 252 * X ^ 3 + 4048 * X ^ 4 + 10303 * X ^ 5 + 3476 * X ^ 6 + 99 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 0 2 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 1 0 2 3 1 100).erase 1 = (bag 0 0 2 3 1 100) := by rfl
  have hm3 : (bag 1 0 2 3 1 100).erase 3 = (bag 1 0 1 3 1 100) := by rfl
  have hm4 : (bag 1 0 2 3 1 100).erase 4 = (bag 1 0 2 2 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 1 0 2 3 1 100) (bag 0 0 2 3 1 100) (bag 1 0 1 3 1 100) (bag 1 0 2 2 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_252 cert_253 cert_262
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_457 : count (rows.drop 13) (bag 2 0 1 3 1 100) (some 3) =
    (6 * X ^ 2 + 699 * X ^ 3 + 7016 * X ^ 4 + 8971 * X ^ 5 + 1488 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 1 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 2 0 1 3 1 100).erase 1 = (bag 1 0 1 3 1 100) := by rfl
  have hm3 : (bag 2 0 1 3 1 100).erase 3 = (bag 2 0 0 3 1 100) := by rfl
  have hm4 : (bag 2 0 1 3 1 100).erase 4 = (bag 2 0 1 2 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 2 0 1 3 1 100) (bag 1 0 1 3 1 100) (bag 2 0 0 3 1 100) (bag 2 0 1 2 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_431 cert_432 cert_441
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_458 : count (rows.drop 14) (bag 1 0 2 2 1 100) (some 1) =
    (2 * X ^ 2 + 245 * X ^ 3 + 3267 * X ^ 4 + 4981 * X ^ 5 + 595 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 0 2 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 1 0 2 2 1 100).erase 1 = (bag 0 0 2 2 1 100) := by rfl
  have hm3 : (bag 1 0 2 2 1 100).erase 3 = (bag 1 0 1 2 1 100) := by rfl
  have hm4 : (bag 1 0 2 2 1 100).erase 4 = (bag 1 0 2 1 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 1 0 2 2 1 100) (bag 0 0 2 2 1 100) (bag 1 0 1 2 1 100) (bag 1 0 2 1 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_254 cert_255 cert_261
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_459 : count (rows.drop 14) (bag 2 0 1 2 1 100) (some 3) =
    (8 * X ^ 2 + 778 * X ^ 3 + 5323 * X ^ 4 + 2882 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 1 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 2 0 1 2 1 100).erase 1 = (bag 1 0 1 2 1 100) := by rfl
  have hm3 : (bag 2 0 1 2 1 100).erase 3 = (bag 2 0 0 2 1 100) := by rfl
  have hm4 : (bag 2 0 1 2 1 100).erase 4 = (bag 2 0 1 1 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 2 0 1 2 1 100) (bag 1 0 1 2 1 100) (bag 2 0 0 2 1 100) (bag 2 0 1 1 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_433 cert_434 cert_440
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_460 : count (rows.drop 15) (bag 1 0 2 1 1 100) (some 1) =
    (2 * X ^ 2 + 234 * X ^ 3 + 2308 * X ^ 4 + 1092 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 0 2 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 1 0 2 1 1 100).erase 1 = (bag 0 0 2 1 1 100) := by rfl
  have hm3 : (bag 1 0 2 1 1 100).erase 3 = (bag 1 0 1 1 1 100) := by rfl
  have hm4 : (bag 1 0 2 1 1 100).erase 4 = (bag 1 0 2 0 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 1 0 2 1 1 100) (bag 0 0 2 1 1 100) (bag 1 0 1 1 1 100) (bag 1 0 2 0 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_256 cert_257 cert_260
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_461 : count (rows.drop 15) (bag 2 0 1 1 1 100) (some 3) =
    (14 * X ^ 2 + 1134 * X ^ 3 + 2290 * X ^ 4 + 198 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 2 0 1 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 2 0 1 1 1 100).erase 1 = (bag 1 0 1 1 1 100) := by rfl
  have hm3 : (bag 2 0 1 1 1 100).erase 3 = (bag 2 0 0 1 1 100) := by rfl
  have hm4 : (bag 2 0 1 1 1 100).erase 4 = (bag 2 0 1 0 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 2 0 1 1 1 100) (bag 1 0 1 1 1 100) (bag 2 0 0 1 1 100) (bag 2 0 1 0 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_435 cert_436 cert_439
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_462 : count (rows.drop 16) (bag 1 0 2 0 1 100) (some 1) =
    (4 * X ^ 2 + 309 * X ^ 3 + 596 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 0 2 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 1 0 2 0 1 100).erase 1 = (bag 0 0 2 0 1 100) := by rfl
  have hm3 : (bag 1 0 2 0 1 100).erase 3 = (bag 1 0 1 0 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 1 0 2 0 1 100) (bag 0 0 2 0 1 100) (bag 1 0 1 0 1 100) (some 1) 4 1 3 hr hs (by decide) hm1 hm3 _ _ cert_258 cert_259
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_463 : count (rows.drop 16) (bag 2 0 1 0 1 100) (some 3) =
    (X + 111 * X ^ 2 + 698 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 2 0 1 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 2 0 1 0 1 100).erase 1 = (bag 1 0 1 0 1 100) := by rfl
  have hm3 : (bag 2 0 1 0 1 100).erase 3 = (bag 2 0 0 0 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 2 0 1 0 1 100) (bag 1 0 1 0 1 100) (bag 2 0 0 0 1 100) (some 3) 4 1 3 hr hs (by decide) hm1 hm3 _ _ cert_437 cert_438
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_464 : count (rows.drop 15) (bag 2 0 2 0 1 100) (some 4) =
    (X + 115 * X ^ 2 + 1007 * X ^ 3 + 695 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 2 0 2 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 2 0 2 0 1 100).erase 1 = (bag 1 0 2 0 1 100) := by rfl
  have hm3 : (bag 2 0 2 0 1 100).erase 3 = (bag 2 0 1 0 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 2 0 2 0 1 100) (bag 1 0 2 0 1 100) (bag 2 0 1 0 1 100) (some 4) 4 1 3 hr hs (by decide) hm1 hm3 _ _ cert_462 cert_463
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_465 : count (rows.drop 14) (bag 2 0 2 1 1 100) (some 4) =
    (X + 131 * X ^ 2 + 2375 * X ^ 3 + 5293 * X ^ 4 + 1290 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 2 0 2 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 2 0 2 1 1 100).erase 1 = (bag 1 0 2 1 1 100) := by rfl
  have hm3 : (bag 2 0 2 1 1 100).erase 3 = (bag 2 0 1 1 1 100) := by rfl
  have hm4 : (bag 2 0 2 1 1 100).erase 4 = (bag 2 0 2 0 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 2 0 2 1 1 100) (bag 1 0 2 1 1 100) (bag 2 0 1 1 1 100) (bag 2 0 2 0 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_460 cert_461 cert_464
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_466 : count (rows.drop 13) (bag 2 0 2 2 1 100) (some 4) =
    (X + 141 * X ^ 2 + 3398 * X ^ 3 + 13883 * X ^ 4 + 9153 * X ^ 5 + 694 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 2 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 2 0 2 2 1 100).erase 1 = (bag 1 0 2 2 1 100) := by rfl
  have hm3 : (bag 2 0 2 2 1 100).erase 3 = (bag 2 0 1 2 1 100) := by rfl
  have hm4 : (bag 2 0 2 2 1 100).erase 4 = (bag 2 0 2 1 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 2 0 2 2 1 100) (bag 1 0 2 2 1 100) (bag 2 0 1 2 1 100) (bag 2 0 2 1 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_458 cert_459 cert_465
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_467 : count (rows.drop 12) (bag 2 0 2 3 1 100) (some 4) =
    (X + 149 * X ^ 2 + 4349 * X ^ 3 + 24947 * X ^ 4 + 28427 * X ^ 5 + 5658 * X ^ 6 + 99 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 0 2 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 2 0 2 3 1 100).erase 1 = (bag 1 0 2 3 1 100) := by rfl
  have hm3 : (bag 2 0 2 3 1 100).erase 3 = (bag 2 0 1 3 1 100) := by rfl
  have hm4 : (bag 2 0 2 3 1 100).erase 4 = (bag 2 0 2 2 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 2 0 2 3 1 100) (bag 1 0 2 3 1 100) (bag 2 0 1 3 1 100) (bag 2 0 2 2 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_456 cert_457 cert_466
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_468 : count (rows.drop 11) (bag 2 0 2 4 1 100) (some 4) =
    (X + 157 * X ^ 2 + 5319 * X ^ 3 + 38119 * X ^ 4 + 61612 * X ^ 5 + 21062 * X ^ 6 + 990 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 0 2 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 2 0 2 4 1 100).erase 1 = (bag 1 0 2 4 1 100) := by rfl
  have hm3 : (bag 2 0 2 4 1 100).erase 3 = (bag 2 0 1 4 1 100) := by rfl
  have hm4 : (bag 2 0 2 4 1 100).erase 4 = (bag 2 0 2 3 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 2 0 2 4 1 100) (bag 1 0 2 4 1 100) (bag 2 0 1 4 1 100) (bag 2 0 2 3 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_454 cert_455 cert_467
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_469 : count (rows.drop 10) (bag 2 0 2 5 1 100) (some 4) =
    (X + 165 * X ^ 2 + 6308 * X ^ 3 + 53417 * X ^ 4 + 110628 * X ^ 5 + 54094 * X ^ 6 + 4455 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 0 2 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 2 0 2 5 1 100).erase 1 = (bag 1 0 2 5 1 100) := by rfl
  have hm3 : (bag 2 0 2 5 1 100).erase 3 = (bag 2 0 1 5 1 100) := by rfl
  have hm4 : (bag 2 0 2 5 1 100).erase 4 = (bag 2 0 2 4 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 2 0 2 5 1 100) (bag 1 0 2 5 1 100) (bag 2 0 1 5 1 100) (bag 2 0 2 4 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_452 cert_453 cert_468
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_470 : count (rows.drop 9) (bag 2 0 2 6 1 100) (some 4) =
    (X + 173 * X ^ 2 + 7316 * X ^ 3 + 70859 * X ^ 4 + 177401 * X ^ 5 + 112566 * X ^ 6 + 13464 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 0 2 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 2 0 2 6 1 100).erase 1 = (bag 1 0 2 6 1 100) := by rfl
  have hm3 : (bag 2 0 2 6 1 100).erase 3 = (bag 2 0 1 6 1 100) := by rfl
  have hm4 : (bag 2 0 2 6 1 100).erase 4 = (bag 2 0 2 5 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 2 0 2 6 1 100) (bag 1 0 2 6 1 100) (bag 2 0 1 6 1 100) (bag 2 0 2 5 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_450 cert_451 cert_469
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_471 : count (rows.drop 8) (bag 2 0 2 7 1 100) (some 4) =
    (X + 181 * X ^ 2 + 8343 * X ^ 3 + 90463 * X ^ 4 + 263863 * X ^ 5 + 204914 * X ^ 6 + 32175 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 0 2 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm1 : (bag 2 0 2 7 1 100).erase 1 = (bag 1 0 2 7 1 100) := by rfl
  have hm3 : (bag 2 0 2 7 1 100).erase 3 = (bag 2 0 1 7 1 100) := by rfl
  have hm4 : (bag 2 0 2 7 1 100).erase 4 = (bag 2 0 2 6 1 100) := by rfl
  have hc := count_three (rows.drop 8) (rows.drop 9) (bag 2 0 2 7 1 100) (bag 1 0 2 7 1 100) (bag 2 0 1 7 1 100) (bag 2 0 2 6 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_448 cert_449 cert_470
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_472 : count (rows.drop 7) (bag 2 0 2 8 1 100) (some 3) =
    (9 * X ^ 2 + 1227 * X ^ 3 + 30127 * X ^ 4 + 198552 * X ^ 5 + 399147 * X ^ 6 + 238673 * X ^ 7 + 32175 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 2 0 2 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 7 = 4 :: rows.drop 8 := by rfl
  have hm1 : (bag 2 0 2 8 1 100).erase 1 = (bag 1 0 2 8 1 100) := by rfl
  have hm3 : (bag 2 0 2 8 1 100).erase 3 = (bag 2 0 1 8 1 100) := by rfl
  have hm4 : (bag 2 0 2 8 1 100).erase 4 = (bag 2 0 2 7 1 100) := by rfl
  have hc := count_three (rows.drop 7) (rows.drop 8) (bag 2 0 2 8 1 100) (bag 1 0 2 8 1 100) (bag 2 0 1 8 1 100) (bag 2 0 2 7 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_401 cert_447 cert_471
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_473 : count (rows.drop 6) (bag 2 0 3 8 1 100) (some 3) =
    (11 * X ^ 2 + 1539 * X ^ 3 + 41321 * X ^ 4 + 299501 * X ^ 5 + 661519 * X ^ 6 + 433094 * X ^ 7 + 62865 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 2 0 3 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 6 = 3 :: rows.drop 7 := by rfl
  have hm1 : (bag 2 0 3 8 1 100).erase 1 = (bag 1 0 3 8 1 100) := by rfl
  have hm3 : (bag 2 0 3 8 1 100).erase 3 = (bag 2 0 2 8 1 100) := by rfl
  have hc := count_two (rows.drop 6) (rows.drop 7) (bag 2 0 3 8 1 100) (bag 1 0 3 8 1 100) (bag 2 0 2 8 1 100) (some 3) 3 1 3 hr hs (by decide) hm1 hm3 _ _ cert_400 cert_472
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_474 : count (rows.drop 5) (bag 2 0 4 8 1 100) (some 2) =
    (X ^ 2 + 162 * X ^ 3 + 6814 * X ^ 4 + 96623 * X ^ 5 + 513181 * X ^ 6 + 970317 * X ^ 7 + 582982 * X ^ 8 + 79695 * X ^ 9 : ℕ[X]) := by
  have hs : (bag 2 0 4 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 5 = 3 :: rows.drop 6 := by rfl
  have hm1 : (bag 2 0 4 8 1 100).erase 1 = (bag 1 0 4 8 1 100) := by rfl
  have hm3 : (bag 2 0 4 8 1 100).erase 3 = (bag 2 0 3 8 1 100) := by rfl
  have hc := count_two (rows.drop 5) (rows.drop 6) (bag 2 0 4 8 1 100) (bag 1 0 4 8 1 100) (bag 2 0 3 8 1 100) (some 2) 3 1 3 hr hs (by decide) hm1 hm3 _ _ cert_399 cert_473
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_475 : count (rows.drop 6) (bag 1 1 3 8 1 100) (some 1) =
    (X ^ 2 + 192 * X ^ 3 + 10113 * X ^ 4 + 146248 * X ^ 5 + 716023 * X ^ 6 + 1265902 * X ^ 7 + 752321 * X ^ 8 + 108900 * X ^ 9 : ℕ[X]) := by
  have hs : (bag 1 1 3 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 6 = 3 :: rows.drop 7 := by rfl
  have hm1 : (bag 1 1 3 8 1 100).erase 1 = (bag 0 1 3 8 1 100) := by rfl
  have hm2 : (bag 1 1 3 8 1 100).erase 2 = (bag 1 0 3 8 1 100) := by rfl
  have hm3 : (bag 1 1 3 8 1 100).erase 3 = (bag 1 1 2 8 1 100) := by rfl
  have hc := count_three (rows.drop 6) (rows.drop 7) (bag 1 1 3 8 1 100) (bag 0 1 3 8 1 100) (bag 1 0 3 8 1 100) (bag 1 1 2 8 1 100) (some 1) 3 1 2 3 hr hs (by decide) (by decide) hm1 hm2 hm3 _ _ _ cert_295 cert_296 cert_396
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_476 : count (rows.drop 6) (bag 2 0 3 8 1 100) (some 2) =
    (2 * X ^ 2 + 321 * X ^ 3 + 12421 * X ^ 4 + 131076 * X ^ 5 + 460924 * X ^ 6 + 593568 * X ^ 7 + 269363 * X ^ 8 + 32175 * X ^ 9 : ℕ[X]) := by
  have hs : (bag 2 0 3 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 6 = 3 :: rows.drop 7 := by rfl
  have hm1 : (bag 2 0 3 8 1 100).erase 1 = (bag 1 0 3 8 1 100) := by rfl
  have hm3 : (bag 2 0 3 8 1 100).erase 3 = (bag 2 0 2 8 1 100) := by rfl
  have hc := count_two (rows.drop 6) (rows.drop 7) (bag 2 0 3 8 1 100) (bag 1 0 3 8 1 100) (bag 2 0 2 8 1 100) (some 2) 3 1 3 hr hs (by decide) hm1 hm3 _ _ cert_400 cert_472
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_477 : count (rows.drop 7) (bag 1 1 2 8 1 100) (some 1) =
    (2 * X ^ 2 + 385 * X ^ 3 + 19350 * X ^ 4 + 229968 * X ^ 5 + 744802 * X ^ 6 + 673445 * X ^ 7 + 131868 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 1 1 2 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 7 = 4 :: rows.drop 8 := by rfl
  have hm1 : (bag 1 1 2 8 1 100).erase 1 = (bag 0 1 2 8 1 100) := by rfl
  have hm2 : (bag 1 1 2 8 1 100).erase 2 = (bag 1 0 2 8 1 100) := by rfl
  have hm3 : (bag 1 1 2 8 1 100).erase 3 = (bag 1 1 1 8 1 100) := by rfl
  have hm4 : (bag 1 1 2 8 1 100).erase 4 = (bag 1 1 2 7 1 100) := by rfl
  have hc := count_four (rows.drop 7) (rows.drop 8) (bag 1 1 2 8 1 100) (bag 0 1 2 8 1 100) (bag 1 0 2 8 1 100) (bag 1 1 1 8 1 100) (bag 1 1 2 7 1 100) (some 1) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_297 cert_298 cert_363 cert_395
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_478 : count (rows.drop 7) (bag 2 0 2 8 1 100) (some 2) =
    (3 * X ^ 2 + 474 * X ^ 3 + 17175 * X ^ 4 + 153957 * X ^ 5 + 394110 * X ^ 6 + 288156 * X ^ 7 + 46035 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 2 0 2 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 7 = 4 :: rows.drop 8 := by rfl
  have hm1 : (bag 2 0 2 8 1 100).erase 1 = (bag 1 0 2 8 1 100) := by rfl
  have hm3 : (bag 2 0 2 8 1 100).erase 3 = (bag 2 0 1 8 1 100) := by rfl
  have hm4 : (bag 2 0 2 8 1 100).erase 4 = (bag 2 0 2 7 1 100) := by rfl
  have hc := count_three (rows.drop 7) (rows.drop 8) (bag 2 0 2 8 1 100) (bag 1 0 2 8 1 100) (bag 2 0 1 8 1 100) (bag 2 0 2 7 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_401 cert_447 cert_471
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_479 : count (rows.drop 8) (bag 1 1 1 8 1 100) (some 1) =
    (2 * X ^ 2 + 329 * X ^ 3 + 12295 * X ^ 4 + 90587 * X ^ 5 + 149831 * X ^ 6 + 46926 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 1 1 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm1 : (bag 1 1 1 8 1 100).erase 1 = (bag 0 1 1 8 1 100) := by rfl
  have hm2 : (bag 1 1 1 8 1 100).erase 2 = (bag 1 0 1 8 1 100) := by rfl
  have hm3 : (bag 1 1 1 8 1 100).erase 3 = (bag 1 1 0 8 1 100) := by rfl
  have hm4 : (bag 1 1 1 8 1 100).erase 4 = (bag 1 1 1 7 1 100) := by rfl
  have hc := count_four (rows.drop 8) (rows.drop 9) (bag 1 1 1 8 1 100) (bag 0 1 1 8 1 100) (bag 1 0 1 8 1 100) (bag 1 1 0 8 1 100) (bag 1 1 1 7 1 100) (some 1) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_299 cert_300 cert_330 cert_362
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_480 : count (rows.drop 8) (bag 2 0 1 8 1 100) (some 2) =
    (3 * X ^ 2 + 417 * X ^ 3 + 10548 * X ^ 4 + 54510 * X ^ 5 + 68172 * X ^ 6 + 16335 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 0 1 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm1 : (bag 2 0 1 8 1 100).erase 1 = (bag 1 0 1 8 1 100) := by rfl
  have hm3 : (bag 2 0 1 8 1 100).erase 3 = (bag 2 0 0 8 1 100) := by rfl
  have hm4 : (bag 2 0 1 8 1 100).erase 4 = (bag 2 0 1 7 1 100) := by rfl
  have hc := count_three (rows.drop 8) (rows.drop 9) (bag 2 0 1 8 1 100) (bag 1 0 1 8 1 100) (bag 2 0 0 8 1 100) (bag 2 0 1 7 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_402 cert_422 cert_446
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_481 : count (rows.drop 9) (bag 1 1 0 8 1 100) (some 1) =
    (2 * X ^ 2 + 258 * X ^ 3 + 4918 * X ^ 4 + 14964 * X ^ 5 + 7128 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 0 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 1 1 0 8 1 100).erase 1 = (bag 0 1 0 8 1 100) := by rfl
  have hm2 : (bag 1 1 0 8 1 100).erase 2 = (bag 1 0 0 8 1 100) := by rfl
  have hm4 : (bag 1 1 0 8 1 100).erase 4 = (bag 1 1 0 7 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 1 1 0 8 1 100) (bag 0 1 0 8 1 100) (bag 1 0 0 8 1 100) (bag 1 1 0 7 1 100) (some 1) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_301 cert_302 cert_329
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_482 : count (rows.drop 9) (bag 2 0 0 8 1 100) (some 2) =
    (3 * X ^ 2 + 345 * X ^ 3 + 3508 * X ^ 4 + 7304 * X ^ 5 + 2475 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 0 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 2 0 0 8 1 100).erase 1 = (bag 1 0 0 8 1 100) := by rfl
  have hm4 : (bag 2 0 0 8 1 100).erase 4 = (bag 2 0 0 7 1 100) := by rfl
  have hc := count_two (rows.drop 9) (rows.drop 10) (bag 2 0 0 8 1 100) (bag 1 0 0 8 1 100) (bag 2 0 0 7 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_403 cert_421
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_483 : count (rows.drop 10) (bag 1 1 0 7 1 100) (some 1) =
    (2 * X ^ 2 + 254 * X ^ 3 + 4478 * X ^ 4 + 12132 * X ^ 5 + 4950 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 1 1 0 7 1 100).erase 1 = (bag 0 1 0 7 1 100) := by rfl
  have hm2 : (bag 1 1 0 7 1 100).erase 2 = (bag 1 0 0 7 1 100) := by rfl
  have hm4 : (bag 1 1 0 7 1 100).erase 4 = (bag 1 1 0 6 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 1 1 0 7 1 100) (bag 0 1 0 7 1 100) (bag 1 0 0 7 1 100) (bag 1 1 0 6 1 100) (some 1) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_303 cert_304 cert_328
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_484 : count (rows.drop 10) (bag 2 0 0 7 1 100) (some 2) =
    (3 * X ^ 2 + 342 * X ^ 3 + 3185 * X ^ 4 + 5794 * X ^ 5 + 1584 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 2 0 0 7 1 100).erase 1 = (bag 1 0 0 7 1 100) := by rfl
  have hm4 : (bag 2 0 0 7 1 100).erase 4 = (bag 2 0 0 6 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 2 0 0 7 1 100) (bag 1 0 0 7 1 100) (bag 2 0 0 6 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_404 cert_420
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_485 : count (rows.drop 11) (bag 1 1 0 6 1 100) (some 1) =
    (2 * X ^ 2 + 250 * X ^ 3 + 4040 * X ^ 4 + 9508 * X ^ 5 + 3168 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 1 1 0 6 1 100).erase 1 = (bag 0 1 0 6 1 100) := by rfl
  have hm2 : (bag 1 1 0 6 1 100).erase 2 = (bag 1 0 0 6 1 100) := by rfl
  have hm4 : (bag 1 1 0 6 1 100).erase 4 = (bag 1 1 0 5 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 1 1 0 6 1 100) (bag 0 1 0 6 1 100) (bag 1 0 0 6 1 100) (bag 1 1 0 5 1 100) (some 1) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_305 cert_306 cert_327
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_486 : count (rows.drop 11) (bag 2 0 0 6 1 100) (some 2) =
    (3 * X ^ 2 + 339 * X ^ 3 + 2863 * X ^ 4 + 4388 * X ^ 5 + 891 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 2 0 0 6 1 100).erase 1 = (bag 1 0 0 6 1 100) := by rfl
  have hm4 : (bag 2 0 0 6 1 100).erase 4 = (bag 2 0 0 5 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 2 0 0 6 1 100) (bag 1 0 0 6 1 100) (bag 2 0 0 5 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_405 cert_419
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_487 : count (rows.drop 12) (bag 1 1 0 5 1 100) (some 1) =
    (2 * X ^ 2 + 246 * X ^ 3 + 3604 * X ^ 4 + 7092 * X ^ 5 + 1782 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 1 1 0 5 1 100).erase 1 = (bag 0 1 0 5 1 100) := by rfl
  have hm2 : (bag 1 1 0 5 1 100).erase 2 = (bag 1 0 0 5 1 100) := by rfl
  have hm4 : (bag 1 1 0 5 1 100).erase 4 = (bag 1 1 0 4 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 1 1 0 5 1 100) (bag 0 1 0 5 1 100) (bag 1 0 0 5 1 100) (bag 1 1 0 4 1 100) (some 1) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_307 cert_308 cert_326
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_488 : count (rows.drop 12) (bag 2 0 0 5 1 100) (some 2) =
    (3 * X ^ 2 + 336 * X ^ 3 + 2542 * X ^ 4 + 3086 * X ^ 5 + 396 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 2 0 0 5 1 100).erase 1 = (bag 1 0 0 5 1 100) := by rfl
  have hm4 : (bag 2 0 0 5 1 100).erase 4 = (bag 2 0 0 4 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 2 0 0 5 1 100) (bag 1 0 0 5 1 100) (bag 2 0 0 4 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_406 cert_418
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_489 : count (rows.drop 13) (bag 1 1 0 4 1 100) (some 1) =
    (2 * X ^ 2 + 242 * X ^ 3 + 3170 * X ^ 4 + 4884 * X ^ 5 + 792 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 1 1 0 4 1 100).erase 1 = (bag 0 1 0 4 1 100) := by rfl
  have hm2 : (bag 1 1 0 4 1 100).erase 2 = (bag 1 0 0 4 1 100) := by rfl
  have hm4 : (bag 1 1 0 4 1 100).erase 4 = (bag 1 1 0 3 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 1 1 0 4 1 100) (bag 0 1 0 4 1 100) (bag 1 0 0 4 1 100) (bag 1 1 0 3 1 100) (some 1) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_309 cert_310 cert_325
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_490 : count (rows.drop 13) (bag 2 0 0 4 1 100) (some 2) =
    (3 * X ^ 2 + 333 * X ^ 3 + 2222 * X ^ 4 + 1888 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 2 0 0 4 1 100).erase 1 = (bag 1 0 0 4 1 100) := by rfl
  have hm4 : (bag 2 0 0 4 1 100).erase 4 = (bag 2 0 0 3 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 2 0 0 4 1 100) (bag 1 0 0 4 1 100) (bag 2 0 0 3 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_407 cert_417
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_491 : count (rows.drop 14) (bag 1 1 0 3 1 100) (some 1) =
    (2 * X ^ 2 + 238 * X ^ 3 + 2738 * X ^ 4 + 2884 * X ^ 5 + 198 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 1 1 0 3 1 100).erase 1 = (bag 0 1 0 3 1 100) := by rfl
  have hm2 : (bag 1 1 0 3 1 100).erase 2 = (bag 1 0 0 3 1 100) := by rfl
  have hm4 : (bag 1 1 0 3 1 100).erase 4 = (bag 1 1 0 2 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 1 1 0 3 1 100) (bag 0 1 0 3 1 100) (bag 1 0 0 3 1 100) (bag 1 1 0 2 1 100) (some 1) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_311 cert_312 cert_324
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_492 : count (rows.drop 14) (bag 2 0 0 3 1 100) (some 2) =
    (3 * X ^ 2 + 330 * X ^ 3 + 1903 * X ^ 4 + 794 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 2 0 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 2 0 0 3 1 100).erase 1 = (bag 1 0 0 3 1 100) := by rfl
  have hm4 : (bag 2 0 0 3 1 100).erase 4 = (bag 2 0 0 2 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 2 0 0 3 1 100) (bag 1 0 0 3 1 100) (bag 2 0 0 2 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_408 cert_416
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_493 : count (rows.drop 15) (bag 1 1 0 2 1 100) (some 1) =
    (2 * X ^ 2 + 234 * X ^ 3 + 2308 * X ^ 4 + 1092 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 1 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 1 1 0 2 1 100).erase 1 = (bag 0 1 0 2 1 100) := by rfl
  have hm2 : (bag 1 1 0 2 1 100).erase 2 = (bag 1 0 0 2 1 100) := by rfl
  have hm4 : (bag 1 1 0 2 1 100).erase 4 = (bag 1 1 0 1 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 1 1 0 2 1 100) (bag 0 1 0 2 1 100) (bag 1 0 0 2 1 100) (bag 1 1 0 1 1 100) (some 1) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_313 cert_314 cert_323
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_494 : count (rows.drop 15) (bag 2 0 0 2 1 100) (some 2) =
    (5 * X ^ 2 + 420 * X ^ 3 + 1294 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 2 0 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 2 0 0 2 1 100).erase 1 = (bag 1 0 0 2 1 100) := by rfl
  have hm4 : (bag 2 0 0 2 1 100).erase 4 = (bag 2 0 0 1 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 2 0 0 2 1 100) (bag 1 0 0 2 1 100) (bag 2 0 0 1 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_409 cert_415
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_495 : count (rows.drop 16) (bag 1 1 0 1 1 100) (some 1) =
    (5 * X ^ 2 + 419 * X ^ 3 + 1295 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 1 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 1 1 0 1 1 100).erase 1 = (bag 0 1 0 1 1 100) := by rfl
  have hm2 : (bag 1 1 0 1 1 100).erase 2 = (bag 1 0 0 1 1 100) := by rfl
  have hm4 : (bag 1 1 0 1 1 100).erase 4 = (bag 1 1 0 0 1 100) := by rfl
  have hc := count_three (rows.drop 16) (rows.drop 17) (bag 1 1 0 1 1 100) (bag 0 1 0 1 1 100) (bag 1 0 0 1 1 100) (bag 1 1 0 0 1 100) (some 1) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_315 cert_316 cert_322
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_496 : count (rows.drop 16) (bag 2 0 0 1 1 100) (some 2) =
    (8 * X ^ 2 + 604 * X ^ 3 + 297 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 2 0 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 2 0 0 1 1 100).erase 1 = (bag 1 0 0 1 1 100) := by rfl
  have hm4 : (bag 2 0 0 1 1 100).erase 4 = (bag 2 0 0 0 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 2 0 0 1 1 100) (bag 1 0 0 1 1 100) (bag 2 0 0 0 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_410 cert_414
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_497 : count (rows.drop 17) (bag 1 1 0 0 1 100) (some 1) =
    (7 * X ^ 2 + 500 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 1 1 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1, 2, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm1 : (bag 1 1 0 0 1 100).erase 1 = (bag 0 1 0 0 1 100) := by rfl
  have hm2 : (bag 1 1 0 0 1 100).erase 2 = (bag 1 0 0 0 1 100) := by rfl
  have hm5 : (bag 1 1 0 0 1 100).erase 5 = (bag 1 1 0 0 0 100) := by rfl
  have hc := count_three (rows.drop 17) (rows.drop 18) (bag 1 1 0 0 1 100) (bag 0 1 0 0 1 100) (bag 1 0 0 0 1 100) (bag 1 1 0 0 0 100) (some 1) 5 1 2 5 hr hs (by decide) (by decide) hm1 hm2 hm5 _ _ _ cert_317 cert_318 cert_321
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_498 : count (rows.drop 17) (bag 2 0 0 0 1 100) (some 2) =
    (X + 104 * X ^ 2 + 198 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 2 0 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm1 : (bag 2 0 0 0 1 100).erase 1 = (bag 1 0 0 0 1 100) := by rfl
  have hm5 : (bag 2 0 0 0 1 100).erase 5 = (bag 2 0 0 0 0 100) := by rfl
  have hc := count_two (rows.drop 17) (rows.drop 18) (bag 2 0 0 0 1 100) (bag 1 0 0 0 1 100) (bag 2 0 0 0 0 100) (some 2) 5 1 5 hr hs (by decide) hm1 hm5 _ _ cert_411 cert_413
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_499 : count (rows.drop 16) (bag 2 1 0 0 1 100) (some 4) =
    (X + 111 * X ^ 2 + 698 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 2 1 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 2 1 0 0 1 100).erase 1 = (bag 1 1 0 0 1 100) := by rfl
  have hm2 : (bag 2 1 0 0 1 100).erase 2 = (bag 2 0 0 0 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 2 1 0 0 1 100) (bag 1 1 0 0 1 100) (bag 2 0 0 0 1 100) (some 4) 4 1 2 hr hs (by decide) hm1 hm2 _ _ cert_497 cert_498
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_500 : count (rows.drop 15) (bag 2 1 0 1 1 100) (some 4) =
    (X + 124 * X ^ 2 + 1721 * X ^ 3 + 1691 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 2 1 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 2 1 0 1 1 100).erase 1 = (bag 1 1 0 1 1 100) := by rfl
  have hm2 : (bag 2 1 0 1 1 100).erase 2 = (bag 2 0 0 1 1 100) := by rfl
  have hm4 : (bag 2 1 0 1 1 100).erase 4 = (bag 2 1 0 0 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 2 1 0 1 1 100) (bag 1 1 0 1 1 100) (bag 2 0 0 1 1 100) (bag 2 1 0 0 1 100) (some 4) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_495 cert_496 cert_499
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_501 : count (rows.drop 14) (bag 2 1 0 2 1 100) (some 4) =
    (X + 131 * X ^ 2 + 2375 * X ^ 3 + 5293 * X ^ 4 + 1290 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 2 1 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 2 1 0 2 1 100).erase 1 = (bag 1 1 0 2 1 100) := by rfl
  have hm2 : (bag 2 1 0 2 1 100).erase 2 = (bag 2 0 0 2 1 100) := by rfl
  have hm4 : (bag 2 1 0 2 1 100).erase 4 = (bag 2 1 0 1 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 2 1 0 2 1 100) (bag 1 1 0 2 1 100) (bag 2 0 0 2 1 100) (bag 2 1 0 1 1 100) (some 4) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_493 cert_494 cert_500
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_502 : count (rows.drop 13) (bag 2 1 0 3 1 100) (some 4) =
    (X + 136 * X ^ 2 + 2943 * X ^ 3 + 9934 * X ^ 4 + 4968 * X ^ 5 + 198 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 1 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 2 1 0 3 1 100).erase 1 = (bag 1 1 0 3 1 100) := by rfl
  have hm2 : (bag 2 1 0 3 1 100).erase 2 = (bag 2 0 0 3 1 100) := by rfl
  have hm4 : (bag 2 1 0 3 1 100).erase 4 = (bag 2 1 0 2 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 2 1 0 3 1 100) (bag 1 1 0 3 1 100) (bag 2 0 0 3 1 100) (bag 2 1 0 2 1 100) (some 4) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_491 cert_492 cert_501
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_503 : count (rows.drop 12) (bag 2 1 0 4 1 100) (some 4) =
    (X + 141 * X ^ 2 + 3518 * X ^ 3 + 15326 * X ^ 4 + 11740 * X ^ 5 + 1089 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 1 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 2 1 0 4 1 100).erase 1 = (bag 1 1 0 4 1 100) := by rfl
  have hm2 : (bag 2 1 0 4 1 100).erase 2 = (bag 2 0 0 4 1 100) := by rfl
  have hm4 : (bag 2 1 0 4 1 100).erase 4 = (bag 2 1 0 3 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 2 1 0 4 1 100) (bag 1 1 0 4 1 100) (bag 2 0 0 4 1 100) (bag 2 1 0 3 1 100) (some 4) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_489 cert_490 cert_502
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_504 : count (rows.drop 11) (bag 2 1 0 5 1 100) (some 4) =
    (X + 146 * X ^ 2 + 4100 * X ^ 3 + 21472 * X ^ 4 + 21918 * X ^ 5 + 3267 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 1 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 2 1 0 5 1 100).erase 1 = (bag 1 1 0 5 1 100) := by rfl
  have hm2 : (bag 2 1 0 5 1 100).erase 2 = (bag 2 0 0 5 1 100) := by rfl
  have hm4 : (bag 2 1 0 5 1 100).erase 4 = (bag 2 1 0 4 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 2 1 0 5 1 100) (bag 1 1 0 5 1 100) (bag 2 0 0 5 1 100) (bag 2 1 0 4 1 100) (some 4) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_487 cert_488 cert_503
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_505 : count (rows.drop 10) (bag 2 1 0 6 1 100) (some 4) =
    (X + 151 * X ^ 2 + 4689 * X ^ 3 + 28375 * X ^ 4 + 35814 * X ^ 5 + 7326 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 1 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 2 1 0 6 1 100).erase 1 = (bag 1 1 0 6 1 100) := by rfl
  have hm2 : (bag 2 1 0 6 1 100).erase 2 = (bag 2 0 0 6 1 100) := by rfl
  have hm4 : (bag 2 1 0 6 1 100).erase 4 = (bag 2 1 0 5 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 2 1 0 6 1 100) (bag 1 1 0 6 1 100) (bag 2 0 0 6 1 100) (bag 2 1 0 5 1 100) (some 4) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_485 cert_486 cert_504
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_506 : count (rows.drop 9) (bag 2 1 0 7 1 100) (some 4) =
    (X + 156 * X ^ 2 + 5285 * X ^ 3 + 36038 * X ^ 4 + 53740 * X ^ 5 + 13860 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 1 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 2 1 0 7 1 100).erase 1 = (bag 1 1 0 7 1 100) := by rfl
  have hm2 : (bag 2 1 0 7 1 100).erase 2 = (bag 2 0 0 7 1 100) := by rfl
  have hm4 : (bag 2 1 0 7 1 100).erase 4 = (bag 2 1 0 6 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 2 1 0 7 1 100) (bag 1 1 0 7 1 100) (bag 2 0 0 7 1 100) (bag 2 1 0 6 1 100) (some 4) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_483 cert_484 cert_505
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_507 : count (rows.drop 8) (bag 2 1 0 8 1 100) (some 3) =
    (6 * X ^ 2 + 759 * X ^ 3 + 13711 * X ^ 4 + 58306 * X ^ 5 + 63343 * X ^ 6 + 13860 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 1 0 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm1 : (bag 2 1 0 8 1 100).erase 1 = (bag 1 1 0 8 1 100) := by rfl
  have hm2 : (bag 2 1 0 8 1 100).erase 2 = (bag 2 0 0 8 1 100) := by rfl
  have hm4 : (bag 2 1 0 8 1 100).erase 4 = (bag 2 1 0 7 1 100) := by rfl
  have hc := count_three (rows.drop 8) (rows.drop 9) (bag 2 1 0 8 1 100) (bag 1 1 0 8 1 100) (bag 2 0 0 8 1 100) (bag 2 1 0 7 1 100) (some 3) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_481 cert_482 cert_506
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_508 : count (rows.drop 9) (bag 1 1 1 7 1 100) (some 1) =
    (2 * X ^ 2 + 319 * X ^ 3 + 11085 * X ^ 4 + 73441 * X ^ 5 + 105593 * X ^ 6 + 27720 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 1 1 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 1 1 1 7 1 100).erase 1 = (bag 0 1 1 7 1 100) := by rfl
  have hm2 : (bag 1 1 1 7 1 100).erase 2 = (bag 1 0 1 7 1 100) := by rfl
  have hm3 : (bag 1 1 1 7 1 100).erase 3 = (bag 1 1 0 7 1 100) := by rfl
  have hm4 : (bag 1 1 1 7 1 100).erase 4 = (bag 1 1 1 6 1 100) := by rfl
  have hc := count_four (rows.drop 9) (rows.drop 10) (bag 1 1 1 7 1 100) (bag 0 1 1 7 1 100) (bag 1 0 1 7 1 100) (bag 1 1 0 7 1 100) (bag 1 1 1 6 1 100) (some 1) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_331 cert_332 cert_333 cert_361
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_509 : count (rows.drop 9) (bag 2 0 1 7 1 100) (some 2) =
    (3 * X ^ 2 + 408 * X ^ 3 + 9509 * X ^ 4 + 43692 * X ^ 5 + 46558 * X ^ 6 + 8910 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 0 1 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 2 0 1 7 1 100).erase 1 = (bag 1 0 1 7 1 100) := by rfl
  have hm3 : (bag 2 0 1 7 1 100).erase 3 = (bag 2 0 0 7 1 100) := by rfl
  have hm4 : (bag 2 0 1 7 1 100).erase 4 = (bag 2 0 1 6 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 2 0 1 7 1 100) (bag 1 0 1 7 1 100) (bag 2 0 0 7 1 100) (bag 2 0 1 6 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_423 cert_424 cert_445
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_510 : count (rows.drop 9) (bag 2 1 0 7 1 100) (some 3) =
    (6 * X ^ 2 + 747 * X ^ 3 + 12352 * X ^ 4 + 46301 * X ^ 5 + 42348 * X ^ 6 + 7326 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 1 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 2 1 0 7 1 100).erase 1 = (bag 1 1 0 7 1 100) := by rfl
  have hm2 : (bag 2 1 0 7 1 100).erase 2 = (bag 2 0 0 7 1 100) := by rfl
  have hm4 : (bag 2 1 0 7 1 100).erase 4 = (bag 2 1 0 6 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 2 1 0 7 1 100) (bag 1 1 0 7 1 100) (bag 2 0 0 7 1 100) (bag 2 1 0 6 1 100) (some 3) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_483 cert_484 cert_505
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_511 : count (rows.drop 10) (bag 1 1 1 6 1 100) (some 1) =
    (2 * X ^ 2 + 309 * X ^ 3 + 9889 * X ^ 4 + 57821 * X ^ 5 + 70039 * X ^ 6 + 14652 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 1 1 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 1 1 1 6 1 100).erase 1 = (bag 0 1 1 6 1 100) := by rfl
  have hm2 : (bag 1 1 1 6 1 100).erase 2 = (bag 1 0 1 6 1 100) := by rfl
  have hm3 : (bag 1 1 1 6 1 100).erase 3 = (bag 1 1 0 6 1 100) := by rfl
  have hm4 : (bag 1 1 1 6 1 100).erase 4 = (bag 1 1 1 5 1 100) := by rfl
  have hc := count_four (rows.drop 10) (rows.drop 11) (bag 1 1 1 6 1 100) (bag 0 1 1 6 1 100) (bag 1 0 1 6 1 100) (bag 1 1 0 6 1 100) (bag 1 1 1 5 1 100) (some 1) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_334 cert_335 cert_336 cert_360
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_512 : count (rows.drop 10) (bag 2 0 1 6 1 100) (some 2) =
    (3 * X ^ 2 + 399 * X ^ 3 + 8479 * X ^ 4 + 33843 * X ^ 5 + 29474 * X ^ 6 + 4158 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 0 1 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 2 0 1 6 1 100).erase 1 = (bag 1 0 1 6 1 100) := by rfl
  have hm3 : (bag 2 0 1 6 1 100).erase 3 = (bag 2 0 0 6 1 100) := by rfl
  have hm4 : (bag 2 0 1 6 1 100).erase 4 = (bag 2 0 1 5 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 2 0 1 6 1 100) (bag 1 0 1 6 1 100) (bag 2 0 0 6 1 100) (bag 2 0 1 5 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_425 cert_426 cert_444
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_513 : count (rows.drop 10) (bag 2 1 0 6 1 100) (some 3) =
    (6 * X ^ 2 + 735 * X ^ 3 + 11003 * X ^ 4 + 35368 * X ^ 5 + 25977 * X ^ 6 + 3267 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 1 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 2 1 0 6 1 100).erase 1 = (bag 1 1 0 6 1 100) := by rfl
  have hm2 : (bag 2 1 0 6 1 100).erase 2 = (bag 2 0 0 6 1 100) := by rfl
  have hm4 : (bag 2 1 0 6 1 100).erase 4 = (bag 2 1 0 5 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 2 1 0 6 1 100) (bag 1 1 0 6 1 100) (bag 2 0 0 6 1 100) (bag 2 1 0 5 1 100) (some 3) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_485 cert_486 cert_504
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_514 : count (rows.drop 11) (bag 1 1 1 5 1 100) (some 1) =
    (2 * X ^ 2 + 299 * X ^ 3 + 8707 * X ^ 4 + 43721 * X ^ 5 + 42545 * X ^ 6 + 6534 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 1 1 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 1 1 1 5 1 100).erase 1 = (bag 0 1 1 5 1 100) := by rfl
  have hm2 : (bag 1 1 1 5 1 100).erase 2 = (bag 1 0 1 5 1 100) := by rfl
  have hm3 : (bag 1 1 1 5 1 100).erase 3 = (bag 1 1 0 5 1 100) := by rfl
  have hm4 : (bag 1 1 1 5 1 100).erase 4 = (bag 1 1 1 4 1 100) := by rfl
  have hc := count_four (rows.drop 11) (rows.drop 12) (bag 1 1 1 5 1 100) (bag 0 1 1 5 1 100) (bag 1 0 1 5 1 100) (bag 1 1 0 5 1 100) (bag 1 1 1 4 1 100) (some 1) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_337 cert_338 cert_339 cert_359
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_515 : count (rows.drop 11) (bag 2 0 1 5 1 100) (some 2) =
    (3 * X ^ 2 + 390 * X ^ 3 + 7458 * X ^ 4 + 24960 * X ^ 5 + 16608 * X ^ 6 + 1485 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 0 1 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 2 0 1 5 1 100).erase 1 = (bag 1 0 1 5 1 100) := by rfl
  have hm3 : (bag 2 0 1 5 1 100).erase 3 = (bag 2 0 0 5 1 100) := by rfl
  have hm4 : (bag 2 0 1 5 1 100).erase 4 = (bag 2 0 1 4 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 2 0 1 5 1 100) (bag 1 0 1 5 1 100) (bag 2 0 0 5 1 100) (bag 2 0 1 4 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_427 cert_428 cert_443
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_516 : count (rows.drop 11) (bag 2 1 0 5 1 100) (some 3) =
    (6 * X ^ 2 + 723 * X ^ 3 + 9664 * X ^ 4 + 25504 * X ^ 5 + 13918 * X ^ 6 + 1089 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 1 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 2 1 0 5 1 100).erase 1 = (bag 1 1 0 5 1 100) := by rfl
  have hm2 : (bag 2 1 0 5 1 100).erase 2 = (bag 2 0 0 5 1 100) := by rfl
  have hm4 : (bag 2 1 0 5 1 100).erase 4 = (bag 2 1 0 4 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 2 1 0 5 1 100) (bag 1 1 0 5 1 100) (bag 2 0 0 5 1 100) (bag 2 1 0 4 1 100) (some 3) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_487 cert_488 cert_503
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_517 : count (rows.drop 12) (bag 1 1 1 4 1 100) (some 1) =
    (2 * X ^ 2 + 289 * X ^ 3 + 7539 * X ^ 4 + 31135 * X ^ 5 + 22487 * X ^ 6 + 2178 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 1 1 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 1 1 1 4 1 100).erase 1 = (bag 0 1 1 4 1 100) := by rfl
  have hm2 : (bag 1 1 1 4 1 100).erase 2 = (bag 1 0 1 4 1 100) := by rfl
  have hm3 : (bag 1 1 1 4 1 100).erase 3 = (bag 1 1 0 4 1 100) := by rfl
  have hm4 : (bag 1 1 1 4 1 100).erase 4 = (bag 1 1 1 3 1 100) := by rfl
  have hc := count_four (rows.drop 12) (rows.drop 13) (bag 1 1 1 4 1 100) (bag 0 1 1 4 1 100) (bag 1 0 1 4 1 100) (bag 1 1 0 4 1 100) (bag 1 1 1 3 1 100) (some 1) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_340 cert_341 cert_342 cert_358
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_518 : count (rows.drop 12) (bag 2 0 1 4 1 100) (some 2) =
    (3 * X ^ 2 + 381 * X ^ 3 + 6446 * X ^ 4 + 17040 * X ^ 5 + 7648 * X ^ 6 + 297 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 0 1 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 2 0 1 4 1 100).erase 1 = (bag 1 0 1 4 1 100) := by rfl
  have hm3 : (bag 2 0 1 4 1 100).erase 3 = (bag 2 0 0 4 1 100) := by rfl
  have hm4 : (bag 2 0 1 4 1 100).erase 4 = (bag 2 0 1 3 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 2 0 1 4 1 100) (bag 1 0 1 4 1 100) (bag 2 0 0 4 1 100) (bag 2 0 1 3 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_429 cert_430 cert_442
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_519 : count (rows.drop 12) (bag 2 1 0 4 1 100) (some 3) =
    (6 * X ^ 2 + 711 * X ^ 3 + 8335 * X ^ 4 + 16706 * X ^ 5 + 5859 * X ^ 6 + 198 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 1 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 2 1 0 4 1 100).erase 1 = (bag 1 1 0 4 1 100) := by rfl
  have hm2 : (bag 2 1 0 4 1 100).erase 2 = (bag 2 0 0 4 1 100) := by rfl
  have hm4 : (bag 2 1 0 4 1 100).erase 4 = (bag 2 1 0 3 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 2 1 0 4 1 100) (bag 1 1 0 4 1 100) (bag 2 0 0 4 1 100) (bag 2 1 0 3 1 100) (some 3) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_489 cert_490 cert_502
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_520 : count (rows.drop 13) (bag 1 1 1 3 1 100) (some 1) =
    (2 * X ^ 2 + 279 * X ^ 3 + 6385 * X ^ 4 + 20057 * X ^ 5 + 9241 * X ^ 6 + 396 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 1 1 1 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 1 1 1 3 1 100).erase 1 = (bag 0 1 1 3 1 100) := by rfl
  have hm2 : (bag 1 1 1 3 1 100).erase 2 = (bag 1 0 1 3 1 100) := by rfl
  have hm3 : (bag 1 1 1 3 1 100).erase 3 = (bag 1 1 0 3 1 100) := by rfl
  have hm4 : (bag 1 1 1 3 1 100).erase 4 = (bag 1 1 1 2 1 100) := by rfl
  have hc := count_four (rows.drop 13) (rows.drop 14) (bag 1 1 1 3 1 100) (bag 0 1 1 3 1 100) (bag 1 0 1 3 1 100) (bag 1 1 0 3 1 100) (bag 1 1 1 2 1 100) (some 1) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_343 cert_344 cert_345 cert_357
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_521 : count (rows.drop 13) (bag 2 0 1 3 1 100) (some 2) =
    (3 * X ^ 2 + 372 * X ^ 3 + 5443 * X ^ 4 + 10080 * X ^ 5 + 2282 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 1 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 2 0 1 3 1 100).erase 1 = (bag 1 0 1 3 1 100) := by rfl
  have hm3 : (bag 2 0 1 3 1 100).erase 3 = (bag 2 0 0 3 1 100) := by rfl
  have hm4 : (bag 2 0 1 3 1 100).erase 4 = (bag 2 0 1 2 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 2 0 1 3 1 100) (bag 1 0 1 3 1 100) (bag 2 0 0 3 1 100) (bag 2 0 1 2 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_431 cert_432 cert_441
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_522 : count (rows.drop 13) (bag 2 1 0 3 1 100) (some 3) =
    (6 * X ^ 2 + 699 * X ^ 3 + 7016 * X ^ 4 + 8971 * X ^ 5 + 1488 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 1 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 2 1 0 3 1 100).erase 1 = (bag 1 1 0 3 1 100) := by rfl
  have hm2 : (bag 2 1 0 3 1 100).erase 2 = (bag 2 0 0 3 1 100) := by rfl
  have hm4 : (bag 2 1 0 3 1 100).erase 4 = (bag 2 1 0 2 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 2 1 0 3 1 100) (bag 1 1 0 3 1 100) (bag 2 0 0 3 1 100) (bag 2 1 0 2 1 100) (some 3) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_491 cert_492 cert_501
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_523 : count (rows.drop 14) (bag 1 1 1 2 1 100) (some 1) =
    (2 * X ^ 2 + 269 * X ^ 3 + 5245 * X ^ 4 + 10481 * X ^ 5 + 2183 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 1 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 1 1 1 2 1 100).erase 1 = (bag 0 1 1 2 1 100) := by rfl
  have hm2 : (bag 1 1 1 2 1 100).erase 2 = (bag 1 0 1 2 1 100) := by rfl
  have hm3 : (bag 1 1 1 2 1 100).erase 3 = (bag 1 1 0 2 1 100) := by rfl
  have hm4 : (bag 1 1 1 2 1 100).erase 4 = (bag 1 1 1 1 1 100) := by rfl
  have hc := count_four (rows.drop 14) (rows.drop 15) (bag 1 1 1 2 1 100) (bag 0 1 1 2 1 100) (bag 1 0 1 2 1 100) (bag 1 1 0 2 1 100) (bag 1 1 1 1 1 100) (some 1) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_346 cert_347 cert_348 cert_356
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_524 : count (rows.drop 14) (bag 2 0 1 2 1 100) (some 2) =
    (3 * X ^ 2 + 363 * X ^ 3 + 4449 * X ^ 4 + 4077 * X ^ 5 + 198 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 1 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 2 0 1 2 1 100).erase 1 = (bag 1 0 1 2 1 100) := by rfl
  have hm3 : (bag 2 0 1 2 1 100).erase 3 = (bag 2 0 0 2 1 100) := by rfl
  have hm4 : (bag 2 0 1 2 1 100).erase 4 = (bag 2 0 1 1 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 2 0 1 2 1 100) (bag 1 0 1 2 1 100) (bag 2 0 0 2 1 100) (bag 2 0 1 1 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_433 cert_434 cert_440
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_525 : count (rows.drop 14) (bag 2 1 0 2 1 100) (some 3) =
    (8 * X ^ 2 + 778 * X ^ 3 + 5323 * X ^ 4 + 2882 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 1 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 2 1 0 2 1 100).erase 1 = (bag 1 1 0 2 1 100) := by rfl
  have hm2 : (bag 2 1 0 2 1 100).erase 2 = (bag 2 0 0 2 1 100) := by rfl
  have hm4 : (bag 2 1 0 2 1 100).erase 4 = (bag 2 1 0 1 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 2 1 0 2 1 100) (bag 1 1 0 2 1 100) (bag 2 0 0 2 1 100) (bag 2 1 0 1 1 100) (some 3) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_493 cert_494 cert_500
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_526 : count (rows.drop 15) (bag 1 1 1 1 1 100) (some 1) =
    (2 * X ^ 2 + 255 * X ^ 3 + 3933 * X ^ 4 + 2983 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 1 1 1 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 1 1 1 1 1 100).erase 1 = (bag 0 1 1 1 1 100) := by rfl
  have hm2 : (bag 1 1 1 1 1 100).erase 2 = (bag 1 0 1 1 1 100) := by rfl
  have hm3 : (bag 1 1 1 1 1 100).erase 3 = (bag 1 1 0 1 1 100) := by rfl
  have hm4 : (bag 1 1 1 1 1 100).erase 4 = (bag 1 1 1 0 1 100) := by rfl
  have hc := count_four (rows.drop 15) (rows.drop 16) (bag 1 1 1 1 1 100) (bag 0 1 1 1 1 100) (bag 1 0 1 1 1 100) (bag 1 1 0 1 1 100) (bag 1 1 1 0 1 100) (some 1) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_349 cert_350 cert_351 cert_355
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_527 : count (rows.drop 15) (bag 2 0 1 1 1 100) (some 2) =
    (6 * X ^ 2 + 538 * X ^ 3 + 2597 * X ^ 4 + 495 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 2 0 1 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 2 0 1 1 1 100).erase 1 = (bag 1 0 1 1 1 100) := by rfl
  have hm3 : (bag 2 0 1 1 1 100).erase 3 = (bag 2 0 0 1 1 100) := by rfl
  have hm4 : (bag 2 0 1 1 1 100).erase 4 = (bag 2 0 1 0 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 2 0 1 1 1 100) (bag 1 0 1 1 1 100) (bag 2 0 0 1 1 100) (bag 2 0 1 0 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_435 cert_436 cert_439
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_528 : count (rows.drop 15) (bag 2 1 0 1 1 100) (some 3) =
    (14 * X ^ 2 + 1134 * X ^ 3 + 2290 * X ^ 4 + 198 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 2 1 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 2 1 0 1 1 100).erase 1 = (bag 1 1 0 1 1 100) := by rfl
  have hm2 : (bag 2 1 0 1 1 100).erase 2 = (bag 2 0 0 1 1 100) := by rfl
  have hm4 : (bag 2 1 0 1 1 100).erase 4 = (bag 2 1 0 0 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 2 1 0 1 1 100) (bag 1 1 0 1 1 100) (bag 2 0 0 1 1 100) (bag 2 1 0 0 1 100) (some 3) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_495 cert_496 cert_499
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_529 : count (rows.drop 16) (bag 1 1 1 0 1 100) (some 1) =
    (5 * X ^ 2 + 419 * X ^ 3 + 1295 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 1 1 1 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 1 1 1 0 1 100).erase 1 = (bag 0 1 1 0 1 100) := by rfl
  have hm2 : (bag 1 1 1 0 1 100).erase 2 = (bag 1 0 1 0 1 100) := by rfl
  have hm3 : (bag 1 1 1 0 1 100).erase 3 = (bag 1 1 0 0 1 100) := by rfl
  have hc := count_three (rows.drop 16) (rows.drop 17) (bag 1 1 1 0 1 100) (bag 0 1 1 0 1 100) (bag 1 0 1 0 1 100) (bag 1 1 0 0 1 100) (some 1) 4 1 2 3 hr hs (by decide) (by decide) hm1 hm2 hm3 _ _ _ cert_352 cert_353 cert_354
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_530 : count (rows.drop 16) (bag 2 0 1 0 1 100) (some 2) =
    (8 * X ^ 2 + 604 * X ^ 3 + 297 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 2 0 1 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 2 0 1 0 1 100).erase 1 = (bag 1 0 1 0 1 100) := by rfl
  have hm3 : (bag 2 0 1 0 1 100).erase 3 = (bag 2 0 0 0 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 2 0 1 0 1 100) (bag 1 0 1 0 1 100) (bag 2 0 0 0 1 100) (some 2) 4 1 3 hr hs (by decide) hm1 hm3 _ _ cert_437 cert_438
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_531 : count (rows.drop 16) (bag 2 1 0 0 1 100) (some 3) =
    (X + 111 * X ^ 2 + 698 * X ^ 3 + 99 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 2 1 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 2 1 0 0 1 100).erase 1 = (bag 1 1 0 0 1 100) := by rfl
  have hm2 : (bag 2 1 0 0 1 100).erase 2 = (bag 2 0 0 0 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 2 1 0 0 1 100) (bag 1 1 0 0 1 100) (bag 2 0 0 0 1 100) (some 3) 4 1 2 hr hs (by decide) hm1 hm2 _ _ cert_497 cert_498
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_532 : count (rows.drop 15) (bag 2 1 1 0 1 100) (some 4) =
    (X + 124 * X ^ 2 + 1721 * X ^ 3 + 1691 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 2 1 1 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 2 1 1 0 1 100).erase 1 = (bag 1 1 1 0 1 100) := by rfl
  have hm2 : (bag 2 1 1 0 1 100).erase 2 = (bag 2 0 1 0 1 100) := by rfl
  have hm3 : (bag 2 1 1 0 1 100).erase 3 = (bag 2 1 0 0 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 2 1 1 0 1 100) (bag 1 1 1 0 1 100) (bag 2 0 1 0 1 100) (bag 2 1 0 0 1 100) (some 4) 4 1 2 3 hr hs (by decide) (by decide) hm1 hm2 hm3 _ _ _ cert_529 cert_530 cert_531
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_533 : count (rows.drop 14) (bag 2 1 1 1 1 100) (some 4) =
    (X + 146 * X ^ 2 + 3648 * X ^ 3 + 10511 * X ^ 4 + 3775 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 1 1 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 2 1 1 1 1 100).erase 1 = (bag 1 1 1 1 1 100) := by rfl
  have hm2 : (bag 2 1 1 1 1 100).erase 2 = (bag 2 0 1 1 1 100) := by rfl
  have hm3 : (bag 2 1 1 1 1 100).erase 3 = (bag 2 1 0 1 1 100) := by rfl
  have hm4 : (bag 2 1 1 1 1 100).erase 4 = (bag 2 1 1 0 1 100) := by rfl
  have hc := count_four (rows.drop 14) (rows.drop 15) (bag 2 1 1 1 1 100) (bag 1 1 1 1 1 100) (bag 2 0 1 1 1 100) (bag 2 1 0 1 1 100) (bag 2 1 1 0 1 100) (some 4) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_526 cert_527 cert_528 cert_532
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_534 : count (rows.drop 13) (bag 2 1 1 2 1 100) (some 4) =
    (X + 159 * X ^ 2 + 5058 * X ^ 3 + 25528 * X ^ 4 + 21215 * X ^ 5 + 2579 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 1 1 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 2 1 1 2 1 100).erase 1 = (bag 1 1 1 2 1 100) := by rfl
  have hm2 : (bag 2 1 1 2 1 100).erase 2 = (bag 2 0 1 2 1 100) := by rfl
  have hm3 : (bag 2 1 1 2 1 100).erase 3 = (bag 2 1 0 2 1 100) := by rfl
  have hm4 : (bag 2 1 1 2 1 100).erase 4 = (bag 2 1 1 1 1 100) := by rfl
  have hc := count_four (rows.drop 13) (rows.drop 14) (bag 2 1 1 2 1 100) (bag 1 1 1 2 1 100) (bag 2 0 1 2 1 100) (bag 2 1 0 2 1 100) (bag 2 1 1 1 1 100) (some 4) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_523 cert_524 cert_525 cert_533
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_535 : count (rows.drop 12) (bag 2 1 1 3 1 100) (some 4) =
    (X + 170 * X ^ 2 + 6408 * X ^ 3 + 44372 * X ^ 4 + 60323 * X ^ 5 + 15590 * X ^ 6 + 396 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 1 1 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 2 1 1 3 1 100).erase 1 = (bag 1 1 1 3 1 100) := by rfl
  have hm2 : (bag 2 1 1 3 1 100).erase 2 = (bag 2 0 1 3 1 100) := by rfl
  have hm3 : (bag 2 1 1 3 1 100).erase 3 = (bag 2 1 0 3 1 100) := by rfl
  have hm4 : (bag 2 1 1 3 1 100).erase 4 = (bag 2 1 1 2 1 100) := by rfl
  have hc := count_four (rows.drop 12) (rows.drop 13) (bag 2 1 1 3 1 100) (bag 1 1 1 3 1 100) (bag 2 0 1 3 1 100) (bag 2 1 0 3 1 100) (bag 2 1 1 2 1 100) (some 4) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_520 cert_521 cert_522 cert_534
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_536 : count (rows.drop 11) (bag 2 1 1 4 1 100) (some 4) =
    (X + 181 * X ^ 2 + 7789 * X ^ 3 + 66692 * X ^ 4 + 125204 * X ^ 5 + 51584 * X ^ 6 + 3069 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 1 1 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 2 1 1 4 1 100).erase 1 = (bag 1 1 1 4 1 100) := by rfl
  have hm2 : (bag 2 1 1 4 1 100).erase 2 = (bag 2 0 1 4 1 100) := by rfl
  have hm3 : (bag 2 1 1 4 1 100).erase 3 = (bag 2 1 0 4 1 100) := by rfl
  have hm4 : (bag 2 1 1 4 1 100).erase 4 = (bag 2 1 1 3 1 100) := by rfl
  have hc := count_four (rows.drop 11) (rows.drop 12) (bag 2 1 1 4 1 100) (bag 1 1 1 4 1 100) (bag 2 0 1 4 1 100) (bag 2 1 0 4 1 100) (bag 2 1 1 3 1 100) (some 4) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_517 cert_518 cert_519 cert_535
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_537 : count (rows.drop 10) (bag 2 1 1 5 1 100) (some 4) =
    (X + 192 * X ^ 2 + 9201 * X ^ 3 + 92521 * X ^ 4 + 219389 * X ^ 5 + 124655 * X ^ 6 + 12177 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 1 1 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 2 1 1 5 1 100).erase 1 = (bag 1 1 1 5 1 100) := by rfl
  have hm2 : (bag 2 1 1 5 1 100).erase 2 = (bag 2 0 1 5 1 100) := by rfl
  have hm3 : (bag 2 1 1 5 1 100).erase 3 = (bag 2 1 0 5 1 100) := by rfl
  have hm4 : (bag 2 1 1 5 1 100).erase 4 = (bag 2 1 1 4 1 100) := by rfl
  have hc := count_four (rows.drop 10) (rows.drop 11) (bag 2 1 1 5 1 100) (bag 1 1 1 5 1 100) (bag 2 0 1 5 1 100) (bag 2 1 0 5 1 100) (bag 2 1 1 4 1 100) (some 4) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_514 cert_515 cert_516 cert_536
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_538 : count (rows.drop 9) (bag 2 1 1 6 1 100) (some 4) =
    (X + 203 * X ^ 2 + 10644 * X ^ 3 + 121892 * X ^ 4 + 346421 * X ^ 5 + 250145 * X ^ 6 + 34254 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 1 1 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 2 1 1 6 1 100).erase 1 = (bag 1 1 1 6 1 100) := by rfl
  have hm2 : (bag 2 1 1 6 1 100).erase 2 = (bag 2 0 1 6 1 100) := by rfl
  have hm3 : (bag 2 1 1 6 1 100).erase 3 = (bag 2 1 0 6 1 100) := by rfl
  have hm4 : (bag 2 1 1 6 1 100).erase 4 = (bag 2 1 1 5 1 100) := by rfl
  have hc := count_four (rows.drop 9) (rows.drop 10) (bag 2 1 1 6 1 100) (bag 1 1 1 6 1 100) (bag 2 0 1 6 1 100) (bag 2 1 0 6 1 100) (bag 2 1 1 5 1 100) (some 4) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_511 cert_512 cert_513 cert_537
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_539 : count (rows.drop 8) (bag 2 1 1 7 1 100) (some 4) =
    (X + 214 * X ^ 2 + 12118 * X ^ 3 + 154838 * X ^ 4 + 509855 * X ^ 5 + 444644 * X ^ 6 + 78210 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 1 1 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm1 : (bag 2 1 1 7 1 100).erase 1 = (bag 1 1 1 7 1 100) := by rfl
  have hm2 : (bag 2 1 1 7 1 100).erase 2 = (bag 2 0 1 7 1 100) := by rfl
  have hm3 : (bag 2 1 1 7 1 100).erase 3 = (bag 2 1 0 7 1 100) := by rfl
  have hm4 : (bag 2 1 1 7 1 100).erase 4 = (bag 2 1 1 6 1 100) := by rfl
  have hc := count_four (rows.drop 8) (rows.drop 9) (bag 2 1 1 7 1 100) (bag 1 1 1 7 1 100) (bag 2 0 1 7 1 100) (bag 2 1 0 7 1 100) (bag 2 1 1 6 1 100) (some 4) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_508 cert_509 cert_510 cert_538
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_540 : count (rows.drop 7) (bag 2 1 1 8 1 100) (some 3) =
    (12 * X ^ 2 + 1719 * X ^ 3 + 48672 * X ^ 4 + 358241 * X ^ 5 + 791201 * X ^ 6 + 521765 * X ^ 7 + 78210 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 2 1 1 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 7 = 4 :: rows.drop 8 := by rfl
  have hm1 : (bag 2 1 1 8 1 100).erase 1 = (bag 1 1 1 8 1 100) := by rfl
  have hm2 : (bag 2 1 1 8 1 100).erase 2 = (bag 2 0 1 8 1 100) := by rfl
  have hm3 : (bag 2 1 1 8 1 100).erase 3 = (bag 2 1 0 8 1 100) := by rfl
  have hm4 : (bag 2 1 1 8 1 100).erase 4 = (bag 2 1 1 7 1 100) := by rfl
  have hc := count_four (rows.drop 7) (rows.drop 8) (bag 2 1 1 8 1 100) (bag 1 1 1 8 1 100) (bag 2 0 1 8 1 100) (bag 2 1 0 8 1 100) (bag 2 1 1 7 1 100) (some 3) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_479 cert_480 cert_507 cert_539
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_541 : count (rows.drop 6) (bag 2 1 2 8 1 100) (some 3) =
    (17 * X ^ 2 + 2578 * X ^ 3 + 85197 * X ^ 4 + 742166 * X ^ 5 + 1930113 * X ^ 6 + 1483366 * X ^ 7 + 256113 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 2 1 2 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 6 = 3 :: rows.drop 7 := by rfl
  have hm1 : (bag 2 1 2 8 1 100).erase 1 = (bag 1 1 2 8 1 100) := by rfl
  have hm2 : (bag 2 1 2 8 1 100).erase 2 = (bag 2 0 2 8 1 100) := by rfl
  have hm3 : (bag 2 1 2 8 1 100).erase 3 = (bag 2 1 1 8 1 100) := by rfl
  have hc := count_three (rows.drop 6) (rows.drop 7) (bag 2 1 2 8 1 100) (bag 1 1 2 8 1 100) (bag 2 0 2 8 1 100) (bag 2 1 1 8 1 100) (some 3) 3 1 2 3 hr hs (by decide) (by decide) hm1 hm2 hm3 _ _ _ cert_477 cert_478 cert_540
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_542 : count (rows.drop 5) (bag 2 1 3 8 1 100) (some 3) =
    (20 * X ^ 2 + 3091 * X ^ 3 + 107731 * X ^ 4 + 1019490 * X ^ 5 + 3107060 * X ^ 6 + 3342836 * X ^ 7 + 1277797 * X ^ 8 + 141075 * X ^ 9 : ℕ[X]) := by
  have hs : (bag 2 1 3 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 5 = 3 :: rows.drop 6 := by rfl
  have hm1 : (bag 2 1 3 8 1 100).erase 1 = (bag 1 1 3 8 1 100) := by rfl
  have hm2 : (bag 2 1 3 8 1 100).erase 2 = (bag 2 0 3 8 1 100) := by rfl
  have hm3 : (bag 2 1 3 8 1 100).erase 3 = (bag 2 1 2 8 1 100) := by rfl
  have hc := count_three (rows.drop 5) (rows.drop 6) (bag 2 1 3 8 1 100) (bag 1 1 3 8 1 100) (bag 2 0 3 8 1 100) (bag 2 1 2 8 1 100) (some 3) 3 1 2 3 hr hs (by decide) (by decide) hm1 hm2 hm3 _ _ _ cert_475 cert_476 cert_541
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_543 : count (rows.drop 4) (bag 2 1 4 8 1 100) (some 1) =
    (46 * X ^ 3 + 6821 * X ^ 4 + 216124 * X ^ 5 + 1893687 * X ^ 6 + 5479872 * X ^ 7 + 5736793 * X ^ 8 + 2177482 * X ^ 9 + 237600 * X ^ 10 : ℕ[X]) := by
  have hs : (bag 2 1 4 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 4 = 3 :: rows.drop 5 := by rfl
  have hm1 : (bag 2 1 4 8 1 100).erase 1 = (bag 1 1 4 8 1 100) := by rfl
  have hm2 : (bag 2 1 4 8 1 100).erase 2 = (bag 2 0 4 8 1 100) := by rfl
  have hm3 : (bag 2 1 4 8 1 100).erase 3 = (bag 2 1 3 8 1 100) := by rfl
  have hc := count_three (rows.drop 4) (rows.drop 5) (bag 2 1 4 8 1 100) (bag 1 1 4 8 1 100) (bag 2 0 4 8 1 100) (bag 2 1 3 8 1 100) (some 1) 3 1 2 3 hr hs (by decide) (by decide) hm1 hm2 hm3 _ _ _ cert_398 cert_474 cert_542
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_544 : count (rows.drop 5) (bag 2 0 4 8 1 100) (some 1) =
    (X ^ 2 + 162 * X ^ 3 + 6814 * X ^ 4 + 96623 * X ^ 5 + 513181 * X ^ 6 + 970317 * X ^ 7 + 582982 * X ^ 8 + 79695 * X ^ 9 : ℕ[X]) := by
  have hs : (bag 2 0 4 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 5 = 3 :: rows.drop 6 := by rfl
  have hm1 : (bag 2 0 4 8 1 100).erase 1 = (bag 1 0 4 8 1 100) := by rfl
  have hm3 : (bag 2 0 4 8 1 100).erase 3 = (bag 2 0 3 8 1 100) := by rfl
  have hc := count_two (rows.drop 5) (rows.drop 6) (bag 2 0 4 8 1 100) (bag 1 0 4 8 1 100) (bag 2 0 3 8 1 100) (some 1) 3 1 3 hr hs (by decide) hm1 hm3 _ _ cert_399 cert_473
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_545 : count (rows.drop 6) (bag 2 0 3 8 1 100) (some 1) =
    (2 * X ^ 2 + 321 * X ^ 3 + 12421 * X ^ 4 + 131076 * X ^ 5 + 460924 * X ^ 6 + 593568 * X ^ 7 + 269363 * X ^ 8 + 32175 * X ^ 9 : ℕ[X]) := by
  have hs : (bag 2 0 3 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 6 = 3 :: rows.drop 7 := by rfl
  have hm1 : (bag 2 0 3 8 1 100).erase 1 = (bag 1 0 3 8 1 100) := by rfl
  have hm3 : (bag 2 0 3 8 1 100).erase 3 = (bag 2 0 2 8 1 100) := by rfl
  have hc := count_two (rows.drop 6) (rows.drop 7) (bag 2 0 3 8 1 100) (bag 1 0 3 8 1 100) (bag 2 0 2 8 1 100) (some 1) 3 1 3 hr hs (by decide) hm1 hm3 _ _ cert_400 cert_472
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_546 : count (rows.drop 7) (bag 2 0 2 8 1 100) (some 1) =
    (3 * X ^ 2 + 474 * X ^ 3 + 17175 * X ^ 4 + 153957 * X ^ 5 + 394110 * X ^ 6 + 288156 * X ^ 7 + 46035 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 2 0 2 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 7 = 4 :: rows.drop 8 := by rfl
  have hm1 : (bag 2 0 2 8 1 100).erase 1 = (bag 1 0 2 8 1 100) := by rfl
  have hm3 : (bag 2 0 2 8 1 100).erase 3 = (bag 2 0 1 8 1 100) := by rfl
  have hm4 : (bag 2 0 2 8 1 100).erase 4 = (bag 2 0 2 7 1 100) := by rfl
  have hc := count_three (rows.drop 7) (rows.drop 8) (bag 2 0 2 8 1 100) (bag 1 0 2 8 1 100) (bag 2 0 1 8 1 100) (bag 2 0 2 7 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_401 cert_447 cert_471
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_547 : count (rows.drop 8) (bag 2 0 1 8 1 100) (some 1) =
    (3 * X ^ 2 + 417 * X ^ 3 + 10548 * X ^ 4 + 54510 * X ^ 5 + 68172 * X ^ 6 + 16335 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 0 1 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm1 : (bag 2 0 1 8 1 100).erase 1 = (bag 1 0 1 8 1 100) := by rfl
  have hm3 : (bag 2 0 1 8 1 100).erase 3 = (bag 2 0 0 8 1 100) := by rfl
  have hm4 : (bag 2 0 1 8 1 100).erase 4 = (bag 2 0 1 7 1 100) := by rfl
  have hc := count_three (rows.drop 8) (rows.drop 9) (bag 2 0 1 8 1 100) (bag 1 0 1 8 1 100) (bag 2 0 0 8 1 100) (bag 2 0 1 7 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_402 cert_422 cert_446
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_548 : count (rows.drop 9) (bag 2 0 0 8 1 100) (some 1) =
    (3 * X ^ 2 + 345 * X ^ 3 + 3508 * X ^ 4 + 7304 * X ^ 5 + 2475 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 0 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 2 0 0 8 1 100).erase 1 = (bag 1 0 0 8 1 100) := by rfl
  have hm4 : (bag 2 0 0 8 1 100).erase 4 = (bag 2 0 0 7 1 100) := by rfl
  have hc := count_two (rows.drop 9) (rows.drop 10) (bag 2 0 0 8 1 100) (bag 1 0 0 8 1 100) (bag 2 0 0 7 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_403 cert_421
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_549 : count (rows.drop 10) (bag 2 0 0 7 1 100) (some 1) =
    (3 * X ^ 2 + 342 * X ^ 3 + 3185 * X ^ 4 + 5794 * X ^ 5 + 1584 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 2 0 0 7 1 100).erase 1 = (bag 1 0 0 7 1 100) := by rfl
  have hm4 : (bag 2 0 0 7 1 100).erase 4 = (bag 2 0 0 6 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 2 0 0 7 1 100) (bag 1 0 0 7 1 100) (bag 2 0 0 6 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_404 cert_420
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_550 : count (rows.drop 11) (bag 2 0 0 6 1 100) (some 1) =
    (3 * X ^ 2 + 339 * X ^ 3 + 2863 * X ^ 4 + 4388 * X ^ 5 + 891 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 2 0 0 6 1 100).erase 1 = (bag 1 0 0 6 1 100) := by rfl
  have hm4 : (bag 2 0 0 6 1 100).erase 4 = (bag 2 0 0 5 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 2 0 0 6 1 100) (bag 1 0 0 6 1 100) (bag 2 0 0 5 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_405 cert_419
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_551 : count (rows.drop 12) (bag 2 0 0 5 1 100) (some 1) =
    (3 * X ^ 2 + 336 * X ^ 3 + 2542 * X ^ 4 + 3086 * X ^ 5 + 396 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 2 0 0 5 1 100).erase 1 = (bag 1 0 0 5 1 100) := by rfl
  have hm4 : (bag 2 0 0 5 1 100).erase 4 = (bag 2 0 0 4 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 2 0 0 5 1 100) (bag 1 0 0 5 1 100) (bag 2 0 0 4 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_406 cert_418
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_552 : count (rows.drop 13) (bag 2 0 0 4 1 100) (some 1) =
    (3 * X ^ 2 + 333 * X ^ 3 + 2222 * X ^ 4 + 1888 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 2 0 0 4 1 100).erase 1 = (bag 1 0 0 4 1 100) := by rfl
  have hm4 : (bag 2 0 0 4 1 100).erase 4 = (bag 2 0 0 3 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 2 0 0 4 1 100) (bag 1 0 0 4 1 100) (bag 2 0 0 3 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_407 cert_417
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_553 : count (rows.drop 14) (bag 2 0 0 3 1 100) (some 1) =
    (3 * X ^ 2 + 330 * X ^ 3 + 1903 * X ^ 4 + 794 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 2 0 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 2 0 0 3 1 100).erase 1 = (bag 1 0 0 3 1 100) := by rfl
  have hm4 : (bag 2 0 0 3 1 100).erase 4 = (bag 2 0 0 2 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 2 0 0 3 1 100) (bag 1 0 0 3 1 100) (bag 2 0 0 2 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_408 cert_416
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_554 : count (rows.drop 15) (bag 2 0 0 2 1 100) (some 1) =
    (5 * X ^ 2 + 420 * X ^ 3 + 1294 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 2 0 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 2 0 0 2 1 100).erase 1 = (bag 1 0 0 2 1 100) := by rfl
  have hm4 : (bag 2 0 0 2 1 100).erase 4 = (bag 2 0 0 1 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 2 0 0 2 1 100) (bag 1 0 0 2 1 100) (bag 2 0 0 1 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_409 cert_415
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_555 : count (rows.drop 16) (bag 2 0 0 1 1 100) (some 1) =
    (8 * X ^ 2 + 604 * X ^ 3 + 297 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 2 0 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 2 0 0 1 1 100).erase 1 = (bag 1 0 0 1 1 100) := by rfl
  have hm4 : (bag 2 0 0 1 1 100).erase 4 = (bag 2 0 0 0 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 2 0 0 1 1 100) (bag 1 0 0 1 1 100) (bag 2 0 0 0 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_410 cert_414
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_556 : count (rows.drop 17) (bag 2 0 0 0 1 100) (some 1) =
    (X + 104 * X ^ 2 + 198 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 2 0 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 5) = {1, 5} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 17 = 5 :: rows.drop 18 := by rfl
  have hm1 : (bag 2 0 0 0 1 100).erase 1 = (bag 1 0 0 0 1 100) := by rfl
  have hm5 : (bag 2 0 0 0 1 100).erase 5 = (bag 2 0 0 0 0 100) := by rfl
  have hc := count_two (rows.drop 17) (rows.drop 18) (bag 2 0 0 0 1 100) (bag 1 0 0 0 1 100) (bag 2 0 0 0 0 100) (some 1) 5 1 5 hr hs (by decide) hm1 hm5 _ _ cert_411 cert_413
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_557 : count (rows.drop 16) (bag 3 0 0 0 1 100) (some 4) =
    (X + 104 * X ^ 2 + 198 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 3 0 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 3 0 0 0 1 100).erase 1 = (bag 2 0 0 0 1 100) := by rfl
  have hc := count_one (rows.drop 16) (rows.drop 17) (bag 3 0 0 0 1 100) (bag 2 0 0 0 1 100) (some 4) 4 1 hr hs hm1 _ cert_556
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_558 : count (rows.drop 15) (bag 3 0 0 1 1 100) (some 4) =
    (X + 112 * X ^ 2 + 802 * X ^ 3 + 297 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 3 0 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 3 0 0 1 1 100).erase 1 = (bag 2 0 0 1 1 100) := by rfl
  have hm4 : (bag 3 0 0 1 1 100).erase 4 = (bag 3 0 0 0 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 3 0 0 1 1 100) (bag 2 0 0 1 1 100) (bag 3 0 0 0 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_555 cert_557
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_559 : count (rows.drop 14) (bag 3 0 0 2 1 100) (some 4) =
    (X + 117 * X ^ 2 + 1222 * X ^ 3 + 1591 * X ^ 4 + 99 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 3 0 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 3 0 0 2 1 100).erase 1 = (bag 2 0 0 2 1 100) := by rfl
  have hm4 : (bag 3 0 0 2 1 100).erase 4 = (bag 3 0 0 1 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 3 0 0 2 1 100) (bag 2 0 0 2 1 100) (bag 3 0 0 1 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_554 cert_558
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_560 : count (rows.drop 13) (bag 3 0 0 3 1 100) (some 4) =
    (X + 120 * X ^ 2 + 1552 * X ^ 3 + 3494 * X ^ 4 + 893 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 3 0 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 3 0 0 3 1 100).erase 1 = (bag 2 0 0 3 1 100) := by rfl
  have hm4 : (bag 3 0 0 3 1 100).erase 4 = (bag 3 0 0 2 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 3 0 0 3 1 100) (bag 2 0 0 3 1 100) (bag 3 0 0 2 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_553 cert_559
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_561 : count (rows.drop 12) (bag 3 0 0 4 1 100) (some 4) =
    (X + 123 * X ^ 2 + 1885 * X ^ 3 + 5716 * X ^ 4 + 2781 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 3 0 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 3 0 0 4 1 100).erase 1 = (bag 2 0 0 4 1 100) := by rfl
  have hm4 : (bag 3 0 0 4 1 100).erase 4 = (bag 3 0 0 3 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 3 0 0 4 1 100) (bag 2 0 0 4 1 100) (bag 3 0 0 3 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_552 cert_560
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_562 : count (rows.drop 11) (bag 3 0 0 5 1 100) (some 4) =
    (X + 126 * X ^ 2 + 2221 * X ^ 3 + 8258 * X ^ 4 + 5867 * X ^ 5 + 495 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 3 0 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 3 0 0 5 1 100).erase 1 = (bag 2 0 0 5 1 100) := by rfl
  have hm4 : (bag 3 0 0 5 1 100).erase 4 = (bag 3 0 0 4 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 3 0 0 5 1 100) (bag 2 0 0 5 1 100) (bag 3 0 0 4 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_551 cert_561
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_563 : count (rows.drop 10) (bag 3 0 0 6 1 100) (some 4) =
    (X + 129 * X ^ 2 + 2560 * X ^ 3 + 11121 * X ^ 4 + 10255 * X ^ 5 + 1386 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 3 0 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 3 0 0 6 1 100).erase 1 = (bag 2 0 0 6 1 100) := by rfl
  have hm4 : (bag 3 0 0 6 1 100).erase 4 = (bag 3 0 0 5 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 3 0 0 6 1 100) (bag 2 0 0 6 1 100) (bag 3 0 0 5 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_550 cert_562
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_564 : count (rows.drop 9) (bag 3 0 0 7 1 100) (some 4) =
    (X + 132 * X ^ 2 + 2902 * X ^ 3 + 14306 * X ^ 4 + 16049 * X ^ 5 + 2970 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 3 0 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 3 0 0 7 1 100).erase 1 = (bag 2 0 0 7 1 100) := by rfl
  have hm4 : (bag 3 0 0 7 1 100).erase 4 = (bag 3 0 0 6 1 100) := by rfl
  have hc := count_two (rows.drop 9) (rows.drop 10) (bag 3 0 0 7 1 100) (bag 2 0 0 7 1 100) (bag 3 0 0 6 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_549 cert_563
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_565 : count (rows.drop 8) (bag 3 0 0 8 1 100) (some 3) =
    (4 * X ^ 2 + 477 * X ^ 3 + 6410 * X ^ 4 + 21610 * X ^ 5 + 18524 * X ^ 6 + 2970 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 3 0 0 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm1 : (bag 3 0 0 8 1 100).erase 1 = (bag 2 0 0 8 1 100) := by rfl
  have hm4 : (bag 3 0 0 8 1 100).erase 4 = (bag 3 0 0 7 1 100) := by rfl
  have hc := count_two (rows.drop 8) (rows.drop 9) (bag 3 0 0 8 1 100) (bag 2 0 0 8 1 100) (bag 3 0 0 7 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_548 cert_564
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_566 : count (rows.drop 9) (bag 2 0 1 7 1 100) (some 1) =
    (3 * X ^ 2 + 408 * X ^ 3 + 9509 * X ^ 4 + 43692 * X ^ 5 + 46558 * X ^ 6 + 8910 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 0 1 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 2 0 1 7 1 100).erase 1 = (bag 1 0 1 7 1 100) := by rfl
  have hm3 : (bag 2 0 1 7 1 100).erase 3 = (bag 2 0 0 7 1 100) := by rfl
  have hm4 : (bag 2 0 1 7 1 100).erase 4 = (bag 2 0 1 6 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 2 0 1 7 1 100) (bag 1 0 1 7 1 100) (bag 2 0 0 7 1 100) (bag 2 0 1 6 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_423 cert_424 cert_445
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_567 : count (rows.drop 9) (bag 3 0 0 7 1 100) (some 3) =
    (4 * X ^ 2 + 471 * X ^ 3 + 5745 * X ^ 4 + 16915 * X ^ 5 + 11839 * X ^ 6 + 1386 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 3 0 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 3 0 0 7 1 100).erase 1 = (bag 2 0 0 7 1 100) := by rfl
  have hm4 : (bag 3 0 0 7 1 100).erase 4 = (bag 3 0 0 6 1 100) := by rfl
  have hc := count_two (rows.drop 9) (rows.drop 10) (bag 3 0 0 7 1 100) (bag 2 0 0 7 1 100) (bag 3 0 0 6 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_549 cert_563
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_568 : count (rows.drop 10) (bag 2 0 1 6 1 100) (some 1) =
    (3 * X ^ 2 + 399 * X ^ 3 + 8479 * X ^ 4 + 33843 * X ^ 5 + 29474 * X ^ 6 + 4158 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 0 1 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 2 0 1 6 1 100).erase 1 = (bag 1 0 1 6 1 100) := by rfl
  have hm3 : (bag 2 0 1 6 1 100).erase 3 = (bag 2 0 0 6 1 100) := by rfl
  have hm4 : (bag 2 0 1 6 1 100).erase 4 = (bag 2 0 1 5 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 2 0 1 6 1 100) (bag 1 0 1 6 1 100) (bag 2 0 0 6 1 100) (bag 2 0 1 5 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_425 cert_426 cert_444
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_569 : count (rows.drop 10) (bag 3 0 0 6 1 100) (some 3) =
    (4 * X ^ 2 + 465 * X ^ 3 + 5084 * X ^ 4 + 12646 * X ^ 5 + 6758 * X ^ 6 + 495 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 3 0 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 3 0 0 6 1 100).erase 1 = (bag 2 0 0 6 1 100) := by rfl
  have hm4 : (bag 3 0 0 6 1 100).erase 4 = (bag 3 0 0 5 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 3 0 0 6 1 100) (bag 2 0 0 6 1 100) (bag 3 0 0 5 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_550 cert_562
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_570 : count (rows.drop 11) (bag 2 0 1 5 1 100) (some 1) =
    (3 * X ^ 2 + 390 * X ^ 3 + 7458 * X ^ 4 + 24960 * X ^ 5 + 16608 * X ^ 6 + 1485 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 0 1 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 2 0 1 5 1 100).erase 1 = (bag 1 0 1 5 1 100) := by rfl
  have hm3 : (bag 2 0 1 5 1 100).erase 3 = (bag 2 0 0 5 1 100) := by rfl
  have hm4 : (bag 2 0 1 5 1 100).erase 4 = (bag 2 0 1 4 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 2 0 1 5 1 100) (bag 1 0 1 5 1 100) (bag 2 0 0 5 1 100) (bag 2 0 1 4 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_427 cert_428 cert_443
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_571 : count (rows.drop 11) (bag 3 0 0 5 1 100) (some 3) =
    (4 * X ^ 2 + 459 * X ^ 3 + 4427 * X ^ 4 + 8802 * X ^ 5 + 3177 * X ^ 6 + 99 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 3 0 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 3 0 0 5 1 100).erase 1 = (bag 2 0 0 5 1 100) := by rfl
  have hm4 : (bag 3 0 0 5 1 100).erase 4 = (bag 3 0 0 4 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 3 0 0 5 1 100) (bag 2 0 0 5 1 100) (bag 3 0 0 4 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_551 cert_561
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_572 : count (rows.drop 12) (bag 2 0 1 4 1 100) (some 1) =
    (3 * X ^ 2 + 381 * X ^ 3 + 6446 * X ^ 4 + 17040 * X ^ 5 + 7648 * X ^ 6 + 297 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 0 1 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 2 0 1 4 1 100).erase 1 = (bag 1 0 1 4 1 100) := by rfl
  have hm3 : (bag 2 0 1 4 1 100).erase 3 = (bag 2 0 0 4 1 100) := by rfl
  have hm4 : (bag 2 0 1 4 1 100).erase 4 = (bag 2 0 1 3 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 2 0 1 4 1 100) (bag 1 0 1 4 1 100) (bag 2 0 0 4 1 100) (bag 2 0 1 3 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_429 cert_430 cert_442
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_573 : count (rows.drop 12) (bag 3 0 0 4 1 100) (some 3) =
    (4 * X ^ 2 + 453 * X ^ 3 + 3774 * X ^ 4 + 5382 * X ^ 5 + 992 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 3 0 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 3 0 0 4 1 100).erase 1 = (bag 2 0 0 4 1 100) := by rfl
  have hm4 : (bag 3 0 0 4 1 100).erase 4 = (bag 3 0 0 3 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 3 0 0 4 1 100) (bag 2 0 0 4 1 100) (bag 3 0 0 3 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_552 cert_560
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_574 : count (rows.drop 13) (bag 2 0 1 3 1 100) (some 1) =
    (3 * X ^ 2 + 372 * X ^ 3 + 5443 * X ^ 4 + 10080 * X ^ 5 + 2282 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 1 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 2 0 1 3 1 100).erase 1 = (bag 1 0 1 3 1 100) := by rfl
  have hm3 : (bag 2 0 1 3 1 100).erase 3 = (bag 2 0 0 3 1 100) := by rfl
  have hm4 : (bag 2 0 1 3 1 100).erase 4 = (bag 2 0 1 2 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 2 0 1 3 1 100) (bag 1 0 1 3 1 100) (bag 2 0 0 3 1 100) (bag 2 0 1 2 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_431 cert_432 cert_441
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_575 : count (rows.drop 13) (bag 3 0 0 3 1 100) (some 3) =
    (4 * X ^ 2 + 447 * X ^ 3 + 3125 * X ^ 4 + 2385 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 3 0 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 3 0 0 3 1 100).erase 1 = (bag 2 0 0 3 1 100) := by rfl
  have hm4 : (bag 3 0 0 3 1 100).erase 4 = (bag 3 0 0 2 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 3 0 0 3 1 100) (bag 2 0 0 3 1 100) (bag 3 0 0 2 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_553 cert_559
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_576 : count (rows.drop 14) (bag 2 0 1 2 1 100) (some 1) =
    (3 * X ^ 2 + 363 * X ^ 3 + 4449 * X ^ 4 + 4077 * X ^ 5 + 198 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 0 1 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 2 0 1 2 1 100).erase 1 = (bag 1 0 1 2 1 100) := by rfl
  have hm3 : (bag 2 0 1 2 1 100).erase 3 = (bag 2 0 0 2 1 100) := by rfl
  have hm4 : (bag 2 0 1 2 1 100).erase 4 = (bag 2 0 1 1 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 2 0 1 2 1 100) (bag 1 0 1 2 1 100) (bag 2 0 0 2 1 100) (bag 2 0 1 1 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_433 cert_434 cert_440
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_577 : count (rows.drop 14) (bag 3 0 0 2 1 100) (some 3) =
    (6 * X ^ 2 + 532 * X ^ 3 + 2096 * X ^ 4 + 396 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 3 0 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 3 0 0 2 1 100).erase 1 = (bag 2 0 0 2 1 100) := by rfl
  have hm4 : (bag 3 0 0 2 1 100).erase 4 = (bag 3 0 0 1 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 3 0 0 2 1 100) (bag 2 0 0 2 1 100) (bag 3 0 0 1 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_554 cert_558
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_578 : count (rows.drop 15) (bag 2 0 1 1 1 100) (some 1) =
    (6 * X ^ 2 + 538 * X ^ 3 + 2597 * X ^ 4 + 495 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 2 0 1 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 2 0 1 1 1 100).erase 1 = (bag 1 0 1 1 1 100) := by rfl
  have hm3 : (bag 2 0 1 1 1 100).erase 3 = (bag 2 0 0 1 1 100) := by rfl
  have hm4 : (bag 2 0 1 1 1 100).erase 4 = (bag 2 0 1 0 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 2 0 1 1 1 100) (bag 1 0 1 1 1 100) (bag 2 0 0 1 1 100) (bag 2 0 1 0 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_435 cert_436 cert_439
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_579 : count (rows.drop 15) (bag 3 0 0 1 1 100) (some 3) =
    (9 * X ^ 2 + 708 * X ^ 3 + 495 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 3 0 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 3 0 0 1 1 100).erase 1 = (bag 2 0 0 1 1 100) := by rfl
  have hm4 : (bag 3 0 0 1 1 100).erase 4 = (bag 3 0 0 0 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 3 0 0 1 1 100) (bag 2 0 0 1 1 100) (bag 3 0 0 0 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_555 cert_557
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_580 : count (rows.drop 16) (bag 2 0 1 0 1 100) (some 1) =
    (8 * X ^ 2 + 604 * X ^ 3 + 297 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 2 0 1 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 2 0 1 0 1 100).erase 1 = (bag 1 0 1 0 1 100) := by rfl
  have hm3 : (bag 2 0 1 0 1 100).erase 3 = (bag 2 0 0 0 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 2 0 1 0 1 100) (bag 1 0 1 0 1 100) (bag 2 0 0 0 1 100) (some 1) 4 1 3 hr hs (by decide) hm1 hm3 _ _ cert_437 cert_438
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_581 : count (rows.drop 16) (bag 3 0 0 0 1 100) (some 3) =
    (X + 104 * X ^ 2 + 198 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 3 0 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 3 0 0 0 1 100).erase 1 = (bag 2 0 0 0 1 100) := by rfl
  have hc := count_one (rows.drop 16) (rows.drop 17) (bag 3 0 0 0 1 100) (bag 2 0 0 0 1 100) (some 3) 4 1 hr hs hm1 _ cert_556
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_582 : count (rows.drop 15) (bag 3 0 1 0 1 100) (some 4) =
    (X + 112 * X ^ 2 + 802 * X ^ 3 + 297 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 3 0 1 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 3 0 1 0 1 100).erase 1 = (bag 2 0 1 0 1 100) := by rfl
  have hm3 : (bag 3 0 1 0 1 100).erase 3 = (bag 3 0 0 0 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 3 0 1 0 1 100) (bag 2 0 1 0 1 100) (bag 3 0 0 0 1 100) (some 4) 4 1 3 hr hs (by decide) hm1 hm3 _ _ cert_580 cert_581
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_583 : count (rows.drop 14) (bag 3 0 1 1 1 100) (some 4) =
    (X + 127 * X ^ 2 + 2048 * X ^ 3 + 3389 * X ^ 4 + 495 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 3 0 1 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 3 0 1 1 1 100).erase 1 = (bag 2 0 1 1 1 100) := by rfl
  have hm3 : (bag 3 0 1 1 1 100).erase 3 = (bag 3 0 0 1 1 100) := by rfl
  have hm4 : (bag 3 0 1 1 1 100).erase 4 = (bag 3 0 1 0 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 3 0 1 1 1 100) (bag 2 0 1 1 1 100) (bag 3 0 0 1 1 100) (bag 3 0 1 0 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_578 cert_579 cert_582
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_584 : count (rows.drop 13) (bag 3 0 1 2 1 100) (some 4) =
    (X + 136 * X ^ 2 + 2943 * X ^ 3 + 9934 * X ^ 4 + 4968 * X ^ 5 + 198 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 3 0 1 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 3 0 1 2 1 100).erase 1 = (bag 2 0 1 2 1 100) := by rfl
  have hm3 : (bag 3 0 1 2 1 100).erase 3 = (bag 3 0 0 2 1 100) := by rfl
  have hm4 : (bag 3 0 1 2 1 100).erase 4 = (bag 3 0 1 1 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 3 0 1 2 1 100) (bag 2 0 1 2 1 100) (bag 3 0 0 2 1 100) (bag 3 0 1 1 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_576 cert_577 cert_583
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_585 : count (rows.drop 12) (bag 3 0 1 3 1 100) (some 4) =
    (X + 143 * X ^ 2 + 3762 * X ^ 3 + 18502 * X ^ 4 + 17433 * X ^ 5 + 2579 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 3 0 1 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 3 0 1 3 1 100).erase 1 = (bag 2 0 1 3 1 100) := by rfl
  have hm3 : (bag 3 0 1 3 1 100).erase 3 = (bag 3 0 0 3 1 100) := by rfl
  have hm4 : (bag 3 0 1 3 1 100).erase 4 = (bag 3 0 1 2 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 3 0 1 3 1 100) (bag 2 0 1 3 1 100) (bag 3 0 0 3 1 100) (bag 3 0 1 2 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_574 cert_575 cert_584
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_586 : count (rows.drop 11) (bag 3 0 1 4 1 100) (some 4) =
    (X + 150 * X ^ 2 + 4596 * X ^ 3 + 28722 * X ^ 4 + 39855 * X ^ 5 + 11219 * X ^ 6 + 297 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 3 0 1 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 3 0 1 4 1 100).erase 1 = (bag 2 0 1 4 1 100) := by rfl
  have hm3 : (bag 3 0 1 4 1 100).erase 3 = (bag 3 0 0 4 1 100) := by rfl
  have hm4 : (bag 3 0 1 4 1 100).erase 4 = (bag 3 0 1 3 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 3 0 1 4 1 100) (bag 2 0 1 4 1 100) (bag 3 0 0 4 1 100) (bag 3 0 1 3 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_572 cert_573 cert_585
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_587 : count (rows.drop 10) (bag 3 0 1 5 1 100) (some 4) =
    (X + 157 * X ^ 2 + 5445 * X ^ 3 + 40607 * X ^ 4 + 73617 * X ^ 5 + 31004 * X ^ 6 + 1881 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 3 0 1 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 3 0 1 5 1 100).erase 1 = (bag 2 0 1 5 1 100) := by rfl
  have hm3 : (bag 3 0 1 5 1 100).erase 3 = (bag 3 0 0 5 1 100) := by rfl
  have hm4 : (bag 3 0 1 5 1 100).erase 4 = (bag 3 0 1 4 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 3 0 1 5 1 100) (bag 2 0 1 5 1 100) (bag 3 0 0 5 1 100) (bag 3 0 1 4 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_570 cert_571 cert_586
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_588 : count (rows.drop 9) (bag 3 0 1 6 1 100) (some 4) =
    (X + 164 * X ^ 2 + 6309 * X ^ 3 + 54170 * X ^ 4 + 120106 * X ^ 5 + 67236 * X ^ 6 + 6534 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 3 0 1 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 3 0 1 6 1 100).erase 1 = (bag 2 0 1 6 1 100) := by rfl
  have hm3 : (bag 3 0 1 6 1 100).erase 3 = (bag 3 0 0 6 1 100) := by rfl
  have hm4 : (bag 3 0 1 6 1 100).erase 4 = (bag 3 0 1 5 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 3 0 1 6 1 100) (bag 2 0 1 6 1 100) (bag 3 0 0 6 1 100) (bag 3 0 1 5 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_568 cert_569 cert_587
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_589 : count (rows.drop 8) (bag 3 0 1 7 1 100) (some 4) =
    (X + 171 * X ^ 2 + 7188 * X ^ 3 + 69424 * X ^ 4 + 180713 * X ^ 5 + 125633 * X ^ 6 + 16830 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 3 0 1 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm1 : (bag 3 0 1 7 1 100).erase 1 = (bag 2 0 1 7 1 100) := by rfl
  have hm3 : (bag 3 0 1 7 1 100).erase 3 = (bag 3 0 0 7 1 100) := by rfl
  have hm4 : (bag 3 0 1 7 1 100).erase 4 = (bag 3 0 1 6 1 100) := by rfl
  have hc := count_three (rows.drop 8) (rows.drop 9) (bag 3 0 1 7 1 100) (bag 2 0 1 7 1 100) (bag 3 0 0 7 1 100) (bag 3 0 1 6 1 100) (some 4) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_566 cert_567 cert_588
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_590 : count (rows.drop 7) (bag 3 0 1 8 1 100) (some 3) =
    (8 * X ^ 2 + 1065 * X ^ 3 + 24146 * X ^ 4 + 145544 * X ^ 5 + 267409 * X ^ 6 + 144938 * X ^ 7 + 16830 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 3 0 1 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 7 = 4 :: rows.drop 8 := by rfl
  have hm1 : (bag 3 0 1 8 1 100).erase 1 = (bag 2 0 1 8 1 100) := by rfl
  have hm3 : (bag 3 0 1 8 1 100).erase 3 = (bag 3 0 0 8 1 100) := by rfl
  have hm4 : (bag 3 0 1 8 1 100).erase 4 = (bag 3 0 1 7 1 100) := by rfl
  have hc := count_three (rows.drop 7) (rows.drop 8) (bag 3 0 1 8 1 100) (bag 2 0 1 8 1 100) (bag 3 0 0 8 1 100) (bag 3 0 1 7 1 100) (some 3) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_547 cert_565 cert_589
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_591 : count (rows.drop 6) (bag 3 0 2 8 1 100) (some 3) =
    (11 * X ^ 2 + 1539 * X ^ 3 + 41321 * X ^ 4 + 299501 * X ^ 5 + 661519 * X ^ 6 + 433094 * X ^ 7 + 62865 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 3 0 2 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 6 = 3 :: rows.drop 7 := by rfl
  have hm1 : (bag 3 0 2 8 1 100).erase 1 = (bag 2 0 2 8 1 100) := by rfl
  have hm3 : (bag 3 0 2 8 1 100).erase 3 = (bag 3 0 1 8 1 100) := by rfl
  have hc := count_two (rows.drop 6) (rows.drop 7) (bag 3 0 2 8 1 100) (bag 2 0 2 8 1 100) (bag 3 0 1 8 1 100) (some 3) 3 1 3 hr hs (by decide) hm1 hm3 _ _ cert_546 cert_590
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_592 : count (rows.drop 5) (bag 3 0 3 8 1 100) (some 3) =
    (13 * X ^ 2 + 1860 * X ^ 3 + 53742 * X ^ 4 + 430577 * X ^ 5 + 1122443 * X ^ 6 + 1026662 * X ^ 7 + 332228 * X ^ 8 + 32175 * X ^ 9 : ℕ[X]) := by
  have hs : (bag 3 0 3 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 5 = 3 :: rows.drop 6 := by rfl
  have hm1 : (bag 3 0 3 8 1 100).erase 1 = (bag 2 0 3 8 1 100) := by rfl
  have hm3 : (bag 3 0 3 8 1 100).erase 3 = (bag 3 0 2 8 1 100) := by rfl
  have hc := count_two (rows.drop 5) (rows.drop 6) (bag 3 0 3 8 1 100) (bag 2 0 3 8 1 100) (bag 3 0 2 8 1 100) (some 3) 3 1 3 hr hs (by decide) hm1 hm3 _ _ cert_545 cert_591
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_593 : count (rows.drop 4) (bag 3 0 4 8 1 100) (some 2) =
    (X ^ 2 + 175 * X ^ 3 + 8674 * X ^ 4 + 150365 * X ^ 5 + 943758 * X ^ 6 + 2092760 * X ^ 7 + 1609644 * X ^ 8 + 411923 * X ^ 9 + 32175 * X ^ 10 : ℕ[X]) := by
  have hs : (bag 3 0 4 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 4 = 3 :: rows.drop 5 := by rfl
  have hm1 : (bag 3 0 4 8 1 100).erase 1 = (bag 2 0 4 8 1 100) := by rfl
  have hm3 : (bag 3 0 4 8 1 100).erase 3 = (bag 3 0 3 8 1 100) := by rfl
  have hc := count_two (rows.drop 4) (rows.drop 5) (bag 3 0 4 8 1 100) (bag 2 0 4 8 1 100) (bag 3 0 3 8 1 100) (some 2) 3 1 3 hr hs (by decide) hm1 hm3 _ _ cert_544 cert_592
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_594 : count (rows.drop 5) (bag 2 1 3 8 1 100) (some 1) =
    (X ^ 2 + 211 * X ^ 3 + 13012 * X ^ 4 + 243866 * X ^ 5 + 1589265 * X ^ 6 + 3656939 * X ^ 7 + 2829255 * X ^ 8 + 634376 * X ^ 9 + 32175 * X ^ 10 : ℕ[X]) := by
  have hs : (bag 2 1 3 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 5 = 3 :: rows.drop 6 := by rfl
  have hm1 : (bag 2 1 3 8 1 100).erase 1 = (bag 1 1 3 8 1 100) := by rfl
  have hm2 : (bag 2 1 3 8 1 100).erase 2 = (bag 2 0 3 8 1 100) := by rfl
  have hm3 : (bag 2 1 3 8 1 100).erase 3 = (bag 2 1 2 8 1 100) := by rfl
  have hc := count_three (rows.drop 5) (rows.drop 6) (bag 2 1 3 8 1 100) (bag 1 1 3 8 1 100) (bag 2 0 3 8 1 100) (bag 2 1 2 8 1 100) (some 1) 3 1 2 3 hr hs (by decide) (by decide) hm1 hm2 hm3 _ _ _ cert_475 cert_476 cert_541
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_595 : count (rows.drop 5) (bag 3 0 3 8 1 100) (some 2) =
    (2 * X ^ 2 + 332 * X ^ 3 + 13960 * X ^ 4 + 172397 * X ^ 5 + 760425 * X ^ 6 + 1255087 * X ^ 7 + 702457 * X ^ 8 + 95040 * X ^ 9 : ℕ[X]) := by
  have hs : (bag 3 0 3 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 5 = 3 :: rows.drop 6 := by rfl
  have hm1 : (bag 3 0 3 8 1 100).erase 1 = (bag 2 0 3 8 1 100) := by rfl
  have hm3 : (bag 3 0 3 8 1 100).erase 3 = (bag 3 0 2 8 1 100) := by rfl
  have hc := count_two (rows.drop 5) (rows.drop 6) (bag 3 0 3 8 1 100) (bag 2 0 3 8 1 100) (bag 3 0 2 8 1 100) (some 2) 3 1 3 hr hs (by decide) hm1 hm3 _ _ cert_545 cert_591
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_596 : count (rows.drop 6) (bag 2 1 2 8 1 100) (some 1) =
    (2 * X ^ 2 + 400 * X ^ 3 + 21543 * X ^ 4 + 295815 * X ^ 5 + 1257000 * X ^ 6 + 1858756 * X ^ 7 + 941789 * X ^ 8 + 124245 * X ^ 9 : ℕ[X]) := by
  have hs : (bag 2 1 2 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 6 = 3 :: rows.drop 7 := by rfl
  have hm1 : (bag 2 1 2 8 1 100).erase 1 = (bag 1 1 2 8 1 100) := by rfl
  have hm2 : (bag 2 1 2 8 1 100).erase 2 = (bag 2 0 2 8 1 100) := by rfl
  have hm3 : (bag 2 1 2 8 1 100).erase 3 = (bag 2 1 1 8 1 100) := by rfl
  have hc := count_three (rows.drop 6) (rows.drop 7) (bag 2 1 2 8 1 100) (bag 1 1 2 8 1 100) (bag 2 0 2 8 1 100) (bag 2 1 1 8 1 100) (some 1) 3 1 2 3 hr hs (by decide) (by decide) hm1 hm2 hm3 _ _ _ cert_477 cert_478 cert_540
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_597 : count (rows.drop 6) (bag 3 0 2 8 1 100) (some 2) =
    (3 * X ^ 2 + 482 * X ^ 3 + 18240 * X ^ 4 + 178103 * X ^ 5 + 539654 * X ^ 6 + 555565 * X ^ 7 + 190973 * X ^ 8 + 16830 * X ^ 9 : ℕ[X]) := by
  have hs : (bag 3 0 2 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 6 = 3 :: rows.drop 7 := by rfl
  have hm1 : (bag 3 0 2 8 1 100).erase 1 = (bag 2 0 2 8 1 100) := by rfl
  have hm3 : (bag 3 0 2 8 1 100).erase 3 = (bag 3 0 1 8 1 100) := by rfl
  have hc := count_two (rows.drop 6) (rows.drop 7) (bag 3 0 2 8 1 100) (bag 2 0 2 8 1 100) (bag 3 0 1 8 1 100) (some 2) 3 1 3 hr hs (by decide) hm1 hm3 _ _ cert_546 cert_590
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_598 : count (rows.drop 7) (bag 2 1 1 8 1 100) (some 1) =
    (3 * X ^ 2 + 552 * X ^ 3 + 25589 * X ^ 4 + 269684 * X ^ 5 + 772502 * X ^ 6 + 623085 * X ^ 7 + 108405 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 2 1 1 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 7 = 4 :: rows.drop 8 := by rfl
  have hm1 : (bag 2 1 1 8 1 100).erase 1 = (bag 1 1 1 8 1 100) := by rfl
  have hm2 : (bag 2 1 1 8 1 100).erase 2 = (bag 2 0 1 8 1 100) := by rfl
  have hm3 : (bag 2 1 1 8 1 100).erase 3 = (bag 2 1 0 8 1 100) := by rfl
  have hm4 : (bag 2 1 1 8 1 100).erase 4 = (bag 2 1 1 7 1 100) := by rfl
  have hc := count_four (rows.drop 7) (rows.drop 8) (bag 2 1 1 8 1 100) (bag 1 1 1 8 1 100) (bag 2 0 1 8 1 100) (bag 2 1 0 8 1 100) (bag 2 1 1 7 1 100) (some 1) 4 1 2 3 4 hr hs (by decide) (by decide) (by decide) hm1 hm2 hm3 hm4 _ _ _ _ cert_479 cert_480 cert_507 cert_539
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_599 : count (rows.drop 7) (bag 3 0 1 8 1 100) (some 2) =
    (4 * X ^ 2 + 592 * X ^ 3 + 18213 * X ^ 4 + 130344 * X ^ 5 + 270495 * X ^ 6 + 160492 * X ^ 7 + 19800 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 3 0 1 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 7 = 4 :: rows.drop 8 := by rfl
  have hm1 : (bag 3 0 1 8 1 100).erase 1 = (bag 2 0 1 8 1 100) := by rfl
  have hm3 : (bag 3 0 1 8 1 100).erase 3 = (bag 3 0 0 8 1 100) := by rfl
  have hm4 : (bag 3 0 1 8 1 100).erase 4 = (bag 3 0 1 7 1 100) := by rfl
  have hc := count_three (rows.drop 7) (rows.drop 8) (bag 3 0 1 8 1 100) (bag 2 0 1 8 1 100) (bag 3 0 0 8 1 100) (bag 3 0 1 7 1 100) (some 2) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_547 cert_565 cert_589
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_600 : count (rows.drop 8) (bag 2 1 0 8 1 100) (some 1) =
    (3 * X ^ 2 + 417 * X ^ 3 + 10548 * X ^ 4 + 54510 * X ^ 5 + 68172 * X ^ 6 + 16335 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 1 0 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm1 : (bag 2 1 0 8 1 100).erase 1 = (bag 1 1 0 8 1 100) := by rfl
  have hm2 : (bag 2 1 0 8 1 100).erase 2 = (bag 2 0 0 8 1 100) := by rfl
  have hm4 : (bag 2 1 0 8 1 100).erase 4 = (bag 2 1 0 7 1 100) := by rfl
  have hc := count_three (rows.drop 8) (rows.drop 9) (bag 2 1 0 8 1 100) (bag 1 1 0 8 1 100) (bag 2 0 0 8 1 100) (bag 2 1 0 7 1 100) (some 1) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_481 cert_482 cert_506
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_601 : count (rows.drop 8) (bag 3 0 0 8 1 100) (some 2) =
    (4 * X ^ 2 + 477 * X ^ 3 + 6410 * X ^ 4 + 21610 * X ^ 5 + 18524 * X ^ 6 + 2970 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 3 0 0 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm1 : (bag 3 0 0 8 1 100).erase 1 = (bag 2 0 0 8 1 100) := by rfl
  have hm4 : (bag 3 0 0 8 1 100).erase 4 = (bag 3 0 0 7 1 100) := by rfl
  have hc := count_two (rows.drop 8) (rows.drop 9) (bag 3 0 0 8 1 100) (bag 2 0 0 8 1 100) (bag 3 0 0 7 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_548 cert_564
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_602 : count (rows.drop 9) (bag 2 1 0 7 1 100) (some 1) =
    (3 * X ^ 2 + 408 * X ^ 3 + 9509 * X ^ 4 + 43692 * X ^ 5 + 46558 * X ^ 6 + 8910 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 1 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 2 1 0 7 1 100).erase 1 = (bag 1 1 0 7 1 100) := by rfl
  have hm2 : (bag 2 1 0 7 1 100).erase 2 = (bag 2 0 0 7 1 100) := by rfl
  have hm4 : (bag 2 1 0 7 1 100).erase 4 = (bag 2 1 0 6 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 2 1 0 7 1 100) (bag 1 1 0 7 1 100) (bag 2 0 0 7 1 100) (bag 2 1 0 6 1 100) (some 1) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_483 cert_484 cert_505
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_603 : count (rows.drop 9) (bag 3 0 0 7 1 100) (some 2) =
    (4 * X ^ 2 + 471 * X ^ 3 + 5745 * X ^ 4 + 16915 * X ^ 5 + 11839 * X ^ 6 + 1386 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 3 0 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 3 0 0 7 1 100).erase 1 = (bag 2 0 0 7 1 100) := by rfl
  have hm4 : (bag 3 0 0 7 1 100).erase 4 = (bag 3 0 0 6 1 100) := by rfl
  have hc := count_two (rows.drop 9) (rows.drop 10) (bag 3 0 0 7 1 100) (bag 2 0 0 7 1 100) (bag 3 0 0 6 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_549 cert_563
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_604 : count (rows.drop 10) (bag 2 1 0 6 1 100) (some 1) =
    (3 * X ^ 2 + 399 * X ^ 3 + 8479 * X ^ 4 + 33843 * X ^ 5 + 29474 * X ^ 6 + 4158 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 1 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 2 1 0 6 1 100).erase 1 = (bag 1 1 0 6 1 100) := by rfl
  have hm2 : (bag 2 1 0 6 1 100).erase 2 = (bag 2 0 0 6 1 100) := by rfl
  have hm4 : (bag 2 1 0 6 1 100).erase 4 = (bag 2 1 0 5 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 2 1 0 6 1 100) (bag 1 1 0 6 1 100) (bag 2 0 0 6 1 100) (bag 2 1 0 5 1 100) (some 1) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_485 cert_486 cert_504
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_605 : count (rows.drop 10) (bag 3 0 0 6 1 100) (some 2) =
    (4 * X ^ 2 + 465 * X ^ 3 + 5084 * X ^ 4 + 12646 * X ^ 5 + 6758 * X ^ 6 + 495 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 3 0 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 3 0 0 6 1 100).erase 1 = (bag 2 0 0 6 1 100) := by rfl
  have hm4 : (bag 3 0 0 6 1 100).erase 4 = (bag 3 0 0 5 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 3 0 0 6 1 100) (bag 2 0 0 6 1 100) (bag 3 0 0 5 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_550 cert_562
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_606 : count (rows.drop 11) (bag 2 1 0 5 1 100) (some 1) =
    (3 * X ^ 2 + 390 * X ^ 3 + 7458 * X ^ 4 + 24960 * X ^ 5 + 16608 * X ^ 6 + 1485 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 1 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 2 1 0 5 1 100).erase 1 = (bag 1 1 0 5 1 100) := by rfl
  have hm2 : (bag 2 1 0 5 1 100).erase 2 = (bag 2 0 0 5 1 100) := by rfl
  have hm4 : (bag 2 1 0 5 1 100).erase 4 = (bag 2 1 0 4 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 2 1 0 5 1 100) (bag 1 1 0 5 1 100) (bag 2 0 0 5 1 100) (bag 2 1 0 4 1 100) (some 1) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_487 cert_488 cert_503
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_607 : count (rows.drop 11) (bag 3 0 0 5 1 100) (some 2) =
    (4 * X ^ 2 + 459 * X ^ 3 + 4427 * X ^ 4 + 8802 * X ^ 5 + 3177 * X ^ 6 + 99 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 3 0 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 3 0 0 5 1 100).erase 1 = (bag 2 0 0 5 1 100) := by rfl
  have hm4 : (bag 3 0 0 5 1 100).erase 4 = (bag 3 0 0 4 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 3 0 0 5 1 100) (bag 2 0 0 5 1 100) (bag 3 0 0 4 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_551 cert_561
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_608 : count (rows.drop 12) (bag 2 1 0 4 1 100) (some 1) =
    (3 * X ^ 2 + 381 * X ^ 3 + 6446 * X ^ 4 + 17040 * X ^ 5 + 7648 * X ^ 6 + 297 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 2 1 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 2 1 0 4 1 100).erase 1 = (bag 1 1 0 4 1 100) := by rfl
  have hm2 : (bag 2 1 0 4 1 100).erase 2 = (bag 2 0 0 4 1 100) := by rfl
  have hm4 : (bag 2 1 0 4 1 100).erase 4 = (bag 2 1 0 3 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 2 1 0 4 1 100) (bag 1 1 0 4 1 100) (bag 2 0 0 4 1 100) (bag 2 1 0 3 1 100) (some 1) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_489 cert_490 cert_502
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_609 : count (rows.drop 12) (bag 3 0 0 4 1 100) (some 2) =
    (4 * X ^ 2 + 453 * X ^ 3 + 3774 * X ^ 4 + 5382 * X ^ 5 + 992 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 3 0 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 3 0 0 4 1 100).erase 1 = (bag 2 0 0 4 1 100) := by rfl
  have hm4 : (bag 3 0 0 4 1 100).erase 4 = (bag 3 0 0 3 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 3 0 0 4 1 100) (bag 2 0 0 4 1 100) (bag 3 0 0 3 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_552 cert_560
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_610 : count (rows.drop 13) (bag 2 1 0 3 1 100) (some 1) =
    (3 * X ^ 2 + 372 * X ^ 3 + 5443 * X ^ 4 + 10080 * X ^ 5 + 2282 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 1 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 2 1 0 3 1 100).erase 1 = (bag 1 1 0 3 1 100) := by rfl
  have hm2 : (bag 2 1 0 3 1 100).erase 2 = (bag 2 0 0 3 1 100) := by rfl
  have hm4 : (bag 2 1 0 3 1 100).erase 4 = (bag 2 1 0 2 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 2 1 0 3 1 100) (bag 1 1 0 3 1 100) (bag 2 0 0 3 1 100) (bag 2 1 0 2 1 100) (some 1) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_491 cert_492 cert_501
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_611 : count (rows.drop 13) (bag 3 0 0 3 1 100) (some 2) =
    (4 * X ^ 2 + 447 * X ^ 3 + 3125 * X ^ 4 + 2385 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 3 0 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 3 0 0 3 1 100).erase 1 = (bag 2 0 0 3 1 100) := by rfl
  have hm4 : (bag 3 0 0 3 1 100).erase 4 = (bag 3 0 0 2 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 3 0 0 3 1 100) (bag 2 0 0 3 1 100) (bag 3 0 0 2 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_553 cert_559
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_612 : count (rows.drop 14) (bag 2 1 0 2 1 100) (some 1) =
    (3 * X ^ 2 + 363 * X ^ 3 + 4449 * X ^ 4 + 4077 * X ^ 5 + 198 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 2 1 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 2 1 0 2 1 100).erase 1 = (bag 1 1 0 2 1 100) := by rfl
  have hm2 : (bag 2 1 0 2 1 100).erase 2 = (bag 2 0 0 2 1 100) := by rfl
  have hm4 : (bag 2 1 0 2 1 100).erase 4 = (bag 2 1 0 1 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 2 1 0 2 1 100) (bag 1 1 0 2 1 100) (bag 2 0 0 2 1 100) (bag 2 1 0 1 1 100) (some 1) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_493 cert_494 cert_500
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_613 : count (rows.drop 14) (bag 3 0 0 2 1 100) (some 2) =
    (6 * X ^ 2 + 532 * X ^ 3 + 2096 * X ^ 4 + 396 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 3 0 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 3 0 0 2 1 100).erase 1 = (bag 2 0 0 2 1 100) := by rfl
  have hm4 : (bag 3 0 0 2 1 100).erase 4 = (bag 3 0 0 1 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 3 0 0 2 1 100) (bag 2 0 0 2 1 100) (bag 3 0 0 1 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_554 cert_558
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_614 : count (rows.drop 15) (bag 2 1 0 1 1 100) (some 1) =
    (6 * X ^ 2 + 538 * X ^ 3 + 2597 * X ^ 4 + 495 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 2 1 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 2 1 0 1 1 100).erase 1 = (bag 1 1 0 1 1 100) := by rfl
  have hm2 : (bag 2 1 0 1 1 100).erase 2 = (bag 2 0 0 1 1 100) := by rfl
  have hm4 : (bag 2 1 0 1 1 100).erase 4 = (bag 2 1 0 0 1 100) := by rfl
  have hc := count_three (rows.drop 15) (rows.drop 16) (bag 2 1 0 1 1 100) (bag 1 1 0 1 1 100) (bag 2 0 0 1 1 100) (bag 2 1 0 0 1 100) (some 1) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_495 cert_496 cert_499
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_615 : count (rows.drop 15) (bag 3 0 0 1 1 100) (some 2) =
    (9 * X ^ 2 + 708 * X ^ 3 + 495 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 3 0 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 3 0 0 1 1 100).erase 1 = (bag 2 0 0 1 1 100) := by rfl
  have hm4 : (bag 3 0 0 1 1 100).erase 4 = (bag 3 0 0 0 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 3 0 0 1 1 100) (bag 2 0 0 1 1 100) (bag 3 0 0 0 1 100) (some 2) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_555 cert_557
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_616 : count (rows.drop 16) (bag 2 1 0 0 1 100) (some 1) =
    (8 * X ^ 2 + 604 * X ^ 3 + 297 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 2 1 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 2 1 0 0 1 100).erase 1 = (bag 1 1 0 0 1 100) := by rfl
  have hm2 : (bag 2 1 0 0 1 100).erase 2 = (bag 2 0 0 0 1 100) := by rfl
  have hc := count_two (rows.drop 16) (rows.drop 17) (bag 2 1 0 0 1 100) (bag 1 1 0 0 1 100) (bag 2 0 0 0 1 100) (some 1) 4 1 2 hr hs (by decide) hm1 hm2 _ _ cert_497 cert_498
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_617 : count (rows.drop 16) (bag 3 0 0 0 1 100) (some 2) =
    (X + 104 * X ^ 2 + 198 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 3 0 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 3 0 0 0 1 100).erase 1 = (bag 2 0 0 0 1 100) := by rfl
  have hc := count_one (rows.drop 16) (rows.drop 17) (bag 3 0 0 0 1 100) (bag 2 0 0 0 1 100) (some 2) 4 1 hr hs hm1 _ cert_556
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_618 : count (rows.drop 15) (bag 3 1 0 0 1 100) (some 4) =
    (X + 112 * X ^ 2 + 802 * X ^ 3 + 297 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 3 1 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 3 1 0 0 1 100).erase 1 = (bag 2 1 0 0 1 100) := by rfl
  have hm2 : (bag 3 1 0 0 1 100).erase 2 = (bag 3 0 0 0 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 3 1 0 0 1 100) (bag 2 1 0 0 1 100) (bag 3 0 0 0 1 100) (some 4) 4 1 2 hr hs (by decide) hm1 hm2 _ _ cert_616 cert_617
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_619 : count (rows.drop 14) (bag 3 1 0 1 1 100) (some 4) =
    (X + 127 * X ^ 2 + 2048 * X ^ 3 + 3389 * X ^ 4 + 495 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 3 1 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 3 1 0 1 1 100).erase 1 = (bag 2 1 0 1 1 100) := by rfl
  have hm2 : (bag 3 1 0 1 1 100).erase 2 = (bag 3 0 0 1 1 100) := by rfl
  have hm4 : (bag 3 1 0 1 1 100).erase 4 = (bag 3 1 0 0 1 100) := by rfl
  have hc := count_three (rows.drop 14) (rows.drop 15) (bag 3 1 0 1 1 100) (bag 2 1 0 1 1 100) (bag 3 0 0 1 1 100) (bag 3 1 0 0 1 100) (some 4) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_614 cert_615 cert_618
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_620 : count (rows.drop 13) (bag 3 1 0 2 1 100) (some 4) =
    (X + 136 * X ^ 2 + 2943 * X ^ 3 + 9934 * X ^ 4 + 4968 * X ^ 5 + 198 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 3 1 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 3 1 0 2 1 100).erase 1 = (bag 2 1 0 2 1 100) := by rfl
  have hm2 : (bag 3 1 0 2 1 100).erase 2 = (bag 3 0 0 2 1 100) := by rfl
  have hm4 : (bag 3 1 0 2 1 100).erase 4 = (bag 3 1 0 1 1 100) := by rfl
  have hc := count_three (rows.drop 13) (rows.drop 14) (bag 3 1 0 2 1 100) (bag 2 1 0 2 1 100) (bag 3 0 0 2 1 100) (bag 3 1 0 1 1 100) (some 4) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_612 cert_613 cert_619
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_621 : count (rows.drop 12) (bag 3 1 0 3 1 100) (some 4) =
    (X + 143 * X ^ 2 + 3762 * X ^ 3 + 18502 * X ^ 4 + 17433 * X ^ 5 + 2579 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 3 1 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 3 1 0 3 1 100).erase 1 = (bag 2 1 0 3 1 100) := by rfl
  have hm2 : (bag 3 1 0 3 1 100).erase 2 = (bag 3 0 0 3 1 100) := by rfl
  have hm4 : (bag 3 1 0 3 1 100).erase 4 = (bag 3 1 0 2 1 100) := by rfl
  have hc := count_three (rows.drop 12) (rows.drop 13) (bag 3 1 0 3 1 100) (bag 2 1 0 3 1 100) (bag 3 0 0 3 1 100) (bag 3 1 0 2 1 100) (some 4) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_610 cert_611 cert_620
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_622 : count (rows.drop 11) (bag 3 1 0 4 1 100) (some 4) =
    (X + 150 * X ^ 2 + 4596 * X ^ 3 + 28722 * X ^ 4 + 39855 * X ^ 5 + 11219 * X ^ 6 + 297 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 3 1 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 3 1 0 4 1 100).erase 1 = (bag 2 1 0 4 1 100) := by rfl
  have hm2 : (bag 3 1 0 4 1 100).erase 2 = (bag 3 0 0 4 1 100) := by rfl
  have hm4 : (bag 3 1 0 4 1 100).erase 4 = (bag 3 1 0 3 1 100) := by rfl
  have hc := count_three (rows.drop 11) (rows.drop 12) (bag 3 1 0 4 1 100) (bag 2 1 0 4 1 100) (bag 3 0 0 4 1 100) (bag 3 1 0 3 1 100) (some 4) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_608 cert_609 cert_621
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_623 : count (rows.drop 10) (bag 3 1 0 5 1 100) (some 4) =
    (X + 157 * X ^ 2 + 5445 * X ^ 3 + 40607 * X ^ 4 + 73617 * X ^ 5 + 31004 * X ^ 6 + 1881 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 3 1 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 3 1 0 5 1 100).erase 1 = (bag 2 1 0 5 1 100) := by rfl
  have hm2 : (bag 3 1 0 5 1 100).erase 2 = (bag 3 0 0 5 1 100) := by rfl
  have hm4 : (bag 3 1 0 5 1 100).erase 4 = (bag 3 1 0 4 1 100) := by rfl
  have hc := count_three (rows.drop 10) (rows.drop 11) (bag 3 1 0 5 1 100) (bag 2 1 0 5 1 100) (bag 3 0 0 5 1 100) (bag 3 1 0 4 1 100) (some 4) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_606 cert_607 cert_622
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_624 : count (rows.drop 9) (bag 3 1 0 6 1 100) (some 4) =
    (X + 164 * X ^ 2 + 6309 * X ^ 3 + 54170 * X ^ 4 + 120106 * X ^ 5 + 67236 * X ^ 6 + 6534 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 3 1 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 3 1 0 6 1 100).erase 1 = (bag 2 1 0 6 1 100) := by rfl
  have hm2 : (bag 3 1 0 6 1 100).erase 2 = (bag 3 0 0 6 1 100) := by rfl
  have hm4 : (bag 3 1 0 6 1 100).erase 4 = (bag 3 1 0 5 1 100) := by rfl
  have hc := count_three (rows.drop 9) (rows.drop 10) (bag 3 1 0 6 1 100) (bag 2 1 0 6 1 100) (bag 3 0 0 6 1 100) (bag 3 1 0 5 1 100) (some 4) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_604 cert_605 cert_623
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_625 : count (rows.drop 8) (bag 3 1 0 7 1 100) (some 4) =
    (X + 171 * X ^ 2 + 7188 * X ^ 3 + 69424 * X ^ 4 + 180713 * X ^ 5 + 125633 * X ^ 6 + 16830 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 3 1 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm1 : (bag 3 1 0 7 1 100).erase 1 = (bag 2 1 0 7 1 100) := by rfl
  have hm2 : (bag 3 1 0 7 1 100).erase 2 = (bag 3 0 0 7 1 100) := by rfl
  have hm4 : (bag 3 1 0 7 1 100).erase 4 = (bag 3 1 0 6 1 100) := by rfl
  have hc := count_three (rows.drop 8) (rows.drop 9) (bag 3 1 0 7 1 100) (bag 2 1 0 7 1 100) (bag 3 0 0 7 1 100) (bag 3 1 0 6 1 100) (some 4) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_602 cert_603 cert_624
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_626 : count (rows.drop 7) (bag 3 1 0 8 1 100) (some 3) =
    (8 * X ^ 2 + 1065 * X ^ 3 + 24146 * X ^ 4 + 145544 * X ^ 5 + 267409 * X ^ 6 + 144938 * X ^ 7 + 16830 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 3 1 0 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 2, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 7 = 4 :: rows.drop 8 := by rfl
  have hm1 : (bag 3 1 0 8 1 100).erase 1 = (bag 2 1 0 8 1 100) := by rfl
  have hm2 : (bag 3 1 0 8 1 100).erase 2 = (bag 3 0 0 8 1 100) := by rfl
  have hm4 : (bag 3 1 0 8 1 100).erase 4 = (bag 3 1 0 7 1 100) := by rfl
  have hc := count_three (rows.drop 7) (rows.drop 8) (bag 3 1 0 8 1 100) (bag 2 1 0 8 1 100) (bag 3 0 0 8 1 100) (bag 3 1 0 7 1 100) (some 3) 4 1 2 4 hr hs (by decide) (by decide) hm1 hm2 hm4 _ _ _ cert_600 cert_601 cert_625
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_627 : count (rows.drop 6) (bag 3 1 1 8 1 100) (some 3) =
    (15 * X ^ 2 + 2209 * X ^ 3 + 67948 * X ^ 4 + 545572 * X ^ 5 + 1310406 * X ^ 6 + 928515 * X ^ 7 + 145035 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 3 1 1 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 6 = 3 :: rows.drop 7 := by rfl
  have hm1 : (bag 3 1 1 8 1 100).erase 1 = (bag 2 1 1 8 1 100) := by rfl
  have hm2 : (bag 3 1 1 8 1 100).erase 2 = (bag 3 0 1 8 1 100) := by rfl
  have hm3 : (bag 3 1 1 8 1 100).erase 3 = (bag 3 1 0 8 1 100) := by rfl
  have hc := count_three (rows.drop 6) (rows.drop 7) (bag 3 1 1 8 1 100) (bag 2 1 1 8 1 100) (bag 3 0 1 8 1 100) (bag 3 1 0 8 1 100) (some 3) 3 1 2 3 hr hs (by decide) (by decide) hm1 hm2 hm3 _ _ _ cert_598 cert_599 cert_626
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_628 : count (rows.drop 5) (bag 3 1 2 8 1 100) (some 3) =
    (20 * X ^ 2 + 3091 * X ^ 3 + 107731 * X ^ 4 + 1019490 * X ^ 5 + 3107060 * X ^ 6 + 3342836 * X ^ 7 + 1277797 * X ^ 8 + 141075 * X ^ 9 : ℕ[X]) := by
  have hs : (bag 3 1 2 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 5 = 3 :: rows.drop 6 := by rfl
  have hm1 : (bag 3 1 2 8 1 100).erase 1 = (bag 2 1 2 8 1 100) := by rfl
  have hm2 : (bag 3 1 2 8 1 100).erase 2 = (bag 3 0 2 8 1 100) := by rfl
  have hm3 : (bag 3 1 2 8 1 100).erase 3 = (bag 3 1 1 8 1 100) := by rfl
  have hc := count_three (rows.drop 5) (rows.drop 6) (bag 3 1 2 8 1 100) (bag 2 1 2 8 1 100) (bag 3 0 2 8 1 100) (bag 3 1 1 8 1 100) (some 3) 3 1 2 3 hr hs (by decide) (by decide) hm1 hm2 hm3 _ _ _ cert_596 cert_597 cert_627
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_629 : count (rows.drop 4) (bag 3 1 3 8 1 100) (some 3) =
    (23 * X ^ 2 + 3634 * X ^ 3 + 134703 * X ^ 4 + 1435753 * X ^ 5 + 5456750 * X ^ 6 + 8254862 * X ^ 7 + 4809509 * X ^ 8 + 870491 * X ^ 9 + 32175 * X ^ 10 : ℕ[X]) := by
  have hs : (bag 3 1 3 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 4 = 3 :: rows.drop 5 := by rfl
  have hm1 : (bag 3 1 3 8 1 100).erase 1 = (bag 2 1 3 8 1 100) := by rfl
  have hm2 : (bag 3 1 3 8 1 100).erase 2 = (bag 3 0 3 8 1 100) := by rfl
  have hm3 : (bag 3 1 3 8 1 100).erase 3 = (bag 3 1 2 8 1 100) := by rfl
  have hc := count_three (rows.drop 4) (rows.drop 5) (bag 3 1 3 8 1 100) (bag 2 1 3 8 1 100) (bag 3 0 3 8 1 100) (bag 3 1 2 8 1 100) (some 3) 3 1 2 3 hr hs (by decide) (by decide) hm1 hm2 hm3 _ _ _ cert_594 cert_595 cert_628
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_630 : count (rows.drop 3) (bag 3 1 4 8 1 100) (some 1) =
    (70 * X ^ 3 + 10630 * X ^ 4 + 359501 * X ^ 5 + 3479805 * X ^ 6 + 11880380 * X ^ 7 + 16084415 * X ^ 8 + 8596635 * X ^ 9 + 1520014 * X ^ 10 + 64350 * X ^ 11 : ℕ[X]) := by
  have hs : (bag 3 1 4 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 2, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 3 = 3 :: rows.drop 4 := by rfl
  have hm1 : (bag 3 1 4 8 1 100).erase 1 = (bag 2 1 4 8 1 100) := by rfl
  have hm2 : (bag 3 1 4 8 1 100).erase 2 = (bag 3 0 4 8 1 100) := by rfl
  have hm3 : (bag 3 1 4 8 1 100).erase 3 = (bag 3 1 3 8 1 100) := by rfl
  have hc := count_three (rows.drop 3) (rows.drop 4) (bag 3 1 4 8 1 100) (bag 2 1 4 8 1 100) (bag 3 0 4 8 1 100) (bag 3 1 3 8 1 100) (some 1) 3 1 2 3 hr hs (by decide) (by decide) hm1 hm2 hm3 _ _ _ cert_543 cert_593 cert_629
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_631 : count (rows.drop 4) (bag 3 0 4 8 1 100) (some 1) =
    (X ^ 2 + 175 * X ^ 3 + 8674 * X ^ 4 + 150365 * X ^ 5 + 943758 * X ^ 6 + 2092760 * X ^ 7 + 1609644 * X ^ 8 + 411923 * X ^ 9 + 32175 * X ^ 10 : ℕ[X]) := by
  have hs : (bag 3 0 4 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 4 = 3 :: rows.drop 5 := by rfl
  have hm1 : (bag 3 0 4 8 1 100).erase 1 = (bag 2 0 4 8 1 100) := by rfl
  have hm3 : (bag 3 0 4 8 1 100).erase 3 = (bag 3 0 3 8 1 100) := by rfl
  have hc := count_two (rows.drop 4) (rows.drop 5) (bag 3 0 4 8 1 100) (bag 2 0 4 8 1 100) (bag 3 0 3 8 1 100) (some 1) 3 1 3 hr hs (by decide) hm1 hm3 _ _ cert_544 cert_592
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_632 : count (rows.drop 5) (bag 3 0 3 8 1 100) (some 1) =
    (2 * X ^ 2 + 332 * X ^ 3 + 13960 * X ^ 4 + 172397 * X ^ 5 + 760425 * X ^ 6 + 1255087 * X ^ 7 + 702457 * X ^ 8 + 95040 * X ^ 9 : ℕ[X]) := by
  have hs : (bag 3 0 3 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 5 = 3 :: rows.drop 6 := by rfl
  have hm1 : (bag 3 0 3 8 1 100).erase 1 = (bag 2 0 3 8 1 100) := by rfl
  have hm3 : (bag 3 0 3 8 1 100).erase 3 = (bag 3 0 2 8 1 100) := by rfl
  have hc := count_two (rows.drop 5) (rows.drop 6) (bag 3 0 3 8 1 100) (bag 2 0 3 8 1 100) (bag 3 0 2 8 1 100) (some 1) 3 1 3 hr hs (by decide) hm1 hm3 _ _ cert_545 cert_591
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_633 : count (rows.drop 6) (bag 3 0 2 8 1 100) (some 1) =
    (3 * X ^ 2 + 482 * X ^ 3 + 18240 * X ^ 4 + 178103 * X ^ 5 + 539654 * X ^ 6 + 555565 * X ^ 7 + 190973 * X ^ 8 + 16830 * X ^ 9 : ℕ[X]) := by
  have hs : (bag 3 0 2 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 6 = 3 :: rows.drop 7 := by rfl
  have hm1 : (bag 3 0 2 8 1 100).erase 1 = (bag 2 0 2 8 1 100) := by rfl
  have hm3 : (bag 3 0 2 8 1 100).erase 3 = (bag 3 0 1 8 1 100) := by rfl
  have hc := count_two (rows.drop 6) (rows.drop 7) (bag 3 0 2 8 1 100) (bag 2 0 2 8 1 100) (bag 3 0 1 8 1 100) (some 1) 3 1 3 hr hs (by decide) hm1 hm3 _ _ cert_546 cert_590
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_634 : count (rows.drop 7) (bag 3 0 1 8 1 100) (some 1) =
    (4 * X ^ 2 + 592 * X ^ 3 + 18213 * X ^ 4 + 130344 * X ^ 5 + 270495 * X ^ 6 + 160492 * X ^ 7 + 19800 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 3 0 1 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 3, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 7 = 4 :: rows.drop 8 := by rfl
  have hm1 : (bag 3 0 1 8 1 100).erase 1 = (bag 2 0 1 8 1 100) := by rfl
  have hm3 : (bag 3 0 1 8 1 100).erase 3 = (bag 3 0 0 8 1 100) := by rfl
  have hm4 : (bag 3 0 1 8 1 100).erase 4 = (bag 3 0 1 7 1 100) := by rfl
  have hc := count_three (rows.drop 7) (rows.drop 8) (bag 3 0 1 8 1 100) (bag 2 0 1 8 1 100) (bag 3 0 0 8 1 100) (bag 3 0 1 7 1 100) (some 1) 4 1 3 4 hr hs (by decide) (by decide) hm1 hm3 hm4 _ _ _ cert_547 cert_565 cert_589
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_635 : count (rows.drop 8) (bag 3 0 0 8 1 100) (some 1) =
    (4 * X ^ 2 + 477 * X ^ 3 + 6410 * X ^ 4 + 21610 * X ^ 5 + 18524 * X ^ 6 + 2970 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 3 0 0 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm1 : (bag 3 0 0 8 1 100).erase 1 = (bag 2 0 0 8 1 100) := by rfl
  have hm4 : (bag 3 0 0 8 1 100).erase 4 = (bag 3 0 0 7 1 100) := by rfl
  have hc := count_two (rows.drop 8) (rows.drop 9) (bag 3 0 0 8 1 100) (bag 2 0 0 8 1 100) (bag 3 0 0 7 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_548 cert_564
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_636 : count (rows.drop 9) (bag 3 0 0 7 1 100) (some 1) =
    (4 * X ^ 2 + 471 * X ^ 3 + 5745 * X ^ 4 + 16915 * X ^ 5 + 11839 * X ^ 6 + 1386 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 3 0 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 3 0 0 7 1 100).erase 1 = (bag 2 0 0 7 1 100) := by rfl
  have hm4 : (bag 3 0 0 7 1 100).erase 4 = (bag 3 0 0 6 1 100) := by rfl
  have hc := count_two (rows.drop 9) (rows.drop 10) (bag 3 0 0 7 1 100) (bag 2 0 0 7 1 100) (bag 3 0 0 6 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_549 cert_563
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_637 : count (rows.drop 10) (bag 3 0 0 6 1 100) (some 1) =
    (4 * X ^ 2 + 465 * X ^ 3 + 5084 * X ^ 4 + 12646 * X ^ 5 + 6758 * X ^ 6 + 495 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 3 0 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 3 0 0 6 1 100).erase 1 = (bag 2 0 0 6 1 100) := by rfl
  have hm4 : (bag 3 0 0 6 1 100).erase 4 = (bag 3 0 0 5 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 3 0 0 6 1 100) (bag 2 0 0 6 1 100) (bag 3 0 0 5 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_550 cert_562
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_638 : count (rows.drop 11) (bag 3 0 0 5 1 100) (some 1) =
    (4 * X ^ 2 + 459 * X ^ 3 + 4427 * X ^ 4 + 8802 * X ^ 5 + 3177 * X ^ 6 + 99 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 3 0 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 3 0 0 5 1 100).erase 1 = (bag 2 0 0 5 1 100) := by rfl
  have hm4 : (bag 3 0 0 5 1 100).erase 4 = (bag 3 0 0 4 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 3 0 0 5 1 100) (bag 2 0 0 5 1 100) (bag 3 0 0 4 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_551 cert_561
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_639 : count (rows.drop 12) (bag 3 0 0 4 1 100) (some 1) =
    (4 * X ^ 2 + 453 * X ^ 3 + 3774 * X ^ 4 + 5382 * X ^ 5 + 992 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 3 0 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 3 0 0 4 1 100).erase 1 = (bag 2 0 0 4 1 100) := by rfl
  have hm4 : (bag 3 0 0 4 1 100).erase 4 = (bag 3 0 0 3 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 3 0 0 4 1 100) (bag 2 0 0 4 1 100) (bag 3 0 0 3 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_552 cert_560
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_640 : count (rows.drop 13) (bag 3 0 0 3 1 100) (some 1) =
    (4 * X ^ 2 + 447 * X ^ 3 + 3125 * X ^ 4 + 2385 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 3 0 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 3 0 0 3 1 100).erase 1 = (bag 2 0 0 3 1 100) := by rfl
  have hm4 : (bag 3 0 0 3 1 100).erase 4 = (bag 3 0 0 2 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 3 0 0 3 1 100) (bag 2 0 0 3 1 100) (bag 3 0 0 2 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_553 cert_559
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_641 : count (rows.drop 14) (bag 3 0 0 2 1 100) (some 1) =
    (6 * X ^ 2 + 532 * X ^ 3 + 2096 * X ^ 4 + 396 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 3 0 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 3 0 0 2 1 100).erase 1 = (bag 2 0 0 2 1 100) := by rfl
  have hm4 : (bag 3 0 0 2 1 100).erase 4 = (bag 3 0 0 1 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 3 0 0 2 1 100) (bag 2 0 0 2 1 100) (bag 3 0 0 1 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_554 cert_558
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_642 : count (rows.drop 15) (bag 3 0 0 1 1 100) (some 1) =
    (9 * X ^ 2 + 708 * X ^ 3 + 495 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 3 0 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 3 0 0 1 1 100).erase 1 = (bag 2 0 0 1 1 100) := by rfl
  have hm4 : (bag 3 0 0 1 1 100).erase 4 = (bag 3 0 0 0 1 100) := by rfl
  have hc := count_two (rows.drop 15) (rows.drop 16) (bag 3 0 0 1 1 100) (bag 2 0 0 1 1 100) (bag 3 0 0 0 1 100) (some 1) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_555 cert_557
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_643 : count (rows.drop 16) (bag 3 0 0 0 1 100) (some 1) =
    (X + 104 * X ^ 2 + 198 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 3 0 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 16 = 4 :: rows.drop 17 := by rfl
  have hm1 : (bag 3 0 0 0 1 100).erase 1 = (bag 2 0 0 0 1 100) := by rfl
  have hc := count_one (rows.drop 16) (rows.drop 17) (bag 3 0 0 0 1 100) (bag 2 0 0 0 1 100) (some 1) 4 1 hr hs hm1 _ cert_556
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_644 : count (rows.drop 15) (bag 4 0 0 0 1 100) (some 4) =
    (X + 104 * X ^ 2 + 198 * X ^ 3 : ℕ[X]) := by
  have hs : (bag 4 0 0 0 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 15 = 4 :: rows.drop 16 := by rfl
  have hm1 : (bag 4 0 0 0 1 100).erase 1 = (bag 3 0 0 0 1 100) := by rfl
  have hc := count_one (rows.drop 15) (rows.drop 16) (bag 4 0 0 0 1 100) (bag 3 0 0 0 1 100) (some 4) 4 1 hr hs hm1 _ cert_643
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_645 : count (rows.drop 14) (bag 4 0 0 1 1 100) (some 4) =
    (X + 113 * X ^ 2 + 906 * X ^ 3 + 495 * X ^ 4 : ℕ[X]) := by
  have hs : (bag 4 0 0 1 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 14 = 4 :: rows.drop 15 := by rfl
  have hm1 : (bag 4 0 0 1 1 100).erase 1 = (bag 3 0 0 1 1 100) := by rfl
  have hm4 : (bag 4 0 0 1 1 100).erase 4 = (bag 4 0 0 0 1 100) := by rfl
  have hc := count_two (rows.drop 14) (rows.drop 15) (bag 4 0 0 1 1 100) (bag 3 0 0 1 1 100) (bag 4 0 0 0 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_642 cert_644
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_646 : count (rows.drop 13) (bag 4 0 0 2 1 100) (some 4) =
    (X + 119 * X ^ 2 + 1438 * X ^ 3 + 2591 * X ^ 4 + 396 * X ^ 5 : ℕ[X]) := by
  have hs : (bag 4 0 0 2 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 13 = 4 :: rows.drop 14 := by rfl
  have hm1 : (bag 4 0 0 2 1 100).erase 1 = (bag 3 0 0 2 1 100) := by rfl
  have hm4 : (bag 4 0 0 2 1 100).erase 4 = (bag 4 0 0 1 1 100) := by rfl
  have hc := count_two (rows.drop 13) (rows.drop 14) (bag 4 0 0 2 1 100) (bag 3 0 0 2 1 100) (bag 4 0 0 1 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_641 cert_645
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_647 : count (rows.drop 12) (bag 4 0 0 3 1 100) (some 4) =
    (X + 123 * X ^ 2 + 1885 * X ^ 3 + 5716 * X ^ 4 + 2781 * X ^ 5 + 99 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 4 0 0 3 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 12 = 4 :: rows.drop 13 := by rfl
  have hm1 : (bag 4 0 0 3 1 100).erase 1 = (bag 3 0 0 3 1 100) := by rfl
  have hm4 : (bag 4 0 0 3 1 100).erase 4 = (bag 4 0 0 2 1 100) := by rfl
  have hc := count_two (rows.drop 12) (rows.drop 13) (bag 4 0 0 3 1 100) (bag 3 0 0 3 1 100) (bag 4 0 0 2 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_640 cert_646
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_648 : count (rows.drop 11) (bag 4 0 0 4 1 100) (some 4) =
    (X + 127 * X ^ 2 + 2338 * X ^ 3 + 9490 * X ^ 4 + 8163 * X ^ 5 + 1091 * X ^ 6 : ℕ[X]) := by
  have hs : (bag 4 0 0 4 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 11 = 4 :: rows.drop 12 := by rfl
  have hm1 : (bag 4 0 0 4 1 100).erase 1 = (bag 3 0 0 4 1 100) := by rfl
  have hm4 : (bag 4 0 0 4 1 100).erase 4 = (bag 4 0 0 3 1 100) := by rfl
  have hc := count_two (rows.drop 11) (rows.drop 12) (bag 4 0 0 4 1 100) (bag 3 0 0 4 1 100) (bag 4 0 0 3 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_639 cert_647
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_649 : count (rows.drop 10) (bag 4 0 0 5 1 100) (some 4) =
    (X + 131 * X ^ 2 + 2797 * X ^ 3 + 13917 * X ^ 4 + 16965 * X ^ 5 + 4268 * X ^ 6 + 99 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 4 0 0 5 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 10 = 4 :: rows.drop 11 := by rfl
  have hm1 : (bag 4 0 0 5 1 100).erase 1 = (bag 3 0 0 5 1 100) := by rfl
  have hm4 : (bag 4 0 0 5 1 100).erase 4 = (bag 4 0 0 4 1 100) := by rfl
  have hc := count_two (rows.drop 10) (rows.drop 11) (bag 4 0 0 5 1 100) (bag 3 0 0 5 1 100) (bag 4 0 0 4 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_638 cert_648
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_650 : count (rows.drop 9) (bag 4 0 0 6 1 100) (some 4) =
    (X + 135 * X ^ 2 + 3262 * X ^ 3 + 19001 * X ^ 4 + 29611 * X ^ 5 + 11026 * X ^ 6 + 594 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 4 0 0 6 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 9 = 4 :: rows.drop 10 := by rfl
  have hm1 : (bag 4 0 0 6 1 100).erase 1 = (bag 3 0 0 6 1 100) := by rfl
  have hm4 : (bag 4 0 0 6 1 100).erase 4 = (bag 4 0 0 5 1 100) := by rfl
  have hc := count_two (rows.drop 9) (rows.drop 10) (bag 4 0 0 6 1 100) (bag 3 0 0 6 1 100) (bag 4 0 0 5 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_637 cert_649
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_651 : count (rows.drop 8) (bag 4 0 0 7 1 100) (some 4) =
    (X + 139 * X ^ 2 + 3733 * X ^ 3 + 24746 * X ^ 4 + 46526 * X ^ 5 + 22865 * X ^ 6 + 1980 * X ^ 7 : ℕ[X]) := by
  have hs : (bag 4 0 0 7 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 8 = 4 :: rows.drop 9 := by rfl
  have hm1 : (bag 4 0 0 7 1 100).erase 1 = (bag 3 0 0 7 1 100) := by rfl
  have hm4 : (bag 4 0 0 7 1 100).erase 4 = (bag 4 0 0 6 1 100) := by rfl
  have hc := count_two (rows.drop 8) (rows.drop 9) (bag 4 0 0 7 1 100) (bag 3 0 0 7 1 100) (bag 4 0 0 6 1 100) (some 4) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_636 cert_650
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_652 : count (rows.drop 7) (bag 4 0 0 8 1 100) (some 3) =
    (5 * X ^ 2 + 616 * X ^ 3 + 10143 * X ^ 4 + 46356 * X ^ 5 + 65050 * X ^ 6 + 25835 * X ^ 7 + 1980 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 4 0 0 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 4) = {1, 4} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 7 = 4 :: rows.drop 8 := by rfl
  have hm1 : (bag 4 0 0 8 1 100).erase 1 = (bag 3 0 0 8 1 100) := by rfl
  have hm4 : (bag 4 0 0 8 1 100).erase 4 = (bag 4 0 0 7 1 100) := by rfl
  have hc := count_two (rows.drop 7) (rows.drop 8) (bag 4 0 0 8 1 100) (bag 3 0 0 8 1 100) (bag 4 0 0 7 1 100) (some 3) 4 1 4 hr hs (by decide) hm1 hm4 _ _ cert_635 cert_651
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_653 : count (rows.drop 6) (bag 4 0 1 8 1 100) (some 3) =
    (9 * X ^ 2 + 1208 * X ^ 3 + 28356 * X ^ 4 + 176700 * X ^ 5 + 335545 * X ^ 6 + 186327 * X ^ 7 + 21780 * X ^ 8 : ℕ[X]) := by
  have hs : (bag 4 0 1 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 6 = 3 :: rows.drop 7 := by rfl
  have hm1 : (bag 4 0 1 8 1 100).erase 1 = (bag 3 0 1 8 1 100) := by rfl
  have hm3 : (bag 4 0 1 8 1 100).erase 3 = (bag 4 0 0 8 1 100) := by rfl
  have hc := count_two (rows.drop 6) (rows.drop 7) (bag 4 0 1 8 1 100) (bag 3 0 1 8 1 100) (bag 4 0 0 8 1 100) (some 3) 3 1 3 hr hs (by decide) hm1 hm3 _ _ cert_634 cert_652
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_654 : count (rows.drop 5) (bag 4 0 2 8 1 100) (some 3) =
    (12 * X ^ 2 + 1690 * X ^ 3 + 46596 * X ^ 4 + 354803 * X ^ 5 + 875199 * X ^ 6 + 741892 * X ^ 7 + 212753 * X ^ 8 + 16830 * X ^ 9 : ℕ[X]) := by
  have hs : (bag 4 0 2 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 5 = 3 :: rows.drop 6 := by rfl
  have hm1 : (bag 4 0 2 8 1 100).erase 1 = (bag 3 0 2 8 1 100) := by rfl
  have hm3 : (bag 4 0 2 8 1 100).erase 3 = (bag 4 0 1 8 1 100) := by rfl
  have hc := count_two (rows.drop 5) (rows.drop 6) (bag 4 0 2 8 1 100) (bag 3 0 2 8 1 100) (bag 4 0 1 8 1 100) (some 3) 3 1 3 hr hs (by decide) hm1 hm3 _ _ cert_633 cert_653
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_655 : count (rows.drop 4) (bag 4 0 3 8 1 100) (some 3) =
    (14 * X ^ 2 + 2022 * X ^ 3 + 60556 * X ^ 4 + 527200 * X ^ 5 + 1635624 * X ^ 6 + 1996979 * X ^ 7 + 915210 * X ^ 8 + 111870 * X ^ 9 : ℕ[X]) := by
  have hs : (bag 4 0 3 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 4 = 3 :: rows.drop 5 := by rfl
  have hm1 : (bag 4 0 3 8 1 100).erase 1 = (bag 3 0 3 8 1 100) := by rfl
  have hm3 : (bag 4 0 3 8 1 100).erase 3 = (bag 4 0 2 8 1 100) := by rfl
  have hc := count_two (rows.drop 4) (rows.drop 5) (bag 4 0 3 8 1 100) (bag 3 0 3 8 1 100) (bag 4 0 2 8 1 100) (some 3) 3 1 3 hr hs (by decide) hm1 hm3 _ _ cert_632 cert_654
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_656 : count (rows.drop 3) (bag 4 0 4 8 1 100) (some 2) =
    (X ^ 2 + 189 * X ^ 3 + 10696 * X ^ 4 + 210921 * X ^ 5 + 1470958 * X ^ 6 + 3728384 * X ^ 7 + 3606623 * X ^ 8 + 1327133 * X ^ 9 + 144045 * X ^ 10 : ℕ[X]) := by
  have hs : (bag 4 0 4 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 3 = 3 :: rows.drop 4 := by rfl
  have hm1 : (bag 4 0 4 8 1 100).erase 1 = (bag 3 0 4 8 1 100) := by rfl
  have hm3 : (bag 4 0 4 8 1 100).erase 3 = (bag 4 0 3 8 1 100) := by rfl
  have hc := count_two (rows.drop 3) (rows.drop 4) (bag 4 0 4 8 1 100) (bag 3 0 4 8 1 100) (bag 4 0 3 8 1 100) (some 2) 3 1 3 hr hs (by decide) hm1 hm3 _ _ cert_631 cert_655
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_657 : count (rows.drop 2) (bag 4 1 4 8 1 100) (some 1) =
    (71 * X ^ 3 + 10819 * X ^ 4 + 370197 * X ^ 5 + 3690726 * X ^ 6 + 13351338 * X ^ 7 + 19812799 * X ^ 8 + 12203258 * X ^ 9 + 2847147 * X ^ 10 + 208395 * X ^ 11 : ℕ[X]) := by
  have hs : (bag 4 1 4 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 2) = {1, 2} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 2 = 2 :: rows.drop 3 := by rfl
  have hm1 : (bag 4 1 4 8 1 100).erase 1 = (bag 3 1 4 8 1 100) := by rfl
  have hm2 : (bag 4 1 4 8 1 100).erase 2 = (bag 4 0 4 8 1 100) := by rfl
  have hc := count_two (rows.drop 2) (rows.drop 3) (bag 4 1 4 8 1 100) (bag 3 1 4 8 1 100) (bag 4 0 4 8 1 100) (some 1) 2 1 2 hr hs (by decide) hm1 hm2 _ _ cert_630 cert_656
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_658 : count (rows.drop 3) (bag 4 0 4 8 1 100) (some 1) =
    (X ^ 2 + 189 * X ^ 3 + 10696 * X ^ 4 + 210921 * X ^ 5 + 1470958 * X ^ 6 + 3728384 * X ^ 7 + 3606623 * X ^ 8 + 1327133 * X ^ 9 + 144045 * X ^ 10 : ℕ[X]) := by
  have hs : (bag 4 0 4 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 3) = {1, 3} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 3 = 3 :: rows.drop 4 := by rfl
  have hm1 : (bag 4 0 4 8 1 100).erase 1 = (bag 3 0 4 8 1 100) := by rfl
  have hm3 : (bag 4 0 4 8 1 100).erase 3 = (bag 4 0 3 8 1 100) := by rfl
  have hc := count_two (rows.drop 3) (rows.drop 4) (bag 4 0 4 8 1 100) (bag 3 0 4 8 1 100) (bag 4 0 3 8 1 100) (some 1) 3 1 3 hr hs (by decide) hm1 hm3 _ _ cert_631 cert_655
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_659 : count (rows.drop 2) (bag 5 0 4 8 1 100) (some 2) =
    (X ^ 2 + 189 * X ^ 3 + 10696 * X ^ 4 + 210921 * X ^ 5 + 1470958 * X ^ 6 + 3728384 * X ^ 7 + 3606623 * X ^ 8 + 1327133 * X ^ 9 + 144045 * X ^ 10 : ℕ[X]) := by
  have hs : (bag 5 0 4 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 2) = {1} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 2 = 2 :: rows.drop 3 := by rfl
  have hm1 : (bag 5 0 4 8 1 100).erase 1 = (bag 4 0 4 8 1 100) := by rfl
  have hc := count_one (rows.drop 2) (rows.drop 3) (bag 5 0 4 8 1 100) (bag 4 0 4 8 1 100) (some 2) 2 1 hr hs hm1 _ cert_658
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_660 : count (rows.drop 1) (bag 5 1 4 8 1 100) (some 1) =
    (72 * X ^ 3 + 11008 * X ^ 4 + 380893 * X ^ 5 + 3901647 * X ^ 6 + 14822296 * X ^ 7 + 23541183 * X ^ 8 + 15809881 * X ^ 9 + 4174280 * X ^ 10 + 352440 * X ^ 11 : ℕ[X]) := by
  have hs : (bag 5 1 4 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 2) = {1, 2} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 1 = 2 :: rows.drop 2 := by rfl
  have hm1 : (bag 5 1 4 8 1 100).erase 1 = (bag 4 1 4 8 1 100) := by rfl
  have hm2 : (bag 5 1 4 8 1 100).erase 2 = (bag 5 0 4 8 1 100) := by rfl
  have hc := count_two (rows.drop 1) (rows.drop 2) (bag 5 1 4 8 1 100) (bag 4 1 4 8 1 100) (bag 5 0 4 8 1 100) (some 1) 2 1 2 hr hs (by decide) hm1 hm2 _ _ cert_657 cert_659
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_661 : count (rows.drop 2) (bag 5 0 4 8 1 100) (some 1) =
    (X ^ 2 + 189 * X ^ 3 + 10696 * X ^ 4 + 210921 * X ^ 5 + 1470958 * X ^ 6 + 3728384 * X ^ 7 + 3606623 * X ^ 8 + 1327133 * X ^ 9 + 144045 * X ^ 10 : ℕ[X]) := by
  have hs : (bag 5 0 4 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 2) = {1} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 2 = 2 :: rows.drop 3 := by rfl
  have hm1 : (bag 5 0 4 8 1 100).erase 1 = (bag 4 0 4 8 1 100) := by rfl
  have hc := count_one (rows.drop 2) (rows.drop 3) (bag 5 0 4 8 1 100) (bag 4 0 4 8 1 100) (some 1) 2 1 hr hs hm1 _ cert_658
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_662 : count (rows.drop 1) (bag 6 0 4 8 1 100) (some 2) =
    (X ^ 2 + 189 * X ^ 3 + 10696 * X ^ 4 + 210921 * X ^ 5 + 1470958 * X ^ 6 + 3728384 * X ^ 7 + 3606623 * X ^ 8 + 1327133 * X ^ 9 + 144045 * X ^ 10 : ℕ[X]) := by
  have hs : (bag 6 0 4 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 2) = {1} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 1 = 2 :: rows.drop 2 := by rfl
  have hm1 : (bag 6 0 4 8 1 100).erase 1 = (bag 5 0 4 8 1 100) := by rfl
  have hc := count_one (rows.drop 1) (rows.drop 2) (bag 6 0 4 8 1 100) (bag 5 0 4 8 1 100) (some 2) 2 1 hr hs hm1 _ cert_661
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private theorem cert_663 : count (rows.drop 0) (bag 6 1 4 8 1 100) none =
    (X ^ 2 + 261 * X ^ 3 + 21704 * X ^ 4 + 591814 * X ^ 5 + 5372605 * X ^ 6 + 18550680 * X ^ 7 + 27147806 * X ^ 8 + 17137014 * X ^ 9 + 4318325 * X ^ 10 + 352440 * X ^ 11 : ℕ[X]) := by
  have hs : (bag 6 1 4 8 1 100).toFinset.filter (fun j => 0 < j ∧ j ≤ 2) = {1, 2} := by
    ext a
    simp only [Finset.mem_filter, Multiset.mem_toFinset, bag, Multiset.mem_coe,
      List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr : rows.drop 0 = 2 :: rows.drop 1 := by rfl
  have hm1 : (bag 6 1 4 8 1 100).erase 1 = (bag 5 1 4 8 1 100) := by rfl
  have hm2 : (bag 6 1 4 8 1 100).erase 2 = (bag 6 0 4 8 1 100) := by rfl
  have hc := count_two (rows.drop 0) (rows.drop 1) (bag 6 1 4 8 1 100) (bag 5 1 4 8 1 100) (bag 6 0 4 8 1 100) none 2 1 2 hr hs (by decide) hm1 hm2 _ _ cert_660 cert_662
  exact hc.trans (by
    simp only [edge, Nat.reduceLT, ite_true, ite_false, pow_zero, pow_one, one_mul]
    ring)

private def examplePolynomial : ℝ[X] :=
  X ^ 2 + 261 * X ^ 3 + 21704 * X ^ 4 + 591814 * X ^ 5 + 5372605 * X ^ 6 + 18550680 * X ^ 7 + 27147806 * X ^ 8 + 17137014 * X ^ 9 + 4318325 * X ^ 10 + 352440 * X ^ 11

private theorem full_polynomial : R board content = examplePolynomial := by
  have ht : (∑ c, content c) = 120 := by decide +kernel
  have hr : List.ofFn board = rows := by decide +kernel
  have hm : (((List.finRange 6).flatMap
      (fun c => List.replicate (content c) (c.val + 1))) : Multiset ℕ) =
      bag 6 1 4 8 1 100 := by decide +kernel
  have h := count_eq_R board content ht
  rw [hr, hm] at h
  change (count (rows.drop 0) (bag 6 1 4 8 1 100) none).map
    (Nat.castRingHom ℝ) = R board content at h
  rw [cert_663] at h
  simpa [examplePolynomial] using h.symm

private theorem laguerre_value :
    examplePolynomial.derivative.eval (-1 / 100 : ℝ) ^ 2 -
      examplePolynomial.eval (-1 / 100 : ℝ) *
        examplePolynomial.derivative.derivative.eval (-1 / 100 : ℝ) =
    -2294232329562528073294509555513 /
      12500000000000000000000000000000000000 := by
  norm_num [examplePolynomial, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow]

/-- The original full polynomial fails to split on a positive 120-row Ferrers board. -/
theorem result : ¬ claim := by
  intro h
  have hp : ∀ i, 0 < board i := by
    intro i
    dsimp [board]
    split_ifs <;> omega
  have hmon : Monotone board := by
    intro i j hij
    have hv : i.val ≤ j.val := hij
    dsimp [board]
    split_ifs <;> omega
  have ht : (∑ c, content c) = 120 := by decide +kernel
  have hs := h 120 6 board content (by decide) hp hmon ht
  have hL := D5.S3.Zeros.Jensen.SourceJensenPositiveExtension.laguerre_splits
    (R board content) hs (-1 / 100)
  rw [full_polynomial] at hL
  change 0 ≤ examplePolynomial.derivative.eval (-1 / 100 : ℝ) ^ 2 -
    examplePolynomial.eval (-1 / 100 : ℝ) *
      examplePolynomial.derivative.derivative.eval (-1 / 100 : ℝ) at hL
  rw [laguerre_value] at hL
  norm_num at hL

#print axioms result

end D5.S3.Combinatorics.Permutation.MultisetRookEulerianRealRootednessRefutation
