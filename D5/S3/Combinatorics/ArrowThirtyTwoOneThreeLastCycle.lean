/- GID: D5/S3/Combinatorics/ArrowThirtyTwoOneThreeLastCycle
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowThirtyTwoOneThreeLastCycle
   mirror-E: none(waiver:positive-last-cycle-bijection-for-the-arrow-pattern-32-1-to-3)
   anchors: []
   utility: none
   digest: Joining the independent gap prefix and a Catalan final-cycle order is bijective onto the positive last-cycle strata. -/

import D5.S3.Combinatorics.ArrowThirtyTwoOneThreeGapCode

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowThirtyTwoOneThreeLastCycle

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArrowThirtyTwoOneThreeCatalan
open D5.S3.Combinatorics.ArrowThirtyTwoOneThreeDecomp
open D5.S3.Combinatorics.ArrowThirtyTwoOneThreeBijection
open D5.S3.Combinatorics.ArrowThirtyTwoOneThreeBijectionGaps
open D5.S3.Combinatorics.ArrowThirtyTwoOneThreeGapCode

noncomputable section

/-- The stratum with `k` letters after the maximum, which starts the final cycle. -/
def Stratum (n k : ℕ) :=
  {p : List ℕ // p ∈ avoiders (n + 1) [3, 2] [(1, 3)] 3 ∧ p.idxOf (n + 1) + k = n}

/-- The allowed orders of a selected set: its maximum is last, and it avoids `132`. -/
def CycleOrders (S : List ℕ) :=
  {w : List ℕ // w.Perm S ∧ (∀ x ∈ w, x ≤ w.getLastD 0) ∧ ¬ Has132 w}

/-- Place the fresh maximum between the gap prefix and the chosen last-cycle word. -/
def joinLastCycle (n k : ℕ) :
    (Σ d : GapData n (k + 1), CycleOrders d.val.1) → Stratum n (k + 1) := by
  intro z
  let d := z.1
  let q := d.val.2
  let w := z.2.val
  have hwperm := z.2.property.1
  have hwmax : ∀ x ∈ w, x ≤ w.getLastD 0 := z.2.property.2.1
  have hw132 : ¬ Has132 w := z.2.property.2.2
  have hqperm : (q ++ w).Perm (List.range' 1 n) :=
    (List.Perm.append_left q hwperm).trans d.property.2.2.1
  have hpperm : (q ++ (n + 1) :: w).Perm (List.range' 1 (n + 1)) := by
    have h := List.perm_middle.trans (hqperm.cons (n + 1))
    have h' : ((n + 1) :: List.range' 1 n).Perm (List.range' 1 (n + 1)) := by
      rw [List.range'_1_concat]
      simpa [Nat.add_comm] using (List.perm_middle (l₁ := List.range' 1 n) (l₂ := [])).symm
    exact h.trans h'
  have hwlen : w.length = k + 1 := hwperm.length_eq.trans d.property.2.1
  have hwne : w ≠ [] := by intro h; simp [h] at hwlen
  let b := w.getLast hwne
  let u := w.dropLast
  have hlast : w.getLast? = some b := List.getLast?_eq_some_getLast hwne
  have hsplit : u ++ [b] = w :=
    List.dropLast_append_getLast? (l := w) b (by simp [hlast])
  have hwnd : w.Nodup := (hqperm.nodup_iff.mpr List.nodup_range').of_append_right
  have hbu : ∀ x ∈ u, x < b := by
    intro x hx
    have hxw : x ∈ w := by rw [← hsplit]; simp [hx]
    have hle : x ≤ b := by simpa [hlast] using hwmax x hxw
    have hne : x ≠ b := by
      intro heq
      have hnd : (u ++ [b]).Nodup := hsplit.symm ▸ hwnd
      exact (List.nodup_append'.mp hnd).2.2 (heq ▸ hx) (by simp)
    omega
  have hcross : ∀ a ∈ q, ∀ c ∈ u ++ [b], ¬ (a < c ∧ c < hat q a) := by
    intro a ha c hc hbad
    have hs := d.property.2.2.2 a c ha hbad.1 hbad.2
    have hcq : c ∈ q := hs.subset (by simp)
    have hcw : c ∈ w := by rwa [hsplit] at hc
    exact (List.nodup_append'.mp (hqperm.nodup_iff.mpr List.nodup_range')).2.2 hcq hcw
  have hp : q ++ (n + 1) :: w ∈ avoiders (n + 1) [3, 2] [(1, 3)] 3 := by
    rw [← hsplit]
    exact construct_avoider_of_local_conditions n q u b (hsplit.symm ▸ hpperm)
      d.property.2.2.2 hcross hbu
      (fun h => hw132 (by rw [← hsplit]; exact (has132_append_max_iff u b hbu).mpr h))
  have hmnot : n + 1 ∉ q := by
    intro hm
    obtain ⟨j, hj, heq⟩ := List.mem_range'.mp (hqperm.mem_iff.mp
      (List.mem_append.mpr (Or.inl hm)))
    omega
  have hlength : q.length + (k + 1) = n := by
    simpa only [List.length_append, List.length_range', hwlen] using hqperm.length_eq
  refine ⟨q ++ (n + 1) :: w, hp, ?_⟩
  rw [List.idxOf_append_of_notMem hmnot]
  simpa using hlength

/-- Last-cycle extraction recovers the prefix, the selected set in increasing
order, and its chosen Catalan order; joining recovers the original permutation. -/
theorem joinLastCycle_bijective (n k : ℕ) : Function.Bijective (joinLastCycle n k) := by
  classical
  have hidx (z : Σ d : GapData n (k + 1), CycleOrders d.val.1) :
      (joinLastCycle n k z).val.idxOf (n + 1) = z.1.val.2.length := by
    have hmnot : n + 1 ∉ z.1.val.2 := by
      intro hm
      obtain ⟨j, hj, heq⟩ := List.mem_range'.mp (z.1.property.2.2.1.mem_iff.mp
        (List.mem_append.mpr (Or.inl hm)))
      omega
    change (z.1.val.2 ++ (n + 1) :: z.2.val).idxOf (n + 1) = _
    simp [List.idxOf_append_of_notMem hmnot]
  constructor
  · intro z z' heq
    obtain ⟨d, w⟩ := z
    obtain ⟨d', w'⟩ := z'
    have hlen : d.val.2.length = d'.val.2.length := by
      have h := congrArg (fun p : Stratum n (k + 1) => p.val.idxOf (n + 1)) heq
      simpa only [hidx] using h
    have hp : d.val.2 ++ (n + 1) :: w.val = d'.val.2 ++ (n + 1) :: w'.val :=
      congrArg Subtype.val heq
    have hq : d.val.2 = d'.val.2 := by
      have h := congrArg (List.take d.val.2.length) hp
      simpa [← hlen] using h
    have hw : w.val = w'.val := by
      rw [hq] at hp
      exact List.cons.inj (List.append_cancel_left hp) |>.2
    have hSperm : d.val.1.Perm d'.val.1 :=
      w.property.1.symm.trans (hw ▸ w'.property.1)
    have hS : d.val.1 = d'.val.1 :=
      hSperm.eq_of_pairwise (fun a b _ _ hab hba => by omega) d.property.1 d'.property.1
    have hdd : d = d' := Subtype.ext (Prod.ext hS hq)
    subst d'
    have hww : w = w' := Subtype.ext hw
    subst w'
    rfl
  · rintro ⟨p, hp, hstr⟩
    have hpmem : n + 1 ∈ p := hp.1.mem_iff.mpr (by
      apply List.mem_range'.mpr; exact ⟨n, by omega, by omega⟩)
    let j := p.idxOf (n + 1)
    let q := p.take j
    let w := p.drop (j + 1)
    have hj : j < p.length := List.idxOf_lt_length_of_mem hpmem
    have hsplit : p = q ++ (n + 1) :: w := by
      calc
        p = p.take j ++ p.drop j := (List.take_append_drop j p).symm
        _ = p.take j ++ p[j] :: p.drop (j + 1) := by rw [List.drop_eq_getElem_cons hj]
        _ = q ++ (n + 1) :: w := by rw [List.getElem_idxOf hj]
    have hp' : q ++ (n + 1) :: w ∈ avoiders (n + 1) [3, 2] [(1, 3)] 3 := hsplit ▸ hp
    have hnd : (q ++ (n + 1) :: w).Nodup := hp'.1.nodup_iff.mpr List.nodup_range'
    have hwnd := hnd.of_append_right.of_cons
    have hplen : p.length = n + 1 := by simpa using hp.1.length_eq
    have hwlen : w.length = k + 1 := by simp [w, j, List.length_drop, hplen]; omega
    have hwne : w ≠ [] := by intro h; simp [h] at hwlen
    let b := w.getLast hwne
    let u := w.dropLast
    have hlast : w.getLast? = some b := List.getLast?_eq_some_getLast hwne
    have hwsplit : u ++ [b] = w :=
      List.dropLast_append_getLast? (l := w) b (by simp [hlast])
    have hbu := final_cycle_strict_max_and_avoid132 n q u b (hwsplit.symm ▸ hp')
    have hmax : ∀ x ∈ w, x ≤ w.getLastD 0 := by
      intro x hx
      rw [← hwsplit] at hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · simpa [hlast] using (hbu.1 x hx).le
      · simp [hlast]
    let S := w.toFinset.sort
    have hSsort : S.Pairwise (· < ·) := w.toFinset.sortedLT_sort.pairwise
    have hSperm : S.Perm w :=
      (w.toFinset.sort_perm_toList (· ≤ ·)).trans (List.toFinset_toList hwnd)
    have hqwperm : (q ++ w).Perm (List.range' 1 n) := by
      have h := List.perm_middle.symm.trans hp'.1
      rw [List.range'_1_concat] at h
      have hr : (List.range' 1 n ++ [1 + n]).Perm ((n + 1) :: List.range' 1 n) := by
        simp [Nat.add_comm]
      exact (h.trans hr).cons_inv
    let d : GapData n (k + 1) :=
      ⟨⟨S, q⟩, hSsort, hSperm.length_eq.trans hwlen,
        (List.Perm.append_left q hSperm).trans hqwperm,
        prefix_edge_condition_of_avoider n q w hp'⟩
    let v : CycleOrders d.val.1 :=
      ⟨w, hSperm.symm, hmax, final_cycle_avoid132 n q w hp'⟩
    refine ⟨⟨d, v⟩, ?_⟩
    apply Subtype.ext
    exact hsplit.symm

end
end D5.S3.Combinatorics.ArrowThirtyTwoOneThreeLastCycle
