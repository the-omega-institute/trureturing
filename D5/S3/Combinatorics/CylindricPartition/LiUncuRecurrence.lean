/- GID: D5/S3/Combinatorics/CylindricPartition/LiUncuRecurrence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CylindricPartition/LiUncuRecurrence
   mirror-E: none(waiver:finite-path-deletion-recurrence)
   anchors: []
   utility: none
   digest: Finite bounded path polynomials satisfy the peak-deletion recurrence. -/

import D5.S3.Combinatorics.CylindricPartition.LiUncuPathSums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CylindricPartition.LiUncu

open Polynomial LiUncuDefs Step

/-- All words of a prescribed length over the three path edges. -/
noncomputable def pathWords : ℕ → Finset (List Step)
  | 0 => by classical exact {[]}
  | L + 1 => by
      classical
      exact (pathWords L).image (up :: ·) ∪ (pathWords L).image (down :: ·) ∪
        (pathWords L).image (flat :: ·)

/-- Genuine nonnegative-length paths, extended by the virtual empty state at negative lengths. -/
noncomputable def refinedPathSum (H : ℕ) (a L : ℤ) (N : ℕ) : ℤ[X] := by
  classical
  exact if L < 0 then (if N = 0 then 1 else 0) else
    ∑ w ∈ pathWords L.toNat,
      if ValidPath H a a w ∧ (peakData w).2.1 + (peakData w).2.2.sum = N then
        X ^ peakWeight 0 w else 0

open Classical in
/-- Peak deletion, including virtual lengths, has the primed Gaussian recurrence. -/
theorem path_deletion_recurrence (H : ℕ) (hH : 1 ≤ H) (a : ℤ)
    (ha : 0 ≤ a) (haH : a ≤ H) (L : ℤ) (hEven : Even L) (N : ℕ)
    (boundary : Bool) (hb : boundary = true ↔ a = H) :
    refinedPathSum H a L N =
      X ^ (N ^ 2 + boundary.toNat * N) *
        ∑ s ∈ Finset.range (N + 1),
          gaussPrime (L - 2 * N - 2 * boundary.toNat + N - s) ((N : ℤ) - s) *
            refinedPathSum (H - 1) (a - boundary.toNat)
              (L - 2 * N - 2 * boundary.toNat) s := by
  classical
  have actual (M N : ℕ) :
    refinedPathSum H a (M + 2 * N + 2 * boundary.toNat : ℕ) N =
      X ^ (N ^ 2 + boundary.toNat * N) *
        ∑ q ∈ (pathWords M).filter
          (ValidPath (H - 1) (a - boundary.toNat) (a - boundary.toNat)),
          if (peakData q).2.1 + (peakData q).2.2.sum ≤ N then
            X ^ peakWeight 0 q *
              gauss (M + (N - ((peakData q).2.1 + (peakData q).2.2.sum)))
                (N - ((peakData q).2.1 + (peakData q).2.2.sum))
          else 0 := by
    have words_mem (L : ℕ) (w : List Step) : w ∈ pathWords L ↔ w.length = L := by
      induction L generalizing w with
      | zero => simp [pathWords]
      | succ L ih =>
          cases w with
          | nil => simp [pathWords]
          | cons s w => cases s <;> simp [pathWords, ih]
    have shape (q : List Step) (t : ℕ) (ts : List ℕ) (hi : Insertible q t ts) :
        ts.length = q.length := by
      induction q generalizing t ts with
      | nil => cases ts <;> simp_all [Insertible]
      | cons s q ih =>
          cases ts with
          | nil => simp [Insertible] at hi
          | cons t ts => simpa using congrArg Nat.succ (ih t ts hi.2)
    have encode (q : List Step) (t : ℕ) (ts : List ℕ)
        (hi : Insertible q t ts) (hn : t + ts.sum = N) :
        ∃ v : Fin (q.length + 1) → Fin (N + 1),
          (Insertible q (v 0).val (List.ofFn (fun j : Fin q.length => (v j.succ).val)) ∧
            ∑ j, (v j).val = N) ∧
          (v 0).val = t ∧ List.ofFn (fun j : Fin q.length => (v j.succ).val) = ts := by
      let l := t :: ts
      have hl : l.length = q.length + 1 := by simp [l, shape q t ts hi]
      have hs : l.sum = N := by simpa [l] using hn
      let v : Fin (q.length + 1) → Fin (N + 1) := fun j =>
        ⟨l[j.val]'(by rw [hl]; exact j.isLt), by
          have h := List.le_sum_of_mem
            (List.getElem_mem (l := l) (n := j.val) (by rw [hl]; exact j.isLt))
          rw [hs] at h
          omega⟩
      have hv : List.ofFn (fun j => (v j).val) = l := by
        apply List.ext_getElem
        · simp [hl]
        · intro j hj hj'
          simp only [List.getElem_ofFn]
          rfl
      have hv' := hv
      rw [List.ofFn_succ] at hv'
      have hhead := (List.cons.inj hv').1
      have htail := (List.cons.inj hv').2
      refine ⟨v, ⟨?_, ?_⟩, hhead, htail⟩
      · rw [hhead, htail]
        exact hi
      · rw [← List.sum_ofFn, hv, hs]
    have append_valid (c d e : ℤ) (w z : List Step)
        (hw : ValidPath H c d w) (hz : ValidPath H d e z) :
        ValidPath H c e (w ++ z) := by
      induction w generalizing c with
      | nil => simpa only [hw.2.2, List.nil_append] using hz
      | cons s w ih =>
          cases s with
          | up => exact ⟨hw.1, hw.2.1, ih (c + 1) hw.2.2⟩
          | down => exact ⟨hw.1, hw.2.1, ih (c - 1) hw.2.2⟩
          | flat => exact ⟨hw.1, ih c hw.2⟩
    have append_insert (q : List Step) (t : ℕ) (ts : List ℕ) (hi : Insertible q t ts) :
        insertPeaks (q ++ [up]) t (ts ++ [0]) = insertPeaks q t ts ++ [up] := by
      induction q generalizing t ts with
      | nil =>
          cases ts with
          | nil => simp [insertPeaks]
          | cons t ts => simp [Insertible] at hi
      | cons s q ih =>
          cases ts with
          | nil => simp [Insertible] at hi
          | cons t' ts =>
              simp only [List.cons_append, insertPeaks]
              rw [ih t' ts hi.2]
              simp [List.append_assoc]
    have boundary_insert (q : List Step) (t : ℕ) (ts : List ℕ) (hi : Insertible q t ts) :
        insertPeaks (down :: (q ++ [up])) 0 (t :: (ts ++ [0])) =
          down :: (insertPeaks q t ts ++ [up]) := by
      simp only [insertPeaks, List.replicate_zero, List.flatten_nil, List.nil_append]
      rw [append_insert q t ts hi]
    have count_append (w : List Step) :
        (peakData (w ++ [up])).2.1 + (peakData (w ++ [up])).2.2.sum =
          (peakData w).2.1 + (peakData w).2.2.sum := by
      induction hn : w.length using Nat.strong_induction_on generalizing w with
      | h n ih =>
          have smaller (v : List Step) (hv : v.length < w.length) :
              (peakData (v ++ [up])).2.1 + (peakData (v ++ [up])).2.2.sum =
                (peakData v).2.1 + (peakData v).2.2.sum := ih v.length (by omega) v rfl
          cases w with
          | nil => rfl
          | cons s w =>
              cases s with
              | down => simpa [peakData] using smaller w (by simp)
              | flat => simpa [peakData] using smaller w (by simp)
              | up =>
                  cases w with
                  | nil => rfl
                  | cons s w =>
                      cases s with
                      | down =>
                          simpa [peakData, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                            congrArg (fun n : ℕ => n + 1) (smaller w (by simp))
                      | up => simpa [peakData] using smaller (up :: w) (by simp)
                      | flat => simpa [peakData] using smaller (flat :: w) (by simp)
    obtain ⟨scan, hscan, hinv, hlen, _⟩ := peak_deletion_bijection
    have reconstruct (w : List Step) :
        insertPeaks (peakData w).1 (peakData w).2.1 (peakData w).2.2 = w := by
      have h := hinv (scan w)
      rw [scan.symm_apply_apply, hscan w] at h
      exact h.symm
    have scan_length (w : List Step) :
        w.length = (peakData w).1.length +
          2 * ((peakData w).2.1 + (peakData w).2.2.sum) := by
      have h := hlen (scan w)
      rw [scan.symm_apply_apply, hscan w] at h
      exact h
    have inserted (q : List Step)
        (v : {v : Fin (q.length + 1) → Fin (N + 1) //
          Insertible q (v 0).val (List.ofFn (fun j : Fin q.length => (v j.succ).val)) ∧
            ∑ j, (v j).val = N}) :
        let w := insertPeaks q (v.val 0).val
          (List.ofFn (fun j : Fin q.length => (v.val j.succ).val))
        w.length = q.length + 2 * N ∧
          (peakData w).2.1 + (peakData w).2.2.sum = N := by
      let d : {d : List Step × ℕ × List ℕ // Insertible d.1 d.2.1 d.2.2} :=
        ⟨(q, (v.val 0).val, List.ofFn (fun j : Fin q.length => (v.val j.succ).val)),
          v.property.1⟩
      have hd := congrArg Subtype.val (scan.apply_symm_apply d)
      rw [hscan (scan.symm d), hinv d] at hd
      have hl := hlen d
      rw [hinv d] at hl
      have hn : (v.val 0).val + ∑ j : Fin q.length, (v.val j.succ).val = N := by
        simpa only [Fin.sum_univ_succ] using v.property.2
      dsimp [d] at hd hl ⊢
      rw [List.sum_ofFn, hn] at hl
      refine ⟨hl, ?_⟩
      rw [hd, List.sum_ofFn, hn]
    let L := M + 2 * N + 2 * boundary.toNat
    let S := (pathWords M).filter
      (ValidPath (H - 1) (a - boundary.toNat) (a - boundary.toNat))
    let A := (pathWords L).filter (fun w =>
      ValidPath H a a w ∧ (peakData w).2.1 + (peakData w).2.2.sum = N)
    have sets : A = S.biUnion (fun q => insertionWords q N boundary) := by
      ext w
      constructor
      · intro hw
        obtain ⟨hwlen, hw, hn⟩ := Finset.mem_filter.mp hw
        have hwlen := (words_mem L w).mp hwlen
        cases hbd : boundary with
        | false =>
            have hat : a < H := by
              have hne : a ≠ H := by
                intro he
                have ht := hb.mpr he
                rw [hbd] at ht
                contradiction
              omega
            have hi := (scan w).property
            rw [hscan w] at hi
            have hq := peak_deletion_interior H hH a a hat hat w hw
            have hlength := scan_length w
            have hm : (peakData w).1.length = M := by
              dsimp [L] at hwlen
              rw [hbd] at hwlen
              simp only [Bool.toNat_false, mul_zero, add_zero] at hwlen
              omega
            obtain ⟨v, hv, ht, hts⟩ := encode _ _ _ hi hn
            apply Finset.mem_biUnion.mpr
            refine ⟨(peakData w).1, ?_, ?_⟩
            · apply Finset.mem_filter.mpr
              exact ⟨(words_mem M _).mpr hm, by simpa [hbd] using hq⟩
            · apply Finset.mem_image.mpr
              refine ⟨⟨v, hv⟩, Finset.mem_univ _, ?_⟩
              simpa only [hbd, Bool.false_eq_true, ite_false, ht, hts] using reconstruct w
        | true =>
            have hat : a = H := hb.mp hbd
            subst a
            have hne : w ≠ [] := by
              intro he
              rw [he] at hwlen
              dsimp [L] at hwlen
              rw [hbd] at hwlen
              simp at hwlen
            obtain ⟨q, t, ts, hd, hq, hi⟩ := peak_deletion_ceiling H hH w hne hw
            have hlength := scan_length w
            rw [hd] at hlength hn
            simp only [List.length_cons, List.length_nil, List.length_append,
              List.sum_cons, List.sum_nil, List.sum_append, add_zero, zero_add]
                at hlength hn
            have hm : q.length = M := by
              dsimp [L] at hwlen
              rw [hbd] at hwlen
              simp only [Bool.toNat_true] at hwlen
              omega
            obtain ⟨v, hv, ht, hts⟩ := encode q t ts hi hn
            apply Finset.mem_biUnion.mpr
            refine ⟨q, ?_, ?_⟩
            · apply Finset.mem_filter.mpr
              exact ⟨(words_mem M q).mpr hm, by simpa [hbd] using hq⟩
            · apply Finset.mem_image.mpr
              refine ⟨⟨v, hv⟩, Finset.mem_univ _, ?_⟩
              have hr := reconstruct w
              rw [hd, boundary_insert q t ts hi] at hr
              simpa only [hbd, ite_true, ht, hts] using hr
      · intro hw
        obtain ⟨q, hq, hw⟩ := Finset.mem_biUnion.mp hw
        obtain ⟨hqm, hq⟩ := Finset.mem_filter.mp hq
        have hqm := (words_mem M q).mp hqm
        obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hw
        have hstat := inserted q v
        have hin := peak_insertion_valid H hH (a - boundary.toNat) (a - boundary.toNat)
          q (v.val 0).val (List.ofFn (fun j : Fin q.length => (v.val j.succ).val))
          v.property.1 hq
        apply Finset.mem_filter.mpr
        cases hbd : boundary with
        | false =>
            simp only [hbd, Bool.false_eq_true, ite_false, Bool.toNat_false, Int.ofNat_zero,
              sub_zero] at hin ⊢
            refine ⟨(words_mem L _).mpr ?_, hin, hstat.2⟩
            dsimp [L]
            rw [hbd, hstat.1, hqm]
            simp
        | true =>
            have hat : a = H := hb.mp hbd
            subst a
            simp only [hbd, ite_true, Bool.toNat_true, Int.ofNat_one] at hin ⊢
            have hend : ValidPath H ((H : ℤ) - 1) H [up] := by
              simp only [ValidPath]
              refine ⟨by omega, by omega, by omega, by omega, ?_⟩
              omega
            refine ⟨(words_mem L _).mpr ?_, ?_, ?_⟩
            · simp only [List.length_cons, List.length_nil, List.length_append]
              dsimp [L]
              rw [hbd, hstat.1, hqm]
              simp only [Bool.toNat_true]
            · exact ⟨by omega, le_refl _, append_valid _ _ _ _ _ hin hend⟩
            · simp only [peakData, List.sum_cons, zero_add]
              rw [count_append]
              exact hstat.2
    have sum_actual : refinedPathSum H a L N = ∑ w ∈ A, (X : ℤ[X]) ^ peakWeight 0 w := by
      unfold refinedPathSum
      rw [if_neg (by dsimp [L]; omega)]
      simp only [Int.toNat_natCast]
      exact (Finset.sum_filter _ _).symm
    rw [sum_actual, sets]
    have h := peak_deletion_weighted_sum S N 0 boundary
    simp only [zero_add] at h
    refine h.trans ?_
    congr 1
    apply Finset.sum_congr rfl
    intro q hq
    have hqm := (words_mem M q).mp (Finset.mem_filter.mp hq).1
    rw [hqm]
  have words_mem (L : ℕ) (w : List Step) : w ∈ pathWords L ↔ w.length = L := by
    induction L generalizing w with
    | zero => simp [pathWords]
    | succ L ih =>
        cases w with
        | nil => simp [pathWords]
        | cons s w => cases s <;> simp [pathWords, ih]
  have prime_nat (m d : ℕ) :
      gaussPrime (m + d : ℕ) (d : ℤ) = gauss (m + d) d := by
    cases d with
    | zero => simp [gaussPrime, gauss]
    | succ d =>
        rw [gaussPrime, if_neg (by omega), gaussInt, if_neg (by omega)]
        simp only [Int.toNat_natCast]
  have prime_outside (A B : ℤ) (hB : 0 < B) (hAB : A < B) : gaussPrime A B = 0 := by
    rw [gaussPrime, if_neg (ne_of_gt hB)]
    by_cases hA : A < 0
    · simp [gaussInt, hA]
    · rw [gaussInt, if_neg (by omega)]
      exact gauss_zero_of_lt A.toNat B.toNat (by omega)
  let M : ℤ := L - 2 * N - 2 * boundary.toNat
  change refinedPathSum H a L N = X ^ (N ^ 2 + boundary.toNat * N) *
    ∑ s ∈ Finset.range (N + 1), gaussPrime (M + N - s) ((N : ℤ) - s) *
      refinedPathSum (H - 1) (a - boundary.toNat) M s
  by_cases hM : 0 ≤ M
  · let S := (pathWords M.toNat).filter
      (ValidPath (H - 1) (a - boundary.toNat) (a - boundary.toNat))
    have hl : L = (M.toNat + 2 * N + 2 * boundary.toNat : ℕ) := by
      dsimp [M] at hM ⊢
      omega
    have hp : refinedPathSum H a L N = X ^ (N ^ 2 + boundary.toNat * N) *
        ∑ q ∈ S, if (peakData q).2.1 + (peakData q).2.2.sum ≤ N then
          X ^ peakWeight 0 q *
            gauss (M.toNat + (N - ((peakData q).2.1 + (peakData q).2.2.sum)))
              (N - ((peakData q).2.1 + (peakData q).2.2.sum)) else 0 := by
      rw [hl]
      exact actual M.toNat N
    rw [hp]
    congr 1
    have lower (s : ℕ) : refinedPathSum (H - 1) (a - boundary.toNat) M s =
        ∑ q ∈ S, if (peakData q).2.1 + (peakData q).2.2.sum = s then
          (X : ℤ[X]) ^ peakWeight 0 q else 0 := by
      unfold refinedPathSum
      rw [if_neg (by omega)]
      simp only [S, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q _
      by_cases hv : ValidPath (H - 1) (a - boundary.toNat) (a - boundary.toNat) q
      · simp only [hv, true_and, ite_true]
      · simp only [hv, false_and, ite_false]
    simp_rw [lower, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    let c := (peakData q).2.1 + (peakData q).2.2.sum
    change (if c ≤ N then X ^ peakWeight 0 q * gauss (M.toNat + (N - c)) (N - c)
      else 0) = ∑ s ∈ Finset.range (N + 1),
        gaussPrime (M + N - s) ((N : ℤ) - s) *
          (if c = s then X ^ peakWeight 0 q else 0)
    by_cases hc : c ≤ N
    · rw [if_pos hc, Finset.sum_eq_single c]
      · have ht : M + N - c = (M.toNat + (N - c) : ℕ) := by omega
        have hd : (N : ℤ) - c = ((N - c : ℕ) : ℤ) := by omega
        rw [ht, hd, prime_nat]
        simp only [ite_true, mul_comm]
      · intro s _ hsc
        simp only [if_neg (Ne.symm hsc), mul_zero]
      · simp [hc]
    · rw [if_neg hc]
      symm
      apply Finset.sum_eq_zero
      intro s hs
      have hsn := Finset.mem_range.mp hs
      have hcs : c ≠ s := by omega
      simp only [if_neg hcs, mul_zero]
  · have hm : M < 0 := by omega
    have hs :
        (∑ s ∈ Finset.range (N + 1), gaussPrime (M + N - s) ((N : ℤ) - s) *
          refinedPathSum (H - 1) (a - boundary.toNat) M s) =
            if N = 0 then 1 else 0 := by
      rw [Finset.sum_eq_single N]
      · simp [gaussPrime, refinedPathSum, hm]
      · intro s hsr hsn
        have hsr := Finset.mem_range.mp hsr
        have hpos : 0 < (N : ℤ) - s := by omega
        rw [prime_outside _ _ hpos (by omega), zero_mul]
      · simp
    have hw : refinedPathSum H a L N = if N = 0 then 1 else 0 := by
      by_cases hL : L < 0
      · simp [refinedPathSum, hL]
      · have hL0 : 0 ≤ L := by omega
        by_cases hz : L = 0
        · rw [hz]
          simp [refinedPathSum, pathWords, ValidPath, peakData, peakWeight, ha, haH, eq_comm]
        · have hpL : 0 < L := by omega
          have hN : N ≠ 0 := by
            obtain ⟨t, ht⟩ := hEven
            have hδ : boundary.toNat ≤ 1 := by cases boundary <;> decide
            dsimp [M] at hm
            omega
          rw [if_neg hN, refinedPathSum, if_neg hL]
          apply Finset.sum_eq_zero
          intro w hw
          have hlenw := (words_mem L.toNat w).mp hw
          by_cases hv : ValidPath H a a w ∧
              (peakData w).2.1 + (peakData w).2.2.sum = N
          · exfalso
            obtain ⟨scan, hscan, _, hlen, _⟩ := peak_deletion_bijection
            have hlen' := hlen (scan w)
            rw [scan.symm_apply_apply, hscan w, hv.2] at hlen'
            cases hbd : boundary with
            | false =>
                dsimp [M] at hm
                rw [hbd] at hm
                simp only [Bool.toNat_false, Nat.cast_zero, mul_zero, sub_zero] at hm
                omega
            | true =>
                have hat : a = H := hb.mp hbd
                have hne : w ≠ [] := by intro he; subst w; simp at hlenw; omega
                obtain ⟨q, t, ts, hd, _, _⟩ :=
                  peak_deletion_ceiling H hH w hne (by simpa [hat] using hv.1)
                rw [hd] at hlen'
                simp only [List.length_cons, List.length_append, List.length_nil] at hlen'
                dsimp [M] at hm
                rw [hbd] at hm
                simp only [Bool.toNat_true] at hm
                omega
          · exact if_neg hv
    rw [hw, hs]
    by_cases hN : N = 0
    · subst N
      simp
    · simp only [if_neg hN, mul_zero]

/-- At height zero, the unique genuine path is the flat word and has no peaks. -/
theorem path_zero_height (L : ℤ) (N : ℕ) :
    refinedPathSum 0 0 L N = if N = 0 then 1 else 0 := by
  classical
  have words_mem (L : ℕ) (w : List Step) : w ∈ pathWords L ↔ w.length = L := by
    induction L generalizing w with
    | zero => simp [pathWords]
    | succ L ih =>
        cases w with
        | nil => simp [pathWords]
        | cons s w => cases s <;> simp [pathWords, ih]
  have only_flat (w : List Step) (hw : ValidPath 0 0 0 w) :
      w = List.replicate w.length flat := by
    induction w with
    | nil => rfl
    | cons s w ih =>
        cases s with
        | up => have h := hw.2.1; omega
        | down => have h := hw.1; omega
        | flat =>
            have ht : ValidPath 0 0 0 w := hw.2
            simpa [List.replicate_succ] using congrArg (flat :: ·) (ih ht)
  have valid_flat (m : ℕ) : ValidPath 0 0 0 (List.replicate m flat) := by
    induction m with
    | zero => simp [ValidPath]
    | succ m ih => simpa [List.replicate_succ, ValidPath] using ih
  have statistics (m offset : ℕ) :
      (peakData (List.replicate m flat)).2.1 +
          (peakData (List.replicate m flat)).2.2.sum = 0 ∧
        peakWeight offset (List.replicate m flat) = 0 := by
    induction m generalizing offset with
    | zero => simp [peakData, peakWeight]
    | succ m ih =>
        simpa [List.replicate_succ, peakData, peakWeight] using ih (offset + 1)
  by_cases hL : L < 0
  · simp [refinedPathSum, hL]
  · rw [refinedPathSum, if_neg hL, Finset.sum_eq_single (List.replicate L.toNat flat)]
    · have hs := statistics L.toNat 0
      simp only [valid_flat, true_and, hs.1, hs.2, pow_zero]
      simp only [eq_comm]
    · intro w hw hne
      by_cases hv : ValidPath 0 0 0 w
      · have he := only_flat w hv
        rw [(words_mem L.toNat w).mp hw] at he
        exact (hne he).elim
      · simp only [hv, false_and, ite_false]
    · intro hnot
      exact (hnot ((words_mem L.toNat _).mpr List.length_replicate)).elim

end D5.S3.Combinatorics.CylindricPartition.LiUncu
