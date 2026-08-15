/- GID: D5/S0/Computability/Coding/KraftConverse
   generality: G
   mirror-B: D5/B/S0/Computability/Coding/KraftConverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Integer-scaled Kraft bounds construct prefix-free codes with exact lengths. -/

import D5.S0.Computability.Coding.PrefixFreeCode
import Mathlib.Data.Multiset.Sort

namespace D5.S0.Computability.Coding.KraftConverse

open D5.S0.Computability.Coding.PrefixFreeCode

private theorem sum_map_mul_right (xs : List ℕ) (f : ℕ → ℕ) (c : ℕ) :
    (xs.map fun x => f x * c).sum = (xs.map f).sum * c := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, add_mul]

private def prefixSuffixEmbedding {u : List (Fin 2)} {l : ℕ} :
    {v : List.Vector (Fin 2) l // u <+: v.1} ↪ List.Vector (Fin 2) (l - u.length) where
  toFun v := ⟨v.1.1.drop u.length, by simp [v.1.2]⟩
  inj' := by
    intro v w hd
    apply Subtype.ext
    apply Subtype.ext
    rw [List.prefix_append_drop v.2, List.prefix_append_drop w.2]
    congr 1
    exact congrArg Subtype.val hd

private theorem card_prefix_vectors_le {u : List (Fin 2)} {l : ℕ} :
    (Finset.univ.filter fun v : List.Vector (Fin 2) l => u <+: v.1).card ≤
      2 ^ (l - u.length) := by
  have hcard := Fintype.card_le_of_embedding (prefixSuffixEmbedding (u := u) (l := l))
  rw [← Fintype.card_subtype]
  simpa [card_vector] using hcard

private theorem exists_vector_avoiding_prefixes (code : List (List (Fin 2))) (l : ℕ)
    (hcode : code.Nodup)
    (hbudget : (code.map fun u => 2 ^ (l - u.length)).sum < 2 ^ l) :
    ∃ w : List.Vector (Fin 2) l, ∀ u ∈ code, ¬u <+: w.1 := by
  classical
  let bad : Finset (List.Vector (Fin 2) l) :=
    code.toFinset.biUnion fun u => Finset.univ.filter fun v => u <+: v.1
  have hbad : bad.card < (Finset.univ : Finset (List.Vector (Fin 2) l)).card := by
    calc
      bad.card ≤ ∑ u ∈ code.toFinset,
          (Finset.univ.filter fun v : List.Vector (Fin 2) l => u <+: v.1).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ u ∈ code.toFinset, 2 ^ (l - u.length) := by
        exact Finset.sum_le_sum fun _ _ => card_prefix_vectors_le
      _ = (code.map fun u => 2 ^ (l - u.length)).sum := by
        simpa using List.sum_toFinset (l := code) hcode (f := fun u => 2 ^ (l - u.length))
      _ < 2 ^ l := hbudget
      _ = (Finset.univ : Finset (List.Vector (Fin 2) l)).card := by
        simp [card_vector]
  obtain ⟨w, hw⟩ := Finset.sdiff_nonempty_of_card_lt_card hbad
  refine ⟨w, fun u hu hup => ?_⟩
  exact (Finset.mem_sdiff.mp hw).2
    (Finset.mem_biUnion.mpr ⟨u, by simpa using hu, Finset.mem_filter.mpr ⟨by simp, hup⟩⟩)

/-- Finite binary Kraft converse in exact integer-scaled form. If all prescribed lengths are at
most `N` and their depth-`N` cylinder capacities total at most `2^N`, then a prefix-free binary
code realizes exactly those lengths. Repeated lengths are retained by the `Nodup` code list. -/
private theorem exists_sorted_isPrefixFree_code_of_kraft (lengths : List ℕ) (N : ℕ)
    (hsorted : lengths.Pairwise (· ≤ ·)) (hdepth : ∀ l ∈ lengths, l ≤ N)
    (hKraft : (lengths.map fun l => 2 ^ (N - l)).sum ≤ 2 ^ N) :
    ∃ code : List (List (Fin 2)), code.Nodup ∧ code.map List.length = lengths ∧
      IsPrefixFree (code.toFinset : Set (List (Fin 2))) := by
  induction lengths using List.reverseRecOn with
  | nil =>
      refine ⟨[], by simp, by simp, ?_⟩
      simp [IsPrefixFree]
  | append_singleton init l ih =>
      have hsortedInit : init.Pairwise (· ≤ ·) :=
        (List.pairwise_append.mp hsorted).1
      have hinitLe : ∀ k ∈ init, k ≤ l := fun k hk =>
        (List.pairwise_append.mp hsorted).2.2 k hk l (by simp)
      have hdepthInit : ∀ k ∈ init, k ≤ N := fun k hk =>
        hdepth k (by simp [hk])
      have hslots : (init.map fun k => 2 ^ (N - k)).sum + 2 ^ (N - l) ≤ 2 ^ N := by
        simpa [List.map_append, List.sum_append] using hKraft
      have hslotsInit : (init.map fun k => 2 ^ (N - k)).sum ≤ 2 ^ N := by
        exact (Nat.le_add_right _ _).trans hslots
      obtain ⟨code, hcode, hlengths, hpf⟩ :=
        ih hsortedInit hdepthInit hslotsInit
      have hlN : l ≤ N := hdepth l (by simp)
      have hfactor (k : ℕ) (hk : k ∈ init) :
          2 ^ (N - k) = 2 ^ (l - k) * 2 ^ (N - l) := by
        rw [← pow_add]
        congr 1
        have hkl := hinitLe k hk
        omega
      have hsumFactor :
          (init.map fun k => 2 ^ (N - k)).sum =
            (init.map fun k => 2 ^ (l - k)).sum * 2 ^ (N - l) := by
        calc
          _ = (init.map fun k => 2 ^ (l - k) * 2 ^ (N - l)).sum := by
            congr 1
            exact List.map_congr_left fun k hk => hfactor k hk
          _ = _ := sum_map_mul_right init (fun k => 2 ^ (l - k)) (2 ^ (N - l))
      have hpowFactor : 2 ^ N = 2 ^ l * 2 ^ (N - l) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hsumFactor, hpowFactor] at hslots
      have hscaled : (init.map fun k => 2 ^ (l - k)).sum + 1 ≤ 2 ^ l := by
        have hc : 0 < 2 ^ (N - l) := pow_pos (by omega) _
        exact le_of_mul_le_mul_right (by simpa [add_mul] using hslots) hc
      have hweightEq :
          (code.map fun u => 2 ^ (l - u.length)).sum =
            (init.map fun k => 2 ^ (l - k)).sum := by
        calc
          _ = ((code.map List.length).map fun k => 2 ^ (l - k)).sum := by
            simp [List.map_map, Function.comp_def]
          _ = _ := by rw [hlengths]
      have hbudget : (code.map fun u => 2 ^ (l - u.length)).sum < 2 ^ l :=
        Nat.lt_iff_add_one_le.mpr (by rw [hweightEq]; exact hscaled)
      have hcodeLe : ∀ u ∈ code, u.length ≤ l := by
        intro u hu
        apply hinitLe u.length
        rw [← hlengths]
        exact List.mem_map.mpr ⟨u, hu, rfl⟩
      obtain ⟨w, hw⟩ := exists_vector_avoiding_prefixes code l hcode hbudget
      have hwmem : w.1 ∉ code := by
        intro hwcode
        exact hw w.1 hwcode (by simp)
      refine ⟨code ++ [w.1], ?_, ?_, ?_⟩
      · simpa only [List.concat_eq_append] using (List.nodup_concat code w.1).mpr ⟨hwmem, hcode⟩
      · simp [hlengths, w.2]
      · intro u hu v hv huv
        simp only [List.coe_toFinset, Set.mem_setOf_eq, List.mem_append, List.mem_singleton] at hu hv
        rcases hu with hu | rfl
        · rcases hv with hv | rfl
          · exact hpf (by simpa using hu) (by simpa using hv) huv
          · exact (hw u hu huv).elim
        · rcases hv with hv | rfl
          · have hvw : v.length ≤ w.1.length := by
              rw [w.2]
              exact hcodeLe v hv
            exact huv.eq_of_length (le_antisymm huv.length_le hvw)
          · rfl

/-- Finite binary Kraft converse for an arbitrary multiset of prescribed lengths. The
integer-scaled hypothesis is the exact finite form, equivalent for lengths bounded by `N` to
`∑ l, 2⁻ˡ ≤ 1`, while avoiding all real-number rounding. -/
theorem exists_isPrefixFree_code_of_kraft (lengths : Multiset ℕ) (N : ℕ)
    (hdepth : ∀ l ∈ lengths, l ≤ N)
    (hKraft : (lengths.map fun l => 2 ^ (N - l)).sum ≤ 2 ^ N) :
    ∃ code : List (List (Fin 2)), code.Nodup ∧
      (code.map List.length : Multiset ℕ) = lengths ∧
      IsPrefixFree (code.toFinset : Set (List (Fin 2))) := by
  let sorted := lengths.sort (· ≤ ·)
  have hsortedEq : (sorted : Multiset ℕ) = lengths :=
    Multiset.sort_eq lengths (· ≤ ·)
  have hdepthSorted : ∀ l ∈ sorted, l ≤ N := fun l hl =>
    hdepth l (by simpa [sorted] using hl)
  have hKraftSorted : (sorted.map fun l => 2 ^ (N - l)).sum ≤ 2 ^ N := by
    change (Multiset.map (fun l => 2 ^ (N - l)) (sorted : Multiset ℕ)).sum ≤ 2 ^ N
    rw [hsortedEq]
    exact hKraft
  obtain ⟨code, hcode, hlengths, hpf⟩ :=
    exists_sorted_isPrefixFree_code_of_kraft sorted N (by simp [sorted])
      hdepthSorted hKraftSorted
  refine ⟨code, hcode, ?_, hpf⟩
  rw [hlengths]
  exact hsortedEq

#print axioms exists_isPrefixFree_code_of_kraft

end D5.S0.Computability.Coding.KraftConverse
