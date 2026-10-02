/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumAvoid
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaBasicSumAvoid
   mirror-E: none(waiver:pattern-occurrences-across-permutation-sums)
   anchors: []
   utility: none
   digest: Descending-end triples cannot cross a direct-sum boundary. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaBasicSumAvoid

/-- A positional triple whose first value exceeds its last value. -/
def DescendingTriple (p : List ℕ) (R : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∃ i j k : ℕ, i < j ∧ j < k ∧ k < p.length ∧
    p.getD i 0 > p.getD k 0 ∧ R (p.getD i 0) (p.getD j 0) (p.getD k 0)

/-- A triple with descending endpoints lies wholly in one summand whenever
its remaining relation is invariant under a common value shift. -/
theorem descendingTriple_sum_iff (w u v : List ℕ)
    (hw : w = u ++ v.map (fun y => y + u.length))
    (hu : u.Perm (List.range' 1 u.length))
    (hv : v.Perm (List.range' 1 v.length))
    (R : ℕ → ℕ → ℕ → Prop)
    (hshift : ∀ a b c m, R (a + m) (b + m) (c + m) ↔ R a b c) :
    DescendingTriple w R ↔ DescendingTriple u R ∨ DescendingTriple v R := by
  let m := u.length
  let n := v.length
  have hlen : w.length = m + n := by simp [hw, m, n]
  have hleft (i : ℕ) (hi : i < m) : w.getD i 0 = u.getD i 0 := by
    rw [hw]
    exact List.getD_append _ _ _ _ hi
  have hright (i : ℕ) (hi : i < n) :
      w.getD (m + i) 0 = v.getD i 0 + m := by
    rw [hw, List.getD_append_right u _ 0 (m + i) (by omega : u.length ≤ m + i)]
    rw [show m + i - u.length = i by dsimp [m]; omega]
    rw [List.getD_eq_getElem _ 0 (by simpa [n] using hi), List.getElem_map,
      List.getD_eq_getElem _ 0 hi]
  have hsmall (i : ℕ) (hi : i < m) : u.getD i 0 ≤ m := by
    have hmem : u.getD i 0 ∈ u := by
      rw [List.getD_eq_getElem _ 0 hi]
      exact List.getElem_mem hi
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hu.mem_iff.mp hmem)
    omega
  have hpositive (i : ℕ) (hi : i < n) : 0 < v.getD i 0 := by
    have hmem : v.getD i 0 ∈ v := by
      rw [List.getD_eq_getElem _ 0 hi]
      exact List.getElem_mem hi
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hv.mem_iff.mp hmem)
    omega
  constructor
  · rintro ⟨i, j, k, hij, hjk, hkl, hfirst, hR⟩
    by_cases hk : k < m
    · left
      refine ⟨i, j, k, hij, hjk, hk, ?_, ?_⟩
      · simpa only [hleft i (by omega), hleft k hk] using hfirst
      · simpa only [hleft i (by omega), hleft j (by omega), hleft k hk] using hR
    · have hkn : k - m < n := by omega
      have hkeq : m + (k - m) = k := by omega
      by_cases hi : i < m
      · have hlow := hsmall i hi
        have hpos := hpositive (k - m) hkn
        rw [hleft i hi, ← hkeq, hright _ hkn] at hfirst
        omega
      · right
        have hin : i - m < n := by omega
        have hjn : j - m < n := by omega
        have hieq : m + (i - m) = i := by omega
        have hjeq : m + (j - m) = j := by omega
        have hvals : w.getD i 0 = v.getD (i - m) 0 + m := by
          simpa only [hieq] using hright (i - m) hin
        have hvalj : w.getD j 0 = v.getD (j - m) 0 + m := by
          simpa only [hjeq] using hright (j - m) hjn
        have hvalk : w.getD k 0 = v.getD (k - m) 0 + m := by
          simpa only [hkeq] using hright (k - m) hkn
        refine ⟨i - m, j - m, k - m, by omega, by omega, hkn, ?_, ?_⟩
        · rw [hvals, hvalk] at hfirst
          omega
        · rw [hvals, hvalj, hvalk] at hR
          exact (hshift _ _ _ m).mp hR
  · intro h
    rcases h with h | h
    · obtain ⟨i, j, k, hij, hjk, hkl, hfirst, hR⟩ := h
      refine ⟨i, j, k, hij, hjk, by omega, ?_, ?_⟩
      · simpa only [hleft i (by omega), hleft k hkl] using hfirst
      · simpa only [hleft i (by omega), hleft j (by omega), hleft k hkl] using hR
    · obtain ⟨i, j, k, hij, hjk, hkl, hfirst, hR⟩ := h
      refine ⟨m + i, m + j, m + k, by omega, by omega, by omega, ?_, ?_⟩
      · rw [hright i (by omega), hright k hkl]
        omega
      · rw [hright i (by omega), hright j (by omega), hright k hkl]
        exact (hshift _ _ _ m).mpr hR

/-- Within one record block of a 312-avoider, later entries strictly decrease. -/
theorem avoid312_record_block_decreasing (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length))
    (havoid : ¬ D5.S3.Combinatorics.ArrowWilfDefs.Contains [3, 1, 2] [] 3 p)
    (s e : ℕ) (hse : s < e) (he : e ≤ p.length)
    (hs : D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p s)
    (hnon : ∀ j, s < j → j < e →
      ¬ D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p j)
    (i j : ℕ) (hsi : s < i) (hij : i < j) (hje : j < e) :
    p.getD j 0 < p.getD i 0 := by
  have hcontains312 (p : List ℕ) :
      D5.S3.Combinatorics.ArrowWilfDefs.Contains [3, 1, 2] [] 3 p ↔
        ∃ i j k : Fin p.length, i < j ∧ j < k ∧ p[i.val] > p[k.val] ∧
        p[k.val] > p[j.val] := by
    constructor
    · rintro ⟨x, hlt, _, hsub, _⟩
      change List.Sublist [x 3, x 1, x 2] p at hsub
      obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      have h0 : p[(f ⟨0, by simp⟩).val] = x 3 := by
        simpa using (hf ⟨0, by simp⟩).symm
      have h1 : p[(f ⟨1, by simp⟩).val] = x 1 := by
        simpa using (hf ⟨1, by simp⟩).symm
      have h2 : p[(f ⟨2, by simp⟩).val] = x 2 := by
        simpa using (hf ⟨2, by simp⟩).symm
      refine ⟨f ⟨0, by simp⟩, f ⟨1, by simp⟩, f ⟨2, by simp⟩,
        f.strictMono (by simp), f.strictMono (by simp), ?_, ?_⟩
      · simpa only [← h0, ← h2] using hlt 2 (by omega) (by omega)
      · simpa only [← h2, ← h1] using hlt 1 (by omega) (by omega)
    · rintro ⟨i, j, k, hij, hjk, hik, hkj⟩
      let x : ℕ → ℕ := fun t => if t = 1 then p[j.val] else if t = 2 then p[k.val]
        else p[i.val]
      have hx1 : x 1 = p[j.val] := by simp [x]
      have hx2 : x 2 = p[k.val] := by simp [x]
      have hx3 : x 3 = p[i.val] := by simp [x]
      have hsub : List.Sublist [p[i.val], p[j.val], p[k.val]] p := by
        let f : Fin 3 → Fin p.length := fun t =>
          if t.val = 0 then i else if t.val = 1 then j else k
        have hf : StrictMono f := by
          intro a b hab
          fin_cases a <;> fin_cases b <;> simp_all [f]; omega
        apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
        refine ⟨OrderEmbedding.ofStrictMono f hf, ?_⟩
        intro t
        fin_cases t <;> simp [f]
      refine ⟨x, ?_, ?_, ?_, by simp⟩
      · intro t ht ht3
        have h : t = 1 ∨ t = 2 := by omega
        rcases h with rfl | rfl <;> simp [hx1, hx2, hx3, hkj, hik]
      · intro t ht ht3
        have h : t = 1 ∨ t = 2 ∨ t = 3 := by omega
        rcases h with rfl | rfl | rfl <;> simp [hx1, hx2, hx3]
      · simpa [hx1, hx2, hx3] using hsub
  have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hsj : s < j := by omega
  have hjs : j < p.length := by omega
  have his : i < p.length := by omega
  have hss : s < p.length := by omega
  have hgreatest :
      Nat.findGreatest (D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p) j = s := by
    have hlow : s ≤ Nat.findGreatest
        (D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p) j :=
      Nat.le_findGreatest (by omega) hs
    have hupp := Nat.findGreatest_le
      (P := D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p) j
    by_contra hne
    have hgt : s < Nat.findGreatest
        (D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p) j := by omega
    exact hnon _ hgt (by omega)
      (Nat.findGreatest_spec (Nat.zero_le j) (by
        intro t ht
        omega))
  have hbound : p.getD j 0 ≤ p.getD s 0 := by
    simpa only [hgreatest] using
      ThetaBasicInverse.last_record_bounds_prefix p j hjs j (le_refl j)
  have hneqs : p.getD s 0 ≠ p.getD j 0 := by
    intro heq
    rw [List.getD_eq_getElem _ 0 hss, List.getD_eq_getElem _ 0 hjs] at heq
    have := (hnodup.getElem_inj_iff).mp heq
    omega
  have hfirst : p.getD s 0 > p.getD j 0 := by omega
  have hnoascent : ¬ p.getD i 0 < p.getD j 0 := by
    intro hascent
    apply havoid
    apply (hcontains312 p).mpr
    refine ⟨⟨s, hss⟩, ⟨i, his⟩, ⟨j, hjs⟩, ?_, ?_, ?_, ?_⟩
    · exact hsi
    · exact hij
    · simpa only [List.getD_eq_getElem _ 0 hss,
        List.getD_eq_getElem _ 0 hjs] using hfirst
    · simpa only [List.getD_eq_getElem _ 0 his,
        List.getD_eq_getElem _ 0 hjs] using hascent
  have hneq : p.getD i 0 ≠ p.getD j 0 := by
    intro heq
    rw [List.getD_eq_getElem _ 0 his, List.getD_eq_getElem _ 0 hjs] at heq
    have := (hnodup.getElem_inj_iff).mp heq
    omega
  omega

end D5.S3.Combinatorics.FundamentalBijection.ThetaBasicSumAvoid
