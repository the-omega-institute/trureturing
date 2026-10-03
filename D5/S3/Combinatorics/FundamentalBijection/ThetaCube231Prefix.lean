/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaCube231Prefix
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaCube231Prefix
   mirror-E: none(waiver:231-prefix-order-constraint)
   anchors: []
   utility: none
   digest: Entries preceding one in a 231-avoider form a decreasing prefix. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaCube231Prefix

open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse

/-- An ascent before the entry `1` is a 231 occurrence, so the prefix
preceding `1` decreases strictly. -/
theorem avoid231_prefix_before_one_decreasing (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length)) (hn : 0 < p.length)
    (havoid : ¬ D5.S3.Combinatorics.ArrowWilfDefs.Contains [2, 3, 1] [] 3 p)
    (i j : ℕ) (hij : i < j) (hjt : j < p.idxOf 1) :
    p.getD j 0 < p.getD i 0 := by
  have hcontains231 (p : List ℕ) :
      D5.S3.Combinatorics.ArrowWilfDefs.Contains [2, 3, 1] [] 3 p ↔
        ∃ i j k : Fin p.length, i < j ∧ j < k ∧ p[j.val] > p[i.val] ∧
        p[i.val] > p[k.val] := by
    constructor
    · rintro ⟨x, hlt, _, hsub, _⟩
      change List.Sublist [x 2, x 3, x 1] p at hsub
      obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      have h0 : p[(f ⟨0, by simp⟩).val] = x 2 := by
        simpa using (hf ⟨0, by simp⟩).symm
      have h1 : p[(f ⟨1, by simp⟩).val] = x 3 := by
        simpa using (hf ⟨1, by simp⟩).symm
      have h2 : p[(f ⟨2, by simp⟩).val] = x 1 := by
        simpa using (hf ⟨2, by simp⟩).symm
      refine ⟨f ⟨0, by simp⟩, f ⟨1, by simp⟩, f ⟨2, by simp⟩,
        f.strictMono (by simp), f.strictMono (by simp), ?_, ?_⟩
      · simpa only [← h1, ← h0] using hlt 2 (by omega) (by omega)
      · simpa only [← h0, ← h2] using hlt 1 (by omega) (by omega)
    · rintro ⟨i, j, k, hij, hjk, hji, hik⟩
      let x : ℕ → ℕ := fun t => if t = 1 then p[k.val] else if t = 2 then p[i.val]
        else p[j.val]
      have hx1 : x 1 = p[k.val] := by simp [x]
      have hx2 : x 2 = p[i.val] := by simp [x]
      have hx3 : x 3 = p[j.val] := by simp [x]
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
        rcases h with rfl | rfl <;> simp [hx1, hx2, hx3, hik, hji]
      · intro t ht ht3
        have h : t = 1 ∨ t = 2 ∨ t = 3 := by omega
        rcases h with rfl | rfl | rfl <;> simp [hx1, hx2, hx3]
      · simpa [hx1, hx2, hx3] using hsub
  have h1mem : 1 ∈ p := hp.mem_iff.mpr
    (List.mem_range'.mpr ⟨0, hn, by omega⟩)
  have ht : p.idxOf 1 < p.length := List.idxOf_lt_length_of_mem h1mem
  rw [List.getD_eq_getElem _ 0 (by omega : j < p.length),
    List.getD_eq_getElem _ 0 (by omega : i < p.length)]
  have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hget1 : p[p.idxOf 1] = 1 := List.getElem_idxOf ht
  have hival : 1 < p[i] := by
    have hm : p[i] ∈ p := List.getElem_mem (by omega : i < p.length)
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hm)
    have hneq : p[i] ≠ 1 := by
      intro heq'
      have hindex : p[i] = p[p.idxOf 1] := by rw [heq', hget1]
      have := (hnodup.getElem_inj_iff).mp hindex
      omega
    omega
  have hne : p[i] ≠ p[j] := by
    intro heq
    have := (hnodup.getElem_inj_iff).mp heq
    omega
  by_contra hnot
  have hascent : p[i] < p[j] := by omega
  apply havoid
  apply (hcontains231 p).mpr
  refine ⟨⟨i, by omega⟩, ⟨j, by omega⟩, ⟨p.idxOf 1, ht⟩,
    hij, hjt, hascent, ?_⟩
  rw [hget1]
  exact hival

end D5.S3.Combinatorics.FundamentalBijection.ThetaCube231Prefix
