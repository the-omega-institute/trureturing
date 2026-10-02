/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaCube231Shape
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaCube231Shape
   mirror-E: none(waiver:231-forced-initial-shape)
   anchors: []
   utility: none
   digest: The first inverse return edge forces the initial low pair in a 231-avoider. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaCube231Shape

local notation "B" =>
  (fun p : List ℕ =>
    List.map (D5.S3.Combinatorics.ArrowWilfDefs.hat p)
      (List.range' 1 (List.length p)))

open ThetaBasicInverse
open D5.S3.Combinatorics.ArrowWilfDefs

theorem return_edge_forces_initial_pair (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length)) (hn : 5 ≤ p.length)
    (havoid : ¬ Contains [2, 3, 1] [] 3 p)
    (hfirst : p.getD 0 0 = p.length)
    (hsecond : p.getD 1 0 = 1)
    (hlast : p.getD (p.length - 1) 0 = p.length - 1)
    (hreturn : (B p).getD (p.length - 3) 0 = 2) :
    p.getD 2 0 = p.length - 2 ∧ p.getD 3 0 = 2 := by
  have hat_one_block (p : List ℕ) (hmax : ∀ y ∈ p, y ≤ p.getD 0 0)
      (x : ℕ) (hx : x ∈ p) :
      hat p x = if p.idxOf x + 1 < p.length then p.getD (p.idxOf x + 1) 0
        else p.getD 0 0 := by
    have hnonrecord (i : ℕ) (hi : 0 < i) (hil : i < p.length) :
        ¬ IsLtrMax p i := by
      intro hrecord
      have hmem : p.getD i 0 ∈ p := by
        rw [List.getD_eq_getElem _ 0 hil]
        exact List.getElem_mem hil
      exact (not_lt_of_ge (hmax _ hmem)) (hrecord 0 hi)
    have hgreatest (i : ℕ) (hi : i < p.length) :
        Nat.findGreatest (IsLtrMax p) i = 0 := by
      induction i with
      | zero => rfl
      | succ j ih =>
          rw [Nat.findGreatest_succ, if_neg (hnonrecord (j + 1) (by omega) hi)]
          exact ih (by omega)
    have hidx : p.idxOf x < p.length := List.idxOf_lt_length_of_mem hx
    unfold hat
    dsimp only
    by_cases hnext : p.idxOf x + 1 < p.length
    · rw [if_pos ⟨hnext, hnonrecord _ (by omega) hnext⟩, if_pos hnext]
    · rw [if_neg (fun h => hnext h.1), if_neg hnext, hgreatest _ hidx]
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
  let n := p.length
  have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hmax : ∀ y ∈ p, y ≤ p.getD 0 0 := by
    intro y hy
    rw [hfirst]
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hy)
    omega
  have hm2mem : n - 2 ∈ p := hp.mem_iff.mpr
    (List.mem_range'.mpr ⟨n - 3, by omega, by omega⟩)
  let i := p.idxOf (n - 2)
  have hi : i < n := List.idxOf_lt_length_of_mem hm2mem
  have hival : p.getD i 0 = n - 2 := by
    rw [List.getD_eq_getElem _ 0 hi]
    exact List.getElem_idxOf hi
  have hhat : hat p (n - 2) = 2 := by
    have hh : (B p).getD (n - 3) 0 = hat p (n - 2) := by
      rw [List.getD_eq_getElem _ 0 (by simp [n]; omega)]
      simp only [List.getElem_map, List.getElem_range'_1]
      congr 1
      omega
    exact hh.symm.trans hreturn
  have hnext : i + 1 < n := by
    by_contra hnot
    have hno : ¬ i + 1 < p.length := by omega
    have hh := hat_one_block p hmax (n - 2) hm2mem
    rw [show p.idxOf (n - 2) = i by rfl, if_neg hno, hfirst] at hh
    rw [hhat] at hh
    omega
  have hnextval : p.getD (i + 1) 0 = 2 := by
    have hh := hat_one_block p hmax (n - 2) hm2mem
    rw [show p.idxOf (n - 2) = i by rfl,
      if_pos (by simpa [n] using hnext)] at hh
    exact hh.symm.trans hhat
  have hige : 2 ≤ i := by
    have hne0 : i ≠ 0 := by
      intro he
      rw [he, hfirst] at hival
      omega
    have hne1 : i ≠ 1 := by
      intro he
      rw [he, hsecond] at hival
      omega
    omega
  have hieq : i = 2 := by
    by_contra hnot
    have h2i : 2 < i := by omega
    let z := p.getD 2 0
    have hzmem : z ∈ p := by
      dsimp [z]
      rw [List.getD_eq_getElem _ 0 (by omega : 2 < p.length)]
      exact List.getElem_mem (by omega : 2 < p.length)
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hzmem)
    have hne (j : ℕ) (hj : j < n) (hj2 : j ≠ 2)
        (hv : p.getD j 0 = z) : False := by
      have helem : p[j] = p[2] := by
        rw [← List.getD_eq_getElem _ 0 hj,
          ← List.getD_eq_getElem _ 0 (by omega : 2 < p.length), hv]
      exact hj2 ((hnodup.getElem_inj_iff).mp helem)
    have hzlow : 2 < z := by
      have hz1 : z ≠ 1 := by
        intro he
        apply hne 1 (by omega) (by omega)
        rw [hsecond]
        exact he.symm
      have hz2 : z ≠ 2 := by
        intro he
        apply hne (i + 1) hnext (by omega)
        rw [hnextval]
        exact he.symm
      omega
    have hzhigh : z < n - 2 := by
      have hzn : z ≠ n := by
        intro he
        apply hne 0 (by omega) (by omega)
        rw [hfirst]
        exact he.symm
      have hzn1 : z ≠ n - 1 := by
        intro he
        apply hne (n - 1) (by omega) (by omega)
        rw [hlast]
        exact he.symm
      have hzn2 : z ≠ n - 2 := by
        intro he
        apply hne i hi (by omega)
        rw [hival]
        exact he.symm
      omega
    apply havoid
    apply (hcontains231 p).mpr
    refine ⟨⟨2, by omega⟩, ⟨i, hi⟩, ⟨i + 1, hnext⟩,
      (by change 2 < i; exact h2i), (by change i < i + 1; omega), ?_, ?_⟩
    · rw [← List.getD_eq_getElem _ 0 (by omega : 2 < p.length),
        ← List.getD_eq_getElem _ 0 hi, hival]
      exact hzhigh
    · rw [← List.getD_eq_getElem _ 0 (by omega : 2 < p.length),
        ← List.getD_eq_getElem _ 0 hnext, hnextval]
      exact hzlow
  constructor
  · simpa only [hieq, n] using hival
  · rw [← show i + 1 = 3 by omega]
    exact hnextval

end D5.S3.Combinatorics.FundamentalBijection.ThetaCube231Shape
