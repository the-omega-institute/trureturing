/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumIndecomp
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaBasicSumIndecomp
   mirror-E: none(waiver:indecomposable-pattern-avoiders)
   anchors: []
   utility: none
   digest: Pattern avoidance forces the extremal entry to mark a sum cut. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicSumAvoid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaBasicSumIndecomp

open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicSum

/-- A nonempty 312-avoider has no proper sum cut exactly when its last
entry is `1`. -/
theorem avoid312_indecomp_iff_last_one (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length)) (hn : 0 < p.length)
    (havoid : ¬ D5.S3.Combinatorics.ArrowWilfDefs.Contains [3, 1, 2] [] 3 p) :
    (∀ k, 0 < k → k < p.length → ∃ x ∈ p.take k, k < x) ↔
      p.getD (p.length - 1) 0 = 1 := by
  have prefix_cut_iff_sum (w : List ℕ)
      (hw : w.Perm (List.range' 1 w.length)) (k : ℕ) (hk : k ≤ w.length) :
      (∀ x ∈ w.take k, x ≤ k) ↔
        ∃ v : List ℕ,
          w = w.take k ++ v.map (fun x => x + k) ∧
          (w.take k).Perm (List.range' 1 k) ∧
          v.Perm (List.range' 1 (w.length - k)) := by
    constructor
    · intro hsmall
      let u := w.take k
      let tail := w.drop k
      have hnodup : w.Nodup := hw.nodup_iff.mpr List.nodup_range'
      have hUlen : u.length = k := by simp [u, hk]
      have hUnodup : u.Nodup := hnodup.take
      have hsubset : u.toFinset ⊆ (List.range' 1 k).toFinset := by
        intro x hx
        have hxu : x ∈ u := List.mem_toFinset.mp hx
        have hxw : x ∈ w := List.mem_of_mem_take hxu
        have hxr : x ∈ List.range' 1 w.length := hw.mem_iff.mp hxw
        obtain ⟨j, hj, hval⟩ := List.mem_range'.mp hxr
        have hx1 : 1 ≤ x := by omega
        have hxk : x ≤ k := hsmall x hxu
        exact List.mem_toFinset.mpr (List.mem_range'.mpr ⟨x - 1, by omega, by omega⟩)
      have hcard : u.toFinset.card = (List.range' 1 k).toFinset.card := by
        simp [List.card_toFinset, List.dedup_eq_self.mpr hUnodup,
          List.dedup_eq_self.mpr List.nodup_range', hUlen]
      have hset : u.toFinset = (List.range' 1 k).toFinset :=
        Finset.eq_of_subset_of_card_le hsubset (by omega)
      have hu : u.Perm (List.range' 1 k) :=
        List.perm_of_nodup_nodup_toFinset_eq hUnodup List.nodup_range' hset
      have hrange : List.range' 1 w.length =
          List.range' 1 k ++ List.range' (k + 1) (w.length - k) := by
        have h := List.range'_append_1 (s := 1) (m := k) (n := w.length - k)
        simpa [Nat.add_sub_of_le hk, Nat.add_comm] using h.symm
      have hwhole : (u ++ tail).Perm (List.range' 1 k ++
          List.range' (k + 1) (w.length - k)) := by
        simpa only [u, tail, List.take_append_drop, hrange] using hw
      have htail : tail.Perm (List.range' (k + 1) (w.length - k)) := by
        have h := (hu.symm.append (List.Perm.refl tail)).trans hwhole
        exact (List.perm_append_left_iff (List.range' 1 k)).mp h
      let v := tail.map (fun x => x - k)
      have htail_shift : tail = v.map (fun x => x + k) := by
        change tail = (tail.map (fun x => x - k)).map (fun x => x + k)
        rw [List.map_map]
        calc
          tail = tail.map (fun x => x) := by simp
          _ = tail.map ((fun x => x + k) ∘ fun x => x - k) := by
            apply List.map_congr_left
            intro x hx
            have hxr : x ∈ List.range' (k + 1) (w.length - k) := htail.mem_iff.mp hx
            obtain ⟨j, _, hxj⟩ := List.mem_range'.mp hxr
            dsimp
            omega
      have hv : v.Perm (List.range' 1 (w.length - k)) := by
        have hmap := htail.map (fun x => x - k)
        have hr : (List.range' (k + 1) (w.length - k)).map (fun x => x - k) =
            List.range' 1 (w.length - k) := by
          have h := List.Ico.map_sub (k + 1) (w.length + 1) k (by omega)
          simpa [List.Ico, Nat.add_sub_of_le hk, Nat.add_comm,
            show w.length + 1 - k - 1 = w.length - k by omega] using h
        simpa only [v, hr] using hmap
      refine ⟨v, ?_, ?_, hv⟩
      · calc
          w = u ++ tail := (List.take_append_drop k w).symm
          _ = w.take k ++ v.map (fun x => x + k) := by rw [htail_shift]
      · exact hu
    · rintro ⟨v, _, hu, _⟩ x hx
      have hxr : x ∈ List.range' 1 k := hu.mem_iff.mp hx
      obtain ⟨j, hj, hval⟩ := List.mem_range'.mp hxr
      omega
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
  have h1range : 1 ∈ List.range' 1 p.length :=
    List.mem_range'.mpr ⟨0, hn, by omega⟩
  have h1mem : 1 ∈ p := hp.mem_iff.mpr h1range
  let t := p.idxOf 1
  have ht : t < p.length := List.idxOf_lt_length_of_mem h1mem
  have hget1 : p.getD t 0 = 1 := by
    rw [List.getD_eq_getElem _ 0 ht]
    exact List.getElem_idxOf ht
  have hlast : t = p.length - 1 ↔ p.getD (p.length - 1) 0 = 1 := by
    constructor
    · intro heq
      rw [← heq]
      exact hget1
    · intro heq
      have hlastlt : p.length - 1 < p.length := by omega
      have helem : p[t] = p[p.length - 1] := by
        rw [← List.getD_eq_getElem _ 0 ht,
          ← List.getD_eq_getElem _ 0 hlastlt, hget1, heq]
      exact (hnodup.getElem_inj_iff).mp helem
  constructor
  · intro hindecomp
    by_contra hnotlast
    have htl : t + 1 < p.length := by
      have hne : t ≠ p.length - 1 := fun h => hnotlast (hlast.mp h)
      omega
    let k := t + 1
    have hsep : ∀ x ∈ p.take k, ∀ y ∈ p.drop k, x < y := by
      intro x hx y hy
      have hxp : x ∈ p := List.mem_of_mem_take hx
      have hyp : y ∈ p := List.mem_of_mem_drop hy
      have hix : p.idxOf x < k := (List.mem_take_iff_idxOf_lt hxp).mp hx
      have hnotake : y ∉ p.take k := by
        intro hyt
        have hdis := List.disjoint_take_drop hnodup (le_refl k)
        have heq := (List.nodup_append.mp (by
          simpa only [List.take_append_drop] using hnodup)).2.2 y hyt y hy
        exact heq rfl
      have hiy : k ≤ p.idxOf y := by
        by_contra h
        exact hnotake ((List.mem_take_iff_idxOf_lt hyp).mpr (by omega))
      have hypos : 1 < y := by
        obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hp.mem_iff.mp hyp)
        have hyne : y ≠ 1 := by
          intro heq
          rw [heq] at hiy
          change k ≤ t at hiy
          dsimp [k] at hiy
          omega
        omega
      by_cases hxeq : x = 1
      · subst x
        exact hypos
      · have hixlt : p.idxOf x < t := by
          have hle : p.idxOf x ≤ t := by dsimp [k] at hix; omega
          by_contra hlt
          have heq : p.idxOf x = t := by omega
          have hxget : p.getD (p.idxOf x) 0 = x := by
            rw [List.getD_eq_getElem _ 0 (List.idxOf_lt_length_of_mem hxp)]
            exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hxp)
          exact hxeq (by rw [heq, hget1] at hxget; exact hxget.symm)
        have hne : x ≠ y := by
          intro heq
          subst y
          have := (List.idxOf_lt_length_of_mem hxp)
          omega
        by_contra hnotlt
        have hxy : y < x := by omega
        apply havoid
        apply (hcontains312 p).mpr
        let ix : Fin p.length := ⟨p.idxOf x, List.idxOf_lt_length_of_mem hxp⟩
        let iy : Fin p.length := ⟨p.idxOf y, List.idxOf_lt_length_of_mem hyp⟩
        let it : Fin p.length := ⟨t, ht⟩
        refine ⟨ix, it, iy, ?_, ?_, ?_, ?_⟩
        · exact hixlt
        · have htly : t < p.idxOf y := by dsimp [k] at hiy; omega
          exact htly
        · have hxget : p.getD (p.idxOf x) 0 = x := by
            rw [List.getD_eq_getElem _ 0 (List.idxOf_lt_length_of_mem hxp)]
            exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hxp)
          have hyget : p.getD (p.idxOf y) 0 = y := by
            rw [List.getD_eq_getElem _ 0 (List.idxOf_lt_length_of_mem hyp)]
            exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hyp)
          change p[p.idxOf x]'(List.idxOf_lt_length_of_mem hxp) >
            p[p.idxOf y]'(List.idxOf_lt_length_of_mem hyp)
          rw [List.getElem_idxOf (List.idxOf_lt_length_of_mem hxp),
            List.getElem_idxOf (List.idxOf_lt_length_of_mem hyp)]
          exact hxy
        · have hyget : p.getD (p.idxOf y) 0 = y := by
            rw [List.getD_eq_getElem _ 0 (List.idxOf_lt_length_of_mem hyp)]
            exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hyp)
          change p[p.idxOf y]'(List.idxOf_lt_length_of_mem hyp) > p[t]'ht
          have htval : p[t] = 1 := by
            simpa only [List.getD_eq_getElem _ 0 ht] using hget1
          rw [List.getElem_idxOf (List.idxOf_lt_length_of_mem hyp), htval]
          exact hypos
    have hcut := separated_prefix_cut p hp k (by dsimp [k]; omega) hsep
    obtain ⟨x, hx, hgt⟩ := hindecomp k (by dsimp [k]; omega) htl
    exact (not_le_of_gt hgt) (hcut x hx)
  · intro hlastone k hk hkl
    by_contra hnone
    push Not at hnone
    have hcut : ∀ x ∈ p.take k, x ≤ k := by
      intro x hx
      exact hnone x hx
    obtain ⟨v, _, hu, _⟩ := (prefix_cut_iff_sum p hp k (by omega)).mp hcut
    have h1low : 1 ∈ List.range' 1 k :=
      List.mem_range'.mpr ⟨0, hk, by omega⟩
    have h1take : 1 ∈ p.take k := hu.mem_iff.mpr h1low
    have htlow : t < k := (List.mem_take_iff_idxOf_lt h1mem).mp h1take
    have htlast : t = p.length - 1 := hlast.mpr hlastone
    omega

/-- A nonempty 231-avoider has no proper sum cut exactly when its first
entry is the maximum. -/
theorem avoid231_indecomp_iff_first_max (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length)) (hn : 0 < p.length)
    (havoid : ¬ D5.S3.Combinatorics.ArrowWilfDefs.Contains [2, 3, 1] [] 3 p) :
    (∀ k, 0 < k → k < p.length → ∃ x ∈ p.take k, k < x) ↔
      p.getD 0 0 = p.length := by
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
  have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hnrange : p.length ∈ List.range' 1 p.length :=
    List.mem_range'.mpr ⟨p.length - 1, by omega, by omega⟩
  have hnmem : p.length ∈ p := hp.mem_iff.mpr hnrange
  let t := p.idxOf p.length
  have ht : t < p.length := List.idxOf_lt_length_of_mem hnmem
  have hgetn : p.getD t 0 = p.length := by
    rw [List.getD_eq_getElem _ 0 ht]
    exact List.getElem_idxOf ht
  have hfirst : t = 0 ↔ p.getD 0 0 = p.length := by
    constructor
    · intro heq
      simpa only [heq] using hgetn
    · intro heq
      have helem : p[t] = p[0] := by
        rw [← List.getD_eq_getElem _ 0 ht,
          ← List.getD_eq_getElem _ 0 hn, hgetn, heq]
      exact (hnodup.getElem_inj_iff).mp helem
  constructor
  · intro hindecomp
    by_contra hnotfirst
    have htpos : 0 < t := by
      have hne : t ≠ 0 := fun h => hnotfirst (hfirst.mp h)
      omega
    let k := t
    have hsep : ∀ x ∈ p.take k, ∀ y ∈ p.drop k, x < y := by
      intro x hx y hy
      have hxp : x ∈ p := List.mem_of_mem_take hx
      have hyp : y ∈ p := List.mem_of_mem_drop hy
      have hix : p.idxOf x < k := (List.mem_take_iff_idxOf_lt hxp).mp hx
      have hnotake : y ∉ p.take k := by
        intro hyt
        have heq := (List.nodup_append.mp (by
          simpa only [List.take_append_drop] using hnodup)).2.2 y hyt y hy
        exact heq rfl
      have hiy : k ≤ p.idxOf y := by
        by_contra h
        exact hnotake ((List.mem_take_iff_idxOf_lt hyp).mpr (by omega))
      have hxbound : x ≤ p.length := by
        obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hxp)
        omega
      by_cases hymax : y = p.length
      · have hxne : x ≠ p.length := by
          intro heq
          rw [heq] at hix
          change t < k at hix
          dsimp [k] at hix
          omega
        omega
      · have hiygt : t < p.idxOf y := by
          have hyget : p.getD (p.idxOf y) 0 = y := by
            rw [List.getD_eq_getElem _ 0 (List.idxOf_lt_length_of_mem hyp)]
            exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hyp)
          have hne : p.idxOf y ≠ t := by
            intro heq
            rw [heq, hgetn] at hyget
            exact hymax hyget.symm
          dsimp [k] at hiy
          omega
        have hne : x ≠ y := by
          intro heq
          rw [heq] at hix
          omega
        by_contra hnotlt
        have hxy : y < x := by omega
        apply havoid
        apply (hcontains231 p).mpr
        let ix : Fin p.length := ⟨p.idxOf x, List.idxOf_lt_length_of_mem hxp⟩
        let iy : Fin p.length := ⟨p.idxOf y, List.idxOf_lt_length_of_mem hyp⟩
        let it : Fin p.length := ⟨t, ht⟩
        refine ⟨ix, it, iy, ?_, ?_, ?_, ?_⟩
        · exact hix
        · exact hiygt
        · change p[t]'ht > p[p.idxOf x]'(List.idxOf_lt_length_of_mem hxp)
          rw [List.getElem_idxOf (List.idxOf_lt_length_of_mem hxp)]
          have htval : p[t] = p.length := by
            simpa only [List.getD_eq_getElem _ 0 ht] using hgetn
          rw [htval]
          have hxne : x ≠ p.length := by
            intro heq
            rw [heq] at hix
            change t < k at hix
            dsimp [k] at hix
            omega
          omega
        · change p[p.idxOf x]'(List.idxOf_lt_length_of_mem hxp) >
            p[p.idxOf y]'(List.idxOf_lt_length_of_mem hyp)
          rw [List.getElem_idxOf (List.idxOf_lt_length_of_mem hxp),
            List.getElem_idxOf (List.idxOf_lt_length_of_mem hyp)]
          exact hxy
    have hcut := separated_prefix_cut p hp k (by dsimp [k]; omega) hsep
    obtain ⟨x, hx, hgt⟩ := hindecomp k htpos ht
    exact (not_le_of_gt hgt) (hcut x hx)
  · intro hfirstmax k hk hkl
    have htzero : t = 0 := hfirst.mpr hfirstmax
    have hntake : p.length ∈ p.take k :=
      (List.mem_take_iff_idxOf_lt hnmem).mpr (by dsimp [t] at htzero; omega)
    exact ⟨p.length, hntake, hkl⟩

end D5.S3.Combinatorics.FundamentalBijection.ThetaBasicSumIndecomp
