/- GID: D5/S3/Combinatorics/ArcherCyclicPadovanCycleWords
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArcherCyclicPadovanCycleWords
   mirror-E: none(waiver:inverse-of-rooted-cycle-word-construction)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: A cyclic permutation is recovered from its rooted orbit word. -/

import D5.S3.Combinatorics.ArcherCyclicTetranacciCycleWords
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArcherCyclicPadovanCycleWords

open ArcherCyclicDefs ArcherCyclicTetranacciCycleWords

theorem oneLine_orbitWord (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length)) (hc : IsCyclic p) :
    oneLine (orbitWord p) = p := by
  let w := orbitWord p
  have hwlen : w.length = p.length := by simp [w, orbitWord]
  have hw : w.Perm (List.range' 1 p.length) := hc
  have hwd : w.Nodup := hw.nodup_iff.mpr List.nodup_range'
  have hpd : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hmem (x : ℕ) (hx : x ∈ List.range' 1 p.length) :
      x - 1 < p.length := by
    obtain ⟨j, hj, hxeq⟩ := List.mem_range'.mp hx
    omega
  have himage (x : ℕ) (hx : x ∈ List.range' 1 p.length) :
      image p x = p[x - 1]'(hmem x hx) := by
    exact List.getD_eq_getElem (l := p) 0 (hmem x hx)
  have hinj (x y : ℕ) (hx : x ∈ List.range' 1 p.length)
      (hy : y ∈ List.range' 1 p.length) (heq : image p x = image p y) : x = y := by
    rw [himage x hx, himage y hy] at heq
    have hidx := hpd.getElem_inj_iff.mp heq
    have hxlo := List.left_le_of_mem_range' hx
    have hylo := List.left_le_of_mem_range' hy
    omega
  have hentry (i : ℕ) (hi : i < w.length) :
      w[i] = (image p)^[i] 1 := by
    simp [w, orbitWord] at hi ⊢
  have hstep (i : ℕ) (hi : i + 1 < w.length) :
      image p w[i] = w[i + 1] := by
    rw [hentry i (by omega), hentry (i + 1) hi]
    simp [Function.iterate_succ_apply']
  have hlast (hn : 0 < w.length) : image p w[w.length - 1] = 1 := by
    have hlmem : w[w.length - 1] ∈ List.range' 1 p.length :=
      hw.mem_iff.mp (List.getElem_mem (by omega))
    have hvalmem : image p w[w.length - 1] ∈ List.range' 1 p.length := by
      rw [himage _ hlmem]
      exact hp.mem_iff.mp (List.getElem_mem (hmem _ hlmem))
    have hvalw : image p w[w.length - 1] ∈ w := hw.mem_iff.mpr hvalmem
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hvalw
    have hj0 : j = 0 := by
      by_contra hne
      have hjpos : 0 < j := by omega
      have hpred : j - 1 + 1 < w.length := by omega
      have hbefore : w[j - 1] ∈ List.range' 1 p.length :=
        hw.mem_iff.mp (List.getElem_mem (by omega))
      have hsame : w[j - 1] = w[w.length - 1] := by
        apply hinj _ _ hbefore hlmem
        rw [hstep (j - 1) hpred]
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ j)] using heq
      have hidx := hwd.getElem_inj_iff.mp hsame
      omega
    subst j
    have hzero : w[0] = 1 := by simp [w, orbitWord]
    simpa [hzero] using heq.symm
  apply List.ext_getElem
  · simp [oneLine, orbitWord]
  · intro i hi hi'
    have hxi : 1 + i ∈ List.range' 1 p.length := by
      apply List.mem_range'.mpr
      refine ⟨i, hi', by omega⟩
    have hwi : 1 + i ∈ w := hw.mem_iff.mpr hxi
    obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.mp hwi
    have hform : w.formPerm w[j] = image p w[j] := by
      rw [List.formPerm_apply_getElem w hwd j hj]
      by_cases hnext : j + 1 < w.length
      · simpa only [Nat.mod_eq_of_lt hnext] using (hstep j hnext).symm
      · have hpos : 0 < w.length := by omega
        have hjlast : j = w.length - 1 := by omega
        subst j
        have hmod : (w.length - 1 + 1) % w.length = 0 := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ w.length)]
          simp
        simpa only [hmod, show w[0] = 1 by simp [w, orbitWord]]
          using (hlast hpos).symm
    have hxindex : (1 + i) - 1 = i := by omega
    simp only [oneLine, List.getElem_map] at hi' ⊢
    rw [List.getElem_range'_1, ← hjx, hform, hjx, himage _ hxi]
    simp only [hxindex]

end D5.S3.Combinatorics.ArcherCyclicPadovanCycleWords
