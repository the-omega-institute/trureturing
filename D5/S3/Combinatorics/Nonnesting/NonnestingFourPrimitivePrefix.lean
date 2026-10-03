/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitivePrefix
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingFourPrimitivePrefix
   mirror-E: none(waiver:row-four-maximum-prefix-patterns)
   anchors: []
   utility: none
   digest: Localizes forbidden patterns in a word with a doubled maximum prefix. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveLarge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitivePrefix

open D5.S3.Combinatorics.Nonnesting
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders

theorem prefix_nesting_reduces (n : ℕ) (v σ : List ℕ)
    (hv : v.Perm ((List.range' 1 (n - 1)).flatMap fun i => [i, i]))
    (hσ : σ = [1, 2, 2, 1] ∨ σ = [2, 1, 1, 2])
    (hocc : NonnestingDefs.Occurs σ (n :: n :: v)) :
    NonnestingDefs.Occurs σ v := by
  have hletters : NonnestingDefs.letters σ = 2 := by
    rcases hσ with h | h <;> subst σ <;> decide
  have hfull : ∀ i, 1 ≤ i → i ≤ NonnestingDefs.letters σ → i ∈ σ := by
    intro i hi hle
    have hcase : i = 1 ∨ i = 2 := by omega
    rcases hσ with h | h <;> subst σ <;>
      rcases hcase with rfl | rfl <;> simp
  have hnNot : n ∉ v := by
    intro hmem
    have hbase := hv.mem_iff.mp hmem
    obtain ⟨i, hi, hni⟩ := List.mem_flatMap.mp hbase
    have heq : n = i := by simpa using hni
    rw [List.mem_range'_1] at hi
    omega
  unfold NonnestingDefs.Occurs D5.S3.Combinatorics.ArrowWilfDefs.Contains at hocc ⊢
  obtain ⟨x, hxmono, hxmem, hxsub, _⟩ := hocc
  have hx12 : x 1 < x 2 := hxmono 1 (by omega) (by simp [hletters])
  have hx2 : x 2 ≤ n := by
    have hm := hxmem 2 (by omega) (by simp [hletters])
    simp only [List.mem_cons] at hm
    rcases hm with h | h | h
    · omega
    · omega
    · have hbase := hv.mem_iff.mp h
      obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hbase
      have heq : x 2 = i := by simpa using hxi
      rw [List.mem_range'_1] at hi
      omega
  have hxsub' : (σ.map x).Sublist ([n, n] ++ v) := by simpa using hxsub
  obtain ⟨p, q, hpq, hpp, hqv⟩ := List.sublist_append_iff.mp hxsub'
  have hpval : ∀ y ∈ p, y = n := by
    intro y hy
    have hy' := hpp.subset hy
    simpa using hy'
  cases p with
  | nil =>
    have hsubV : (σ.map x).Sublist v := by simpa [hpq] using hqv
    refine ⟨x, hxmono, ?_, hsubV, by simp⟩
    intro i hi hle
    exact hsubV.subset (List.mem_map_of_mem (hfull i hi hle))
  | cons y ys =>
    have hy : y = n := hpval y (by simp)
    subst y
    have hpfirst : (σ.map x).head? = some n := by rw [hpq]; simp
    rcases hσ with h | h
    · subst σ
      simp at hpfirst
      omega
    · subst σ
      have hx2n : x 2 = n := by simpa using hpfirst
      cases ys with
      | nil =>
        have hq : q = [x 1, x 1, x 2] := by
          simp [hx2n] at hpq
          simpa [hx2n] using hpq.symm
        have hmem : n ∈ v := by
          apply hqv.subset
          simp [hq, hx2n]
        exact False.elim (hnNot hmem)
      | cons z zs =>
        have hz : z = n := hpval z (by simp)
        subst z
        have hlen : (n :: n :: zs).length ≤ 2 := hpp.length_le
        have hnil : zs = [] := by
          cases zs with
          | nil => rfl
          | cons t ts => simp at hlen
        subst zs
        simp [hx2n] at hpq
        omega

theorem prefix_pattern_reduces (n : ℕ) (v σ : List ℕ)
    (hv : v.Perm ((List.range' 1 (n - 1)).flatMap fun i => [i, i]))
    (hσ : σ ∈ [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
    (hocc : NonnestingDefs.Occurs σ (n :: n :: v)) :
    NonnestingDefs.Occurs σ v ∨
      ∃ a b : ℕ, a < b ∧ List.Sublist [b, b, a] v := by
  have hletters : NonnestingDefs.letters σ = 3 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with h | h | h | h <;> subst σ <;> decide
  have hfull : ∀ i, 1 ≤ i → i ≤ NonnestingDefs.letters σ → i ∈ σ := by
    intro i hi hle
    have hcase : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with h | h | h | h <;> subst σ <;>
      rcases hcase with rfl | rfl | rfl <;> simp
  have hbound (z : ℕ) (hz : z ∈ n :: n :: v) : z ≤ n := by
    simp only [List.mem_cons] at hz
    rcases hz with rfl | rfl | hz
    · exact le_refl _
    · exact le_refl _
    · have hzbase := hv.mem_iff.mp hz
      obtain ⟨i, hi, hzi⟩ := List.mem_flatMap.mp hzbase
      have heq : z = i := by simpa using hzi
      subst z
      rw [List.mem_range'_1] at hi
      omega
  unfold NonnestingDefs.Occurs D5.S3.Combinatorics.ArrowWilfDefs.Contains at hocc ⊢
  obtain ⟨x, hxmono, hxmem, hxsub, _⟩ := hocc
  have hx3 : x 3 ≤ n := by
    apply hbound (x 3)
    exact hxmem 3 (by omega) (by simp [hletters])
  have hx12 : x 1 < x 2 ∧ x 2 < x 3 := by
    constructor
    · exact hxmono 1 (by omega) (by simp [hletters])
    · exact hxmono 2 (by omega) (by simp [hletters])
  have hxsub' : (σ.map x).Sublist ([n, n] ++ v) := by simpa using hxsub
  obtain ⟨p, q, hpq, hpp, hqv⟩ := List.sublist_append_iff.mp hxsub'
  have hpval : ∀ y ∈ p, y = n := by
    intro y hy
    have hy' := hpp.subset hy
    simpa using hy'
  cases p with
  | nil =>
    left
    have hsubV : (σ.map x).Sublist v := by simpa [hpq] using hqv
    refine ⟨x, hxmono, ?_, hsubV, by simp⟩
    intro i hi hle
    have hiσ := hfull i hi hle
    have himap : x i ∈ σ.map x := List.mem_map_of_mem hiσ
    exact hsubV.subset himap
  | cons y ys =>
    have hy : y = n := hpval y (by simp)
    subst y
    have hpfirst : (σ.map x).head? = some n := by
      rw [hpq]
      simp
    have hσcases : σ = [1, 2, 3, 1] ∨ σ = [1, 3, 1, 2] ∨
        σ = [2, 2, 3, 1] ∨ σ = [3, 2, 2, 1] := by
      simpa using hσ
    rcases hσcases with h | h | h | h
    · subst σ
      simp at hpfirst
      omega
    · subst σ
      simp at hpfirst
      omega
    · subst σ
      simp at hpfirst
      omega
    · subst σ
      have hx3n : x 3 = n := by simpa using hpfirst
      cases ys with
      | nil =>
        right
        have hq : q = [x 2, x 2, x 1] := by
          simp [hx3n] at hpq
          exact hpq.symm
        refine ⟨x 1, x 2, hx12.1, ?_⟩
        simpa [hq] using hqv
      | cons z zs =>
        have hz : z = n := hpval z (by simp)
        subst z
        have hlen : (n :: n :: zs).length ≤ 2 := hpp.length_le
        have hnil : zs = [] := by
          cases zs with
          | nil => rfl
          | cons t ts => simp at hlen
        subst zs
        simp [hx3n] at hpq
        omega

end D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitivePrefix

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitivePrefix.prefix_pattern_reduces
#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitivePrefix.prefix_nesting_reduces
