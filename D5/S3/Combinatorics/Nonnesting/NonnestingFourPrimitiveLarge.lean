/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveLarge
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveLarge
   mirror-E: none(waiver:row-four-large-primitive-family)
   anchors: []
   utility: none
   digest: Reduces a large-first-letter primitive word to an increasing tail. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingFourLargeFirst
import D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveIncUnique

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveLarge

open D5.S3.Combinatorics.Nonnesting
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum
open D5.S3.Combinatorics.Nonnesting.NonnestingFourBlocks
open D5.S3.Combinatorics.Nonnesting.NonnestingFourLargeFirst

theorem primitive_large_prefix (n : ℕ) (v : List ℕ) :
    primitive (n :: n :: v) n := by
  intro k hk hkn hcut
  obtain ⟨u, z, heq, hlen, hu, _⟩ := hcut
  cases u with
  | nil => simp at hlen; omega
  | cons a t =>
    have ha : a = n := by
      have h := congrArg List.head? heq
      simpa using h.symm
    have hak := (hu a (by simp)).2
    omega

theorem large_first_tail (n : ℕ) (v : List ℕ) (hn : 3 ≤ n)
    (hw : (n :: n :: v) ∈ NonnestingDefs.avoiders n
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]]) :
    v ∈ NonnestingDefs.avoiders (n - 1)
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]] ∧
    (∀ a b, 1 ≤ a → a < b → b ≤ n - 1 → (v).idxOf a < (v).idxOf b) := by
  let Λ := [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]]
  have hbase : ((List.range' 1 n).flatMap fun i => [i, i]) =
      ((List.range' 1 (n - 1)).flatMap fun i => [i, i]) ++ [n, n] := by
    have hnn : n - 1 + 1 = n := by omega
    have hrange : List.range' 1 n = List.range' 1 (n - 1) ++ [n] := by
      calc
        List.range' 1 n = List.range' 1 (n - 1 + 1) := by rw [hnn]
        _ = List.range' 1 (n - 1) ++ [1 + (n - 1)] :=
          List.range'_1_concat
        _ = List.range' 1 (n - 1) ++ [n] := by
          rw [show 1 + (n - 1) = n by omega]
    rw [hrange, List.flatMap_append]
    simp
  have hperm : v.Perm ((List.range' 1 (n - 1)).flatMap fun i => [i, i]) := by
    apply List.perm_iff_count.mpr
    intro x
    have hc := hw.1.count_eq x
    rw [hbase] at hc
    simp only [List.count_cons, List.count_append] at hc
    simp only [List.count_nil] at hc
    omega
  have hocc (σ : List ℕ) : NonnestingDefs.Occurs σ v →
      NonnestingDefs.Occurs σ (n :: n :: v) := by
    unfold NonnestingDefs.Occurs D5.S3.Combinatorics.ArrowWilfDefs.Contains
    rintro ⟨x, hxlt, hxmem, hxsub, hnil⟩
    refine ⟨x, hxlt, ?_, ?_, by simp⟩
    · intro i hi hle
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hxmem i hi hle))
    · exact (hxsub.trans (List.sublist_cons_self n v)).trans
        (List.sublist_cons_self n (n :: v))
  have htail : v ∈ NonnestingDefs.avoiders (n - 1) Λ := by
    refine ⟨hperm, ?_, ?_, ?_⟩
    · exact fun h => hw.2.1 (hocc _ h)
    · exact fun h => hw.2.2.1 (hocc _ h)
    · intro σ hσ h
      exact hw.2.2.2 σ hσ (hocc σ h)
  have hblock := first_block_structure (n :: n :: v) n n hw
    ⟨by omega, le_refl _⟩ (by simp [])
  refine ⟨htail, ?_⟩
  intro a b ha hab hb
  have hlt := hblock.1 a b ha hab (by omega)
  have hna : n ≠ a := by omega
  have hnb : n ≠ b := by omega
  simpa [List.idxOf_cons_ne, hna, hnb] using hlt

end D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveLarge

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveLarge.large_first_tail
#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveLarge.primitive_large_prefix
