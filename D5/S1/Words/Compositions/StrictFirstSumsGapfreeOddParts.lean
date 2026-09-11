/- GID: D5/S1/Words/Compositions/StrictFirstSumsGapfreeOddParts
   generality: G
   mirror-B: D5/B/S1/Words/Compositions/StrictFirstSumsGapfreeOddParts
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Strict zero-prepended first sums correspond to gapfree odd partitions. -/

import D5.S1.Words.Compositions.ZeroPrependedFirstSumsOddParts

/-!
# Strict first sums and gapfree odd parts

The weak correspondence is reused from the frozen sibling. Its auxiliary
constants are private in a legacy (non-module-system) file, so `import all`
is unavailable. The local elaborator below returns the unique existing
constant; it creates no mathematical declaration and copies no proof.
This explicit coupling can disappear when an upstream public API is available.

The new content is the strict-row/complete-column-height characterization.
The empty partition is included: these counts have constant term one,
whereas the OEIS A053251 mock theta series has constant term zero.
-/

namespace D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts

open FirstSumsPartitionCharacterization ZeroPrependedFirstSumsOddParts

open Lean Elab Term in
local elab "sibling% " n:ident : term => do
  let userName := `D5.S1.Words.Compositions.ZeroPrependedFirstSumsOddParts ++ n.getId
  let found := (← getEnv).constants.toList.filter
    (fun (name, _) => privateToUserName? name == some userName)
  match found with
  | [(name, info)] => return mkConst name (info.levelParams.map Level.param)
  | _ => throwError "Expected one frozen sibling declaration: {userName}"

/-- Adjacent sums after prepending zero to a strictly increasing positive list. -/
def IsStrictFirstSums (y : List ℕ) : Prop :=
  ∃ s : List ℕ, s.Pairwise (· < ·) ∧ (∀ x ∈ s, 0 < x) ∧ firstSums (0 :: s) = y

/-- The support is exactly `{1,3,...,2*k-1}` for some k, including k=0. -/
def GapfreeOdd (m : Multiset ℕ) : Prop :=
  ∃ k : ℕ, ∀ x : ℕ, x ∈ m ↔ ∃ i < k, x = 2 * i + 1

private theorem strict_implies_weak {y : List ℕ} (hy : IsStrictFirstSums y) :
    IsZeroPrependedFirstSums y := by
  obtain ⟨s, hs, hp, he⟩ := hy
  exact ⟨s, hs.imp (fun h => Nat.le_of_lt h), hp, he⟩

private theorem gapfree_implies_odd {m : Multiset ℕ} (hm : GapfreeOdd m) :
    ∀ x ∈ m, ¬ Even x := by
  obtain ⟨k, hk⟩ := hm
  intro x hx
  obtain ⟨i, _, rfl⟩ := (hk x).mp hx
  rw [Nat.even_iff]
  omega

private theorem rowLen_zero (d : YoungDiagram) (i : ℕ) (hi : d.colLen 0 ≤ i) :
    d.rowLen i = 0 := by
  have h : ¬ (i, 0) ∈ d := by rw [YoungDiagram.mem_iff_lt_colLen]; omega
  rw [YoungDiagram.mem_iff_lt_rowLen] at h
  omega

-- Height h occurs among the columns precisely at a strict drop after row h-1.
private theorem height_mem_iff (d : YoungDiagram) (h : ℕ) (hp : 0 < h) :
    h ∈ d.transpose.rowLens ↔ d.rowLen h < d.rowLen (h - 1) := by
  constructor
  · intro hm
    obtain ⟨j, hj, he⟩ := List.mem_map.mp hm
    change d.transpose.rowLen j = h at he
    rw [YoungDiagram.rowLen_transpose] at he
    have hmem : (h - 1, j) ∈ d := by rw [YoungDiagram.mem_iff_lt_colLen, he]; omega
    have hnmem : ¬ (h, j) ∈ d := by rw [YoungDiagram.mem_iff_lt_colLen, he]; omega
    rw [YoungDiagram.mem_iff_lt_rowLen] at hmem hnmem
    omega
  · intro hdrop
    have hmem : (h - 1, d.rowLen h) ∈ d :=
      YoungDiagram.mem_iff_lt_rowLen.mpr hdrop
    have hnmem : ¬ (h, d.rowLen h) ∈ d := by
      rw [YoungDiagram.mem_iff_lt_rowLen]; omega
    rw [YoungDiagram.mem_iff_lt_colLen] at hmem hnmem
    have he : d.colLen (d.rowLen h) = h := by omega
    have hj : d.rowLen h < d.rowLen 0 :=
      lt_of_lt_of_le hdrop (d.rowLen_anti 0 (h - 1) (Nat.zero_le _))
    apply List.mem_map.mpr
    refine ⟨d.rowLen h, ?_, ?_⟩
    · simpa [YoungDiagram.colLen_transpose] using hj
    · simpa [YoungDiagram.rowLen_transpose] using he

private theorem height_bounds (d : YoungDiagram) (h : ℕ)
    (hm : h ∈ d.transpose.rowLens) : 0 < h ∧ h ≤ d.colLen 0 := by
  refine ⟨d.transpose.pos_of_mem_rowLens h hm, ?_⟩
  obtain ⟨j, _, he⟩ := List.mem_map.mp hm
  change d.transpose.rowLen j = h at he
  rw [YoungDiagram.rowLen_transpose] at he
  rw [← he]
  exact d.colLen_anti 0 j (Nat.zero_le _)

private theorem max_height_mem (d : YoungDiagram) (hp : 0 < d.colLen 0) :
    d.colLen 0 ∈ d.transpose.rowLens := by
  have hmem : (0, 0) ∈ d := YoungDiagram.mem_iff_lt_colLen.mpr hp
  rw [YoungDiagram.mem_iff_lt_rowLen] at hmem
  apply List.mem_map.mpr
  refine ⟨0, ?_, YoungDiagram.rowLen_transpose d 0⟩
  simpa [YoungDiagram.colLen_transpose] using hmem

private theorem strict_rows_iff_heights (d : YoungDiagram) :
    d.rowLens.Pairwise (· > ·) ↔
      ∀ h : ℕ, h ∈ d.transpose.rowLens ↔ 0 < h ∧ h ≤ d.colLen 0 := by
  constructor
  · intro hs h
    refine ⟨height_bounds d h, ?_⟩
    rintro ⟨hp, hb⟩
    apply (height_mem_iff d h hp).mpr
    have hi : h - 1 < d.rowLens.length := by rw [YoungDiagram.length_rowLens]; omega
    by_cases hh : h < d.rowLens.length
    · have hd := List.pairwise_iff_getElem.mp hs (h - 1) h hi hh (by omega)
      simpa only [YoungDiagram.get_rowLens] using hd
    · rw [rowLen_zero d h (by rw [YoungDiagram.length_rowLens] at hh; omega)]
      have hm := List.getElem_mem hi
      have hp' := d.pos_of_mem_rowLens _ hm
      simpa only [YoungDiagram.get_rowLens] using hp'
  · intro hs
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have hm := (hs (i + 1)).mpr ⟨by omega, by
      rw [YoungDiagram.length_rowLens] at hi hj
      omega⟩
    have hd := (height_mem_iff d (i + 1) (by omega)).mp hm
    have ha := d.rowLen_anti (i + 1) j (by omega)
    simp only [YoungDiagram.get_rowLens]
    simpa using lt_of_le_of_lt ha hd

private theorem strict_rows_iff_interval (d : YoungDiagram) :
    d.rowLens.Pairwise (· > ·) ↔
      ∃ k : ℕ, ∀ h : ℕ, h ∈ d.transpose.rowLens ↔ 0 < h ∧ h ≤ k := by
  constructor
  · intro hs
    exact ⟨d.colLen 0, (strict_rows_iff_heights d).mp hs⟩
  · rintro ⟨k, hk⟩
    have hk_le : k ≤ d.colLen 0 := by
      by_cases hp : 0 < k
      · exact (height_bounds d k ((hk k).mpr ⟨hp, le_rfl⟩)).2
      · omega
    have hl_le : d.colLen 0 ≤ k := by
      by_cases hp : 0 < d.colLen 0
      · exact ((hk _).mp (max_height_mem d hp)).2
      · omega
    have he : k = d.colLen 0 := by omega
    subst k
    exact (strict_rows_iff_heights d).mpr hk

private theorem oddify_gapfree (r : sibling% Rows) :
    GapfreeOdd ((sibling% oddify) r).val.val ↔
      ∃ k : ℕ, ∀ h : ℕ, h ∈ r.val ↔ 0 < h ∧ h ≤ k := by
  change (∃ k : ℕ, ∀ x : ℕ, x ∈ r.val.map (fun h => 2 * h - 1) ↔
    ∃ i < k, x = 2 * i + 1) ↔ _
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, fun h => ⟨?_, ?_⟩⟩
    · intro hh
      have hp := r.property.2 h hh
      have hm : 2 * h - 1 ∈ r.val.map (fun h => 2 * h - 1) :=
        List.mem_map.mpr ⟨h, hh, rfl⟩
      obtain ⟨i, hi, he⟩ := (hk _).mp hm
      exact ⟨hp, by omega⟩
    · rintro ⟨hp, hb⟩
      have hm := (hk (2 * h - 1)).mpr ⟨h - 1, by omega, by omega⟩
      obtain ⟨a, ha, he⟩ := List.mem_map.mp hm
      have hap := r.property.2 a ha
      have heq : a = h := by omega
      simpa only [heq] using ha
  · rintro ⟨k, hk⟩
    refine ⟨k, fun x => ⟨?_, ?_⟩⟩
    · intro hx
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
      obtain ⟨hp, hb⟩ := (hk h).mp hh
      exact ⟨h - 1, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      exact List.mem_map.mpr ⟨i + 1, (hk _).mpr ⟨by omega, by omega⟩, by omega⟩

private theorem row_gapfree (r : sibling% Rows) :
    r.val.Pairwise (· > ·) ↔
      GapfreeOdd ((sibling% oddify) ((sibling% conjugate) r)).val.val := by
  rw [oddify_gapfree]
  have h := strict_rows_iff_interval (YoungDiagram.ofRowLens r.val r.property.1)
  rw [YoungDiagram.rowLens_ofRowLens_eq_self r.property.2] at h
  exact h

private theorem strict_row_first (r : sibling% Rows) :
    IsStrictFirstSums (firstSums (0 :: r.val.reverse)) ↔ r.val.Pairwise (· > ·) := by
  constructor
  · rintro ⟨s, hs, _, he⟩
    have heq := (sibling% firstSums_injective) 0 he
    rw [heq] at hs
    simpa using hs.reverse
  · intro hs
    exact ⟨r.val.reverse, hs.reverse, by simpa using r.property.2, rfl⟩

private theorem firstOddEquiv_gapfree
    (y : {y : List ℕ // IsZeroPrependedFirstSums y}) :
    IsStrictFirstSums y.val ↔ GapfreeOdd ((sibling% firstOddEquiv) y).val.val := by
  obtain ⟨r, rfl⟩ := (sibling% rowFirstEquiv).surjective y
  change IsStrictFirstSums (firstSums (0 :: r.val.reverse)) ↔ _
  rw [strict_row_first]
  have he : (sibling% firstOddEquiv) ((sibling% rowFirstEquiv) r) =
      (sibling% oddify) ((sibling% conjugate) r) := by
    change (sibling% oddify) ((sibling% conjugate)
      ((sibling% rowFirstEquiv).symm ((sibling% rowFirstEquiv) r))) = _
    rw [Equiv.symm_apply_apply]
  rw [he]
  exact row_gapfree r

private noncomputable def strictPartitionEquiv (n : ℕ) :
    {p : Nat.Partition n // IsStrictFirstSums (p.parts.sort (· ≤ ·))} ≃
      {p : Nat.Partition n // GapfreeOdd p.parts} := by
  let e := ((sibling% firstListEquiv) n).trans
    (((sibling% firstOddEquiv).subtypeEquiv (fun y => by
      rw [sibling% firstOddEquiv_sum])).trans ((sibling% oddListEquiv) n).symm)
  have h (p : {p : Nat.Partition n //
      IsZeroPrependedFirstSums (p.parts.sort (· ≤ ·))}) :
      IsStrictFirstSums (p.val.parts.sort (· ≤ ·)) ↔ GapfreeOdd (e p).val.parts := by
    exact firstOddEquiv_gapfree (((sibling% firstListEquiv) n) p).val
  exact (Equiv.subtypeSubtypeEquivSubtype (fun hy => strict_implies_weak hy)).symm.trans
    ((e.subtypeEquiv h).trans
      (Equiv.subtypeSubtypeEquivSubtype (fun hm => gapfree_implies_odd hm)))

open scoped Classical in
/-- Strict zero-prepended first-sums partitions are counted by gapfree odd partitions. -/
theorem card_strictFirstSums_eq_gapfreeOdd (n : ℕ) :
    ((Finset.univ : Finset (Nat.Partition n)).filter
      (fun p => IsStrictFirstSums (p.parts.sort (· ≤ ·)))).card =
    ((Finset.univ : Finset (Nat.Partition n)).filter
      (fun p => GapfreeOdd p.parts)).card := by
  classical
  simpa only [Fintype.card_subtype] using Fintype.card_congr (strictPartitionEquiv n)

end D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts
