/- GID: D5/S3/Combinatorics/Graph/Domination/PathEndpointCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/PathEndpointCount
   mirror-E: none(waiver:unbounded-constructive-proof)
   anchors: []
   utility: none
   digest: Two-endpoint path subsets have an explicit inverse middle restriction. -/

module

public import D5.S3.Combinatorics.Graph.Domination.PathMaximalIndependentCount

/-! Restrict actual path maximal independent sets by their two endpoint labels. -/

@[expose] public section

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Domination.PathEndpointCount

open Finset
open PathMaximalIndependentCount

/-- Add both endpoints, shifting the middle path by two. -/
def cap (n : ℕ) (I : Finset ℕ) : Finset ℕ :=
  insert 0 (insert (n + 3) (I.image (fun i => i + 2)))

/-- Delete the endpoints and their excluded neighbors. -/
def middle (n : ℕ) (I : Finset ℕ) : Finset ℕ :=
  (I.filter (fun i => 2 ≤ i ∧ i < n + 2)).image (fun i => i - 2)

@[simp] private theorem mem_cap_shift (n : ℕ) (I : Finset ℕ) (i : ℕ) (hi : i < n) :
    i + 2 ∈ cap n I ↔ i ∈ I := by
  have h0 : i + 2 ≠ 0 := by omega
  have hn : i + 2 ≠ n + 3 := by omega
  simp [cap]
  omega

private theorem valid_cap (n : ℕ) (I : Finset ℕ) (hI : Valid n I) :
    Valid (n + 4) (cap n I) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rcases mem_insert.mp hi with h0 | hi
    · omega
    · rcases mem_insert.mp hi with hn | hi
      · omega
      · obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
        have hb := hI.1 j hj
        omega
  · intro i hi hnext
    rcases mem_insert.mp hi with h0 | hi
    · rcases mem_insert.mp hnext with hh | hh
      · omega
      · rcases mem_insert.mp hh with hh | hh
        · omega
        · obtain ⟨j, hj, he⟩ := mem_image.mp hh
          omega
    · rcases mem_insert.mp hi with hn | hi
      · rcases mem_insert.mp hnext with hh | hh
        · omega
        · rcases mem_insert.mp hh with hh | hh
          · omega
          · obtain ⟨j, hj, he⟩ := mem_image.mp hh
            have hb := hI.1 j hj
            omega
      · obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
        have hb := hI.1 j hj
        rcases mem_insert.mp hnext with hh | hh
        · omega
        · rcases mem_insert.mp hh with hh | hh
          · omega
          · obtain ⟨k, hk, he⟩ := mem_image.mp hh
            have hkj : k = j + 1 := by omega
            exact hI.2.1 j hj (hkj ▸ hk)
  · intro i hin
    by_cases h0 : i = 0
    · exact Or.inl (mem_insert.mpr (Or.inl h0))
    by_cases h1 : i = 1
    · exact Or.inr ⟨0, mem_insert_self _ _, Or.inr (by omega)⟩
    by_cases h2 : i = n + 2
    · exact Or.inr ⟨n + 3, mem_insert_of_mem (mem_insert_self _ _), Or.inl (by omega)⟩
    by_cases h3 : i = n + 3
    · exact Or.inl (mem_insert_of_mem (mem_insert_self _ _) |> fun h => h3 ▸ h)
    have hmid : i - 2 < n := by omega
    rcases hI.2.2 (i - 2) hmid with h | ⟨j, hj, hji⟩
    · left
      have he : i = (i - 2) + 2 := by omega
      rw [he]
      exact (mem_cap_shift n I _ hmid).mpr h
    · right
      exact ⟨j + 2, (mem_cap_shift n I j (hI.1 j hj)).mpr hj, by omega⟩

private theorem middle_valid {n : ℕ} {I : Finset ℕ} (hI : Valid (n + 4) I)
    (h0 : 0 ∈ I) (hl : n + 3 ∈ I) : Valid n (middle n I) := by
  have h1 : 1 ∉ I := hI.2.1 0 h0
  have h2 : n + 2 ∉ I := fun h => hI.2.1 (n + 2) h hl
  have hmem (i : ℕ) : i ∈ middle n I ↔ i + 2 ∈ I ∧ i < n := by
    constructor
    · intro hi
      obtain ⟨j, hj, he⟩ := mem_image.mp hi
      obtain ⟨hj, hjlo, hjhi⟩ := mem_filter.mp hj
      have hji : j = i + 2 := by omega
      exact ⟨hji ▸ hj, by omega⟩
    · rintro ⟨hi, hin⟩
      exact mem_image.mpr ⟨i + 2, mem_filter.mpr ⟨hi, by omega, by omega⟩, by omega⟩
  refine ⟨fun i hi => ((hmem i).mp hi).2, ?_, ?_⟩
  · intro i hi hnext
    have hi' := ((hmem i).mp hi).1
    have hn' := ((hmem (i + 1)).mp hnext).1
    exact hI.2.1 (i + 2) hi' (by convert hn' using 1 <;> omega)
  · intro i hin
    rcases hI.2.2 (i + 2) (by omega) with hi | ⟨j, hj, hji⟩
    · exact Or.inl ((hmem i).mpr ⟨hi, hin⟩)
    · have hb := hI.1 j hj
      have hj1 : j ≠ 1 := fun h => h1 (h ▸ hj)
      have hj2 : j ≠ n + 2 := fun h => h2 (h ▸ hj)
      have hjlo : 2 ≤ j := by omega
      have hjhi : j - 2 < n := by omega
      have hshift : (j - 2) + 2 = j := by omega
      refine Or.inr ⟨j - 2, (hmem _).mpr ⟨hshift.symm ▸ hj, hjhi⟩, ?_⟩
      omega

private theorem cap_middle {n : ℕ} {I : Finset ℕ} (hI : Valid (n + 4) I)
    (h0 : 0 ∈ I) (hl : n + 3 ∈ I) : cap n (middle n I) = I := by
  have h1 : 1 ∉ I := hI.2.1 0 h0
  have h2 : n + 2 ∉ I := fun h => hI.2.1 (n + 2) h hl
  ext i
  constructor
  · intro hi
    rcases mem_insert.mp hi with hi | hi
    · exact hi ▸ h0
    · rcases mem_insert.mp hi with hi | hi
      · exact hi ▸ hl
      · obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
        obtain ⟨k, hk, he⟩ := mem_image.mp hj
        obtain ⟨hk, hklo, hkhi⟩ := mem_filter.mp hk
        have hkj : k = j + 2 := by omega
        exact hkj ▸ hk
  · intro hi
    have hb := hI.1 i hi
    by_cases hi0 : i = 0
    · exact mem_insert.mpr (Or.inl hi0)
    by_cases hil : i = n + 3
    · exact mem_insert_of_mem (mem_insert.mpr (Or.inl hil))
    have hi1 : i ≠ 1 := fun h => h1 (h ▸ hi)
    have hi2 : i ≠ n + 2 := fun h => h2 (h ▸ hi)
    have him : 2 ≤ i ∧ i < n + 2 := by omega
    apply mem_insert_of_mem
    apply mem_insert_of_mem
    exact mem_image.mpr ⟨i - 2, mem_image.mpr ⟨i, mem_filter.mpr ⟨hi, him⟩, rfl⟩, by omega⟩

/-- Actual maximal independent subsets containing both endpoints. -/
noncomputable def bothFamily (n : ℕ) : Finset (Finset ℕ) :=
  (family n).filter (fun I => 0 ∈ I ∧ n - 1 ∈ I)

/-- Actual maximal independent subsets omitting at least one endpoint. -/
noncomputable def restrictedFamily (n : ℕ) : Finset (Finset ℕ) :=
  (family n).filter (fun I => ¬ (0 ∈ I ∧ n - 1 ∈ I))

/-- The restricted path count, with source-series convention below order three. -/
noncomputable def restrictedCount (n : ℕ) : ℕ :=
  if 3 ≤ n then (restrictedFamily n).card else 0

private theorem bothFamily_eq (n : ℕ) : bothFamily (n + 4) = (family n).image (cap n) := by
  classical
  ext I
  constructor
  · intro hi
    obtain ⟨hi, h0, hl⟩ := mem_filter.mp hi
    have hv := (mem_family _ _).mp hi
    have hl' : n + 3 ∈ I := by simpa using hl
    exact mem_image.mpr ⟨middle n I,
      (mem_family _ _).mpr (middle_valid hv h0 hl'), cap_middle hv h0 hl'⟩
  · intro hi
    obtain ⟨J, hJ, rfl⟩ := mem_image.mp hi
    apply mem_filter.mpr
    refine ⟨(mem_family _ _).mpr (valid_cap n J ((mem_family _ _).mp hJ)), ?_, ?_⟩
    · exact mem_insert_self _ _
    · change n + 3 ∈ cap n J
      exact mem_insert_of_mem (mem_insert_self _ _)

/-- Deleting the two endpoints and their neighbors leaves an arbitrary n-vertex path. -/
theorem both_count (n : ℕ) : (bothFamily (n + 4)).card = count n := by
  classical
  rw [bothFamily_eq, card_image_of_injOn]
  · rfl
  · intro I hI J hJ heq
    have hvI := (mem_family _ _).mp hI
    have hvJ := (mem_family _ _).mp hJ
    ext i
    by_cases hi : i < n
    · have he := congrArg (fun S : Finset ℕ => i + 2 ∈ S) heq
      exact (mem_cap_shift n I i hi).symm.trans
        (he.to_iff.trans (mem_cap_shift n J i hi))
    · exact iff_of_false (fun h => hi (hvI.1 i h)) (fun h => hi (hvJ.1 i h))

/-- Restricted and forbidden endpoint families partition every order n+4. -/
theorem restricted_complement (n : ℕ) :
    restrictedCount (n + 4) + count n = count (n + 4) := by
  classical
  rw [restrictedCount, if_pos (by omega), ← both_count]
  have h := card_filter_add_card_filter_not (s := family (n + 4))
    (fun I => 0 ∈ I ∧ n + 4 - 1 ∈ I)
  simpa [restrictedFamily, bothFamily, count, add_comm] using h

private theorem restrictedFamily_three : restrictedFamily 3 = {{1}} := by
  classical
  ext I
  constructor
  · intro h
    obtain ⟨hf, he⟩ := mem_filter.mp h
    have hv := (mem_family _ _).mp hf
    have hone : 1 ∈ I := by
      by_contra hn
      have h0 : 0 ∈ I := by
        rcases hv.2.2 0 (by omega) with h | ⟨j, hj, hji⟩
        · exact h
        · have hj1 : j = 1 := by omega
          exact False.elim (hn (hj1 ▸ hj))
      have h2 : 2 ∈ I := by
        rcases hv.2.2 2 (by omega) with h | ⟨j, hj, hji⟩
        · exact h
        · have hb := hv.1 j hj
          have hj1 : j = 1 := by omega
          exact False.elim (hn (hj1 ▸ hj))
      exact he ⟨h0, h2⟩
    have h0 : 0 ∉ I := fun h => hv.2.1 0 h hone
    have h2 : 2 ∉ I := hv.2.1 1 hone
    apply mem_singleton.mpr
    ext i
    constructor
    · intro hi
      have hb := hv.1 i hi
      have hi1 : i = 1 := by
        by_contra hn
        have hcases : i = 0 ∨ i = 2 := by omega
        exact hcases.elim (fun h => h0 (h ▸ hi)) (fun h => h2 (h ▸ hi))
      exact mem_singleton.mpr hi1
    · intro hi
      exact mem_singleton.mp hi ▸ hone
  · intro h
    have he := mem_singleton.mp h
    subst I
    apply mem_filter.mpr
    refine ⟨(mem_family _ _).mpr (valid_singleton 3 1 (by omega) ?_), by simp⟩
    intro i hi
    omega

/-- The entire zero prefix and the cubic boundary belong to the series convention. -/
theorem restricted_initial : restrictedCount 0 = 0 ∧ restrictedCount 1 = 0 ∧
    restrictedCount 2 = 0 ∧ restrictedCount 3 = 1 := by
  simp [restrictedCount, restrictedFamily_three]

end D5.S3.Combinatorics.Graph.Domination.PathEndpointCount
