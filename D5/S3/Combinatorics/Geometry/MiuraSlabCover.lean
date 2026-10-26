/- GID: D5/S3/Combinatorics/Geometry/MiuraSlabCover
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraSlabCover
   mirror-E: none(waiver:non-computational)
   anchors: []
   utility: none
   digest: Every occupied row belongs to a unique actual maximal occupied interval. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraSlabIncidence

/-! Existence and uniqueness of canonical occupied slabs in the actual grid. -/

@[expose] public section

namespace D5.S3.Combinatorics.Geometry.MiuraSlabCover

open MiuraHeightEnvelope MiuraSlabExtrema MiuraSlabNeutral MiuraSlabIncidence

variable {m n : ℕ}

/-- An actual occupied row extends to a maximal occupied interval. -/
theorem occupied_row_has_slab (h : Cell m n → ℤ) (i : Fin m) (hi : RowOccupied h i) :
    ∃ I : Interval m, I.Contains i ∧ IsRowSlab h I := by
  classical
  let T : Finset (Interval m) := Finset.univ.filter (fun I =>
    I.Contains i ∧ ∀ j, I.Contains j → RowOccupied h j)
  let single : Interval m := ⟨i, i, le_rfl⟩
  have hsingle : single ∈ T := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨le_rfl, le_rfl⟩, ?_⟩
    intro j hj
    have he : j = i := le_antisymm hj.2 hj.1
    exact he.symm ▸ hi
  obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image T
    (fun I => I.last.val - I.first.val) ⟨single, hsingle⟩
  have hI' := (Finset.mem_filter.mp hI).2
  refine ⟨I, hI'.1, hI'.2, ?_, ?_⟩
  · intro k hk hko
    let J : Interval m := ⟨k, I.last, by
      change k.val ≤ I.last.val
      have := I.ordered
      change I.first.val ≤ I.last.val at this
      omega⟩
    have hJT : J ∈ T := by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · change k.val ≤ i.val ∧ i.val ≤ I.last.val
        have hi' : I.first.val ≤ i.val ∧ i.val ≤ I.last.val := hI'.1
        omega
      · intro j hj
        by_cases he : j = k
        · exact he.symm ▸ hko
        · apply hI'.2 j
          change I.first.val ≤ j.val ∧ j.val ≤ I.last.val
          change k.val ≤ j.val ∧ j.val ≤ I.last.val at hj
          have hne : j.val ≠ k.val := by intro hv; exact he (Fin.ext hv)
          omega
    have he := hmax J hJT
    change I.last.val - k.val ≤ I.last.val - I.first.val at he
    have := I.ordered
    change I.first.val ≤ I.last.val at this
    omega
  · intro k hk hko
    let J : Interval m := ⟨I.first, k, by
      change I.first.val ≤ k.val
      have := I.ordered
      change I.first.val ≤ I.last.val at this
      omega⟩
    have hJT : J ∈ T := by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · change I.first.val ≤ i.val ∧ i.val ≤ k.val
        have hi' : I.first.val ≤ i.val ∧ i.val ≤ I.last.val := hI'.1
        omega
      · intro j hj
        by_cases he : j = k
        · exact he.symm ▸ hko
        · apply hI'.2 j
          change I.first.val ≤ j.val ∧ j.val ≤ I.last.val
          change I.first.val ≤ j.val ∧ j.val ≤ k.val at hj
          have hne : j.val ≠ k.val := by intro hv; exact he (Fin.ext hv)
          omega
    have he := hmax J hJT
    change k.val - I.first.val ≤ I.last.val - I.first.val at he
    have := I.ordered
    change I.first.val ≤ I.last.val at this
    omega

end D5.S3.Combinatorics.Geometry.MiuraSlabCover
