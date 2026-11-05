/- GID: D5/S3/Combinatorics/Geometry/MiuraEqualityClassification
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraEqualityClassification
   mirror-E: none(waiver:non-computational)
   anchors: []
   utility: none
   digest: Actual run equality is single-side or degree four, giving the strict residual bound. -/
module
public import D5.S3.Combinatorics.Geometry.MiuraEqualitySides
import all D5.S3.Combinatorics.Geometry.MiuraSlabIncidence

/-! Geometric equality and the strict original residual run bound. -/
@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraEqualityClassification
open MiuraHeightEnvelope MiuraSlabExtrema MiuraSlabNeutral MiuraSlabIncidence
open MiuraSlabRunBound MiuraEqualityCrossed MiuraEqualitySides MiuraResidualCount
variable {m n : ℕ}

private theorem min_transpose_iff (h : Cell m n → ℤ) (v : Cell m n) :
    IsStrictLocalMin (transposeHeight h) (v.2, v.1) ↔ IsStrictLocalMin h v := by
  constructor
  · exact fun hv => transpose_min hv
  · exact fun hv => transpose_min (h := transposeHeight h) hv

private theorem max_transpose_iff (h : Cell m n → ℤ) (v : Cell m n) :
    IsStrictLocalMax (transposeHeight h) (v.2, v.1) ↔ IsStrictLocalMax h v := by
  constructor
  · exact fun hv => transpose_max hv
  · exact fun hv => transpose_max (h := transposeHeight h) hv

private theorem extrema_card_transpose (h : Cell m n → ℤ) :
    (extrema (transposeHeight h)).card = (extrema h).card := by
  classical
  symm
  apply Finset.card_bij (fun v _ => (v.2, v.1))
  · intro v hv
    have hx : IsStrictLocalMin h v ∨ IsStrictLocalMax h v := (Finset.mem_filter.mp hv).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hx with hx | hx
    · exact Or.inl ((min_transpose_iff h v).mpr hx)
    · exact Or.inr ((max_transpose_iff h v).mpr hx)
  · intro v hv u hu he
    exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
  · intro v hv
    have hx : IsStrictLocalMin (transposeHeight h) v ∨ IsStrictLocalMax (transposeHeight h) v :=
      (Finset.mem_filter.mp hv).2
    refine ⟨(v.2, v.1), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hx with hx | hx
    · exact Or.inl (transpose_min hx)
    · exact Or.inr (transpose_max hx)

/-- Equality in the actual frozen-run bound places all original minima on
one common physical side, unless there are exactly four individual extrema. -/
theorem equality_single_side_or_four {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hr : ∃ i, ¬ RowOccupied h i) (hc : ∃ j, ¬ RowOccupied (transposeHeight h) j)
    (heq : (extrema h).card = (frozenRowRunStarts h).card +
      (frozenRowRunStarts (transposeHeight h)).card) :
    (∃ sd : Side, AllOnSide
      (fun v : Cell m n => ((v.1.val : ℤ) + 1, (v.2.val : ℤ) + 1))
      (minima h) (m : ℤ) (n : ℤ) sd) ∨ (extrema h).card = 4 := by
  classical
  rcases equality_two_slabs_or_four hh hm hn hr hc heq with
    ⟨hrm, hrM⟩ | ⟨hcm, hcM⟩ | hfour
  · rcases equality_two_row_types_minima_boundary hh hm hn hr hc heq hrm hrM with ht | hb
    · left; refine ⟨.top, ?_⟩
      change ∀ v ∈ minima h, (v.1.val : ℤ) + 1 = 1
      intro v hv
      have he := ht v (Finset.mem_filter.mp hv).2
      omega
    · left; refine ⟨.bottom, ?_⟩
      change ∀ v ∈ minima h, (v.1.val : ℤ) + 1 = (m : ℤ)
      intro v hv
      have he := hb v (Finset.mem_filter.mp hv).2
      omega
  · have hct : ∃ i, ¬ RowOccupied (transposeHeight (transposeHeight h)) i := hr
    have het : (extrema (transposeHeight h)).card =
        (frozenRowRunStarts (transposeHeight h)).card +
        (frozenRowRunStarts (transposeHeight (transposeHeight h))).card := by
      rw [extrema_card_transpose]
      change (extrema h).card = (frozenRowRunStarts (transposeHeight h)).card + (frozenRowRunStarts h).card
      omega
    rcases equality_two_row_types_minima_boundary (transpose_isHeight hh) hn hm hc hct het hcm hcM with ht | hb
    · left; refine ⟨.left, ?_⟩
      change ∀ v ∈ minima h, (v.2.val : ℤ) + 1 = 1
      intro v hv
      have he := ht (v.2, v.1) ((min_transpose_iff h v).mpr (Finset.mem_filter.mp hv).2)
      change v.2.val = 0 at he
      omega
    · left; refine ⟨.right, ?_⟩
      change ∀ v ∈ minima h, (v.2.val : ℤ) + 1 = (n : ℤ)
      intro v hv
      have he := hb (v.2, v.1) ((min_transpose_iff h v).mpr (Finset.mem_filter.mp hv).2)
      change v.2.val + 1 = n at he
      omega
  · exact Or.inr hfour

/-- The same actual normalized residual array with d at least five and a
frozen row on each axis has at most d minus one frozen runs in total. -/
theorem residual_frozen_runs_strict {h : Cell m n → ℤ} {a b d : ℕ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hd : 5 ≤ d) (hsplit : a + b = d)
    (hres : Residual a b h)
    (hr : ∃ i, ¬ RowOccupied h i) (hc : ∃ j, ¬ RowOccupied (transposeHeight h) j) :
    (frozenRowRunStarts h).card + (frozenRowRunStarts (transposeHeight h)).card ≤ d - 1 := by
  have hh : IsHeight h := hres.1.1
  have hext : (extrema h).card = d := by
    rw [extrema_card_split hm h, hres.2.1, hres.2.2.1, hsplit]
  have hbound := frozen_runs_le_extrema hh hm hn hr hc
  by_contra hnot
  have heq : (extrema h).card = (frozenRowRunStarts h).card +
      (frozenRowRunStarts (transposeHeight h)).card := by omega
  rcases equality_single_side_or_four hh hm hn hr hc heq with hside | hfour
  · exact hres.2.2.2 hside
  · omega
end D5.S3.Combinatorics.Geometry.MiuraEqualityClassification
