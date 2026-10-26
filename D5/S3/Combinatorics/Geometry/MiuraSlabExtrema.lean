/- GID: D5/S3/Combinatorics/Geometry/MiuraSlabExtrema
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraSlabExtrema
   mirror-E: none(waiver:non-computational)
   anchors: []
   utility: none
   digest: Matching rectangular slab types force actual ambient extrema. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraStripRigidity
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Interval.Finset.Fin

/-! Slab boundary signs and actual ambient extrema. -/

@[expose] public section

namespace D5.S3.Combinatorics.Geometry.MiuraSlabExtrema

open MiuraHeightEnvelope MiuraStripRigidity

variable {m n : ℕ}

/-- A nonempty interval of actual grid coordinates, including physical ends. -/
structure Interval (m : ℕ) where
  first : Fin m
  last : Fin m
  ordered : first ≤ last
  deriving DecidableEq

namespace Interval

def Contains (I : Interval m) (i : Fin m) : Prop := I.first ≤ i ∧ i ≤ I.last

def rows (I : Interval m) : Finset (Fin m) := Finset.Icc I.first I.last

@[simp] theorem mem_rows (I : Interval m) (i : Fin m) : i ∈ I.rows ↔ I.Contains i := by
  simp [rows, Contains]

end Interval

/-- The actual rectangle cut out by two coordinate intervals. -/
def rectangle (I : Interval m) (J : Interval n) : Finset (Cell m n) :=
  I.rows ×ˢ J.rows

/-- All existing vertical edges leaving the row interval go up by `s`.
No edge is postulated beyond the physical boundary. -/
def RowOutward (h : Cell m n → ℤ) (I : Interval m) (s : ℤ) : Prop :=
  ∀ v u : Cell m n, I.Contains v.1 → ¬ I.Contains u.1 → adj v u → h u = h v + s

/-- All existing horizontal edges leaving the column interval go up by `s`. -/
def ColOutward (h : Cell m n → ℤ) (J : Interval n) (s : ℤ) : Prop :=
  ∀ v u : Cell m n, J.Contains v.2 → ¬ J.Contains u.2 → adj v u → h u = h v + s

/-- Matching minimum-type row and column intervals force a minimum of the
same ambient array, with all ambient neighbours retained. -/
theorem matching_minimum {h : Cell m n → ℤ} (hh : IsHeight h)
    (I : Interval m) (J : Interval n)
    (hrow : RowOutward h I 1) (hcol : ColOutward h J 1) :
    ∃ v ∈ rectangle I J, IsStrictLocalMin h v := by
  classical
  have hne : (rectangle I J).Nonempty := by
    refine ⟨(I.first, J.first), ?_⟩
    simp [rectangle, Interval.Contains, I.ordered, J.ordered]
  obtain ⟨v, hv, hleast⟩ := Finset.exists_min_image (rectangle I J) h hne
  refine ⟨v, hv, ?_⟩
  intro u hadj
  have hv' : I.Contains v.1 ∧ J.Contains v.2 := by
    simpa only [rectangle, Finset.mem_product, Interval.mem_rows] using hv
  by_cases hr : I.Contains u.1
  · by_cases hc : J.Contains u.2
    · have hu : u ∈ rectangle I J := by
        simpa only [rectangle, Finset.mem_product, Interval.mem_rows] using And.intro hr hc
      have hle := hleast u hu
      have hedge := hh v u hadj
      rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at hedge
      omega
    · exact hcol v u hv'.2 hc hadj
  · exact hrow v u hv'.1 hr hadj

/-- Matching maximum-type intervals force a full-grid maximum. -/
theorem matching_maximum {h : Cell m n → ℤ} (hh : IsHeight h)
    (I : Interval m) (J : Interval n)
    (hrow : RowOutward h I (-1)) (hcol : ColOutward h J (-1)) :
    ∃ v ∈ rectangle I J, IsStrictLocalMax h v := by
  have hn : IsHeight (fun v => -h v) := by
    intro v u hadj
    have he := hh v u hadj
    simpa only [neg_sub_neg, abs_sub_comm] using he
  obtain ⟨v, hv, hmin⟩ := matching_minimum hn I J (by
    intro v u hv hu hadj
    have he := hrow v u hv hu hadj
    dsimp
    omega) (by
    intro v u hv hu hadj
    have he := hcol v u hv hu hadj
    dsimp
    omega)
  refine ⟨v, hv, ?_⟩
  intro u hu
  have := hmin u hu
  dsimp at this
  omega

end D5.S3.Combinatorics.Geometry.MiuraSlabExtrema
