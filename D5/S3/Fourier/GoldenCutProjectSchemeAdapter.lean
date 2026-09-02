/- GID: D5/S3/Fourier/GoldenCutProjectSchemeAdapter
   generality: I
   mirror-B: D5/B/S3/Fourier/GoldenCutProjectSchemeAdapter
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: The existing golden Minkowski lattice instantiates the generic cut-and-project carrier without changing its model sets. -/

import D5.S1.Scale.MinkowskiModelSet
import D5.S3.Fourier.CutProjectScheme

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.GoldenCutProjectSchemeAdapter

open D5.S0.Carrier
open D5.S1.Depth
open D5.S1.Scale
open D5.S3.Fourier.CutProjectScheme

/-- The golden Minkowski lattice as an instance of the generic cut-and-project carrier. -/
noncomputable def goldenScheme : Scheme ℝ ℝ where
  lattice := D5.S1.Scale.goldenLattice
  physical_injective := by
    rintro ⟨left, hLeft⟩ ⟨right, hRight⟩ hPhysical
    apply Subtype.ext
    change left.1 = right.1 at hPhysical
    change left ∈ AddMonoidHom.range D5.S1.Scale.minkowskiEmbedding at hLeft
    change right ∈ AddMonoidHom.range D5.S1.Scale.minkowskiEmbedding at hRight
    rcases hLeft with ⟨x, rfl⟩
    rcases hRight with ⟨y, rfl⟩
    change embedding x = embedding y at hPhysical
    exact congrArg D5.S1.Scale.minkowskiEmbedding (embedding_injective hPhysical)

/-- The generic window construction recovers the repository's existing golden model set exactly. -/
theorem goldenScheme_modelSet_eq (window : Set ℝ) :
    goldenScheme.modelSet window = D5.S1.Scale.modelSet window := by
  ext y
  constructor
  · intro hy
    rcases (goldenScheme.mem_modelSet_iff window y).1 hy with
      ⟨point, hInternal, hPhysical⟩
    rcases point with ⟨point, hPoint⟩
    change point ∈ AddMonoidHom.range D5.S1.Scale.minkowskiEmbedding at hPoint
    rcases hPoint with ⟨x, rfl⟩
    change embedding (conj x) ∈ window at hInternal
    change embedding x = y at hPhysical
    exact ⟨x, hPhysical, hInternal⟩
  · intro hy
    change ∃ x : GoldenInt,
      embedding x = y ∧ embedding (conj x) ∈ window at hy
    rcases hy with ⟨x, hPhysical, hInternal⟩
    let point : goldenScheme.lattice :=
      ⟨D5.S1.Scale.minkowskiEmbedding x, by
        change D5.S1.Scale.minkowskiEmbedding x ∈
          AddMonoidHom.range D5.S1.Scale.minkowskiEmbedding
        exact ⟨x, rfl⟩⟩
    exact (goldenScheme.mem_modelSet_iff window y).2
      ⟨point,
        by
          simpa [point, goldenScheme, Scheme.internalProjection,
            D5.S1.Scale.minkowskiEmbedding] using hInternal,
        by
          simpa [point, goldenScheme, Scheme.physicalProjection,
            D5.S1.Scale.minkowskiEmbedding] using hPhysical⟩

/-- Window intersection for the old golden model set is inherited from the generic scheme. -/
theorem golden_modelSet_inter (left right : Set ℝ) :
    D5.S1.Scale.modelSet (left ∩ right) =
      D5.S1.Scale.modelSet left ∩ D5.S1.Scale.modelSet right := by
  rw [← goldenScheme_modelSet_eq, goldenScheme.modelSet_inter,
    goldenScheme_modelSet_eq, goldenScheme_modelSet_eq]

#print axioms goldenScheme_modelSet_eq
#print axioms golden_modelSet_inter

end D5.S3.Fourier.GoldenCutProjectSchemeAdapter
