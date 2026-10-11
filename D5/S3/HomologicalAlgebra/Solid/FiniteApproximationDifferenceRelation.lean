/- GID: D5/S3/HomologicalAlgebra/Solid/FiniteApproximationDifferenceRelation
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/FiniteApproximationDifferenceRelation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.FiniteApproximationDifferences
import Mathlib.Topology.Category.CompHausLike.Limits

/-!
The full kernel pair of the actual representative-difference cover is covered
by its diagonal and its infinity fiber. Both pieces are closed light-profinite
spaces, and their finite coproduct maps surjectively onto the whole relation.
These concrete data justify free sheaf descent; equality only on ordinary
finite points is not substituted for the kernel-pair relation.
New proofs, Apache-2.0; Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightProfinite OnePoint

namespace CWSolid

def finiteApproximationDifferenceRelationSpace (S : LightProfinite) (s₀ : S) :
    LightProfinite := by
  let E := finiteApproximationDifferenceSpace S s₀
  let R := {x : E × E | finiteApproximationDifferenceProjection S s₀ x.1 =
    finiteApproximationDifferenceProjection S s₀ x.2}
  have hR : IsClosed R :=
    isClosed_eq ((finiteApproximationDifferenceProjection S s₀).hom.hom.continuous.comp
      continuous_fst) ((finiteApproximationDifferenceProjection S s₀).hom.hom.continuous.comp
      continuous_snd)
  letI : CompactSpace R := isCompact_iff_compactSpace.mp hR.isCompact
  exact LightProfinite.of R

def finiteApproximationDifferenceRelationFst (S : LightProfinite) (s₀ : S) :
    finiteApproximationDifferenceRelationSpace S s₀ ⟶ finiteApproximationDifferenceSpace S s₀ :=
  ConcreteCategory.ofHom ⟨fun r => r.val.1, continuous_fst.comp continuous_subtype_val⟩

def finiteApproximationDifferenceRelationSnd (S : LightProfinite) (s₀ : S) :
    finiteApproximationDifferenceRelationSpace S s₀ ⟶ finiteApproximationDifferenceSpace S s₀ :=
  ConcreteCategory.ofHom ⟨fun r => r.val.2, continuous_snd.comp continuous_subtype_val⟩

def finiteApproximationDifferenceRelationPiece (S : LightProfinite) (s₀ : S)
    (b : Bool) : Set (finiteApproximationDifferenceRelationSpace S s₀) :=
  if b then {r | finiteApproximationDifferenceProjection S s₀ r.val.1 = ∞}
  else {r | r.val.1 = r.val.2}

theorem finiteApproximationDifferenceRelationPiece_closed
    (S : LightProfinite) (s₀ : S) (b : Bool) :
    IsClosed (finiteApproximationDifferenceRelationPiece S s₀ b) := by
  cases b
  · exact isClosed_eq (continuous_fst.comp continuous_subtype_val)
      (continuous_snd.comp continuous_subtype_val)
  · exact isClosed_eq
      ((finiteApproximationDifferenceProjection S s₀).hom.hom.continuous.comp
        (continuous_fst.comp continuous_subtype_val)) continuous_const

theorem finiteApproximationDifferenceRelationPiece_cover (S : LightProfinite) (s₀ : S)
    (r : finiteApproximationDifferenceRelationSpace S s₀) :
    ∃ b : Bool, r ∈ finiteApproximationDifferenceRelationPiece S s₀ b := by
  cases hp : finiteApproximationDifferenceProjection S s₀ r.val.1 using OnePoint.rec
  · exact ⟨true, hp⟩
  · rename_i k
    refine ⟨false, ?_⟩
    exact (finiteApproximationDifference_finite_fiber S s₀ r.val.1 k hp).trans
      (finiteApproximationDifference_finite_fiber S s₀ r.val.2 k
        (r.property.symm.trans hp)).symm

def finiteApproximationDifferenceRelationPieceSpace (S : LightProfinite) (s₀ : S)
    (b : Bool) : LightProfinite := by
  let C := finiteApproximationDifferenceRelationPiece S s₀ b
  letI : CompactSpace C := isCompact_iff_compactSpace.mp
    (finiteApproximationDifferenceRelationPiece_closed S s₀ b).isCompact
  exact LightProfinite.of C

def finiteApproximationDifferenceRelationPieceInclusion (S : LightProfinite) (s₀ : S)
    (b : Bool) : finiteApproximationDifferenceRelationPieceSpace S s₀ b ⟶
      finiteApproximationDifferenceRelationSpace S s₀ :=
  ConcreteCategory.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def finiteApproximationDifferenceRelationCover (S : LightProfinite) (s₀ : S) :
    CompHausLike.finiteCoproduct (finiteApproximationDifferenceRelationPieceSpace S s₀) ⟶
      finiteApproximationDifferenceRelationSpace S s₀ :=
  CompHausLike.finiteCoproduct.desc (finiteApproximationDifferenceRelationPieceSpace S s₀)
    (finiteApproximationDifferenceRelationPieceInclusion S s₀)

theorem finiteApproximationDifferenceRelationCover_surjective
    (S : LightProfinite) (s₀ : S) :
    Function.Surjective (finiteApproximationDifferenceRelationCover S s₀) := by
  intro r
  obtain ⟨b, hb⟩ := finiteApproximationDifferenceRelationPiece_cover S s₀ r
  exact ⟨⟨b, ⟨r, hb⟩⟩, rfl⟩

theorem finiteApproximationDifferenceRelation_diagonal (S : LightProfinite) (s₀ : S) :
    finiteApproximationDifferenceRelationPieceInclusion S s₀ false ≫
        finiteApproximationDifferenceRelationFst S s₀ =
      finiteApproximationDifferenceRelationPieceInclusion S s₀ false ≫
        finiteApproximationDifferenceRelationSnd S s₀ := by
  ext r
  exact r.property

theorem finiteApproximationDifferenceRelation_infty_first (S : LightProfinite) (s₀ : S) :
    finiteApproximationDifferenceRelationPieceInclusion S s₀ true ≫
        finiteApproximationDifferenceRelationFst S s₀ ≫
          finiteApproximationDifferenceFirst S s₀ =
      finiteApproximationDifferenceRelationPieceInclusion S s₀ true ≫
        finiteApproximationDifferenceRelationFst S s₀ ≫
          finiteApproximationDifferenceSecond S s₀ := by
  ext r
  exact finiteApproximationDifference_infty_fiber S s₀ r.val.val.1 r.property

theorem finiteApproximationDifferenceRelation_infty_second (S : LightProfinite) (s₀ : S) :
    finiteApproximationDifferenceRelationPieceInclusion S s₀ true ≫
        finiteApproximationDifferenceRelationSnd S s₀ ≫
          finiteApproximationDifferenceFirst S s₀ =
      finiteApproximationDifferenceRelationPieceInclusion S s₀ true ≫
        finiteApproximationDifferenceRelationSnd S s₀ ≫
          finiteApproximationDifferenceSecond S s₀ := by
  ext r
  exact finiteApproximationDifference_infty_fiber S s₀ r.val.val.2
    (r.val.property.symm.trans r.property)

end CWSolid
