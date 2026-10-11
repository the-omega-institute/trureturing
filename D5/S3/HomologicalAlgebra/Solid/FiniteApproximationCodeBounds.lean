/- GID: D5/S3/HomologicalAlgebra/Solid/FiniteApproximationCodeBounds
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/FiniteApproximationCodeBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.FiniteApproximationIndex

/-!
The finite set of codes in the first N approximation stages. Its complement
has stage at least N, uniformly in the represented finite quotient point.
This is the finite-support estimate needed to prove that the actual free
representative differences have diagonal infinity fibers. It includes empty
and finite S. New proofs, Apache-2.0; Rodriguez Camargo, Notes on Solid
Geometry, Lemma 3.3.2.
-/

noncomputable section
open CategoryTheory LightProfinite Filter

namespace CWSolid

local instance (S : LightProfinite) (n : ℕ) :
    Fintype (S.fintypeDiagram.obj ⟨n⟩) := Fintype.ofFinite _

def finiteApproximationStageCodes (S : LightProfinite) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).biUnion (fun n =>
    (Finset.univ : Finset (S.fintypeDiagram.obj ⟨n⟩)).image
      (fun b => finiteApproximationIndexCode S ⟨n, b⟩))

theorem finiteApproximationStageCodes_mem (S : LightProfinite) (N : ℕ)
    (j : finiteApproximationIndex S) :
    finiteApproximationIndexCode S j ∈ finiteApproximationStageCodes S N ↔ j.1 < N := by
  classical
  constructor
  · intro h
    obtain ⟨n, hn, hm⟩ := Finset.mem_biUnion.mp h
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hm
    have he : (⟨n, b⟩ : finiteApproximationIndex S) = j :=
      finiteApproximationIndexCode_injective S hb
    have hnj : n = j.1 := congrArg Sigma.fst he
    simpa only [hnj, Finset.mem_range] using hn
  · intro h
    exact Finset.mem_biUnion.mpr ⟨j.1, Finset.mem_range.mpr h,
      Finset.mem_image.mpr ⟨j.2, Finset.mem_univ _, rfl⟩⟩

theorem finiteApproximationIndex_stage_eventually (S : LightProfinite) (N : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ j : finiteApproximationIndex S,
      finiteApproximationIndexCode S j = k → N ≤ j.1 := by
  classical
  refine eventually_atTop.mpr ⟨(finiteApproximationStageCodes S N).sup id + 1, ?_⟩
  intro k hk j hj
  by_contra hn
  have hm := (finiteApproximationStageCodes_mem S N j).mpr (by omega)
  have hle := Finset.le_sup (f := id) hm
  change finiteApproximationIndexCode S j ≤ (finiteApproximationStageCodes S N).sup id at hle
  omega

end CWSolid
