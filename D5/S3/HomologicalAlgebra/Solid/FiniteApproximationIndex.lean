/- GID: D5/S3/HomologicalAlgebra/Solid/FiniteApproximationIndex
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/FiniteApproximationIndex
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.FiniteApproximation
import Mathlib.Logic.Encodable.Basic

/-!
Actual countable indexing and finite stage bounds for the coefficient
selector in the free-profinite generator retract. An injection into N is
sufficient: no bijection with N is claimed for finite or empty S.
New proofs, Apache-2.0. Research construction: Rodriguez Camargo,
Notes on Solid Geometry, Lemma 3.3.2.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory LightProfinite

namespace CWSolid

def finiteApproximationIndex (S : LightProfinite) : Type :=
  Σ n : ℕ, S.fintypeDiagram.obj ⟨n⟩

instance finiteApproximationIndex_countable (S : LightProfinite) :
    Countable (finiteApproximationIndex S) :=
  inferInstanceAs (Countable (Σ n : ℕ, S.fintypeDiagram.obj ⟨n⟩))

@[instance_reducible] def finiteApproximationIndexEncoding (S : LightProfinite) :
    Encodable (finiteApproximationIndex S) := Encodable.ofCountable _

def finiteApproximationIndexCode (S : LightProfinite) :
    finiteApproximationIndex S → ℕ :=
  @Encodable.encode _ (finiteApproximationIndexEncoding S)

theorem finiteApproximationIndexCode_injective (S : LightProfinite) :
    Function.Injective (finiteApproximationIndexCode S) :=
  @Encodable.encode_injective _ (finiteApproximationIndexEncoding S)

/-- A concrete uniform stage bound for every output code below N. The
default value zero also covers the empty preimage. -/
def finiteApproximationIndexStageBound (S : LightProfinite) (N : ℕ) : ℕ :=
  (Finset.range N).sup (fun k =>
    ((@Encodable.decode _ (finiteApproximationIndexEncoding S) k).map Sigma.fst).getD 0)

theorem finiteApproximationIndex_stage_le_bound (S : LightProfinite) (N : ℕ)
    (j : finiteApproximationIndex S) (hj : finiteApproximationIndexCode S j < N) :
    j.1 ≤ finiteApproximationIndexStageBound S N := by
  letI := finiteApproximationIndexEncoding S
  have h := Finset.le_sup (f := fun k =>
    ((Encodable.decode (α := finiteApproximationIndex S) k).map Sigma.fst).getD 0)
    (Finset.mem_range.mpr hj)
  simpa only [finiteApproximationIndexCode, Encodable.encodek,
    Option.map_some, Option.getD_some, finiteApproximationIndexStageBound] using h

end CWSolid
