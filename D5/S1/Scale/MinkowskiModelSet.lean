/- GID: D5/S1/Scale/MinkowskiModelSet
   generality: I
   mirror-B: D5/B/S1/Scale/MinkowskiModelSet
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Golden embeddings define a lattice range, window model sets, and coordinate labels. -/

import D5.S1.Depth.JointCoordinates

namespace D5.S1.Scale

open D5.S0.Carrier
open D5.S1.Depth

/-- The physical/internal pair `(x, conj x)` under the distinguished real embedding. -/
noncomputable def minkowskiEmbedding : GoldenInt →+ ℝ × ℝ where
  toFun x := (embedding x, embedding (conj x))
  map_zero' := by simp
  map_add' x y := by
    ext <;> simp <;> ring

/-- The additive golden lattice realized as the range of the two embeddings. -/
noncomputable def goldenLattice : AddSubgroup (ℝ × ℝ) :=
  AddMonoidHom.range minkowskiEmbedding

/-- Physical projections whose internal conjugate lies in `window`. -/
noncomputable def modelSet (window : Set ℝ) : Set ℝ :=
  {y | ∃ x : GoldenInt, embedding x = y ∧ embedding (conj x) ∈ window}

/-- A model-set point together with one joint `(A, Z, G)` coordinate label. -/
noncomputable def labeledModelSet (window : Set ℝ) :
    Set (ℝ × JointCoordinates) :=
  {point | ∃ (x : GoldenInt) (n : ℕ),
    embedding x = point.1 ∧
      embedding (conj x) ∈ window ∧
      jointCoordinates x n = point.2}

/-- Exact formal echo of the embedding, lattice range, window, and labeled model set. -/
theorem minkowski_model_set_spec (window : Set ℝ) (y : ℝ)
    (label : JointCoordinates) :
    Function.Injective minkowskiEmbedding ∧
      (goldenLattice : Set (ℝ × ℝ)) = Set.range minkowskiEmbedding ∧
      (y ∈ modelSet window ↔
        ∃ x : GoldenInt, embedding x = y ∧ embedding (conj x) ∈ window) ∧
      ((y, label) ∈ labeledModelSet window ↔
        ∃ (x : GoldenInt) (n : ℕ),
          embedding x = y ∧
            embedding (conj x) ∈ window ∧
            jointCoordinates x n = label) := by
  refine ⟨?_, rfl, Iff.rfl, Iff.rfl⟩
  intro x z h
  apply embedding_injective
  exact congrArg Prod.fst h

end D5.S1.Scale
