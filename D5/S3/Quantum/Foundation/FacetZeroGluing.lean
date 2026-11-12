/- GID: D5/S3/Quantum/Foundation/FacetZeroGluing
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FacetZeroGluing
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Original mixed-state zero gluing and native codimension-one cone faces. -/

import D5.S3.Quantum.Foundation.WeightedRelationConfirmation
import Mathlib.Geometry.Convex.Cone.Face.Lattice
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section

namespace D5.S3.Quantum.Foundation.FacetZeroGluing

open CircuitBalancedConfirmation WeightedRelationConfirmation

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A]

/-- The entire original mixed-state exclusion set. -/
def exclusion (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) (p : A) : Set A :=
  {x | x ∈ base C u ∧ ∃ f, confirms C u p f ∧ f x = 0}

private theorem finite_zero_test {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    (hZ : zeroGluing C u) (p : pure C u)
    (hD : (exclusion C u p).Nonempty) (s : Finset A)
    (hs : (s : Set A) ⊆ exclusion C u p) :
    ∃ z ∈ exclusion C u p, ∀ f, confirms C u p f → f z = 0 →
      ∀ x ∈ s, f x = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨z, hz⟩ := hD
    exact ⟨z, hz, by simp⟩
  | @insert a s ha ih =>
    have haD := hs (Finset.mem_insert_self a s)
    obtain ⟨z, hz, htest⟩ := ih (fun x hx => hs (Finset.mem_insert_of_mem hx))
    let w := (1 / 2 : ℝ) • (a + z)
    have hwK : w ∈ base C u := by
      simpa [w, smul_add] using
        base_convex C u haD.1 hz.1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    refine ⟨w, ⟨hwK, hZ p a z haD.1 hz.1 haD.2 hz.2⟩, ?_⟩
    intro f hf hfw x hx
    have hfa := (hf.1 a haD.1.1).1
    have hfz := (hf.1 z hz.1.1).1
    have heq : (1 / 2 : ℝ) * (f a + f z) = 0 := by
      simpa [w, map_smul, map_add] using hfw
    have hfa0 : f a = 0 := by linarith
    have hfz0 : f z = 0 := by linarith
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hfa0
    · exact htest f hf hfz0 x hx

/-- A single original proper confirmer cuts out all original exclusions.
Neither a least effect nor exposedness of the exclusion set is an input. -/
theorem zero_gluing_common_effect {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    (hZ : zeroGluing C u) (p : pure C u)
    (hD : (exclusion C u p).Nonempty) :
    ∃ f, confirms C u p f ∧
      exclusion C u p = {x | x ∈ base C u ∧ f x = 0} := by
  classical
  obtain ⟨s, hs, _, hspan, _⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn ℝ (exclusion C u p)
  obtain ⟨z, hz, htest⟩ := finite_zero_test hZ p hD s hs
  obtain ⟨f, hf, hfz⟩ := hz.2
  have hker : Submodule.span ℝ (exclusion C u p) ≤ LinearMap.ker f := by
    rw [← hspan]
    exact Submodule.span_le.mpr (fun x hx => htest f hf hfz x hx)
  refine ⟨f, hf, Set.ext fun x => ?_⟩
  constructor
  · intro hx
    exact ⟨hx.1, hker (Submodule.subset_span hx)⟩
  · intro hx
    exact ⟨hx.1, f, hf, hx.2⟩

private theorem face_span_inter {C : PointedCone ℝ A} (F : PointedCone.Face C)
    {x : A} (hx : x ∈ C) (hxspan : x ∈ Submodule.span ℝ (F : Set A)) : x ∈ F := by
  obtain ⟨a, ha, b, hb, hab⟩ := F.toPointedCone.mem_span.mp hxspan
  apply F.isFaceOf.mem_of_add_mem_left hx (F.isFaceOf.le hb)
  simpa [hab] using ha

private theorem native_facet_support {C : PointedCone ℝ A}
    (hgen : Submodule.span ℝ (C : Set A) = ⊤) (F : PointedCone.Face C)
    (hdim : Module.finrank ℝ (Submodule.span ℝ (F : Set A)) + 1 =
      Module.finrank ℝ A) :
    ∃ g : A →ₗ[ℝ] ℝ, g ≠ 0 ∧ (∀ x ∈ C, 0 ≤ g x) ∧
      (∀ x ∈ C, g x = 0 ↔ x ∈ F) ∧
      LinearMap.ker g = Submodule.span ℝ (F : Set A) := by
  classical
  let S := Submodule.span ℝ (F : Set A)
  have hS : S < ⊤ := by
    apply lt_of_le_of_ne le_top
    intro he
    have hh : Module.finrank ℝ S = Module.finrank ℝ A := by rw [he, Submodule.finrank_top]
    dsimp [S] at hh
    omega
  obtain ⟨g, hg, hSg⟩ := S.exists_le_ker_of_lt_top hS
  have hker : LinearMap.ker g = S := by
    apply (Submodule.eq_of_le_of_finrank_eq hSg ?_).symm
    have hh := g.finrank_ker_add_one_of_ne_zero hg
    dsimp [S]
    omega
  have hx : ∃ x ∈ C, g x ≠ 0 := by
    by_contra! h
    have hh : Submodule.span ℝ (C : Set A) ≤ LinearMap.ker g :=
      Submodule.span_le.mpr h
    rw [hgen] at hh
    exact hg (LinearMap.ker_eq_top.mp (top_le_iff.mp hh))
  obtain ⟨x, hx, hgx⟩ := hx
  let f := if 0 < g x then g else -g
  have hfker : LinearMap.ker f = S := by
    dsimp [f]
    split_ifs <;> simpa using hker
  have hfx : 0 < f x := by
    dsimp [f]
    split_ifs with h
    · exact h
    · simp only [LinearMap.neg_apply]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt h) hgx)
  have hnonneg : ∀ y ∈ C, 0 ≤ f y := by
    intro y hy
    by_contra! hfy
    let z := (-f y) • x + (f x) • y
    have hzC : z ∈ C := C.add_mem (C.smul_mem (neg_pos.mpr hfy).le hx)
      (C.smul_mem hfx.le hy)
    have hz0 : f z = 0 := by simp [z, map_add, map_smul]; ring
    have hzF : z ∈ F := face_span_inter F hzC (hfker ▸ hz0)
    have hxF := F.isFaceOf.mem_of_smul_add_mem hx (C.smul_mem hfx.le hy)
      (neg_pos.mpr hfy) hzF
    have hx0 : f x = 0 := by
      apply (show S ≤ LinearMap.ker f by rw [hfker])
      exact Submodule.subset_span hxF
    linarith
  refine ⟨f, (by intro hf; simpa [hf] using hfx), hnonneg, ?_, hfker⟩
  intro y hy
  constructor
  · intro hy0
    exact face_span_inter F hy (hfker ▸ hy0)
  · intro hyF
    exact (show S ≤ LinearMap.ker f by rw [hfker]) (Submodule.subset_span hyF)

end D5.S3.Quantum.Foundation.FacetZeroGluing
