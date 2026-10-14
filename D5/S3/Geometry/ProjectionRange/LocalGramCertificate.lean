/- GID: D5/S3/Geometry/ProjectionRange/LocalGramCertificate
   generality: G
   mirror-B: D5/B/S3/Geometry/ProjectionRange/LocalGramCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.PosDef]
   utility: none
   digest: Locally constant matrix rank gives locally invertible selected-column Gram matrices and spanning ranges. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Separation.Basic

noncomputable section
open Filter Topology
open scoped Matrix ComplexOrder

theorem exact_original_local_gram_certificate {E : Type*} [TopologicalSpace E]
    {n : Type} [Fintype n] [DecidableEq n]
    (Q : E → Matrix n n ℂ) (s : Set E) (x0 : E)
    (hx0 : x0 ∈ s)
    (hPSD : ∀ y ∈ s, (Q y).PosSemidef)
    (hQ : ContinuousWithinAt Q s x0)
    (hrank : ∀ᶠ y in 𝓝[s] x0,
      Module.finrank ℂ (LinearMap.range (Q y).mulVecLin) =
        Module.finrank ℂ (LinearMap.range (Q x0).mulVecLin)) :
    let k := Module.finrank ℂ (LinearMap.range (Q x0).mulVecLin)
    ∃ J : Fin k → n, Function.Injective J ∧
      ∃ U : Set E, IsOpen U ∧ x0 ∈ U ∩ s ∧
        ∀ y ∈ U ∩ s,
          let C : Matrix n (Fin k) ℂ := fun i j => Q y i (J j)
          (Q y).PosSemidef ∧ IsUnit (Cᴴ * C) ∧
            Submodule.span ℂ (Set.range C.col) =
              Submodule.span ℂ (Set.range (Q y).col) := by
  classical
  dsimp only
  let k : ℕ := Module.finrank ℂ (LinearMap.range (Q x0).mulVecLin)
  obtain ⟨ι, a, ha, hspan, hli⟩ :=
    exists_linearIndependent' ℂ (Q x0).col
  letI : Finite ι := Finite.of_injective a ha
  letI : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι = k := by
    dsimp only [k]
    rw [Matrix.range_mulVecLin, ← hspan, finrank_span_eq_card hli]
  let e : ι ≃ Fin k := Fintype.equivFinOfCardEq hcard
  let J : Fin k → n := a ∘ e.symm
  have hJ : Function.Injective J := ha.comp e.symm.injective
  let C : E → Matrix n (Fin k) ℂ := fun y i j => Q y i (J j)
  let G : E → Matrix (Fin k) (Fin k) ℂ := fun y => (C y)ᴴ * C y
  have hli0 : LinearIndependent ℂ (C x0).col := by
    change LinearIndependent ℂ (((Q x0).col ∘ a) ∘ e.symm)
    exact hli.comp e.symm e.symm.injective
  have hG0 : IsUnit (G x0) :=
    (Matrix.PosDef.conjTranspose_mul_self (C x0)
      (Matrix.mulVec_injective_iff.mpr hli0)).isUnit
  let select : Matrix n n ℂ → Matrix n (Fin k) ℂ :=
    fun A => A.submatrix id J
  have hs : Continuous select := continuous_id.matrix_submatrix id J
  have hD : Continuous (fun A : Matrix n n ℂ =>
      ((select A)ᴴ * select A).det) :=
    (hs.matrix_conjTranspose.matrix_mul hs).matrix_det
  have hd : ContinuousWithinAt (fun y => (G y).det) s x0 :=
    hD.continuousAt.comp_continuousWithinAt hQ
  have hdet0 : (G x0).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det (G x0)).mp hG0).ne_zero
  have hdet : ∀ᶠ y in 𝓝[s] x0, (G y).det ≠ 0 :=
    hd.tendsto.eventually (compl_singleton_mem_nhds hdet0)
  have hunits : ∀ᶠ y in 𝓝[s] x0, IsUnit (G y) :=
    hdet.mono fun y hy =>
      (Matrix.isUnit_iff_isUnit_det (G y)).mpr (isUnit_iff_ne_zero.mpr hy)
  have hevent : ∀ᶠ y in 𝓝[s] x0,
      IsUnit (G y) ∧
        Submodule.span ℂ (Set.range (C y).col) =
          Submodule.span ℂ (Set.range (Q y).col) := by
    apply (hunits.and hrank).mono
    intro y hy
    obtain ⟨hGy, hry⟩ := hy
    refine ⟨hGy, ?_⟩
    have hyli : LinearIndependent ℂ (C y).col := by
      apply LinearIndependent.of_comp ((C y)ᴴ).mulVecLin
      change LinearIndependent ℂ (G y).col
      exact Matrix.linearIndependent_cols_of_isUnit hGy
    have hle : Submodule.span ℂ (Set.range (C y).col) ≤
        Submodule.span ℂ (Set.range (Q y).col) := by
      apply Submodule.span_mono
      rintro v ⟨j, rfl⟩
      exact ⟨J j, rfl⟩
    have hCy : Module.finrank ℂ
        (Submodule.span ℂ (Set.range (C y).col)) = k := by
      simpa only [Fintype.card_fin] using finrank_span_eq_card hyli
    have hQy : Module.finrank ℂ
        (Submodule.span ℂ (Set.range (Q y).col)) = k := by
      rw [← Matrix.range_mulVecLin]
      exact hry
    exact Submodule.eq_of_le_of_finrank_eq hle (hCy.trans hQy.symm)
  obtain ⟨U, hU, hxU, hUg⟩ := mem_nhdsWithin.mp hevent
  refine ⟨J, hJ, U, hU, ⟨hxU, hx0⟩, ?_⟩
  intro y hy
  exact ⟨hPSD y hy.2, hUg hy⟩

end
