/- GID: D5/S1/Eigenstructure/CommonEigenvalueFieldDegree
   generality: G
   mirror-B: D5/B/S1/Eigenstructure/CommonEigenvalueFieldDegree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A common eigenvector bounds the degree of the full eigenvalue field. -/

import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Span.Basic

open scoped BigOperators Matrix

namespace D5.S1.Eigenstructure.CommonEigenvalueFieldDegree

noncomputable section

/-- An arbitrary family of base-field matrices with one common nonzero eigenvector
has a finite eigenvalue-generated field of degree at most the matrix size.
The family may be infinite, and the matrices need not commute. -/
theorem common_eigenvalue_field_degree
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    {I J : Type*} [Fintype J]
    (M : I → Matrix J J F) (eigenvalues : I → L) (x : J → L)
    (hx : x ≠ 0)
    (heig : ∀ i, (M i).map (algebraMap F L) *ᵥ x = eigenvalues i • x) :
    FiniteDimensional F (IntermediateField.adjoin F (Set.range eigenvalues)) ∧
      Module.finrank F (IntermediateField.adjoin F (Set.range eigenvalues)) ≤ Fintype.card J := by
  classical
  obtain ⟨j₀, hj₀⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  let y : J → L := (x j₀)⁻¹ • x
  have hy : y j₀ = 1 := by simp [y, hj₀]
  have heigy (i : I) : (M i).map (algebraMap F L) *ᵥ y = eigenvalues i • y := by
    simp only [y, Matrix.mulVec_smul, heig]
    exact smul_comm _ _ _
  let A : Subalgebra F (Matrix J J F) := Algebra.adjoin F (Set.range M)
  let φ : Matrix J J F →ₐ[F] Matrix J J L := (Algebra.ofId F L).mapMatrix
  have hstable (a : A) : ∃ t : L, φ a.val *ᵥ y = t • y := by
    rcases a with ⟨a, ha⟩
    change ∃ t : L, φ a *ᵥ y = t • y
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      exact ⟨eigenvalues i, heigy i⟩
    | algebraMap r =>
      refine ⟨algebraMap F L r, ?_⟩
      rw [φ.commutes r, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
        Matrix.one_mulVec]
      ext j
      exact Algebra.smul_def r (y j)
    | add a b ha hb ih₁ ih₂ =>
      obtain ⟨s, hs⟩ := ih₁
      obtain ⟨t, ht⟩ := ih₂
      refine ⟨s + t, ?_⟩
      rw [map_add, Matrix.add_mulVec, hs, ht, add_smul]
    | mul a b ha hb ih₁ ih₂ =>
      obtain ⟨s, hs⟩ := ih₁
      obtain ⟨t, ht⟩ := ih₂
      refine ⟨s * t, ?_⟩
      rw [map_mul, ← Matrix.mulVec_mulVec, ht, Matrix.mulVec_smul, hs,
        smul_smul, mul_comm t s]
  let ρ : A →ₗ[F] (J → F) := (LinearMap.proj j₀).comp A.val.toLinearMap
  let ev : (J → F) →ₗ[F] L :=
    ∑ j : J, (LinearMap.toSpanSingleton F L (y j)).comp (LinearMap.proj j)
  let γ : A →ₗ[F] L := ev.comp ρ
  have hread (a : A) : γ a = (φ a.val *ᵥ y) j₀ := by
    simp [γ, ev, ρ, φ, Matrix.mulVec, dotProduct, Algebra.smul_def]
    rfl
  have haction (a : A) : φ a.val *ᵥ y = γ a • y := by
    obtain ⟨t, ht⟩ := hstable a
    have hγ : γ a = t := by rw [hread, ht]; simp [hy]
    rw [hγ]
    exact ht
  have hone : γ 1 = 1 := by
    rw [hread]
    simp [hy]
  have hmul (a b : A) : γ (a * b) = γ a * γ b := by
    rw [hread]
    change (φ (a.val * b.val) *ᵥ y) j₀ = _
    rw [map_mul, ← Matrix.mulVec_mulVec, haction b, Matrix.mulVec_smul, haction a]
    simp [hy, mul_comm]
  let χ : A →ₐ[F] L := AlgHom.ofLinearMap γ hone hmul
  let W : Submodule F (J → F) := ρ.range
  let C : Subalgebra F L := χ.range
  have hev_mem (r : W) : ev (r : J → F) ∈ C := by
    obtain ⟨a, ha⟩ := r.property
    refine ⟨a, ?_⟩
    change γ a = ev (r : J → F)
    change ev (ρ a) = ev (r : J → F)
    rw [ha]
  let eC : W →ₗ[F] C :=
    C.toSubmoduleEquiv.toLinearMap.comp
      ((ev.domRestrict W).codRestrict C.toSubmodule hev_mem)
  have heC : Function.Surjective eC := by
    intro c
    obtain ⟨a, ha⟩ := c.property
    refine ⟨⟨ρ a, ⟨a, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact ha
  let : FiniteDimensional F C := FiniteDimensional.of_surjective eC heC
  have hC : Module.finrank F C ≤ Fintype.card J :=
    (LinearMap.finrank_le_finrank_of_surjective heC).trans
      ((Submodule.finrank_le W).trans (by simp))
  let Cfld : IntermediateField F L :=
    C.toIntermediateField' (IsField.of_isDomain_of_finite F C)
  let : FiniteDimensional F Cfld := inferInstanceAs (FiniteDimensional F C)
  have heigenvalues (i : I) : eigenvalues i ∈ Cfld := by
    let a : A := ⟨M i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
    have hγ : γ a = eigenvalues i := by
      rw [hread]
      change ((M i).map (algebraMap F L) *ᵥ y) j₀ = eigenvalues i
      rw [heigy]
      simp [hy]
    exact ⟨a, hγ⟩
  have hK : IntermediateField.adjoin F (Set.range eigenvalues) ≤ Cfld := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact heigenvalues i
  refine ⟨FiniteDimensional.of_injective
    (IntermediateField.inclusion hK).toLinearMap
    (IntermediateField.inclusion_injective hK), ?_⟩
  exact (IntermediateField.finrank_le_of_le_right hK).trans hC

end
end D5.S1.Eigenstructure.CommonEigenvalueFieldDegree

#print axioms D5.S1.Eigenstructure.CommonEigenvalueFieldDegree.common_eigenvalue_field_degree
