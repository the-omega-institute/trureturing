/- GID: D5/S3/Quantum/Analysis/CompactGroups/MatrixCoefficientDensity
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/CompactGroups/MatrixCoefficientDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The span of unitary matrix coefficients of a compact group is dense in C(G). -/

import D5.S3.Quantum.Analysis.CompactGroups.UnitaryRepresentationKernel
import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.SeparationQuotient.Basic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Separation.Regular

/-!
# Density of matrix coefficients on compact groups

Let `G` be a compact topological group; no separation axiom is assumed. The complex span of the
matrix coefficients `g ↦ (ρ g) i j` of continuous homomorphisms `ρ : G → U(n)` is dense in
`C(G, ℂ)` for the uniform norm (Peter-Weyl).

The span is a unital star subalgebra: the trivial representation of dimension one gives the
constant `1`, the Kronecker product `ρ ⊗ σ` (reindexed by `Fin`) has the products of coefficients
as coefficients, and the entrywise conjugate of a unitary representation is a unitary
representation whose coefficients are the conjugates.

On the separation quotient `Q` of `G`, a compact topological group in which points are closed,
two distinct points `x`, `y` are separated by a coefficient of a representation `ρ` of `Q` whose
kernel avoids `x * y⁻¹`; such a `ρ` exists because every neighbourhood of `1` contains the kernel
of a continuous finite-dimensional unitary representation. Its coefficients pull back to
coefficients of `ρ ∘ mk` on `G`. By the Stone-Weierstrass theorem the star subalgebra of
`C(Q, ℂ)` of functions whose pullback lies in the span is dense. Precomposition with
`mk : G → Q` is continuous and surjective onto `C(G, ℂ)`, since a continuous function into
`ℂ` is constant on inseparable points, so the span is dense in `C(G, ℂ)`.
-/

open scoped Kronecker

namespace D5.S3.Quantum.Analysis.CompactGroups.MatrixCoefficientDensity

section Coefficients

variable (G : Type*) [Group G] [TopologicalSpace G]

/-- Matrix coefficients `g ↦ (ρ g) i j` of continuous unitary matrix representations. -/
private def coeffSet : Set C(G, ℂ) :=
  {f : C(G, ℂ) | ∃ (n : ℕ) (ρ : G →ₜ* Matrix.unitaryGroup (Fin n) ℂ) (i j : Fin n),
    ∀ g, f g = (ρ g : Matrix (Fin n) (Fin n) ℂ) i j}

variable {G}

/-- A continuous multiplicative unitary-valued matrix function on any finite index type gives
matrix coefficients, after reindexing by `Fin`. -/
private lemma mem_coeffSet_of_rep {κ : Type*} [Fintype κ] [DecidableEq κ]
    (F : G → Matrix κ κ ℂ) (hu : ∀ g, F g ∈ Matrix.unitaryGroup κ ℂ) (h1 : F 1 = 1)
    (hmul : ∀ g h, F (g * h) = F g * F h) (hc : Continuous F) (f : C(G, ℂ)) (i j : κ)
    (hf : ∀ g, f g = F g i j) : f ∈ coeffSet G := by
  let e := Fintype.equivFin κ
  refine ⟨Fintype.card κ,
    { toFun := fun g => ⟨Matrix.reindex e e (F g),
        Matrix.submatrix_equiv_mem_unitary.2 (hu g)⟩
      map_one' := Subtype.ext (by simp [h1])
      map_mul' := fun g h => Subtype.ext (by simp [hmul])
      continuous_toFun := ?_ }, e i, e j, fun g => ?_⟩
  · exact (continuous_pi fun a => continuous_pi fun b => hc.matrix_elem _ _).subtype_mk _
  · change f g = (F g).submatrix e.symm e.symm (e i) (e j)
    simp [hf]

/-- Entries of a continuous unitary matrix representation are continuous. -/
private lemma continuous_entry {n : ℕ} (ρ : G →ₜ* Matrix.unitaryGroup (Fin n) ℂ) (i j : Fin n) :
    Continuous fun g => (ρ g : Matrix (Fin n) (Fin n) ℂ) i j :=
  (continuous_subtype_val.comp ρ.continuous).matrix_elem i j

private lemma one_mem_coeffSet : (1 : C(G, ℂ)) ∈ coeffSet G :=
  mem_coeffSet_of_rep (κ := Fin 1) (fun _ => 1) (fun _ => one_mem _) rfl
    (fun _ _ => (mul_one 1).symm) continuous_const 1 0 0 fun _ => by simp

/-- Kronecker products of unitary representations. -/
private lemma mul_mem_coeffSet {f f' : C(G, ℂ)} (hf : f ∈ coeffSet G) (hf' : f' ∈ coeffSet G) :
    f * f' ∈ coeffSet G := by
  obtain ⟨n, ρ, i, j, hρ⟩ := hf
  obtain ⟨m, σ, k, l, hσ⟩ := hf'
  refine mem_coeffSet_of_rep
    (fun g => (ρ g : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ (σ g : Matrix (Fin m) (Fin m) ℂ))
    (fun g => Matrix.kronecker_mem_unitary (ρ g).2 (σ g).2) ?_ ?_ ?_ _ (i, k) (j, l) ?_
  · simp
  · intro g h
    simp [Matrix.mul_kronecker_mul]
  · exact continuous_pi fun p => continuous_pi fun q =>
      (continuous_entry ρ p.1 q.1).mul (continuous_entry σ p.2 q.2)
  · intro g
    simp [hρ, hσ]

/-- Entrywise conjugates of unitary representations. -/
private lemma star_mem_coeffSet {f : C(G, ℂ)} (hf : f ∈ coeffSet G) : star f ∈ coeffSet G := by
  obtain ⟨n, ρ, i, j, hρ⟩ := hf
  refine mem_coeffSet_of_rep (fun g => (ρ g : Matrix (Fin n) (Fin n) ℂ).map star)
    (fun g => Matrix.map_star_mem_unitaryGroup_iff.2 (ρ g).2) ?_ ?_ ?_ _ i j ?_
  · simp
  · intro g h
    ext a b
    simp [Matrix.mul_apply]
  · exact continuous_pi fun a => continuous_pi fun b => (continuous_entry ρ a b).star
  · intro g
    simp [hρ]

variable (G) in
/-- The span of the matrix coefficients is a unital star subalgebra of `C(G, ℂ)`. -/
private noncomputable def coeffAlgebra : StarSubalgebra ℂ C(G, ℂ) :=
  { (Submodule.span ℂ (coeffSet G)).toSubalgebra (Submodule.subset_span one_mem_coeffSet)
      (fun x y hx hy => by
        have := Submodule.mul_mem_mul hx hy
        rw [Submodule.span_mul_span] at this
        refine Submodule.span_le.2 ?_ this
        rintro _ ⟨a, ha, b, hb, rfl⟩
        exact Submodule.subset_span (mul_mem_coeffSet ha hb)) with
    star_mem' := fun {x} hx => by
      induction hx using Submodule.span_induction with
      | mem a ha => exact Submodule.subset_span (star_mem_coeffSet ha)
      | zero => simp
      | add a b _ _ ha hb => simpa [star_add] using Submodule.add_mem _ ha hb
      | smul c a _ ha => simpa [star_smul] using Submodule.smul_mem _ (star c) ha }

end Coefficients

/-- Peter-Weyl density: for a compact topological group `G`, with no separation axiom, the complex
span of the matrix coefficients of continuous finite-dimensional unitary matrix representations is
dense in `C(G, ℂ)`. -/
theorem dense_span_unitary_coefficients {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] :
    Dense (Submodule.span ℂ {f : C(G, ℂ) | ∃ (n : ℕ)
      (ρ : G →ₜ* Matrix.unitaryGroup (Fin n) ℂ) (i j : Fin n),
        ∀ g, f g = (ρ g : Matrix (Fin n) (Fin n) ℂ) i j} : Set C(G, ℂ)) := by
  have : CompactSpace (SeparationQuotient G) :=
    SeparationQuotient.surjective_mk.compactSpace SeparationQuotient.continuous_mk
  let π : C(G, SeparationQuotient G) := ⟨SeparationQuotient.mk, SeparationQuotient.continuous_mk⟩
  let πh : G →ₜ* SeparationQuotient G :=
    { toMonoidHom := SeparationQuotient.mkMonoidHom
      continuous_toFun := SeparationQuotient.continuous_mk }
  let Φ := ContinuousMap.compStarAlgHom' ℂ ℂ π
  let A := (coeffAlgebra G).comap Φ
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨n, ρ, hρ⟩ := UnitaryRepresentationKernel.exists_unitaryRep_ker_subset
      (G := SeparationQuotient G) (U := {x * y⁻¹}ᶜ)
      (isOpen_compl_singleton.mem_nhds fun h => hxy (mul_inv_eq_one.1 h.symm))
    have hne : ρ x ≠ ρ y := fun h => hρ (x * y⁻¹) (by rw [map_mul, map_inv, h, mul_inv_cancel]) rfl
    have hne' : (ρ x : Matrix (Fin n) (Fin n) ℂ) ≠ ρ y := fun h => hne (Subtype.ext h)
    obtain ⟨i, j, hij⟩ : ∃ i j, (ρ x : Matrix (Fin n) (Fin n) ℂ) i j ≠
        (ρ y : Matrix (Fin n) (Fin n) ℂ) i j := by
      by_contra! h
      exact hne' (Matrix.ext h)
    exact ⟨_, ⟨⟨fun q => (ρ q : Matrix (Fin n) (Fin n) ℂ) i j, continuous_entry ρ i j⟩,
      Submodule.subset_span ⟨n, ρ.comp πh, i, j, fun _ => rfl⟩, rfl⟩, hij⟩
  have hdense : Dense (A : Set C(SeparationQuotient G, ℂ)) := by
    rw [dense_iff_closure_eq, ← StarSubalgebra.topologicalClosure_coe,
      ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep]
    rfl
  have hsurj : Function.Surjective Φ := fun f =>
    ⟨⟨SeparationQuotient.lift f fun _ _ h => (h.map f.continuous).eq,
      SeparationQuotient.continuous_lift f.continuous⟩, ContinuousMap.ext fun _ => rfl⟩
  have hcont : Continuous Φ := ContinuousMap.continuous_precomp π
  refine (hsurj.denseRange.dense_image hcont hdense).mono ?_
  rintro _ ⟨f, hf, rfl⟩
  exact hf

end D5.S3.Quantum.Analysis.CompactGroups.MatrixCoefficientDensity
