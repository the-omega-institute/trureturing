/- GID: D5/S3/Quantum/AURICOmega/InvariantGramRepresentation
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/InvariantGramRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-rank invariant Gram kernels: orthogonal representation, kernel = stabilizer. -/

import D5.S3.Quantum.AURICOmega.GramIsometryExtension
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Orthogonal representations from invariant Gram kernels

Let `G` be a group with a topology and `φ : G → V` a map into a real inner product space whose
Gram kernel is left invariant: `⟪φ (g * x), φ (g * y)⟫_ℝ = ⟪φ x, φ y⟫_ℝ`. Assume that the span
`W` of the image of `φ` is finite-dimensional and that every orbit map `g ↦ φ (g * x)` is
continuous.

For each `g`, the permutation `x ↦ g * x` of `G` preserves the Gram kernel of the spanning
family `φ : G → W`, so it extends to a unique linear isometry `U g` of `W` with
`U g (φ x) = φ (g * x)`. Uniqueness gives `U (g * h) = U g ∘ U h` and `U 1 = id`. The vectors
`U g w` depend continuously on `g`: this holds for `w = φ x` by continuity of the orbit maps,
and it passes to finite linear combinations, which exhaust `W`. In an orthonormal basis of `W`
the matrices of the `U g` are orthogonal, so `g ↦ U g` is a continuous homomorphism into the
orthogonal group of size `dim W`. Its kernel is exactly the stabilizer of the family,
`{g | ∀ x, φ (g * x) = φ x}`: the representation is faithful whenever only the identity fixes
every `φ (g * x)`, for instance when `φ` is injective.
-/

open scoped InnerProductSpace

namespace D5.S3.Quantum.AURICOmega.InvariantGramRepresentation

open D5.S3.Quantum.AURICOmega.GramIsometryExtension

/-- The family `φ`, viewed as a family of vectors of the span of its image. -/
private def spanFamily {G V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (φ : G → V) (x : G) : Submodule.span ℝ (Set.range φ) :=
  ⟨φ x, Submodule.subset_span (Set.mem_range_self x)⟩

/-- The family `φ` spans the span of its image. -/
private lemma span_range_spanFamily {G V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (φ : G → V) :
    Submodule.span ℝ (Set.range (spanFamily φ)) = ⊤ := by
  have h : Set.range (spanFamily φ) =
      ((↑) : Submodule.span ℝ (Set.range φ) → V) ⁻¹' Set.range φ := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  rw [h]
  exact Submodule.span_span_coe_preimage

/-- Let `φ` be a map from a topological group into a real inner product space whose Gram kernel
is invariant under left multiplication, whose image spans a finite-dimensional subspace, and
whose orbit maps `g ↦ φ (g * x)` are continuous. Then there is a continuous homomorphism into
the orthogonal group whose size is the dimension of the span of the image of `φ`, and its
kernel is the stabilizer `{g | ∀ x, φ (g * x) = φ x}`. In particular it is injective as soon as
only the identity fixes every `φ (g * x)`. -/
theorem exists_orthogonal_rep_ker_eq {G V : Type*} [TopologicalSpace G] [Group G]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] (φ : G → V)
    [FiniteDimensional ℝ (Submodule.span ℝ (Set.range φ))]
    (hφc : ∀ x : G, Continuous fun g => φ (g * x))
    (hinv : ∀ g x y : G, ⟪φ (g * x), φ (g * y)⟫_ℝ = ⟪φ x, φ y⟫_ℝ) :
    ∃ ρ : G →* Matrix.orthogonalGroup
        (Fin (Module.finrank ℝ (Submodule.span ℝ (Set.range φ)))) ℝ,
      Continuous ρ ∧ ∀ g : G, ρ g = 1 ↔ ∀ x : G, φ (g * x) = φ x := by
  set W := Submodule.span ℝ (Set.range φ)
  set ψ : G → W := spanFamily φ with hψdef
  have hψ : Submodule.span ℝ (Set.range ψ) = ⊤ := span_range_spanFamily φ
  have hgram : ∀ g a b : G, ⟪ψ (Equiv.mulLeft g a), ψ (Equiv.mulLeft g b)⟫_ℝ = ⟪ψ a, ψ b⟫_ℝ :=
    fun g a b => by
      simp only [Submodule.coe_inner, hψdef, spanFamily, Equiv.coe_mulLeft]
      exact hinv g a b
  choose U hU huniq using fun g : G =>
    existsUnique_linearIsometryEquiv_of_gram_preserving ψ hψ (Equiv.mulLeft g) (hgram g)
  have hUapp : ∀ g a : G, U g (ψ a) = ψ (g * a) := fun g a => hU g a
  have hone : U 1 = LinearIsometryEquiv.refl ℝ W :=
    (huniq 1 _ fun a => by simp only [LinearIsometryEquiv.coe_refl, id, Equiv.coe_mulLeft,
      one_mul]).symm
  have hmul : ∀ g h : G, U (g * h) = (U h).trans (U g) := fun g h =>
    (huniq (g * h) _ fun a => by
      simp only [LinearIsometryEquiv.coe_trans, Function.comp_apply, hUapp,
        Equiv.coe_mulLeft, mul_assoc]).symm
  have hcont : ∀ w : W, Continuous fun g => U g w := by
    intro w
    have hw : w ∈ Submodule.span ℝ (Set.range ψ) := hψ ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      simp only [hUapp]
      exact (hφc a).subtype_mk _
    | zero =>
      simp only [map_zero]
      exact continuous_const
    | add x y _ _ hx hy =>
      simp only [map_add]
      exact hx.add hy
    | smul r x _ hx =>
      simp only [map_smul]
      exact hx.const_smul r
  let b := stdOrthonormalBasis ℝ W
  let M : G → Matrix (Fin (Module.finrank ℝ W)) (Fin (Module.finrank ℝ W)) ℝ := fun g =>
    LinearMap.toMatrixOrthonormal b (U g).toLinearEquiv.toLinearMap
  have hmem : ∀ g, M g ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ W)) ℝ := fun g =>
    (U g).toMatrix_mem_unitaryGroup b b
  have hM1 : M 1 = 1 := by
    simp only [M, hone]
    exact map_one (LinearMap.toMatrixOrthonormal b)
  have hMmul : ∀ g h, M (g * h) = M g * M h := fun g h => by
    simp only [M, hmul]
    exact map_mul (LinearMap.toMatrixOrthonormal b) _ _
  let ρ : G →* Matrix.orthogonalGroup (Fin (Module.finrank ℝ W)) ℝ :=
    { toFun := fun g => ⟨M g, hmem g⟩
      map_one' := Subtype.ext hM1
      map_mul' := fun g h => Subtype.ext (hMmul g h) }
  have hρc : Continuous ρ := by
    refine Continuous.subtype_mk (f := M) ?_ _
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [M, LinearMap.toMatrixOrthonormal_apply_apply]
    exact continuous_const.inner (hcont (b j))
  refine ⟨ρ, hρc, fun g => ⟨fun hg x => ?_, fun hx => ?_⟩⟩
  · have h1 : M g = M 1 := by
      rw [hM1]
      exact congrArg Subtype.val hg
    have h2 := LinearMap.congr_fun ((LinearMap.toMatrixOrthonormal b).injective h1) (ψ x)
    change U g (ψ x) = U 1 (ψ x) at h2
    rw [hUapp, hUapp, one_mul] at h2
    exact congrArg Subtype.val h2
  · have hg : U g = U 1 := by
      rw [hone]
      exact (huniq g _ fun a => Subtype.ext (hx a).symm).symm
    refine Subtype.ext ?_
    change M g = 1
    rw [← hM1]
    simp only [M, hg]

end D5.S3.Quantum.AURICOmega.InvariantGramRepresentation
