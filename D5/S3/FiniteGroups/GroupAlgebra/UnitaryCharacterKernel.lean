/- GID: D5/S3/FiniteGroups/GroupAlgebra/UnitaryCharacterKernel
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/UnitaryCharacterKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Isometric representations are semisimple; positivity of character kernels. -/

import D5.S3.FiniteGroups.GroupAlgebra.CharacterKernelRank
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Semisimple

/-!
# Unitary representations and positivity of character kernels

Let `G` be an arbitrary group, with no topology.

* A representation of `G` on a finite-dimensional inner product space by isometries is
  semisimple: the orthogonal complement of an invariant subspace is invariant, because the
  adjoint of `ρ g` is `ρ g⁻¹`.
* Let `ρ i`, for `i` in a finite type, be pairwise inequivalent irreducible representations of
  `G` on finite-dimensional complex inner product spaces, each acting by isometries, and let
  `c i` be complex weights. The kernel `(x, y) ↦ ∑ i, c i * χ_i (x * y⁻¹)` on `G` is positive
  semidefinite exactly when every `c i` is a nonnegative real number (order of `ℂ` from
  `ComplexOrder`).

For the positivity statement, `χ_i (x * y⁻¹) = ∑ k, ⟪ρ i x⁻¹ e_k, ρ i y⁻¹ e_k⟫` for an
orthonormal basis `e`, so the kernel is a nonnegative combination of Gram kernels. Conversely,
Burnside's theorem for the family (`CharacterKernelRank.span_range_pi_eq_top`) gives a finitely
supported `b` with `∑ y, b y • (ρ j y⁻¹)_j` equal to the identity on the factor `i` and to zero
on the other factors; unitarity makes `∑ x, conj (b x) • (ρ j x)_j` the same element, and the
quadratic form of the kernel at `b` equals `c i * dim W i`.

Irreducibility and pairwise inequivalence are needed for the converse: on the symmetric group
of order two, `triv ⊕ sign` and `triv` with weights `(1, -1)` give the positive semidefinite
kernel `sign x * sign y`, and two copies of `triv` with weights `(1, -1)` give the zero kernel.
-/

namespace D5.S3.FiniteGroups.GroupAlgebra.UnitaryCharacterKernel

open Module D5.S3.FiniteGroups.GroupAlgebra.CharacterKernelRank
open scoped ComplexOrder InnerProductSpace ComplexConjugate

/-- A representation of a group on a finite-dimensional inner product space by isometries is
semisimple: every subrepresentation has a complement. -/
theorem isSemisimpleRepresentation_of_norm_map {𝕜 G E : Type*} [RCLike 𝕜] [Group G]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (ρ : Representation 𝕜 G E) (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) :
    ρ.IsSemisimpleRepresentation := by
  have hinner : ∀ g v w, ⟪ρ g v, ρ g w⟫_𝕜 = ⟪v, w⟫_𝕜 :=
    fun g => (LinearMap.norm_map_iff_inner_map_map (ρ g)).1 (hρ g)
  refine ⟨fun σ => ?_⟩
  let τ : Subrepresentation ρ :=
    { toSubmodule := σ.toSubmoduleᗮ
      apply_mem_toSubmodule := fun g v hv => by
        rw [Submodule.mem_orthogonal] at hv ⊢
        intro w hw
        have h := hv _ (σ.apply_mem_toSubmodule g⁻¹ hw)
        rwa [← hinner g, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply] at h }
  have h := σ.toSubmodule.isCompl_orthogonal
  exact ⟨τ, disjoint_iff.2 (Subrepresentation.ext (disjoint_iff.1 h.disjoint)),
    codisjoint_iff.2 (Subrepresentation.ext (codisjoint_iff.1 h.codisjoint))⟩

/-- The Gram kernel `(x, y) ↦ ⟪v x, v y⟫` of a family indexed by an arbitrary type is positive
semidefinite. -/
private theorem posSemidef_of_inner {n E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (v : n → E) : (Matrix.of fun x y => ⟪v x, v y⟫_ℂ).PosSemidef := by
  refine ⟨Matrix.ext fun x y => by simp [Matrix.conjTranspose_apply], fun a => ?_⟩
  have : (a.sum fun i ai => a.sum fun j aj =>
      star ai * Matrix.of (fun x y => ⟪v x, v y⟫_ℂ) i j * aj) =
      ⟪a.sum fun i ai => ai • v i, a.sum fun j aj => aj • v j⟫_ℂ := by
    simp only [Finsupp.sum, sum_inner, inner_smul_left, inner_sum, inner_smul_right,
      Finset.mul_sum, Matrix.of_apply, RCLike.star_def]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [this, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
  exact RCLike.ofReal_nonneg.2 (sq_nonneg _)

/-- For pairwise inequivalent irreducible representations `ρ i` of a group on
finite-dimensional complex inner product spaces, each acting by isometries, the character kernel
`(x, y) ↦ ∑ i, c i * χ_i (x * y⁻¹)` is positive semidefinite exactly when every weight `c i` is
nonnegative. -/
theorem posSemidef_sum_character_kernel_iff {G : Type*} [Group G] {ι : Type*} [Fintype ι]
    {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℂ (W i)]
    [∀ i, FiniteDimensional ℂ (W i)] (ρ : ∀ i, Representation ℂ G (W i))
    [∀ i, (ρ i).IsIrreducible] (hne : ∀ i j, i ≠ j → IsEmpty ((ρ i).Equiv (ρ j)))
    (hunit : ∀ i g v, ‖ρ i g v‖ = ‖v‖) (c : ι → ℂ) :
    (Matrix.of fun x y : G => ∑ i, c i * (ρ i).character (x * y⁻¹)).PosSemidef ↔
      ∀ i, 0 ≤ c i := by
  classical
  have hinner : ∀ i g v w, ⟪ρ i g v, ρ i g w⟫_ℂ = ⟪v, w⟫_ℂ :=
    fun i g => (LinearMap.norm_map_iff_inner_map_map (ρ i g)).1 (hunit i g)
  constructor
  · intro hK i
    have hspan : Submodule.span ℂ
        (Set.range fun g : G => (fun j => ρ j g⁻¹ : ∀ j, Module.End ℂ (W j))) = ⊤ := by
      rw [show (fun g : G => (fun j => ρ j g⁻¹ : ∀ j, Module.End ℂ (W j))) =
          (fun g : G => (fun j => ρ j g : ∀ j, Module.End ℂ (W j))) ∘ (·⁻¹) from rfl,
        inv_surjective.range_comp]
      exact span_range_pi_eq_top ρ hne
    obtain ⟨b, hb⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1
      (hspan ▸ Submodule.mem_top : (Pi.single i 1 : ∀ j, Module.End ℂ (W j)) ∈ _)
    set Y : ∀ j, Module.End ℂ (W j) := b.sum fun g a => a • fun j => ρ j g⁻¹ with hY
    set X : ∀ j, Module.End ℂ (W j) := b.sum fun g a => star a • fun j => ρ j g with hX
    -- `X` is the adjoint of `Y` factorwise, because every `ρ j g` is unitary.
    have hadj : ∀ j u w, ⟪X j u, w⟫_ℂ = ⟪u, Y j w⟫_ℂ := by
      intro j u w
      simp only [X, Y, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
        RCLike.star_def, RCLike.conj_conj]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [← hinner j g u (ρ j g⁻¹ w), ← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
        map_one, Module.End.one_apply]
    have hXY : X = Pi.single i 1 := by
      rw [← hb]
      funext j
      refine LinearMap.ext fun u => ext_inner_right ℂ fun w => ?_
      rw [hadj, hb]
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Pi.single_eq_of_ne hj]
    -- The quadratic form of the kernel at `b` is the weighted trace pairing of `X` and `Y`.
    have hQ : (b.sum fun x bx => b.sum fun y bY => star bx *
        (Matrix.of fun x y : G => ∑ j, c j * (ρ j).character (x * y⁻¹)) x y * bY) =
        tracePairing c X Y := by
      rw [hX, hY]
      simp only [Finsupp.sum, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      simp only [tracePairing, LinearMap.mk₂_apply, Matrix.of_apply, Representation.character,
        map_mul]
      ring
    have hval : tracePairing c (Pi.single i 1 : ∀ j, Module.End ℂ (W j)) (Pi.single i 1) =
        c i * Module.finrank ℂ (W i) := by
      simp only [tracePairing, LinearMap.mk₂_apply]
      rw [Finset.sum_eq_single i]
      · simp [LinearMap.trace_one]
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · intro h
        exact absurd (Finset.mem_univ i) h
    have hpos := hK.2 b
    rw [hQ, hXY, hb, hval] at hpos
    have : Nontrivial (ρ i).asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) _
    have : Nontrivial (W i) := (ρ i).asModuleEquiv.symm.toEquiv.nontrivial
    have hd : (0 : ℂ) < Module.finrank ℂ (W i) := by exact_mod_cast Module.finrank_pos
    have := mul_nonneg hpos (inv_nonneg.2 hd.le)
    rwa [mul_assoc, mul_inv_cancel₀ hd.ne', mul_one] at this
  · intro hc
    let b := fun i => stdOrthonormalBasis ℂ (W i)
    -- The kernel is a nonnegative combination of Gram kernels.
    have hK : (Matrix.of fun x y : G => ∑ i, c i * (ρ i).character (x * y⁻¹)) =
        ∑ i, ∑ k, c i • Matrix.of fun x y : G => ⟪ρ i x⁻¹ (b i k), ρ i y⁻¹ (b i k)⟫_ℂ := by
      ext x y
      simp only [Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        ← Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Representation.character, LinearMap.trace_eq_sum_inner _ (b i)]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hinner i x⁻¹ (b i k) (ρ i (x * y⁻¹) (b i k)), ← Module.End.mul_apply, ← map_mul,
        inv_mul_cancel_left]
    rw [hK]
    exact Matrix.posSemidef_sum _ fun i _ => Matrix.posSemidef_sum _ fun k _ =>
      (posSemidef_of_inner _).smul (hc i)

end D5.S3.FiniteGroups.GroupAlgebra.UnitaryCharacterKernel
