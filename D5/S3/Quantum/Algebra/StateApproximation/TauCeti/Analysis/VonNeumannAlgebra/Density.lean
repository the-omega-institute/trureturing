/- GID: D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Star.Subalgebra, mathlib/module/Mathlib.Analysis.InnerProductSpace.Adjoint]
   utility: none
   digest: Original real states, pure cyclic representations and self-adjoint operator approximation. -/

module

public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Semisimple
public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.LocallyConvex.PointwiseConvergence
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology

public section

section
/- Source: TauCeti, immutable revision 23caf7311c77a86c3a20d58a0b596b6da705bd94, TauCeti/Analysis/LocallyConvex/PointwiseConvergence.lean.
Modified for ordinary D5 imports and necessary declaration selection; mathematical telescopes are preserved.
Full license and attribution: docs/reports/licenses/state-approximation-suppliers/.
Retire each transplanted result when the actual pinned mathlib contains an equivalent statement,
and replace its consumers with direct imports and applications of that pinned result. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


namespace PointwiseConvergenceCLM

variable {𝕜₁ 𝕜 E F : Type*} [NormedField 𝕜₁] [RCLike 𝕜] {σ : 𝕜₁ →+* 𝕜} [AddCommGroup E]
    [TopologicalSpace E] [Module 𝕜₁ E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/- **Continuous functionals in the strong operator topology.** A linear functional on operators
which is continuous for the topology of pointwise convergence is a finite sum of functionals
`T ↦ g x (T x)`, each a continuous functional on `F` applied to the value at a vector `x`. -/
theorem exists_finset_sum_eq (φ : StrongDual 𝕜 (E →SLₚₜ[σ] F)) :
    ∃ (s : Finset E) (g : E → StrongDual 𝕜 F), ∀ T : E →SLₚₜ[σ] F,
      φ T = ∑ x ∈ s, g x (T x) := by
  classical
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous PointwiseConvergenceCLM.withSeminorms
    ((normSeminorm 𝕜 𝕜).comp (φ : (E →SLₚₜ[σ] F) →ₗ[𝕜] 𝕜)) (continuous_norm.comp φ.continuous)
  -- `Φ T` records the values of `T` on `s`; the sup norm of `Φ T` controls `φ T`.
  let Φ : (E →SLₚₜ[σ] F) →ₗ[𝕜] (s → F) :=
    { toFun T x := T x, map_add' _ _ := rfl, map_smul' _ _ := rfl }
  have hbound (T : E →SLₚₜ[σ] F) : ‖φ T‖ ≤ C * ‖Φ T‖ := by
    refine (hC T).trans ?_
    rw [smul_apply, NNReal.smul_def, smul_eq_mul]
    gcongr
    exact Seminorm.finset_sup_apply_le (norm_nonneg _) fun x hx ↦ norm_le_pi_norm (Φ T) ⟨x, hx⟩
  -- Hence `φ` factors through `Φ`, and the factor extends to `s → F` by Hahn–Banach.
  let f : Module.Dual 𝕜 (LinearMap.range Φ) := (φ : (E →SLₚₜ[σ] F) →ₗ[𝕜] 𝕜).compLeftInverse Φ
  have hf (T : E →SLₚₜ[σ] F) : f ⟨Φ T, LinearMap.mem_range_self Φ T⟩ = φ T :=
    LinearMap.compLeftInverse_apply_of_bdd _ _ ⟨C, hbound⟩ T (Φ T) rfl
  obtain ⟨G, hG, -⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm
    (LinearMap.range Φ) f (p := C • normSeminorm 𝕜 (s → F))
    (continuous_norm.const_smul (C : ℝ)) (by
      rintro ⟨-, T, rfl⟩
      simpa [hf, NNReal.smul_def] using hbound T)
  refine ⟨s, fun x ↦ if hx : x ∈ s then G ∘L ContinuousLinearMap.single 𝕜 (fun _ : s ↦ F) ⟨x, hx⟩
    else 0, fun T ↦ ?_⟩
  rw [← hf, ← hG, ← Finset.sum_coe_sort s]
  simp only [Finset.coe_mem, dite_true]
  -- The coordinates of `Φ T` are the values `T x`, by definition of `Φ`.
  exact (ContinuousLinearMap.sum_comp_single 𝕜 (fun _ ↦ F) G (Φ T)).symm

end PointwiseConvergenceCLM

end


section
section
/- Source: TauCeti, immutable revision 23caf7311c77a86c3a20d58a0b596b6da705bd94, TauCeti/Topology/Algebra/Module/Spaces/PointwiseConvergenceCLM.lean.
Modified for ordinary D5 imports and necessary declaration selection; mathematical telescopes are preserved.
Full license and attribution: docs/reports/licenses/state-approximation-suppliers/.
Retire each transplanted result when the actual pinned mathlib contains an equivalent statement,
and replace its consumers with direct imports and applications of that pinned result. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Basic facts on the topology of pointwise convergence

Scalar multiplication on `E →SLₚₜ[σ] F` is jointly continuous whenever it is on `F`, since it is
computed pointwise (`PointwiseConvergenceCLM.continuousSMul`). Passing from `E →SL[σ] F` to its
pointwise-convergence copy is injective
(`ContinuousLinearMap.toPointwiseConvergenceCLM_injective`).
-/

namespace PointwiseConvergenceCLM

variable {𝕜₁ 𝕜₂ M E F : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂}
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E] [AddCommGroup F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [Module 𝕜₂ F] [Monoid M] [TopologicalSpace M]
    [DistribMulAction M F] [SMulCommClass 𝕜₂ M F] [ContinuousSMul M F]

/- Scalar multiplication is jointly continuous for the topology of pointwise convergence, since
it is computed pointwise. -/
instance continuousSMul : ContinuousSMul M (E →SLₚₜ[σ] F) where
  continuous_smul := continuous_of_continuous_eval fun x ↦
    continuous_fst.smul (((continuous_apply x).comp
      (PointwiseConvergenceCLM.isEmbedding_coeFn σ E F).continuous).comp continuous_snd :
        Continuous fun p : M × (E →SLₚₜ[σ] F) ↦ p.2 x)

end PointwiseConvergenceCLM

/- Passing to the topology of pointwise convergence does not identify distinct maps. -/
theorem ContinuousLinearMap.toPointwiseConvergenceCLM_injective {𝕜₁ 𝕜₂ E F : Type*}
    [NormedField 𝕜₁] [NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} [AddCommGroup E] [TopologicalSpace E]
    [Module 𝕜₁ E] [ContinuousSMul 𝕜₁ E] [AddCommGroup F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [Module 𝕜₂ F] [ContinuousConstSMul 𝕜₂ F] :
    Function.Injective (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜₂ σ E F) :=
  fun _ _ h ↦ ContinuousLinearMap.ext fun v ↦ congrArg (fun T : E →SLₚₜ[σ] F ↦ T v) h
end

section
/- Source: TauCeti, immutable revision 23caf7311c77a86c3a20d58a0b596b6da705bd94, TauCeti/Analysis/InnerProductSpace/Amplification.lean.
Modified for ordinary D5 imports and necessary declaration selection; mathematical telescopes are preserved.
Full license and attribution: docs/reports/licenses/state-approximation-suppliers/.
Retire each transplanted result when the actual pinned mathlib contains an equivalent statement,
and replace its consumers with direct imports and applications of that pinned result. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Amplification of operators to a finite Hilbert sum

For a Hilbert space `H` over `ℝ` or `ℂ` and a finite index type `ι`, an operator `s` on `H`
acts diagonally on the Hilbert sum `PiLp 2 (fun _ : ι => H)` of copies of `H`, as
`s ⊕ ⋯ ⊕ s`. This diagonal amplification is a star algebra homomorphism,
`PiLp.diagStarAlgHom`. Conversely, every operator `T` on the Hilbert sum has matrix entries
`ContinuousLinearMap.piLpEntry T i j : H →L[𝕜] H`, and `T` acts through them
(`ContinuousLinearMap.apply_eq_sum_piLpEntry`). The amplification of `s` has `s` on the diagonal
and `0` off it (`ContinuousLinearMap.piLpEntry_diagStarAlgHom`).

Amplification turns statements about finitely many vectors of `H` into statements about a single
vector of the Hilbert sum; this is how the von Neumann density theorem passes from one vector to
finitely many.
-/

open scoped InnerProductSpace

variable {𝕜 H ι : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

namespace ContinuousLinearMap

variable [DecidableEq ι]

/- The `(i, j)` matrix entry of an operator on the Hilbert sum of copies of `H`: the component
at `i` of the image of a vector supported at `j`. -/
noncomputable def piLpEntry (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))
    (i j : ι) : H →L[𝕜] H :=
  PiLp.proj 2 (fun _ : ι => H) i ∘L T ∘L
    (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => H)).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.single 𝕜 (fun _ : ι => H) j

@[simp]
theorem piLpEntry_apply (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))
    (i j : ι) (h : H) : T.piLpEntry i j h = T (PiLp.single 2 j h) i :=
  (rfl)

/- An operator on the Hilbert sum acts through its matrix entries. -/
theorem apply_eq_sum_piLpEntry [Fintype ι]
    (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))
    (w : PiLp 2 (fun _ : ι => H)) (i : ι) : T w i = ∑ j, T.piLpEntry i j (w j) := by
  have hw : w = ∑ j, WithLp.toLp 2 (Pi.single j (w j)) := by
    ext k
    simp [Pi.single_apply]
  conv_lhs => rw [hw]
  simp [map_sum]

end ContinuousLinearMap

namespace PiLp

variable [Fintype ι] [CompleteSpace H]

variable (𝕜 H ι) in
/- The diagonal amplification `s ↦ s ⊕ ⋯ ⊕ s` of operators on `H` to the Hilbert sum of copies
of `H` indexed by `ι`, as a star algebra homomorphism. -/
noncomputable def diagStarAlgHom :
    (H →L[𝕜] H) →⋆ₐ[𝕜] (PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) where
  toFun s := (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.piMap (fun _ => s) ∘L
      (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => H)).toContinuousLinearMap
  map_one' := by ext; simp
  map_mul' s t := by ext; simp
  map_zero' := by ext; simp
  map_add' s t := by ext; simp
  commutes' r := by ext; simp [Algebra.algebraMap_eq_smul_one]
  map_star' s := by
    simp only [ContinuousLinearMap.star_eq_adjoint]
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro w w'
    simp [PiLp.inner_apply, ContinuousLinearMap.adjoint_inner_left]

@[simp]
theorem diagStarAlgHom_apply (s : H →L[𝕜] H) (w : PiLp 2 (fun _ : ι => H)) (i : ι) :
    diagStarAlgHom 𝕜 H ι s w i = s (w i) :=
  (rfl)

@[simp]
theorem diagStarAlgHom_apply_single [DecidableEq ι] (s : H →L[𝕜] H) (j : ι) (h : H) :
    diagStarAlgHom 𝕜 H ι s (PiLp.single 2 j h) = PiLp.single 2 j (s h) := by
  ext k
  by_cases hk : k = j
  · subst hk; simp
  · simp [hk]

end PiLp

namespace ContinuousLinearMap

variable [Fintype ι] [DecidableEq ι] [CompleteSpace H]

/- The diagonal amplification of `s` has `s` on the diagonal and `0` off it. -/
end ContinuousLinearMap
end

section
/- Source: TauCeti, immutable revision 23caf7311c77a86c3a20d58a0b596b6da705bd94, TauCeti/Analysis/InnerProductSpace/InvariantSubspace.lean.
Modified for ordinary D5 imports and necessary declaration selection; mathematical telescopes are preserved.
Pointwise endomorphism multiplication uses Module.End.mul_apply.
Full license and attribution: docs/reports/licenses/state-approximation-suppliers/.
Retire each transplanted result when the actual pinned mathlib contains an equivalent statement,
and replace its consumers with direct imports and applications of that pinned result. -/

/-
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, GPT 5.6 High, OpenAI GPT-6
-/

/-!
# Reducing subspaces of inner-product spaces

A subspace reduces an endomorphism when both it and its orthogonal complement are invariant.
For a symmetric endomorphism, invariance of the subspace alone is enough. When an orthogonal
projection exists, reduction is equivalently commutation with that projection; in particular the
orthogonal projection onto a subspace invariant under a symmetric endomorphism commutes with it.
More generally, an idempotent whose range and kernel are orthogonal both for the inner product and
for the form of a symmetric endomorphism commutes with that endomorphism
(`LinearMap.IsSymmetric.commute_of_isIdempotentElem`).

For a bounded operator `A` on a Hilbert space and a complete subspace invariant under both `A`
and its adjoint, the adjoint of the restriction of `A` is the restriction of the adjoint
(`ContinuousLinearMap.adjoint_restrict`), so the restriction of a normal operator is normal
(`IsStarNormal.restrict`).
-/

open Module End

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/- A subspace is reducing for an endomorphism when both it and its orthogonal complement are
invariant under the endomorphism. -/
def IsReducing (U : Submodule 𝕜 E) (A : Module.End 𝕜 E) : Prop :=
  U ∈ A.invtSubmodule ∧ Uᗮ ∈ A.invtSubmodule

/- A subspace is reducing exactly when it and its orthogonal complement are invariant. -/
theorem isReducing_iff (U : Submodule 𝕜 E) (A : Module.End 𝕜 E) :
    U.IsReducing A ↔ U ∈ A.invtSubmodule ∧ Uᗮ ∈ A.invtSubmodule :=
  Iff.rfl

/- A reducing subspace is invariant under the endomorphism. -/
/- An idempotent endomorphism `p` whose range is orthogonal to its kernel, both for the inner
product and for the form `⟪A ·, ·⟫` of a symmetric endomorphism `A`, commutes with `A`: its range
and its kernel are invariant under `A`. -/
variable {U V : Submodule 𝕜 E} {A : End 𝕜 E}

/- The supremum of a family of reducing subspaces is reducing. -/
end Submodule

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {U : Submodule 𝕜 E}

/- A subspace with an orthogonal projection reduces a bounded operator `A` exactly when `A`
commutes with the orthogonal projection onto it. -/
theorem isReducing_coe_iff_commute_starProjection [U.HasOrthogonalProjection] {A : E →L[𝕜] E} :
    U.IsReducing A ↔ Commute U.starProjection A := by
  rw [ContinuousLinearMap.IsIdempotentElem.commute_iff (isIdempotentElem_starProjection U),
    isReducing_iff, range_starProjection, ker_starProjection]

end Submodule

open Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {U : Submodule 𝕜 E}

/- A subspace with an orthogonal projection reduces a bounded operator `A` on a Hilbert space
exactly when it is invariant under both `A` and its adjoint. -/
theorem ContinuousLinearMap.isReducing_iff_mem_invtSubmodule_adjoint [CompleteSpace E]
    [U.HasOrthogonalProjection] {A : E →L[𝕜] E} :
    U.IsReducing A ↔
      U ∈ invtSubmodule (A : End 𝕜 E) ∧ U ∈ invtSubmodule (A.adjoint : End 𝕜 E) := by
  rw [isReducing_iff, mem_invtSubmodule_adjoint_iff]

/- A subspace with an orthogonal projection reduces the adjoint of a bounded operator `A` on a
Hilbert space exactly when it reduces `A`. -/
namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] {U : Submodule 𝕜 E} [CompleteSpace U] {A : E →L[𝕜] E}

/- The adjoint of the restriction of a bounded operator `A` to a complete subspace invariant
under both `A` and its adjoint is the restriction of the adjoint. -/
end ContinuousLinearMap
end

section
/- Source: TauCeti, immutable revision 23caf7311c77a86c3a20d58a0b596b6da705bd94, TauCeti/Analysis/VonNeumannAlgebra/Density.lean.
Modified for ordinary D5 imports and necessary declaration selection; mathematical telescopes are preserved.
Full license and attribution: docs/reports/licenses/state-approximation-suppliers/.
Retire each transplanted result when the actual pinned mathlib contains an equivalent statement,
and replace its consumers with direct imports and applications of that pinned result. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# The von Neumann density theorem

Let `S` be a unital star subalgebra of the bounded operators on a Hilbert space `H` over `ℝ` or
`ℂ`. Every operator `x` in the double commutant `S''` is a strong-operator limit of elements of
`S`: for finitely many vectors `v i` and every `ε > 0` there is `s ∈ S` with
`‖x (v i) - s (v i)‖ < ε` for all `i`,
`StarSubalgebra.exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer`.

For a von Neumann algebra generated by a set `s` of operators on a complex Hilbert space, every
element of `VonNeumannAlgebra.adjoin s` is approximated in this sense by elements of the star
algebra generated by `s`, `VonNeumannAlgebra.exists_forall_norm_sub_apply_lt_of_mem_adjoin`.

For a single vector `v` this is `StarSubalgebra.apply_mem_closure_of_mem_centralizer_centralizer`.
The closure `K` of the orbit `S v` is invariant under `S`, and so is its orthogonal complement
because `S` is closed under adjoints. Hence the orthogonal projection onto `K` lies in the
commutant `S'` and commutes with `x`; since `v ∈ K`, this gives `x v ∈ K`.

Finitely many vectors are handled by amplification: `S` acts diagonally on the Hilbert sum
`PiLp 2 (fun _ : ι => H)` through `PiLp.diagStarAlgHom`. Every operator on this sum commuting
with the diagonal copy of `S` has matrix entries (`ContinuousLinearMap.piLpEntry`) in `S'`, so
the diagonal copy of `x` lies in the double commutant of the diagonal copy of `S`, and the
single-vector case applies to the sum.

Simultaneous approximation on finitely many vectors is what lets an identity between vector
functionals `y ↦ ⟪u, y v⟫`, proved for `y` in the range `π(A)` of a representation, pass to the
von Neumann algebra `π(A)''` that it generates.

## References

Kadison–Ringrose, *Fundamentals of the Theory of Operator Algebras I*, Theorem 5.3.1, for the
double commutant theorem and its amplification proof.
-/

open scoped InnerProductSpace

namespace StarSubalgebra

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/- **The von Neumann density theorem for one vector.** An operator in the double commutant of a
unital star subalgebra `S` maps each vector `v` into the closure of the orbit `S v`. -/
theorem apply_mem_closure_of_mem_centralizer_centralizer [CompleteSpace H]
    (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) {x : H →L[𝕜] H}
    (hx : x ∈ (S : Set (H →L[𝕜] H)).centralizer.centralizer) (v : H) :
    x v ∈ closure ((fun s : H →L[𝕜] H => s v) '' S) := by
  -- the closed subspace `K` spanned by the orbit `S v`
  set K : Submodule 𝕜 H :=
    (S.toSubalgebra.toSubmodule.map
      (ContinuousLinearMap.apply 𝕜 H v).toLinearMap).topologicalClosure with hK
  have hKcoe : (K : Set H) = closure ((fun s : H →L[𝕜] H => s v) '' S) := by
    rw [hK, Submodule.topologicalClosure_coe, Submodule.map_coe]
    -- the carrier of the submodule underlying `S` is the carrier of `S`
    rfl
  have hKc : IsClosed (K : Set H) := Submodule.isClosed_topologicalClosure _
  -- `K` is invariant under every element of `S`
  have hinv : ∀ t ∈ S, K ∈ Module.End.invtSubmodule (t : Module.End 𝕜 H) := by
    intro t ht
    rw [Module.End.mem_invtSubmodule]
    refine Submodule.topologicalClosure_minimal _ ?_ (hKc.preimage t.continuous)
    rintro _ ⟨s, hs, rfl⟩
    exact Submodule.le_topologicalClosure _ ⟨t * s, S.mul_mem ht hs, rfl⟩
  -- since `S` is closed under adjoints, the orthogonal projection onto `K` commutes with `S`
  have hp : K.starProjection ∈ (S : Set (H →L[𝕜] H)).centralizer := by
    intro t ht
    have hadj : K ∈ Module.End.invtSubmodule (t.adjoint : Module.End 𝕜 H) := by
      simpa [← ContinuousLinearMap.star_eq_adjoint] using hinv (star t) (star_mem ht)
    have hred : K.IsReducing (t : Module.End 𝕜 H) :=
      ContinuousLinearMap.isReducing_iff_mem_invtSubmodule_adjoint.mpr ⟨hinv t ht, hadj⟩
    exact (Submodule.isReducing_coe_iff_commute_starProjection.mp hred).eq.symm
  have hvK : v ∈ K := Submodule.le_topologicalClosure _ ⟨1, S.one_mem, rfl⟩
  have hcomm : K.starProjection (x v) = x (K.starProjection v) := by
    simpa using DFunLike.congr_fun (hx _ hp) v
  rw [← hKcoe, SetLike.mem_coe, ← K.starProjection_eq_self_iff.mpr hvK, ← hcomm]
  exact K.starProjection_apply_mem _

section Amplification

variable {ι : Type*} [Fintype ι] [CompleteSpace H]

/- The diagonal amplification of an operator in `S''` lies in the double commutant of the
diagonal amplification of `S`. -/
private theorem diag_mem_centralizer_centralizer
    (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) {x : H →L[𝕜] H}
    (hx : x ∈ (S : Set (H →L[𝕜] H)).centralizer.centralizer) :
    PiLp.diagStarAlgHom 𝕜 H ι x ∈
      (S.map (PiLp.diagStarAlgHom 𝕜 H ι) : Set _).centralizer.centralizer := by
  classical
  intro T hT
  -- the matrix entries of an operator commuting with the diagonal copy of `S` lie in `S'`
  have hentry (i j : ι) : T.piLpEntry i j ∈ (S : Set (H →L[𝕜] H)).centralizer := by
    intro s hs
    have hsT := hT _ (StarSubalgebra.mem_map.mpr ⟨s, hs, rfl⟩)
    ext h
    have h' := congr_arg (fun w => w i) (DFunLike.congr_fun hsT (PiLp.single 2 j h))
    simp only [mul_apply_eq_comp, PiLp.diagStarAlgHom_apply, PiLp.diagStarAlgHom_apply_single]
      at h'
    simpa [mul_apply_eq_comp] using h'
  ext w i
  simp only [mul_apply_eq_comp]
  rw [ContinuousLinearMap.apply_eq_sum_piLpEntry, PiLp.diagStarAlgHom_apply,
    ContinuousLinearMap.apply_eq_sum_piLpEntry, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PiLp.diagStarAlgHom_apply]
  simpa using DFunLike.congr_fun (hx _ (hentry i j)) (w j)

end Amplification

/- **The von Neumann density theorem.** An operator `x` in the double commutant of a unital star
subalgebra `S` of the bounded operators on a Hilbert space is a strong-operator limit of elements
of `S`: for every finite family of vectors `v i` and every `ε > 0` there is `s ∈ S` with
`‖x (v i) - s (v i)‖ < ε` for all `i`. -/
theorem exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer [CompleteSpace H]
    (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) {x : H →L[𝕜] H}
    (hx : x ∈ (S : Set (H →L[𝕜] H)).centralizer.centralizer) {ι : Type*} [Finite ι]
    (v : ι → H) {ε : ℝ} (hε : 0 < ε) : ∃ s ∈ S, ∀ i, ‖x (v i) - s (v i)‖ < ε := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨_, ⟨T, hT, rfl⟩, hlt⟩ := Metric.mem_closure_iff.mp
    ((S.map (PiLp.diagStarAlgHom 𝕜 H ι)).apply_mem_closure_of_mem_centralizer_centralizer
      (diag_mem_centralizer_centralizer S hx) (WithLp.toLp 2 v)) ε hε
  obtain ⟨s, hs, rfl⟩ := StarSubalgebra.mem_map.mp hT
  refine ⟨s, hs, fun i => ?_⟩
  beta_reduce at hlt
  rw [dist_eq_norm, ← sub_apply, ← map_sub] at hlt
  calc ‖x (v i) - s (v i)‖ = ‖PiLp.diagStarAlgHom 𝕜 H ι (x - s) (WithLp.toLp 2 v) i‖ := by simp
    _ ≤ ‖PiLp.diagStarAlgHom 𝕜 H ι (x - s) (WithLp.toLp 2 v)‖ := PiLp.norm_apply_le _ _
    _ < ε := hlt

end StarSubalgebra

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- **The von Neumann density theorem for a generated von Neumann algebra.** An operator `x` in
the von Neumann algebra generated by a set `s` of bounded operators is a strong-operator limit of
elements of the star algebra generated by `s`: for every finite family of vectors `v i` and every
`ε > 0` there is `t ∈ StarAlgebra.adjoin ℂ s` with `‖x (v i) - t (v i)‖ < ε` for all `i`. -/
end VonNeumannAlgebra
end
end

section
/- Source: TauCeti, immutable revision 23caf7311c77a86c3a20d58a0b596b6da705bd94, TauCeti/Analysis/LocallyConvex/WeakOperatorTopology.lean.
Modified for ordinary D5 imports and necessary declaration selection; mathematical telescopes are preserved.
Full license and attribution: docs/reports/licenses/state-approximation-suppliers/.
Retire each transplanted result when the actual pinned mathlib contains an equivalent statement,
and replace its consumers with direct imports and applications of that pinned result. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Comparing the strong and weak operator topologies

The identity from the pointwise-convergence copy of continuous linear maps to the weak
operator copy is continuous. Centralizers of sets of operators are weak-operator closed.
These facts allow strong approximation results to identify weak operator closures without
changing the norm topology on the original operator space.

The two topologies have the same continuous linear functionals: every functional continuous for
pointwise convergence is a finite sum `T ↦ ∑ x ∈ s, g x (T x)` of continuous functionals of
values (`PointwiseConvergenceCLM.exists_finset_sum_eq`, in
`TauCeti.Analysis.LocallyConvex.PointwiseConvergence`), hence weak-operator continuous, and
conversely (`ContinuousLinearMapWOT.exists_finset_sum_eq`). On a Hilbert space, writing each
`g x` as an inner product gives the usual finite sums of matrix coefficients. By locally convex
separation, a convex set of operators therefore has the same closure in both topologies
(`Convex.toPointwiseConvergenceCLM_mem_closure_image_iff`).

## References

Kadison–Ringrose, *Fundamentals of the Theory of Operator Algebras I*, Theorem 5.1.2 and
Corollary 5.1.3.
-/

open scoped Topology

namespace ContinuousLinearMapWOT

variable {𝕜₁ 𝕜₂ E F : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂]
    {σ : 𝕜₁ →+* 𝕜₂} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E]
    [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [Module 𝕜₂ F] [ContinuousConstSMul 𝕜₂ F]

/- Pointwise (strong operator) convergence is stronger than weak operator convergence. -/
@[fun_prop]
theorem continuous_ofPointwiseConvergenceCLM :
    Continuous (fun T : E →SLₚₜ[σ] F => ofCLM (T : E →SL[σ] F)) := by
  apply continuous_of_dual_apply_continuous
  intro x y
  exact y.continuous.comp (continuous_eval_const x)

end ContinuousLinearMapWOT

namespace Set

variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [Module 𝕜 E] [ContinuousConstSMul 𝕜 E]
    [SeparatingDual 𝕜 E]

/- The commutant of any set of operators is closed in the weak operator topology. -/
theorem isClosed_image_ofCLM_centralizer (s : Set (E →L[𝕜] E)) :
    IsClosed (ContinuousLinearMapWOT.ofCLM '' s.centralizer) := by
  have h : ContinuousLinearMapWOT.ofCLM '' s.centralizer =
      (ContinuousLinearMapWOT.ofCLM '' s).centralizer := by
    ext T
    obtain ⟨T, rfl⟩ := ContinuousLinearMapWOT.ofCLM_surjective T
    rw [ContinuousLinearMapWOT.ofCLM_injective.mem_set_image]
    simp only [mem_centralizer_iff, forall_mem_image,
      ← ContinuousLinearMapWOT.ofCLM_mul, ContinuousLinearMapWOT.ofCLM_injective.eq_iff]
  rw [h]
  exact isClosed_centralizer _

end Set

namespace ContinuousLinearMapWOT

variable {𝕜₁ 𝕜 E F : Type*} [NormedField 𝕜₁] [RCLike 𝕜] {σ : 𝕜₁ →+* 𝕜} [AddCommGroup E]
    [TopologicalSpace E] [Module 𝕜₁ E] [ContinuousSMul 𝕜₁ E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F]

/- A linear functional on operators which is continuous for the topology of pointwise
convergence is continuous for the weak operator topology. -/
theorem continuous_strongDual_apply_toPointwiseConvergenceCLM
    (φ : StrongDual 𝕜 (E →SLₚₜ[σ] F)) :
    Continuous fun A : E →SWOT[σ] F ↦
      φ (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 σ E F A.toCLM) := by
  obtain ⟨s, g, hg⟩ := PointwiseConvergenceCLM.exists_finset_sum_eq φ
  simp only [hg]
  exact continuous_finsetSum _ fun x _ ↦ continuous_dual_apply x (g x)

/- **Continuous functionals in the weak operator topology.** A linear functional on operators
which is continuous for the weak operator topology is a finite sum of functionals
`A ↦ g x (A x)`. -/
variable [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

/- For a convex set of operators, the closures in the topology of pointwise convergence (the
strong operator topology) and in the weak operator topology contain the same operators. -/
theorem _root_.Convex.toPointwiseConvergenceCLM_mem_closure_image_iff {s : Set (E →SL[σ] F)}
    (hs : Convex ℝ s) {T : E →SL[σ] F} :
    ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 σ E F T ∈
        closure (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 σ E F '' s) ↔
      ofCLM T ∈ closure (ofCLM '' s) := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 σ E F
  refine ⟨fun h ↦ map_mem_closure (f := fun A : E →SLₚₜ[σ] F ↦ ofCLM (A : E →SL[σ] F))
    continuous_ofPointwiseConvergenceCLM h ?_, fun h ↦ ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · -- `e` is the identity on underlying operators, from the weak to the strong operator copy.
    let e : (E →SWOT[σ] F) →ₗ[𝕜] (E →SLₚₜ[σ] F) := q.toLinearMap ∘ₗ (linearEquiv 𝕜).toLinearMap
    have he (a : E →SL[σ] F) : e (ofCLM a) = q a := rfl
    have hconv : Convex ℝ (ofCLM '' s) := hs.linear_image (linearEquiv ℝ).symm.toLinearMap
    have himage : e '' (ofCLM '' s) = q '' s := by
      simp only [Set.image_image, he]
    exact himage ▸ he T ▸ e.image_closure_of_convex hconv
      (fun f ↦ continuous_strongDual_apply_toPointwiseConvergenceCLM f) ⟨_, h, rfl⟩

end ContinuousLinearMapWOT
end

section
/- Source: TauCeti, immutable revision 23caf7311c77a86c3a20d58a0b596b6da705bd94, TauCeti/Analysis/VonNeumannAlgebra/Bicommutant.lean.
Modified for ordinary D5 imports and necessary declaration selection; mathematical telescopes are preserved.
Full license and attribution: docs/reports/licenses/state-approximation-suppliers/.
Retire each transplanted result when the actual pinned mathlib contains an equivalent statement,
and replace its consumers with direct imports and applications of that pinned result. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# The bicommutant theorem

For a unital star subalgebra of bounded operators on a complete real or complex Hilbert
space, both its strong operator closure and its weak operator closure are its double
commutant. In particular, equality with the double commutant is equivalent to closedness
in either operator topology.

The closures are taken on Mathlib's separate topology copies, not in the operator norm.
For a concrete complex von Neumann algebra this gives strong and weak operator closedness;
for a generated algebra it identifies the closure of the star algebra generated by the
original set (`VonNeumannAlgebra.image_ofCLM_adjoin_eq_closure`). Taking the star algebra
first is essential for a set not closed under adjoints.

Since operator balls are weak operator compact, weak operator closedness makes every closed
norm ball of a concrete von Neumann algebra weak operator compact.

The approximation input is the finite-vector density theorem in
`TauCeti.Analysis.VonNeumannAlgebra.Density`.

The same holds for self-adjoint parts: the strong and weak operator closures of the self-adjoint
elements of the algebra are the self-adjoint elements of the double commutant. The weak form
applies the weak-operator continuous map `A ↦ 2⁻¹ • (A + A⋆)` to the bicommutant theorem; the
strong form follows because the self-adjoint part is convex, so its two closures agree. This is
the density statement used in the proof of the Kaplansky density theorem.

## References

Kadison–Ringrose, *Fundamentals of the Theory of Operator Algebras I*, Theorem 5.3.1, and the
proof of Theorem 5.3.5 for the self-adjoint parts.
-/

open scoped Topology

namespace StarSubalgebra

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [CompleteSpace H]

/- The strong operator closure of a unital star subalgebra is its double commutant. -/
theorem closure_image_toPointwiseConvergenceCLM
    (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
      (S : Set (H →L[𝕜] H))) =
      ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
        (S : Set (H →L[𝕜] H)).centralizer.centralizer := by
  let q := ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H
  have hclosed : IsClosed (q '' (S : Set (H →L[𝕜] H)).centralizer.centralizer) := by
    -- The pointwise copy has the same underlying maps; the preimage is along the
    -- continuous identity to the WOT copy, not along a norm-continuous inverse.
    convert ((S : Set (H →L[𝕜] H)).centralizer.isClosed_image_ofCLM_centralizer).preimage
      ContinuousLinearMapWOT.continuous_ofPointwiseConvergenceCLM using 1
    ext T
    simp only [q, Set.mem_image, Set.mem_preimage,
      ContinuousLinearMap.toPointwiseConvergenceCLM_apply]
    constructor
    · rintro ⟨a, ha, h⟩
      exact ⟨a, ha, congrArg ContinuousLinearMapWOT.ofCLM h⟩
    · rintro ⟨a, ha, h⟩
      exact ⟨a, ha, ContinuousLinearMapWOT.ofCLM_injective h⟩
  refine subset_antisymm
    (closure_minimal (Set.image_mono Set.subset_centralizer_centralizer) hclosed) ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_closure_iff_nhds_basis
    ((PointwiseConvergenceCLM.hasBasis_nhds_zero_of_basis
      (σ := RingHom.id 𝕜) (E := H) Metric.nhds_basis_ball).nhds_of_zero (q x))]
  rintro ⟨F, ε⟩ ⟨hF, hε⟩
  obtain ⟨s, hs, happrox⟩ := S.exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer
    hx (fun v : F => (v : H)) hε
  refine ⟨q s, ⟨s, hs, rfl⟩, ?_⟩
  intro v hv
  rw [Metric.mem_ball, dist_zero_right, sub_apply, norm_sub_rev]
  exact happrox ⟨v, hv⟩

/- The weak operator closure of a unital star subalgebra is its double commutant. -/
theorem closure_image_ofCLM (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) :
    closure (ContinuousLinearMapWOT.ofCLM '' (S : Set (H →L[𝕜] H))) =
      ContinuousLinearMapWOT.ofCLM '' (S : Set (H →L[𝕜] H)).centralizer.centralizer := by
  refine subset_antisymm
    (closure_minimal (Set.image_mono Set.subset_centralizer_centralizer)
      ((S : Set (H →L[𝕜] H)).centralizer.isClosed_image_ofCLM_centralizer)) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx' : ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H x ∈
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
        (S : Set (H →L[𝕜] H))) := by
    rw [S.closure_image_toPointwiseConvergenceCLM]
    exact ⟨x, hx, rfl⟩
  simpa only [Set.image_image, Function.comp_def,
    ContinuousLinearMap.toPointwiseConvergenceCLM_apply] using
    mem_closure_image
      ContinuousLinearMapWOT.continuous_ofPointwiseConvergenceCLM.continuousAt hx'

/- The weak operator closure of the self-adjoint part of a unital star subalgebra is the
self-adjoint part of its double commutant. -/
theorem closure_image_ofCLM_inter_selfAdjoint (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) :
    closure (ContinuousLinearMapWOT.ofCLM ''
      ((S : Set (H →L[𝕜] H)) ∩ selfAdjoint (H →L[𝕜] H))) =
      ContinuousLinearMapWOT.ofCLM ''
        ((S : Set (H →L[𝕜] H)).centralizer.centralizer ∩ selfAdjoint (H →L[𝕜] H)) := by
  -- Adjoints on the WOT copy are computed on the underlying operators.
  have hsa {x : H →L[𝕜] H} : IsSelfAdjoint (ContinuousLinearMapWOT.ofCLM x) ↔
      IsSelfAdjoint x :=
    ContinuousLinearMapWOT.ofCLM_injective.eq_iff
  refine subset_antisymm (fun A hA ↦ ?_) ?_
  · have hA' :
        A ∈ ContinuousLinearMapWOT.ofCLM '' (S : Set (H →L[𝕜] H)).centralizer.centralizer :=
      S.closure_image_ofCLM ▸ closure_mono (Set.image_mono Set.inter_subset_left) hA
    have hAsa : IsSelfAdjoint A := by
      refine closure_minimal ?_ (isClosed_eq continuous_star continuous_id) hA
      rintro _ ⟨a, ha, rfl⟩
      exact hsa.mpr ha.2
    obtain ⟨x, hx, rfl⟩ := hA'
    exact ⟨x, ⟨hx, hsa.mp hAsa⟩, rfl⟩
  · rintro _ ⟨x, ⟨hx, hxsa⟩, rfl⟩
    -- Apply the WOT-continuous real part `A ↦ 2⁻¹ • (A + A⋆)` to the WOT density of `S`.
    have hmem : ContinuousLinearMapWOT.ofCLM x ∈
        closure (ContinuousLinearMapWOT.ofCLM '' (S : Set (H →L[𝕜] H))) :=
      S.closure_image_ofCLM ▸ ⟨x, hx, rfl⟩
    have h2 : IsSelfAdjoint (2⁻¹ : 𝕜) := by simp [IsSelfAdjoint]
    have hre := map_mem_closure (f := fun A : H →WOT[𝕜] H ↦ (2⁻¹ : 𝕜) • (A + star A))
      (by fun_prop) hmem (t := ContinuousLinearMapWOT.ofCLM ''
        ((S : Set (H →L[𝕜] H)) ∩ selfAdjoint (H →L[𝕜] H))) (by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨(2⁻¹ : 𝕜) • (a + star a),
          ⟨SMulMemClass.smul_mem _ (add_mem ha (star_mem ha)), h2.smul (.add_star_self a)⟩, rfl⟩)
    have hx2 : (2⁻¹ : 𝕜) • (x + star x) = x := by
      rw [hxsa.star_eq, ← two_smul 𝕜 x, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    convert hre using 1
    exact congrArg ContinuousLinearMapWOT.ofCLM hx2.symm

/- The strong operator closure of the self-adjoint part of a unital star subalgebra is the
self-adjoint part of its double commutant. -/
theorem closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint [NormedSpace ℝ H]
    [IsScalarTower ℝ 𝕜 H] (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
      ((S : Set (H →L[𝕜] H)) ∩ selfAdjoint (H →L[𝕜] H))) =
      ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
        ((S : Set (H →L[𝕜] H)).centralizer.centralizer ∩ selfAdjoint (H →L[𝕜] H)) := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H
  -- The self-adjoint part is convex, so its strong and weak operator closures agree.
  -- Mathlib records only `StarModule 𝕜` here; real scalars act through `𝕜`, so they commute
  -- with adjoints and `selfAdjoint.submodule ℝ` is available.
  have : StarModule ℝ (H →L[𝕜] H) := ⟨fun r a ↦ by
    simp only [RCLike.real_smul_eq_coe_smul (K := 𝕜), star_smul, RCLike.star_def,
      RCLike.conj_ofReal, star_trivial]⟩
  have hconv : Convex ℝ ((S : Set (H →L[𝕜] H)) ∩ selfAdjoint (H →L[𝕜] H)) :=
    (S.toSubalgebra.toSubmodule.restrictScalars ℝ).convex.inter
      (selfAdjoint.submodule ℝ (H →L[𝕜] H)).convex
  ext T
  -- `q` is the identity on underlying operators.
  obtain ⟨x, rfl⟩ : ∃ x : H →L[𝕜] H, q x = T := ⟨T, rfl⟩
  rw [hconv.toPointwiseConvergenceCLM_mem_closure_image_iff,
    S.closure_image_ofCLM_inter_selfAdjoint, ContinuousLinearMapWOT.ofCLM_injective.mem_set_image,
    ContinuousLinearMap.toPointwiseConvergenceCLM_injective.mem_set_image]

/- **The bicommutant theorem:** a unital star subalgebra equals its double commutant
if and only if it is weak operator closed. -/
end StarSubalgebra

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- A concrete von Neumann algebra is weak operator closed. -/
end VonNeumannAlgebra
end
