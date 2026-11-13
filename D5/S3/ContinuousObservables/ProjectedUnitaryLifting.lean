/- GID: D5/S3/ContinuousObservables/ProjectedUnitaryLifting
   generality: G
   mirror-B: D5/B/S3/ContinuousObservables/ProjectedUnitaryLifting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Projected unitary words act polynomially on arbitrary input Gram spectra. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Unitary
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license; the full license is in
`docs/reports/licenses/auto-res-lean-qsvt-LICENSE.txt`.
Authors of the reused proofs: shosonoda.

Selected proof bodies from auto-res/lean-qsvt, immutable revision
42c4b9149d5957db497e4226bc02da92d10f7a3c:
QSVT/Operator/Basic.lean; Encoding/Projected.lean; QSP/Conventions.lean;
SVT/PhaseOp.lean; AltSeq.lean; EigenBasis.lean; SVTransform.lean;
SVD.lean; TwoVector.lean; TwoFrame.lean; SingularPair.lean.
Literal original locators are retained by declaration name.
Namespaces, imports, visibility and the standard Hilbert-space typeclasses are adapted.
The exact scalar-premise operator assembly uses the original structural action proofs.
Replace this transplant by equivalent declarations when available at the receiver's
own pinned Mathlib revision.

Operator.Basic retains copied lean-quantum provenance:
https://github.com/Hayata-Yamasaki-Group/lean-quantum,
Quantum/QuantumMechanics/D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Operator.lean, Apache License 2.0.
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
namespace D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Operator
universe u
abbrev L (ℋ : Type u) [AddCommGroup ℋ] [Module ℂ ℋ] : Type u :=
  ℋ →ₗ[ℂ] ℋ

notation X"†" => LinearMap.adjoint X
variable {ℋ : Type u} [NormedAddCommGroup ℋ]
  [InnerProductSpace ℂ ℋ] [FiniteDimensional ℂ ℋ]
def IsProjective (X : L ℋ) : Prop :=
  X.IsPositive ∧ IsIdempotentElem X

private theorem isPositive_of_isStarProjection {Q : L ℋ} (hQ : IsStarProjection Q) : Q.IsPositive := by
  refine ⟨(LinearMap.isSymmetric_iff_isSelfAdjoint Q).mpr hQ.isSelfAdjoint, fun x => ?_⟩
  have hQQ : Q (Q x) = Q x := by
    rw [← Module.End.mul_apply, hQ.isIdempotentElem.eq]
  have hadj : Q† = Q := hQ.isSelfAdjoint.star_eq
  have key : inner ℂ (Q x) (Q x) = inner ℂ (Q x) x := by
    rw [← LinearMap.adjoint_inner_left Q x (Q x), hadj, hQQ]
  calc (0 : ℝ) ≤ RCLike.re (inner ℂ (Q x) (Q x)) := inner_self_nonneg
    _ = RCLike.re (inner ℂ (Q x) x) := by rw [key]

private theorem isProjective_iff_isStarProjection {X : L ℋ} :
    IsProjective X ↔ IsStarProjection X :=
  ⟨fun h => ⟨h.2, h.1.isSelfAdjoint⟩,
    fun h => ⟨isPositive_of_isStarProjection h, h.isIdempotentElem⟩⟩

namespace IsProjective

variable {P : L ℋ}

private theorem isSelfAdjoint (h : IsProjective P) : IsSelfAdjoint P := h.1.isSelfAdjoint

private theorem adjoint_eq (h : IsProjective P) : P† = P := h.isSelfAdjoint.star_eq

private theorem mul_self (h : IsProjective P) : P * P = P := h.2.eq

private theorem mul_one_sub (h : IsProjective P) : P * (1 - P) = 0 := h.2.mul_one_sub_self

end IsProjective

end D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Operator

namespace D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Encoding

open D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Operator

universe u

structure ProjUnitaryEncoding (ℋ : Type u) [NormedAddCommGroup ℋ]
  [InnerProductSpace ℂ ℋ] [FiniteDimensional ℂ ℋ] where
  
  U : L ℋ
  
  hU : U ∈ unitary (L ℋ)
  
  P : L ℋ
  
  P' : L ℋ
  
  hP : IsProjective P
  
  hP' : IsProjective P'

variable {ℋ : Type u} [NormedAddCommGroup ℋ]
  [InnerProductSpace ℂ ℋ] [FiniteDimensional ℂ ℋ]

namespace ProjUnitaryEncoding

variable (E : ProjUnitaryEncoding ℋ)

def encoded : L ℋ := E.P' * E.U * E.P

@[simp] private theorem U_adjoint_mul_U : E.U† * E.U = 1 := Unitary.star_mul_self_of_mem E.hU

@[simp] private theorem U_mul_U_adjoint : E.U * E.U† = 1 := Unitary.mul_star_self_of_mem E.hU

private theorem U_adjoint_mem_unitary : E.U† ∈ unitary (L ℋ) := Unitary.star_mem E.hU

private theorem encoded_adjoint : (E.encoded)† = E.P * E.U† * E.P' := by
  rw [← LinearMap.star_eq_adjoint, ← LinearMap.star_eq_adjoint]
  simp only [encoded, star_mul, E.hP.isSelfAdjoint.star_eq, E.hP'.isSelfAdjoint.star_eq, mul_assoc]

private theorem P'_mul_encoded : E.P' * E.encoded = E.encoded := by
  rw [encoded, ← mul_assoc, ← mul_assoc, E.hP'.mul_self]

private theorem encoded_mul_P : E.encoded * E.P = E.encoded := by
  simp only [encoded, mul_assoc, E.hP.mul_self]

end ProjUnitaryEncoding
end D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Encoding

namespace D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Scalar

open Matrix Complex

abbrev M₂ := Matrix (Fin 2) (Fin 2) ℂ

noncomputable def Rref (x : ℝ) : M₂ :=
  !![(x : ℂ), (Real.sqrt (1 - x ^ 2) : ℂ); (Real.sqrt (1 - x ^ 2) : ℂ), -(x : ℂ)]

noncomputable def phaseZ (φ : ℝ) : M₂ :=
  !![Complex.exp (Complex.I * φ), 0; 0, Complex.exp (-(Complex.I * φ))]

noncomputable def seqR : List ℝ → ℝ → M₂
  | [], _ => 1
  | φ :: Φ, x => phaseZ φ * Rref x * seqR Φ x

noncomputable def Wrot (x : ℝ) : M₂ :=
  !![(x : ℂ), Complex.I * Real.sqrt (1 - x ^ 2); Complex.I * Real.sqrt (1 - x ^ 2), (x : ℂ)]

noncomputable def seqW (φ₀ : ℝ) (Φ : List ℝ) (x : ℝ) : M₂ :=
  phaseZ φ₀ * (Φ.map (fun φ => Wrot x * phaseZ φ)).prod

@[simp]
private theorem seqR_nil (x : ℝ) : seqR [] x = 1 := rfl

@[simp]
private theorem seqR_cons (φ : ℝ) (Φ : List ℝ) (x : ℝ) :
    seqR (φ :: Φ) x = phaseZ φ * Rref x * seqR Φ x := rfl

end D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Scalar

namespace D5.S3.ContinuousObservables.ProjectedUnitaryLifting

open D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Operator

universe u

variable {ℋ : Type u} [NormedAddCommGroup ℋ]
  [InnerProductSpace ℂ ℋ] [FiniteDimensional ℂ ℋ]

noncomputable def phaseOp (P : L ℋ) (φ : ℝ) : L ℋ :=
  Complex.exp (Complex.I * φ) • P + Complex.exp (-(Complex.I * φ)) • (1 - P)

end D5.S3.ContinuousObservables.ProjectedUnitaryLifting

namespace D5.S3.ContinuousObservables.ProjectedUnitaryLifting

open D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Operator D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Encoding

universe u

variable {ℋ : Type u} [NormedAddCommGroup ℋ]
  [InnerProductSpace ℂ ℋ] [FiniteDimensional ℂ ℋ]

noncomputable def altSeq (E : ProjUnitaryEncoding ℋ) : List ℝ → L ℋ
  | [] => 1
  | φ :: Φ => (if Even Φ.length then phaseOp E.P' φ * E.U else phaseOp E.P φ * E.U†) * altSeq E Φ

variable (E : ProjUnitaryEncoding ℋ)

@[simp] private theorem altSeq_nil : altSeq E [] = 1 := rfl

@[simp] private theorem altSeq_cons (φ : ℝ) (Φ : List ℝ) :
    altSeq E (φ :: Φ) =
      (if Even Φ.length then phaseOp E.P' φ * E.U else phaseOp E.P φ * E.U†) * altSeq E Φ := rfl

end D5.S3.ContinuousObservables.ProjectedUnitaryLifting

namespace D5.S3.ContinuousObservables.ProjectedUnitaryLifting

open D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Operator D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Encoding

universe u

variable {ℋ : Type u} [NormedAddCommGroup ℋ]
  [InnerProductSpace ℂ ℋ] [FiniteDimensional ℂ ℋ]

private theorem norm_proj_apply_le {P : L ℋ} (hP : IsProjective P) (x : ℋ) : ‖P x‖ ≤ ‖x‖ := by
  have key : inner ℂ (P x) (P x) = inner ℂ x (P x) := by
    rw [← LinearMap.adjoint_inner_right P x (P x), hP.adjoint_eq, ← Module.End.mul_apply,
      hP.mul_self]
  have h1 : ‖P x‖ ^ 2 ≤ ‖x‖ * ‖P x‖ :=
    calc ‖P x‖ ^ 2 = RCLike.re (inner ℂ (P x) (P x)) := (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
      _ = RCLike.re (inner ℂ x (P x)) := by rw [key]
      _ ≤ ‖inner ℂ x (P x)‖ := RCLike.re_le_norm _
      _ ≤ ‖x‖ * ‖P x‖ := norm_inner_le_norm x (P x)
  rcases (norm_nonneg (P x)).eq_or_lt with h0 | h0
  · rw [← h0]; exact norm_nonneg x
  · exact le_of_mul_le_mul_right (by rwa [sq] at h1) h0

private theorem norm_unitary_apply {U : L ℋ} (hU : U ∈ unitary (L ℋ)) (x : ℋ) : ‖U x‖ = ‖x‖ := by
  have key : inner ℂ (U x) (U x) = inner ℂ x x := by
    rw [← LinearMap.adjoint_inner_right U x (U x), ← Module.End.mul_apply,
      ← LinearMap.star_eq_adjoint, Unitary.star_mul_self_of_mem hU, Module.End.one_apply]
  have h := congrArg RCLike.re key
  rw [inner_self_eq_norm_sq (𝕜 := ℂ), inner_self_eq_norm_sq (𝕜 := ℂ)] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

private theorem mem_range_proj_iff {P : L ℋ} (hP : IsProjective P) (x : ℋ) :
    x ∈ LinearMap.range P ↔ P x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [← Module.End.mul_apply, hP.mul_self]
  · intro h
    exact ⟨x, h⟩

end D5.S3.ContinuousObservables.ProjectedUnitaryLifting

namespace D5.S3.ContinuousObservables.ProjectedUnitaryLifting
open D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Operator D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Encoding Polynomial
universe u
variable {ℋ : Type u} [NormedAddCommGroup ℋ]
  [InnerProductSpace ℂ ℋ] [FiniteDimensional ℂ ℋ]
variable (E : ProjUnitaryEncoding ℋ)
private theorem P_mul_encoded_adjoint : E.P * E.encoded† = E.encoded† := by
  rw [← LinearMap.star_eq_adjoint, ← E.hP.isSelfAdjoint.star_eq, ← star_mul, E.encoded_mul_P]

private theorem commute_P_adjoint_mul_encoded : Commute E.P (E.encoded† * E.encoded) := by
  change E.P * (E.encoded† * E.encoded) = E.encoded† * E.encoded * E.P
  rw [← mul_assoc, P_mul_encoded_adjoint, mul_assoc, E.encoded_mul_P]


private theorem commute_P_aeval (R : ℂ[X]) : Commute E.P (aeval (E.encoded† * E.encoded) R) := by
  induction R using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | monomial n a =>
    rw [aeval_monomial]
    have h0 : Commute E.P (algebraMap ℂ (L ℋ) a) := (Algebra.commutes a E.P).symm
    exact h0.mul_right ((commute_P_adjoint_mul_encoded E).pow_right n)


end D5.S3.ContinuousObservables.ProjectedUnitaryLifting

namespace D5.S3.ContinuousObservables.ProjectedUnitaryLifting

open D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Operator D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Encoding Polynomial

universe u

variable {ℋ : Type u} [NormedAddCommGroup ℋ]
  [InnerProductSpace ℂ ℋ] [FiniteDimensional ℂ ℋ]

private theorem _root_.D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Encoding.ProjUnitaryEncoding.norm_encoded_apply_le
    (E : ProjUnitaryEncoding ℋ) (x : ℋ) : ‖E.encoded x‖ ≤ ‖x‖ :=
  calc ‖E.encoded x‖ = ‖E.P' (E.U (E.P x))‖ := rfl
    _ ≤ ‖E.U (E.P x)‖ := norm_proj_apply_le E.hP' _
    _ = ‖E.P x‖ := norm_unitary_apply E.hU _
    _ ≤ ‖x‖ := norm_proj_apply_le E.hP x

section Gram

variable (E : ProjUnitaryEncoding ℋ)

private theorem gram_isSymmetric : LinearMap.IsSymmetric (E.encoded† * E.encoded) :=
  (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr (IsSelfAdjoint.star_mul_self E.encoded)

private theorem P_mul_gram : E.P * (E.encoded† * E.encoded) = E.encoded† * E.encoded := by
  rw [← mul_assoc, P_mul_encoded_adjoint]

private theorem gram_mem_range (x : ℋ) : (E.encoded† * E.encoded) x ∈ LinearMap.range E.P :=
  ⟨(E.encoded† * E.encoded) x, by rw [← Module.End.mul_apply, P_mul_gram]⟩

private theorem gram_range_invariant :
    ∀ x ∈ LinearMap.range E.P, (E.encoded† * E.encoded) x ∈ LinearMap.range E.P :=
  fun x _ => gram_mem_range E x

abbrev inputSpace : Submodule ℂ ℋ := LinearMap.range E.P

abbrev svIndex : Type := Fin (Module.finrank ℂ (inputSpace E))

noncomputable def gramRestricted : inputSpace E →ₗ[ℂ] inputSpace E :=
  (E.encoded† * E.encoded).restrict (gram_range_invariant E)

@[simp] private theorem coe_gramRestricted_apply (v : inputSpace E) :
    (gramRestricted E v : ℋ) = (E.encoded† * E.encoded) v := rfl

private theorem gramRestricted_isSymmetric : LinearMap.IsSymmetric (gramRestricted E) :=
  (gram_isSymmetric E).restrict_invariant (gram_range_invariant E)

noncomputable def rvBasis : OrthonormalBasis (svIndex E) ℂ (inputSpace E) :=
  (gramRestricted_isSymmetric E).eigenvectorBasis rfl

noncomputable def σsq (i : svIndex E) : ℝ :=
  (gramRestricted_isSymmetric E).eigenvalues rfl i

noncomputable def rv (i : svIndex E) : ℋ :=
  (rvBasis E i : ℋ)

private theorem rv_mem (i : svIndex E) : rv E i ∈ LinearMap.range E.P :=
  (rvBasis E i).2

private theorem P_rv (i : svIndex E) : E.P (rv E i) = rv E i :=
  (mem_range_proj_iff E.hP _).mp (rv_mem E i)

private theorem gram_rv (i : svIndex E) :
    (E.encoded† * E.encoded) (rv E i) = (σsq E i : ℂ) • rv E i := by
  have h : gramRestricted E (rvBasis E i) = (σsq E i : ℂ) • rvBasis E i :=
    (gramRestricted_isSymmetric E).apply_eigenvectorBasis rfl i
  have h' := congrArg Subtype.val h
  rw [Submodule.coe_smul, coe_gramRestricted_apply] at h'
  exact h'

private theorem norm_rv (i : svIndex E) : ‖rv E i‖ = 1 := by
  rw [rv, Submodule.norm_coe]
  exact (rvBasis E).orthonormal.1 i

private theorem rv_ne_zero (i : svIndex E) : rv E i ≠ 0 := by
  intro h
  have h1 := norm_rv E i
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

private theorem hasEigenvector_rv (i : svIndex E) :
    Module.End.HasEigenvector (E.encoded† * E.encoded) (σsq E i : ℂ) (rv E i) :=
  ⟨Module.End.mem_eigenspace_iff.mpr (gram_rv E i), rv_ne_zero E i⟩

private theorem σsq_eq_norm_sq (i : svIndex E) : σsq E i = ‖E.encoded (rv E i)‖ ^ 2 := by
  have h1 : inner ℂ ((E.encoded† * E.encoded) (rv E i)) (rv E i) =
      inner ℂ (E.encoded (rv E i)) (E.encoded (rv E i)) := by
    rw [Module.End.mul_apply, LinearMap.adjoint_inner_left]
  rw [gram_rv, inner_smul_left, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, norm_rv,
    Complex.conj_ofReal] at h1
  norm_num at h1
  exact_mod_cast h1

private theorem σsq_nonneg (i : svIndex E) : 0 ≤ σsq E i := by
  rw [σsq_eq_norm_sq]
  positivity

noncomputable def σ (i : svIndex E) : ℝ :=
  Real.sqrt (σsq E i)

private theorem σ_nonneg (i : svIndex E) : 0 ≤ σ E i :=
  Real.sqrt_nonneg _

private theorem σ_sq (i : svIndex E) : σ E i ^ 2 = σsq E i :=
  Real.sq_sqrt (σsq_nonneg E i)

private theorem ofReal_σ_sq (i : svIndex E) : (σ E i : ℂ) ^ 2 = (σsq E i : ℂ) := by
  rw [← Complex.ofReal_pow, σ_sq]

private theorem σ_eq_norm (i : svIndex E) : σ E i = ‖E.encoded (rv E i)‖ := by
  rw [σ, σsq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

private theorem σ_le_one (i : svIndex E) : σ E i ≤ 1 := by
  rw [σ_eq_norm]
  have h := E.norm_encoded_apply_le (rv E i)
  rwa [norm_rv] at h

private theorem σ_mem_Icc (i : svIndex E) : σ E i ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨σ_nonneg E i, σ_le_one E i⟩

private theorem aeval_gram_rv (R : ℂ[X]) (i : svIndex E) :
    aeval (E.encoded† * E.encoded) R (rv E i) = R.eval ((σ E i : ℂ) ^ 2) • rv E i := by
  rw [Module.End.aeval_apply_of_hasEigenvector (hasEigenvector_rv E i), ofReal_σ_sq]

private theorem sum_repr_rv (x : ℋ) (hx : E.P x = x) :
    x = ∑ i, inner ℂ (rv E i) x • rv E i := by
  have h := congrArg Subtype.val
    ((rvBasis E).sum_repr' ⟨x, (mem_range_proj_iff E.hP x).mpr hx⟩)
  rw [Submodule.coe_sum] at h
  simp only [Submodule.coe_smul, Submodule.coe_inner] at h
  exact h.symm

private theorem ext_of_rv {T S : L ℋ} (h1 : ∀ i, T (rv E i) = S (rv E i))
    (h2 : ∀ x, E.P x = 0 → T x = S x) : T = S := by
  ext x
  have hsplit : ∀ R : L ℋ, R x = R (E.P x) + R ((1 - E.P) x) := fun R => by
    rw [← map_add, LinearMap.sub_apply, Module.End.one_apply, add_sub_cancel]
  have hPx : T (E.P x) = S (E.P x) := by
    have hP : E.P (E.P x) = E.P x := by rw [← Module.End.mul_apply, E.hP.mul_self]
    rw [sum_repr_rv E (E.P x) hP, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul, h1 i]
  have hQx : T ((1 - E.P) x) = S ((1 - E.P) x) :=
    h2 _ (by rw [← Module.End.mul_apply, E.hP.mul_one_sub, LinearMap.zero_apply])
  rw [hsplit T, hsplit S, hPx, hQx]

private theorem ext_mul_P_of_rv {T S : L ℋ} (h : ∀ i, T (rv E i) = S (rv E i)) :
    T * E.P = S * E.P := by
  refine ext_of_rv E (fun i => ?_) (fun x hx => ?_)
  · rw [Module.End.mul_apply, Module.End.mul_apply, P_rv, h i]
  · rw [Module.End.mul_apply, Module.End.mul_apply, hx, map_zero, map_zero]

end Gram

end D5.S3.ContinuousObservables.ProjectedUnitaryLifting

namespace D5.S3.ContinuousObservables.ProjectedUnitaryLifting

open D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Operator D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Encoding D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Scalar

universe u

variable {ℋ : Type u} [NormedAddCommGroup ℋ]
  [InnerProductSpace ℂ ℋ] [FiniteDimensional ℂ ℋ]

section Proj

variable {P : L ℋ}

private theorem _root_.D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Operator.IsProjective.apply_one_sub_apply (hP : IsProjective P) (v : ℋ) :
    P ((1 - P) v) = 0 := by
  rw [← Module.End.mul_apply, hP.mul_one_sub, LinearMap.zero_apply]

private theorem _root_.D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Operator.IsProjective.inner_apply_one_sub_apply (hP : IsProjective P) (v : ℋ) :
    inner ℂ (P v) ((1 - P) v) = 0 := by
  have h := LinearMap.adjoint_inner_left P ((1 - P) v) v
  rwa [hP.adjoint_eq, hP.apply_one_sub_apply, inner_zero_right] at h

private theorem _root_.D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Operator.IsProjective.inner_one_sub_apply_apply (hP : IsProjective P) (v : ℋ) :
    inner ℂ ((1 - P) v) (P v) = 0 := by
  rw [← inner_conj_symm, hP.inner_apply_one_sub_apply, map_zero]

private theorem _root_.D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Operator.IsProjective.inner_self_eq_add (hP : IsProjective P) (v : ℋ) :
    inner ℂ v v = inner ℂ (P v) (P v) + inner ℂ ((1 - P) v) ((1 - P) v) := by
  have hv : P v + (1 - P) v = v := by
    rw [LinearMap.sub_apply, Module.End.one_apply, add_sub_cancel]
  conv_lhs => rw [← hv]
  rw [inner_add_add_self, hP.inner_apply_one_sub_apply, hP.inner_one_sub_apply_apply, add_zero,
    add_zero]

private theorem phaseOp_apply_of_proj_eq (φ : ℝ) {v : ℋ} (hv : P v = v) :
    phaseOp P φ v = Complex.exp (Complex.I * φ) • v := by
  simp only [phaseOp, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.one_apply, hv, sub_self, smul_zero, add_zero]

private theorem phaseOp_apply_of_proj_eq_zero (φ : ℝ) {v : ℋ} (hv : P v = 0) :
    phaseOp P φ v = Complex.exp (-(Complex.I * φ)) • v := by
  simp only [phaseOp, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.one_apply, hv, sub_zero, smul_zero, zero_add]

end Proj
private theorem phaseZ_mul_Rref_mul_apply_zero_zero (φ x : ℝ) (M : M₂) :
    (phaseZ φ * Rref x * M) 0 0 =
      Complex.exp (Complex.I * φ) * ((x : ℂ) * M 0 0 + (Real.sqrt (1 - x ^ 2) : ℂ) * M 1 0) := by
  simp [phaseZ, Rref, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem phaseZ_mul_Rref_mul_apply_one_zero (φ x : ℝ) (M : M₂) :
    (phaseZ φ * Rref x * M) 1 0 =
      Complex.exp (-(Complex.I * φ)) *
        ((Real.sqrt (1 - x ^ 2) : ℂ) * M 0 0 - (x : ℂ) * M 1 0) := by
  simp [phaseZ, Rref, Matrix.mul_apply, Fin.sum_univ_two]
  ring

variable {ς : ℝ}
private theorem ofReal_sqrt_ne_zero (hς : ς ^ 2 < 1) : (Real.sqrt (1 - ς ^ 2) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by linarith)).ne'

private theorem ofReal_sqrt_mul_self' (hς : ς ^ 2 ≤ 1) :
    (Real.sqrt (1 - ς ^ 2) : ℂ) * (Real.sqrt (1 - ς ^ 2) : ℂ) = 1 - (ς : ℂ) ^ 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  push_cast
  ring

private theorem unitary_apply_eq_of_proj_apply {P : L ℋ} (hP : IsProjective P) {V : L ℋ}
    (hV : V ∈ unitary (L ℋ)) {ψ χ : ℋ} (hn : ‖χ‖ = ‖ψ‖) (hPV : P (V ψ) = χ) : V ψ = χ := by
  have hV1 : V† * V = 1 := Unitary.star_mul_self_of_mem hV
  have hVV : inner ℂ (V ψ) (V ψ) = inner ℂ ψ ψ := by
    rw [← LinearMap.adjoint_inner_left V ψ (V ψ), ← Module.End.mul_apply, hV1,
      Module.End.one_apply]
  have hχ : inner ℂ χ χ = inner ℂ ψ ψ := by
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hn]
  have hpy := hP.inner_self_eq_add (V ψ)
  rw [hVV, hPV, hχ] at hpy
  have hw : inner ℂ ((1 - P) (V ψ)) ((1 - P) (V ψ)) = 0 := by linear_combination -hpy
  rw [inner_self_eq_zero, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw
  rw [hw, hPV]

end D5.S3.ContinuousObservables.ProjectedUnitaryLifting

namespace D5.S3.ContinuousObservables.ProjectedUnitaryLifting

open D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Operator D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Encoding D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Scalar

universe u

variable {ℋ : Type u} [NormedAddCommGroup ℋ]
  [InnerProductSpace ℂ ℋ] [FiniteDimensional ℂ ℋ]

structure IsSingularPair (E : ProjUnitaryEncoding ℋ) (ψ : ℋ) (σ : ℝ) : Prop where
  
  P_eq : E.P ψ = ψ
  
  nonneg : 0 ≤ σ
  
  le_one : σ ≤ 1
  
  gram : (E.encoded†) (E.encoded ψ) = ((σ : ℂ) ^ 2) • ψ

section Defs

variable (E : ProjUnitaryEncoding ℋ)

noncomputable def lvOf (ψ : ℋ) (σ : ℝ) : ℋ :=
  if σ = 0 then 0 else ((σ : ℂ)⁻¹) • E.encoded ψ

noncomputable def lvtOf (ψ : ℋ) (σ : ℝ) : ℋ :=
  ((Real.sqrt (1 - σ ^ 2) : ℂ)⁻¹) • ((1 - E.P') (E.U ψ))

noncomputable def rvpOf (ψ : ℋ) (σ : ℝ) : ℋ :=
  ((Real.sqrt (1 - σ ^ 2) : ℂ)⁻¹) • ((1 - E.P) ((E.U†) (lvOf E ψ σ)))

private theorem lvOf_of_eq_zero {ψ : ℋ} {σ : ℝ} (h0 : σ = 0) : lvOf E ψ σ = 0 := by
  rw [lvOf, ite_eq_left h0]

private theorem lvOf_of_ne_zero {ψ : ℋ} {σ : ℝ} (h0 : σ ≠ 0) :
    lvOf E ψ σ = ((σ : ℂ)⁻¹) • E.encoded ψ := by
  rw [lvOf, ite_eq_right h0]

private theorem P'_lvOf (ψ : ℋ) (σ : ℝ) : E.P' (lvOf E ψ σ) = lvOf E ψ σ := by
  by_cases h0 : σ = 0
  · rw [lvOf_of_eq_zero E h0, map_zero]
  · rw [lvOf_of_ne_zero E h0, map_smul, ← Module.End.mul_apply, E.P'_mul_encoded]

private theorem P'_lvtOf (ψ : ℋ) (σ : ℝ) : E.P' (lvtOf E ψ σ) = 0 := by
  rw [lvtOf, map_smul, E.hP'.apply_one_sub_apply, smul_zero]

private theorem P_rvpOf (ψ : ℋ) (σ : ℝ) : E.P (rvpOf E ψ σ) = 0 := by
  rw [rvpOf, map_smul, E.hP.apply_one_sub_apply, smul_zero]

private theorem phaseOp_P'_lvOf (ψ : ℋ) (σ : ℝ) (φ : ℝ) :
    phaseOp E.P' φ (lvOf E ψ σ) = Complex.exp (Complex.I * φ) • lvOf E ψ σ :=
  phaseOp_apply_of_proj_eq φ (P'_lvOf E ψ σ)

private theorem phaseOp_P'_lvtOf (ψ : ℋ) (σ : ℝ) (φ : ℝ) :
    phaseOp E.P' φ (lvtOf E ψ σ) = Complex.exp (-(Complex.I * φ)) • lvtOf E ψ σ :=
  phaseOp_apply_of_proj_eq_zero φ (P'_lvtOf E ψ σ)

private theorem phaseOp_P_rvpOf (ψ : ℋ) (σ : ℝ) (φ : ℝ) :
    phaseOp E.P φ (rvpOf E ψ σ) = Complex.exp (-(Complex.I * φ)) • rvpOf E ψ σ :=
  phaseOp_apply_of_proj_eq_zero φ (P_rvpOf E ψ σ)

private theorem ofReal_sqrt_one_sub_sq_eq_zero {σ : ℝ} (h1 : σ = 1) :
    (Real.sqrt (1 - σ ^ 2) : ℂ) = 0 := by
  rw [h1, one_pow, sub_self, Real.sqrt_zero, Complex.ofReal_zero]

private theorem lvtOf_of_eq_one {ψ : ℋ} {σ : ℝ} (h1 : σ = 1) : lvtOf E ψ σ = 0 := by
  rw [lvtOf, ofReal_sqrt_one_sub_sq_eq_zero h1, inv_zero, zero_smul]

private theorem rvpOf_of_eq_one {ψ : ℋ} {σ : ℝ} (h1 : σ = 1) : rvpOf E ψ σ = 0 := by
  rw [rvpOf, ofReal_sqrt_one_sub_sq_eq_zero h1, inv_zero, zero_smul]

end Defs
namespace IsSingularPair

variable {E : ProjUnitaryEncoding ℋ} {ψ : ℋ} {σ : ℝ}

private theorem sq_le_one (h : IsSingularPair E ψ σ) : σ ^ 2 ≤ 1 := pow_le_one₀ h.nonneg h.le_one

private theorem eq_one_of_sq_eq_one (h : IsSingularPair E ψ σ) (h1 : σ ^ 2 = 1) : σ = 1 :=
  (pow_eq_one_iff_of_nonneg h.nonneg two_ne_zero).mp h1

private theorem norm_encoded_sq (h : IsSingularPair E ψ σ) : ‖E.encoded ψ‖ ^ 2 = σ ^ 2 * ‖ψ‖ ^ 2 := by
  have h1 : inner ℂ ((E.encoded†) (E.encoded ψ)) ψ = inner ℂ (E.encoded ψ) (E.encoded ψ) :=
    LinearMap.adjoint_inner_left _ _ _
  rw [h.gram, inner_smul_left, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, map_pow,
    Complex.conj_ofReal] at h1
  have h2 := congrArg Complex.re h1
  simpa [← Complex.ofReal_pow, ← Complex.ofReal_mul] using h2.symm

private theorem norm_encoded (h : IsSingularPair E ψ σ) : ‖E.encoded ψ‖ = σ * ‖ψ‖ := by
  have h1 := h.norm_encoded_sq
  rw [← mul_pow] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg h.nonneg (norm_nonneg _)) two_ne_zero).mp h1

private theorem encoded_eq_zero_of_eq_zero (h : IsSingularPair E ψ σ) (h0 : σ = 0) :
    E.encoded ψ = 0 := by
  rw [← norm_eq_zero, h.norm_encoded, h0, zero_mul]

private theorem A_apply (h : IsSingularPair E ψ σ) : E.encoded ψ = (σ : ℂ) • lvOf E ψ σ := by
  by_cases h0 : σ = 0
  · rw [lvOf_of_eq_zero E h0, h.encoded_eq_zero_of_eq_zero h0, smul_zero]
  · rw [lvOf_of_ne_zero E h0, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr h0), one_smul]

private theorem A_adjoint_lvOf (h : IsSingularPair E ψ σ) :
    (E.encoded†) (lvOf E ψ σ) = (σ : ℂ) • ψ := by
  by_cases h0 : σ = 0
  · rw [lvOf_of_eq_zero E h0, map_zero, h0, Complex.ofReal_zero, zero_smul]
  · have hc : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0
    rw [lvOf_of_ne_zero E h0, map_smul, h.gram, smul_smul, sq, ← mul_assoc, inv_mul_cancel₀ hc,
      one_mul]

private theorem norm_lvOf (h : IsSingularPair E ψ σ) (h0 : σ ≠ 0) : ‖lvOf E ψ σ‖ = ‖ψ‖ := by
  rw [lvOf_of_ne_zero E h0, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg h.nonneg, h.norm_encoded, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]

private theorem P'_U_apply (h : IsSingularPair E ψ σ) : E.P' (E.U ψ) = (σ : ℂ) • lvOf E ψ σ := by
  calc E.P' (E.U ψ) = E.P' (E.U (E.P ψ)) := by rw [h.P_eq]
    _ = E.encoded ψ := rfl
    _ = (σ : ℂ) • lvOf E ψ σ := h.A_apply

private theorem P_U_adjoint_lvOf (h : IsSingularPair E ψ σ) :
    E.P ((E.U†) (lvOf E ψ σ)) = (σ : ℂ) • ψ := by
  calc E.P ((E.U†) (lvOf E ψ σ)) = E.P ((E.U†) (E.P' (lvOf E ψ σ))) := by rw [P'_lvOf]
    _ = ((E.encoded)†) (lvOf E ψ σ) := by rw [E.encoded_adjoint]; rfl
    _ = (σ : ℂ) • ψ := h.A_adjoint_lvOf

private theorem U_apply_of_eq_one (h : IsSingularPair E ψ σ) (h1 : σ = 1) : E.U ψ = lvOf E ψ σ := by
  have h0 : σ ≠ 0 := by rw [h1]; exact one_ne_zero
  refine unitary_apply_eq_of_proj_apply E.hP' E.hU (h.norm_lvOf h0) ?_
  rw [h.P'_U_apply, h1, Complex.ofReal_one, one_smul]

private theorem U_adjoint_lvOf_of_eq_one (h : IsSingularPair E ψ σ) (h1 : σ = 1) :
    (E.U†) (lvOf E ψ σ) = ψ := by
  have h0 : σ ≠ 0 := by rw [h1]; exact one_ne_zero
  refine unitary_apply_eq_of_proj_apply E.hP E.U_adjoint_mem_unitary (h.norm_lvOf h0).symm ?_
  rw [h.P_U_adjoint_lvOf, h1, Complex.ofReal_one, one_smul]

private theorem U_apply (h : IsSingularPair E ψ σ) :
    E.U ψ = (σ : ℂ) • lvOf E ψ σ + (Real.sqrt (1 - σ ^ 2) : ℂ) • lvtOf E ψ σ := by
  rcases h.sq_le_one.lt_or_eq with hlt | heq
  · rw [lvtOf, smul_smul, mul_inv_cancel₀ (ofReal_sqrt_ne_zero hlt), one_smul, LinearMap.sub_apply,
      Module.End.one_apply, h.P'_U_apply, add_sub_cancel]
  · have h1 := h.eq_one_of_sq_eq_one heq
    rw [ofReal_sqrt_one_sub_sq_eq_zero h1, zero_smul, add_zero, h.U_apply_of_eq_one h1, h1,
      Complex.ofReal_one, one_smul]

private theorem U_adjoint_lvOf (h : IsSingularPair E ψ σ) :
    (E.U†) (lvOf E ψ σ) = (σ : ℂ) • ψ + (Real.sqrt (1 - σ ^ 2) : ℂ) • rvpOf E ψ σ := by
  rcases h.sq_le_one.lt_or_eq with hlt | heq
  · rw [rvpOf, smul_smul, mul_inv_cancel₀ (ofReal_sqrt_ne_zero hlt), one_smul, LinearMap.sub_apply,
      Module.End.one_apply, h.P_U_adjoint_lvOf, add_sub_cancel]
  · have h1 := h.eq_one_of_sq_eq_one heq
    rw [ofReal_sqrt_one_sub_sq_eq_zero h1, zero_smul, add_zero, h.U_adjoint_lvOf_of_eq_one h1, h1,
      Complex.ofReal_one, one_smul]

private theorem U_rvpOf (h : IsSingularPair E ψ σ) :
    E.U (rvpOf E ψ σ) = (Real.sqrt (1 - σ ^ 2) : ℂ) • lvOf E ψ σ - (σ : ℂ) • lvtOf E ψ σ := by
  rcases h.sq_le_one.lt_or_eq with hlt | heq
  · have h1 : E.U ((E.U†) (lvOf E ψ σ)) = lvOf E ψ σ := by
      rw [← Module.End.mul_apply, E.U_mul_U_adjoint, Module.End.one_apply]
    rw [h.U_adjoint_lvOf, map_add, map_smul, map_smul, h.U_apply] at h1
    refine smul_right_injective ℋ (ofReal_sqrt_ne_zero hlt) ?_
    have h2 : (Real.sqrt (1 - σ ^ 2) : ℂ) • E.U (rvpOf E ψ σ) =
        lvOf E ψ σ - (σ : ℂ) • ((σ : ℂ) • lvOf E ψ σ +
          (Real.sqrt (1 - σ ^ 2) : ℂ) • lvtOf E ψ σ) :=
      eq_sub_of_add_eq' h1
    change (Real.sqrt (1 - σ ^ 2) : ℂ) • E.U (rvpOf E ψ σ) =
      (Real.sqrt (1 - σ ^ 2) : ℂ) •
        ((Real.sqrt (1 - σ ^ 2) : ℂ) • lvOf E ψ σ - (σ : ℂ) • lvtOf E ψ σ)
    rw [h2, smul_sub, smul_smul, smul_smul, ofReal_sqrt_mul_self' hlt.le]
    module
  · have h1 := h.eq_one_of_sq_eq_one heq
    rw [rvpOf_of_eq_one E h1, lvtOf_of_eq_one E h1, ofReal_sqrt_one_sub_sq_eq_zero h1, map_zero,
      zero_smul, smul_zero, sub_zero]

private theorem U_adjoint_lvtOf (h : IsSingularPair E ψ σ) :
    (E.U†) (lvtOf E ψ σ) = (Real.sqrt (1 - σ ^ 2) : ℂ) • ψ - (σ : ℂ) • rvpOf E ψ σ := by
  rcases h.sq_le_one.lt_or_eq with hlt | heq
  · have h1 : (E.U†) (E.U ψ) = ψ := by
      rw [← Module.End.mul_apply, E.U_adjoint_mul_U, Module.End.one_apply]
    rw [h.U_apply, map_add, map_smul, map_smul, h.U_adjoint_lvOf] at h1
    refine smul_right_injective ℋ (ofReal_sqrt_ne_zero hlt) ?_
    have h2 : (Real.sqrt (1 - σ ^ 2) : ℂ) • (E.U†) (lvtOf E ψ σ) =
        ψ - (σ : ℂ) • ((σ : ℂ) • ψ + (Real.sqrt (1 - σ ^ 2) : ℂ) • rvpOf E ψ σ) :=
      eq_sub_of_add_eq' h1
    change (Real.sqrt (1 - σ ^ 2) : ℂ) • (E.U†) (lvtOf E ψ σ) =
      (Real.sqrt (1 - σ ^ 2) : ℂ) •
        ((Real.sqrt (1 - σ ^ 2) : ℂ) • ψ - (σ : ℂ) • rvpOf E ψ σ)
    rw [h2, smul_sub, smul_smul, smul_smul, ofReal_sqrt_mul_self' hlt.le]
    module
  · have h1 := h.eq_one_of_sq_eq_one heq
    rw [lvtOf_of_eq_one E h1, rvpOf_of_eq_one E h1, ofReal_sqrt_one_sub_sq_eq_zero h1, map_zero,
      zero_smul, smul_zero, sub_zero]

private theorem phaseOp_P_apply (h : IsSingularPair E ψ σ) (φ : ℝ) :
    phaseOp E.P φ ψ = Complex.exp (Complex.I * φ) • ψ :=
  phaseOp_apply_of_proj_eq φ h.P_eq

end IsSingularPair

section Headline

variable {E : ProjUnitaryEncoding ℋ} {ψ : ℋ} {σ : ℝ}

theorem altSeq_apply_singular (h : IsSingularPair E ψ σ) (Φ : List ℝ) :
    altSeq E Φ ψ =
      (seqR Φ σ) 0 0 • (if Even Φ.length then ψ else lvOf E ψ σ) +
        (seqR Φ σ) 1 0 • (if Even Φ.length then rvpOf E ψ σ else lvtOf E ψ σ) := by
  induction Φ with
  | nil => simp
  | cons φ Φ ih =>
    have hlen : Even (φ :: Φ).length ↔ ¬ Even Φ.length := by
      rw [List.length_cons]
      exact Nat.even_add_one
    rw [altSeq_cons, Module.End.mul_apply, ih, seqR_cons, phaseZ_mul_Rref_mul_apply_zero_zero,
      phaseZ_mul_Rref_mul_apply_one_zero]
    by_cases he : Even Φ.length
    · have he' : ¬ Even (φ :: Φ).length := fun h2 => hlen.mp h2 he
      rw [ite_eq_left he, ite_eq_left he, ite_eq_left he, ite_eq_right he', ite_eq_right he',
        Module.End.mul_apply, map_add, map_smul, map_smul, h.U_apply, h.U_rvpOf]
      simp only [map_add, map_sub, map_smul, phaseOp_P'_lvOf E ψ σ, phaseOp_P'_lvtOf E ψ σ]
      module
    · have he' : Even (φ :: Φ).length := hlen.mpr he
      rw [ite_eq_right he, ite_eq_right he, ite_eq_right he, ite_eq_left he', ite_eq_left he',
        Module.End.mul_apply, map_add, map_smul, map_smul, h.U_adjoint_lvOf, h.U_adjoint_lvtOf]
      simp only [map_add, map_sub, map_smul, h.phaseOp_P_apply, phaseOp_P_rvpOf E ψ σ]
      module

end Headline
end D5.S3.ContinuousObservables.ProjectedUnitaryLifting

namespace D5.S3.ContinuousObservables.ProjectedUnitaryLifting
open Operator Encoding Scalar Polynomial
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

/-- The raw self-adjoint idempotents give the original projected-unitary encoding. -/
noncomputable def ofRaw (U P Pt : H →ₗ[ℂ] H)
    (hU : star U * U = 1) (hU' : U * star U = 1)
    (hP : IsStarProjection P) (hPt : IsStarProjection Pt) : ProjUnitaryEncoding H where
  U := U
  hU := Unitary.mem_iff.mpr ⟨hU, hU'⟩
  P := P
  P' := Pt
  hP := Operator.isProjective_iff_isStarProjection.mpr hP
  hP' := Operator.isProjective_iff_isStarProjection.mpr hPt

private theorem singular_pair_rv (E : ProjUnitaryEncoding H) (i : svIndex E) :
    IsSingularPair E (rv E i) (σ E i) where
  P_eq := P_rv E i
  nonneg := σ_nonneg E i
  le_one := σ_le_one E i
  gram := by rw [← Module.End.mul_apply, gram_rv, ofReal_σ_sq]

/-- Exact lifting of an arbitrary scalar 00 identity, including the input kernel term. -/
theorem polynomial_lifting (E : ProjUnitaryEncoding H) (Ψ : List ℝ) (R : ℂ[X])
    (hscalar : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      seqR Ψ x 0 0 = if Even Ψ.length then R.eval ((x : ℂ) ^ 2)
        else (x : ℂ) * R.eval ((x : ℂ) ^ 2)) :
    (Even Ψ.length → E.P * altSeq E Ψ * E.P =
      E.P * aeval (E.encoded† * E.encoded) R * E.P) ∧
    (Odd Ψ.length → E.P' * altSeq E Ψ * E.P =
      E.encoded * aeval (E.encoded† * E.encoded) R) := by
  constructor
  · intro he
    apply ext_mul_P_of_rv E
    intro i
    have h := altSeq_apply_singular (singular_pair_rv E i) Ψ
    rw [ite_eq_left he, ite_eq_left he] at h
    rw [Module.End.mul_apply, h, map_add, map_smul, map_smul,
      P_rv, P_rvpOf, smul_zero, add_zero, hscalar _ (σ_mem_Icc E i), ite_eq_left he,
      Module.End.mul_apply, aeval_gram_rv, map_smul, P_rv]
  · intro ho
    have he : ¬ Even Ψ.length := Nat.not_even_iff_odd.mpr ho
    have hs : (E.encoded * aeval (E.encoded† * E.encoded) R) * E.P =
        E.encoded * aeval (E.encoded† * E.encoded) R := by
      rw [mul_assoc, ← (commute_P_aeval E R).eq, ← mul_assoc, E.encoded_mul_P]
    rw [← hs]
    apply ext_mul_P_of_rv E
    intro i
    have h := altSeq_apply_singular (singular_pair_rv E i) Ψ
    rw [ite_eq_right he, ite_eq_right he] at h
    rw [Module.End.mul_apply, h, map_add, map_smul, map_smul,
      P'_lvOf, P'_lvtOf, smul_zero, add_zero, hscalar _ (σ_mem_Icc E i), ite_eq_right he,
      Module.End.mul_apply, aeval_gram_rv, map_smul,
      (singular_pair_rv E i).A_apply, smul_smul, mul_comm]

end D5.S3.ContinuousObservables.ProjectedUnitaryLifting
