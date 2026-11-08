/- GID: D5/S3/ContinuousObservables/C128IdealJordan
   generality: I
   mirror-B: D5/B/S3/ContinuousObservables/C128IdealJordan
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Star.SelfAdjoint]
   utility: none
   digest: Restriction of the entire selfadjoint zero-extension ideal is an onto real linear isometry preserving the original Jordan product and oriented commutator. -/

import D5.S3.ContinuousObservables.C128ZeroExtension
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-! # The whole selfadjoint ideal and its original operations -/

noncomputable section

open Set Filter
open scoped Topology ZeroAtInfty ComplexOrder

namespace D5.S3.ContinuousObservables.C128IdealJordan

open C0Multipliers C128ZeroExtension

/-- The whole ambient selfadjoint space. -/
abbrev X := selfAdjoint C(Y, MatrixFiber)

/-- All selfadjoint continuous fields vanishing outside the original open domain. -/
def I : Submodule ℝ X where
  carrier := {r | (r.val : C(Y, MatrixFiber)) ∈ wholeIdeal}
  zero_mem' := wholeIdeal.zero_mem
  add_mem' hr hs := wholeIdeal.add_mem hr hs
  smul_mem' c r hr := by
    intro y hy
    change c • r.val y = 0
    rw [hr y hy, smul_zero]

private def extendSelfAdjoint (f : selfAdjoint SourceAlgebra) : I :=
  ⟨⟨extensionHom f.val, by
      change star (extensionHom f.val) = extensionHom f.val
      rw [← map_star, selfAdjoint.star_val_eq]⟩,
    by
      change extensionHom f.val ∈ (wholeIdeal : Set C(Y, MatrixFiber))
      rw [← whole_zero_extension.2.1]
      exact ⟨f.val, rfl⟩⟩

private def restrictSelfAdjoint (r : I) : selfAdjoint SourceAlgebra :=
  ⟨restriction ⟨r.val.val, r.property⟩, by
    apply ZeroAtInftyContinuousMap.ext
    intro t
    change star (r.val.val (inclusion t)) = r.val.val (inclusion t)
    exact congrArg (fun g : C(Y, MatrixFiber) => g (inclusion t)) r.val.property⟩

/-- Restriction on the whole ideal, with zero extension as its inverse. -/
def j : I ≃ₗᵢ[ℝ] selfAdjoint SourceAlgebra where
  toFun := restrictSelfAdjoint
  invFun := extendSelfAdjoint
  left_inv r := by
    apply Subtype.ext
    apply Subtype.ext
    exact whole_zero_extension.2.2.2.1 ⟨r.val.val, r.property⟩
  right_inv f := by
    apply Subtype.ext
    apply ZeroAtInftyContinuousMap.ext
    intro t
    exact whole_zero_extension.2.2.2.2.1 f.val t
  map_add' r s := by
    apply Subtype.ext
    apply ZeroAtInftyContinuousMap.ext
    intro t
    rfl
  map_smul' c r := by
    apply Subtype.ext
    apply ZeroAtInftyContinuousMap.ext
    intro t
    rfl
  norm_map' r := by
    have h := whole_zero_extension.1.dist_eq
      (restriction ⟨r.val.val, r.property⟩) 0
    simp only [map_zero, dist_zero_right] at h
    rw [show extensionHom (restriction ⟨r.val.val, r.property⟩) = r.val.val from
      whole_zero_extension.2.2.2.1 ⟨r.val.val, r.property⟩] at h
    exact h.symm

/-- The original real Jordan product in the ambient space. -/
def S (a b : X) : X :=
  ⟨(1 / 2 : ℝ) • (a.val * b.val + b.val * a.val), by
    simp only [selfAdjoint.mem_iff, star_smul, star_trivial, star_add, star_mul,
      selfAdjoint.star_val_eq, add_comm]⟩

/-- The original oriented commutator in the ambient space. -/
def D (a b : X) : X :=
  ⟨(Complex.I / 2) • (a.val * b.val - b.val * a.val), by
    simp only [selfAdjoint.mem_iff, star_smul, star_sub, star_mul,
      selfAdjoint.star_val_eq, star_div₀, Complex.star_def, Complex.conj_I, map_ofNat]
    rw [← neg_sub (a.val * b.val) (b.val * a.val), neg_div, neg_smul, smul_neg,
      neg_neg]⟩

private theorem S_mem (a : X) (r : I) : S a r.val ∈ I := by
  intro y hy
  change (1 / 2 : ℝ) • (a.val y * r.val.val y + r.val.val y * a.val y) = 0
  rw [r.property y hy]
  simp

private theorem D_mem (r s : I) : D r.val s.val ∈ I := by
  intro y hy
  change (Complex.I / 2) • (r.val.val y * s.val.val y - s.val.val y * r.val.val y) = 0
  rw [r.property y hy]
  simp

/-- The ideal is closed and Jordan invariant. The onto isometry j preserves the exact
Jordan product and the original oriented commutator on every pair of ideal elements. -/
theorem whole_selfadjoint_ideal :
    IsClosed (I : Set X) ∧
    (∀ (a : X) (r : I), S a r.val ∈ I) ∧
    (∀ (r s : I), D r.val s.val ∈ I) ∧
    (∀ r : I, ∀ t : sourceDomain, (j r).val t = r.val.val (inclusion t)) ∧
    (∀ r s : I,
      (j ⟨S r.val s.val, S_mem r.val s⟩).val =
        (1 / 2 : ℝ) • ((j r).val * (j s).val + (j s).val * (j r).val)) ∧
    (∀ r s : I,
      (j ⟨D r.val s.val, D_mem r s⟩).val =
        (Complex.I / 2) • ((j r).val * (j s).val - (j s).val * (j r).val)) := by
  refine ⟨whole_zero_extension.2.2.1.preimage continuous_subtype_val, S_mem, D_mem,
    fun _ _ => rfl, ?_, ?_⟩
  · intro r s
    apply ZeroAtInftyContinuousMap.ext
    intro t
    rfl
  · intro r s
    apply ZeroAtInftyContinuousMap.ext
    intro t
    rfl

end D5.S3.ContinuousObservables.C128IdealJordan
