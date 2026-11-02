/- GID: D5/S3/Quantum/Measurements/HaarPureProjectorMoment
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/HaarPureProjectorMoment
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The Haar second moment of a pure projector is the normalized symmetric projector. -/

import D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
import D5.S3.Quantum.Measurements.UnitaryPureProjectorSpan
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-! The pure-projector specialization of the two-copy Haar twirl. -/

open Matrix MeasureTheory TopologicalSpace
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.Elementwise

noncomputable section

namespace D5.S3.Quantum.Measurements.HaarPureProjectorMoment

open D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem pure_twirl {d : ℕ} [NeZero d] :
    (haarAverage (Fin d)).mulVec
        (Matrix.vec (Matrix.single (0, 0) (0, 0) (1 : ℂ))) =
      (1 / ((d : ℂ) * (d + 1))) •
        (Matrix.vec (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) +
          Matrix.vec (Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d)))) := by
  classical
  by_cases hd : d = 1
  · subst d
    have hy : (Matrix.single (0, 0) (0, 0) (1 : ℂ) :
        Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) = 1 := by
      ext a b
      simp [Matrix.single, Matrix.one_apply, Subsingleton.elim a (0, 0),
        Subsingleton.elim b (0, 0)]
    rw [hy, haarAverage_identity_fixed]
    ext r
    simp [Matrix.vec, Matrix.one_apply, Equiv.Perm.permMatrix, Subsingleton.elim r.1 (0, 0),
      Subsingleton.elim r.2 (0, 0)]
  have hd2 : 2 ≤ d := by have := NeZero.ne d; omega
  let a : Fin d := ⟨0, by omega⟩
  let b : Fin d := ⟨1, by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; simp [a, b] at this
  let y : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
    Matrix.single (0, 0) (0, 0) 1
  let s := Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d))
  let w : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
    Matrix.of (Function.curry (((haarAverage (Fin d)).mulVec (Matrix.vec y)) ∘ Prod.swap))
  obtain ⟨α, β, hspan⟩ := haarAverage_image_span (Matrix.vec y) a b hab
  have hw : w = α • 1 + β • s := by
    ext r c
    exact congrFun hspan (c, r)
  have hs : s.IsHermitian := by
    ext r c
    simp [s, Matrix.conjTranspose_apply, Equiv.Perm.permMatrix, Prod.ext_iff,
      eq_comm, and_comm]
  have hss : s * s = 1 := by
    have hh : Equiv.prodComm (Fin d) (Fin d) * Equiv.prodComm (Fin d) (Fin d) =
        (1 : Equiv.Perm (Fin d × Fin d)) := by ext r <;> rfl
    simp [s, ← Matrix.permMatrix_mul, hh]
  have hts : s.trace = (d : ℂ) := by
    simp only [s, Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
    simp [Equiv.Perm.permMatrix, Prod.ext_iff, eq_comm]
  have hv : Matrix.vec w = (haarAverage (Fin d)).mulVec (Matrix.vec y) := rfl
  have ht := hermitian_fixed_pairing (haarAverage (Fin d)) haarAverage_hermitian
    (Matrix.vec (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ))
    (Matrix.vec y) haarAverage_identity_fixed
  rw [← hv, Matrix.star_vec_dotProduct_vec, Matrix.star_vec_dotProduct_vec] at ht
  have ht0 : w.trace = 1 := by simpa [y] using ht
  have ht' := hermitian_fixed_pairing (haarAverage (Fin d)) haarAverage_hermitian
    (Matrix.vec s) (Matrix.vec y) haarAverage_swap_fixed
  rw [← hv, Matrix.star_vec_dotProduct_vec, Matrix.star_vec_dotProduct_vec,
    hs.eq] at ht'
  have ht1 : (s * w).trace = 1 := by
    simpa [y, s, Matrix.trace_mul_single, Equiv.Perm.permMatrix] using ht'
  rw [hw, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one, hts] at ht0
  rw [hw, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
    hss, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hts,
    Matrix.trace_one] at ht1
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, smul_eq_mul] at ht0 ht1
  have hn : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hn1 : (d + 1 : ℂ) ≠ 0 := by exact_mod_cast (show d + 1 ≠ 0 by omega)
  have hnm1 : (d - 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show (d : ℤ) - 1 ≠ 0 by omega)
  have hα : α = 1 / ((d : ℂ) * (d + 1)) := by
    field_simp
    apply mul_left_cancel₀ hnm1
    linear_combination ht0 * (d : ℂ) - ht1
  have hβ : β = 1 / ((d : ℂ) * (d + 1)) := by
    field_simp
    apply mul_left_cancel₀ hnm1
    linear_combination ht1 * (d : ℂ) - ht0
  rw [hspan, hα, hβ, smul_add]

theorem pure_tensor_integral {d : ℕ} [NeZero d] :
    (∫ u : Matrix.unitaryGroup (Fin d) ℂ,
      (u.1 * Matrix.single 0 0 1 * u.1ᴴ) ⊗ₖ
        (u.1 * Matrix.single 0 0 1 * u.1ᴴ) ∂(Measure.haarMeasure
          (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ)))) =
      (1 / ((d : ℂ) * (d + 1))) •
        (1 + Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d))) := by
  classical
  let z := fun u : Matrix.unitaryGroup (Fin d) ℂ =>
    (u.1 * Matrix.single 0 0 1 * u.1ᴴ) ⊗ₖ (u.1 * Matrix.single 0 0 1 * u.1ᴴ)
  have hp (u : Matrix.unitaryGroup (Fin d) ℂ) (i j : Fin d) :
      ((u.1 * Matrix.single 0 0 1 * u.1ᴴ) : Matrix (Fin d) (Fin d) ℂ) i j = u.1 i 0 * star (u.1 j 0) := by
    simp [Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply,
      Finset.sum_mul, Finset.mul_sum, ite_and]
  have hz : Continuous z := by
    apply continuous_pi
    intro r
    apply continuous_pi
    intro c
    simp only [z, Matrix.kroneckerMap_apply, hp]
    have he (i j : Fin d) : Continuous (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
        u.1 i j) := (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
    exact ((he _ _).mul (he _ _).star).mul ((he _ _).mul (he _ _).star)
  have hi := hz.integrable_of_hasCompactSupport
    (μ := Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ)))
    (HasCompactSupport.of_compactSpace z)
  ext r c
  let ev : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →L[ℂ] ℂ :=
    ({ toFun := fun x => x r c
       map_add' := fun x y => rfl
       map_smul' := fun k x => rfl } :
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ] ℂ).toContinuousLinearMap
  have heval := ev.integral_comp_comm hi
  change (∫ u, z u r c ∂_) = (∫ u, z u ∂_) r c at heval
  rw [← heval]
  have h := congrFun (pure_twirl (d := d)) (c, r)
  simp only [Matrix.vec_single, Matrix.mulVec_single_one] at h
  change (∫ u : Matrix.unitaryGroup (Fin d) ℂ,
    literalMoment u.1 (c, r) ((0, 0), (0, 0)) ∂_) = _ at h
  convert h using 1
  · apply integral_congr_ae
    filter_upwards [] with u
    simp only [z, Matrix.kroneckerMap_apply, hp, literalMoment, Matrix.kronecker, Matrix.map_apply]
    ring
  · rfl

theorem pure_quadratic {d : ℕ} [NeZero d] (a : Matrix (Fin d) (Fin d) ℂ) :
    (∫ u : Matrix.unitaryGroup (Fin d) ℂ,
      Matrix.trace ((u.1 * Matrix.single 0 0 1 * u.1ᴴ) * a *
        (u.1 * Matrix.single 0 0 1 * u.1ᴴ) * a) ∂(Measure.haarMeasure
          (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ)))) =
      (a.trace ^ 2 + (a * a).trace) / ((d : ℂ) * (d + 1)) := by
  classical
  let q : Matrix (Fin d) (Fin d) ℂ := Matrix.single 0 0 1
  let p := fun u : Matrix.unitaryGroup (Fin d) ℂ => u.1 * q * u.1ᴴ
  let z := fun u : Matrix.unitaryGroup (Fin d) ℂ => p u ⊗ₖ p u
  have hp : Continuous p :=
    (continuous_subtype_val.matrix_mul continuous_const).matrix_mul
      continuous_subtype_val.matrix_conjTranspose
  have hz : Continuous z := by
    apply continuous_pi
    intro r
    apply continuous_pi
    intro c
    exact (((continuous_apply c.1).comp ((continuous_apply r.1).comp hp)).mul
      ((continuous_apply c.2).comp ((continuous_apply r.2).comp hp)))
  have hi := hz.integrable_of_hasCompactSupport
    (μ := Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ)))
    (HasCompactSupport.of_compactSpace z)
  let f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →L[ℂ] ℂ :=
    ((Matrix.traceLinearMap (Fin d × Fin d) ℂ ℂ).comp
      (LinearMap.mulLeft ℂ (a ⊗ₖ a))).toContinuousLinearMap
  have heq : ∀ u, f (z u) = (p u * a * p u * a).trace := by
    intro u
    change ((a ⊗ₖ a) * (p u ⊗ₖ p u)).trace = _
    rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]
    have hu : u.1ᴴ * u.1 = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp u.2
    have hb : q * q = q := by
      simp [q, Matrix.single_mul_single_same]
    have hpp : p u * p u = p u := by
      simp only [p, Matrix.mul_assoc, ← Matrix.mul_assoc u.1ᴴ u.1, hu,
        Matrix.one_mul, ← Matrix.mul_assoc q q, hb]
    have hpt : (p u).trace = 1 := by
      dsimp only [p]
      rw [Matrix.trace_mul_cycle, hu, Matrix.one_mul]
      simp [q]
    rw [UnitaryPureProjectorSpan.trace_one_sandwich (p u) a hpp hpt,
      Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm a (p u)]
  have hs : ((a ⊗ₖ a) *
      Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d))).trace =
        (a * a).trace := by
    rw [PEquiv.mul_toMatrix_toPEquiv]
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply, Function.id_def,
      Equiv.prodComm_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
      Matrix.mul_apply]
    rfl
  calc
    (∫ u, (p u * a * p u * a).trace ∂_) = ∫ u, f (z u) ∂_ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun u => (heq u).symm)
    _ = f (∫ u, z u ∂_) := f.integral_comp_comm hi
    _ = _ := by
      rw [show (∫ u, z u ∂_) = _ from pure_tensor_integral (d := d)]
      change ((a ⊗ₖ a) * ((1 / ((d : ℂ) * (d + 1))) •
        (1 + Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d))))).trace = _
      rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.mul_one,
        Matrix.trace_add, Matrix.trace_kronecker, hs]
      simp [pow_two, div_eq_mul_inv, mul_comm]

end D5.S3.Quantum.Measurements.HaarPureProjectorMoment
