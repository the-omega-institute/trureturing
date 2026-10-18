/- GID: D5/S3/Quantum/Measurement/PositiveBranchRealRationalResponse
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/PositiveBranchRealRationalResponse
   mirror-E: none(waiver:finite-dimensional-response)
   anchors: []
   utility: none
   digest: A fixed real CP-word space carries the actual absorbing response. -/

import D5.S3.Quantum.Measurement.PositiveBranchReachableResponse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic
import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Tactic

/-! Fixed real coordinates of the original completely positive branch words. -/

noncomputable section
open Matrix Filter Topology Polynomial
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace

open Polynomial

namespace D5.S3.Quantum.Measurement.AffineMatrixResponse
set_option autoImplicit false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem eval_affine_det (A B : Matrix ι ι ℝ) (t : ℝ) :
    (Matrix.det ((X : ℝ[X]) • A.map C + B.map C)).eval t =
      Matrix.det (t • A + B) := by
  change (Polynomial.evalRingHom t) (Matrix.det _) = _
  rw [(Polynomial.evalRingHom t).map_det]
  congr 1
  ext i j
  simp
  ring

private theorem rank_one_det (A : Matrix ι ι ℝ) (hA : A.det ≠ 0)
    (r ell : ι → ℝ) :
    (A + replicateCol Unit r * replicateRow Unit ell).det =
      A.det * (1 + ell ⬝ᵥ (A⁻¹ *ᵥ r)) := by
  rw [Matrix.det_add_replicateCol_mul_replicateRow (ι := Unit)
    (isUnit_iff_ne_zero.mpr hA)]
  simp only [Matrix.det_unique (n := Unit)]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply,
    Matrix.replicateRow_apply, Matrix.replicateCol_apply, dotProduct,
    Finset.mul_sum]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  congr 2
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- An affine scalar readout of an affine inverse has numerator and denominator
of degree at most the matrix dimension. No positivity of matrix entries is
assumed, and the empty matrix gives the constant response. -/
private theorem affine_matrix_rational_response
    (A B : Matrix ι ι ℝ) (r ell₀ ell₁ : ι → ℝ) (γ : ℝ) (U : Set ℝ)
    (hdet : ∀ t ∈ U, (t • A + B).det ≠ 0) :
    ∃ P Q : ℝ[X], P.natDegree ≤ Fintype.card ι ∧ Q.natDegree ≤ Fintype.card ι ∧
      (∀ t ∈ U, Q.eval t ≠ 0 ∧
        γ + (ell₀ + t • ell₁) ⬝ᵥ ((t • A + B)⁻¹ *ᵥ r) = P.eval t / Q.eval t) ∧
      AnalyticOnNhd ℝ (fun t => P.eval t / Q.eval t) U := by
  let Q := (Matrix.det ((X : ℝ[X]) • A.map C + B.map C))
  let R₀ := replicateCol Unit r * replicateRow Unit ell₀
  let R₁ := replicateCol Unit r * replicateRow Unit ell₁
  let P := C (γ - 1) * Q +
    Matrix.det ((X : ℝ[X]) • (A + R₁).map C + (B + R₀).map C)
  have hQdeg : Q.natDegree ≤ Fintype.card ι := natDegree_det_X_add_C_le A B
  have hPdeg : P.natDegree ≤ Fintype.card ι := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact (natDegree_C_mul_le _ _).trans hQdeg
    · exact natDegree_det_X_add_C_le _ _
  have heval (t : ℝ) (ht : t ∈ U) :
      Q.eval t ≠ 0 ∧
        γ + (ell₀ + t • ell₁) ⬝ᵥ ((t • A + B)⁻¹ *ᵥ r) = P.eval t / Q.eval t := by
    have hQ : Q.eval t = (t • A + B).det := eval_affine_det A B t
    refine ⟨hQ ▸ hdet t ht, ?_⟩
    have hR : t • (A + R₁) + (B + R₀) =
        (t • A + B) + replicateCol Unit r * replicateRow Unit (ell₀ + t • ell₁) := by
      ext i j
      simp [R₀, R₁, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
      ring
    have hP : P.eval t = (γ - 1) * Q.eval t +
        (t • A + B).det *
          (1 + (ell₀ + t • ell₁) ⬝ᵥ ((t • A + B)⁻¹ *ᵥ r)) := by
      simp only [P, eval_add, eval_mul, eval_C]
      simp only [eval_affine_det]
      rw [hR, rank_one_det _ (hdet t ht)]
    rw [hP, hQ]
    field_simp [hdet t ht]
    <;> ring
  refine ⟨P, Q, hPdeg, hQdeg, heval, ?_⟩
  intro t ht
  exact ((analyticOnNhd_id.aeval_polynomial P) t (Set.mem_univ t)).div
    ((analyticOnNhd_id.aeval_polynomial Q) t (Set.mem_univ t)) (heval t ht).1

end D5.S3.Quantum.Measurement.AffineMatrixResponse

namespace D5.S3.Quantum.Measurement.PositiveBranchReachableResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {d : ℕ} {α J : Type} [Fintype α] [Fintype J] [DecidableEq J]

/-- A group is one original CP branch; its Kraus summands are not treated as
separate observed branches. A zero Kraus summand is allowed. -/
def originalBranch (K : α → Matrix (Fin d) (Fin d) ℂ) (group : α → J) (j : J) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ :=
  (weightedCP K (fun a => if group a = j then 1 else 0)).restrictScalars ℝ

/-- Composition of the original CP maps, including the empty composition. -/
def cpWord (K : α → Matrix (Fin d) (Fin d) ℂ) (group : α → J) :
    List J → Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ
  | [] => LinearMap.id
  | j :: w => (originalBranch K group j).comp (cpWord K group w)

/-- This real space and its bases depend on the original maps and initial
state alone, and are independent of the source weights. -/
def realWordSpace (K : α → Matrix (Fin d) (Fin d) ℂ) (group : α → J)
    (ρ : Matrix (Fin d) (Fin d) ℂ) : Submodule ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  Submodule.span ℝ (Set.range (fun w : List J => cpWord K group w ρ))

private theorem initial_support (K : α → Matrix (Fin d) (Fin d) ℂ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) : matrixSupport ρ ≤ reachableSpace K ρ := by
  intro v hv
  apply (le_iSup (fun l => wordSpan K ρ l) 0)
  exact Submodule.subset_span ⟨[], by simp, v, hv, by simp [krausWord]⟩

private theorem cpWord_positive_supported (K : α → Matrix (Fin d) (Fin d) ℂ)
    (group : α → J) (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef)
    (w : List J) : (cpWord K group w ρ).PosSemidef ∧
      matrixSupport (cpWord K group w ρ) ≤ reachableSpace K ρ := by
  induction w with
  | nil => exact ⟨hρ, initial_support K ρ⟩
  | cons j w ih =>
      exact ⟨weightedCP_psd K _ (fun a => by split_ifs <;> norm_num) ih.1,
        weightedCP_reachable_support K _ (fun a => by split_ifs <;> norm_num)
          ρ _ ih.1 ih.2⟩

private theorem initial_mem_realWordSpace (K : α → Matrix (Fin d) (Fin d) ℂ)
    (group : α → J) (ρ : Matrix (Fin d) (Fin d) ℂ) : ρ ∈ realWordSpace K group ρ :=
  Submodule.subset_span ⟨[], rfl⟩

private theorem originalBranch_invariant (K : α → Matrix (Fin d) (Fin d) ℂ)
    (group : α → J) (ρ : Matrix (Fin d) (Fin d) ℂ) (j : J) :
    ∀ X ∈ realWordSpace K group ρ, originalBranch K group j X ∈ realWordSpace K group ρ := by
  intro X hX
  induction hX using Submodule.span_induction with
  | mem X hX =>
      obtain ⟨w, rfl⟩ := hX
      exact Submodule.subset_span ⟨j :: w, rfl⟩
  | zero => simp
  | add X Y _ _ hX hY => simpa only [map_add] using Submodule.add_mem _ hX hY
  | smul r X _ hX => simpa only [map_smul] using Submodule.smul_mem _ r hX

private theorem grouped_weightedCP (K : α → Matrix (Fin d) (Fin d) ℂ)
    (group : α → J) (w : J → ℝ) :
    (weightedCP K (fun a => w (group a))).restrictScalars ℝ =
      ∑ j, w j • originalBranch K group j := by
  ext X : 1
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, originalBranch,
    LinearMap.restrictScalars_apply]
  change (∑ a, (w (group a) : ℂ) • (K a * X * (K a)ᴴ)) =
    ∑ j, w j • (∑ a, ((if group a = j then 1 else 0 : ℝ) : ℂ) •
      (K a * X * (K a)ᴴ))
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

private theorem weightedCP_word_invariant (K : α → Matrix (Fin d) (Fin d) ℂ)
    (group : α → J) (ρ : Matrix (Fin d) (Fin d) ℂ) (w : J → ℝ) :
    ∀ X ∈ realWordSpace K group ρ,
      weightedCP K (fun a => w (group a)) X ∈ realWordSpace K group ρ := by
  intro X hX
  have h := LinearMap.congr_fun (grouped_weightedCP K group w) X
  rw [LinearMap.restrictScalars_apply, LinearMap.sum_apply] at h
  rw [h]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ (w j) (originalBranch_invariant K group ρ j X hX)

private theorem realWordSpace_supported_span (K : α → Matrix (Fin d) (Fin d) ℂ)
    (group : α → J) (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) :
    realWordSpace K group ρ ≤ Submodule.span ℝ
      {σ : Matrix (Fin d) (Fin d) ℂ | σ.PosSemidef ∧
        matrixSupport σ ≤ reachableSpace K ρ} := by
  apply Submodule.span_le.mpr
  rintro X ⟨w, rfl⟩
  exact Submodule.subset_span (cpWord_positive_supported K group ρ hρ w)

private theorem realWordSpace_hermitian (K : α → Matrix (Fin d) (Fin d) ℂ)
    (group : α → J) (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) :
    realWordSpace K group ρ ≤
      D5.S3.Quantum.Measurement.BasisMeasurementProjection.HermitianSpace d := by
  apply Submodule.span_le.mpr
  rintro X ⟨w, rfl⟩
  change cpWord K group w ρ ∈ selfAdjoint (Matrix (Fin d) (Fin d) ℂ)
  rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
  exact (cpWord_positive_supported K group ρ hρ w).1.isHermitian

private theorem realWordSpace_range (K : α → Matrix (Fin d) (Fin d) ℂ)
    (group : α → J) (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) :
    ∀ X ∈ realWordSpace K group ρ, ∀ v : EuclideanSpace ℂ (Fin d),
      X.toEuclideanLin v ∈ reachableSpace K ρ := by
  intro X hX
  induction hX using Submodule.span_induction with
  | mem X hX =>
      obtain ⟨w, rfl⟩ := hX
      intro v
      obtain ⟨hp, hs⟩ := cpWord_positive_supported K group ρ hρ w
      apply hs
      rw [matrixSupport_eq_range hp.isHermitian]
      exact ⟨v, rfl⟩
  | zero => simp
  | add X Y _ _ hX hY =>
      intro v
      simpa only [map_add, LinearMap.add_apply] using
        (reachableSpace K ρ).add_mem (hX v) (hY v)
  | smul r X _ hX =>
      intro v
      change ((r : ℂ) • X).toEuclideanLin v ∈ _
      simpa only [map_smul, LinearMap.smul_apply] using
        (reachableSpace K ρ).smul_mem (r : ℂ) (hX v)

private theorem realWordSpace_dimension (K : α → Matrix (Fin d) (Fin d) ℂ)
    (group : α → J) (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) :
    Module.finrank ℝ (realWordSpace K group ρ) ≤
        (Module.finrank ℂ (reachableSpace K ρ)) ^ 2 ∧
      (Module.finrank ℂ (reachableSpace K ρ)) ^ 2 ≤ d ^ 2 := by
  let S := reachableSpace K ρ
  let V := realWordSpace K group ρ
  let b := stdOrthonormalBasis ℂ S
  have hrange := realWordSpace_range K group ρ hρ
  have hherm (X : V) : (X : Matrix (Fin d) (Fin d) ℂ).IsHermitian :=
    realWordSpace_hermitian K group ρ hρ X.property
  let f : V →ₗ[ℝ] (S →ₗ[ℂ] S) :=
    { toFun X := (X : Matrix (Fin d) (Fin d) ℂ).toEuclideanLin.restrict
        (fun v _ => hrange X X.property v)
      map_add' X Y := by
        ext v : 1
        apply Subtype.ext
        change ((X : Matrix (Fin d) (Fin d) ℂ) + Y).toEuclideanLin v = _
        simp only [map_add, LinearMap.add_apply]
        rfl
      map_smul' r X := by
        ext v : 1
        apply Subtype.ext
        change (r • (X : Matrix (Fin d) (Fin d) ℂ)).toEuclideanLin v = _
        change ((r : ℂ) • (X : Matrix (Fin d) (Fin d) ℂ)).toEuclideanLin v = _
        simp only [map_smul, LinearMap.smul_apply]
        rfl }
  let g₀ := ((LinearMap.toMatrix b.toBasis b.toBasis).toLinearMap.restrictScalars ℝ).comp f
  have hg₀ (X : V) : g₀ X ∈
      D5.S3.Quantum.Measurement.BasisMeasurementProjection.HermitianSpace
        (Module.finrank ℂ S) := by
    change (g₀ X)ᴴ = g₀ X
    apply (LinearMap.isHermitian_toMatrix_iff b).mpr
    exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr (hherm X)).restrict_invariant
      (fun v _ => hrange X X.property v)
  let g := g₀.codRestrict _ hg₀
  have hginj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    have hmat : LinearMap.toMatrix b.toBasis b.toBasis (f X) = 0 :=
      congrArg Subtype.val hX
    have hf : f X = 0 := (LinearMap.toMatrix b.toBasis b.toBasis).injective
      (hmat.trans (map_zero _).symm)
    apply Subtype.ext
    apply Matrix.toEuclideanLin.injective
    ext v : 1
    simp only [Submodule.coe_zero, map_zero, LinearMap.zero_apply]
    change (X : Matrix (Fin d) (Fin d) ℂ).toEuclideanLin v = 0
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [(Matrix.isSymmetric_toEuclideanLin_iff.mpr (hherm X))]
    have hz := congrArg Subtype.val (LinearMap.congr_fun hf
      ⟨(X : Matrix (Fin d) (Fin d) ℂ).toEuclideanLin v, hrange X X.property v⟩)
    change (X : Matrix (Fin d) (Fin d) ℂ).toEuclideanLin
      ((X : Matrix (Fin d) (Fin d) ℂ).toEuclideanLin v) = 0 at hz
    rw [hz, inner_zero_right]
  refine ⟨?_, ?_⟩
  · exact (LinearMap.finrank_le_finrank_of_injective hginj).trans_eq
      (D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition.hermitian_space_finrank _)
  · have hr : Module.finrank ℂ S ≤ d := by
      simpa using Submodule.finrank_le S
    exact Nat.pow_le_pow_left hr 2

/-- The continuation operator restricted to the fixed original CP-word space. -/
def wordTransfer (K : α → Matrix (Fin d) (Fin d) ℂ) (group : α → J)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (w : J → ℝ) :
    realWordSpace K group ρ →ₗ[ℝ] realWordSpace K group ρ :=
  ((weightedCP K (fun a => w (group a))).restrictScalars ℝ).restrict
    (weightedCP_word_invariant K group ρ w)

/-- Initial coordinates are fixed before any source parameter is chosen. -/
def wordInitial (K : α → Matrix (Fin d) (Fin d) ℂ) (group : α → J)
    (ρ : Matrix (Fin d) (Fin d) ℂ) : realWordSpace K group ρ :=
  ⟨ρ, initial_mem_realWordSpace K group ρ⟩

private theorem wordTransfer_iterate (K : α → Matrix (Fin d) (Fin d) ℂ)
    (group : α → J) (ρ : Matrix (Fin d) (Fin d) ℂ) (w : J → ℝ)
    (X : realWordSpace K group ρ) (n : ℕ) :
    ((wordTransfer K group ρ w)^[n] X : Matrix (Fin d) (Fin d) ℂ) =
      (weightedCP K (fun a => w (group a)))^[n] X := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change weightedCP K (fun a => w (group a))
        ((wordTransfer K group ρ w)^[n] X : Matrix (Fin d) (Fin d) ℂ) = _
      rw [ih]

private theorem word_resolvent_unit (K : α → Matrix (Fin d) (Fin d) ℂ)
    (group : α → J) (ρ : Matrix (Fin d) (Fin d) ℂ) (w : J → ℝ)
    (hs : ∀ X ∈ realWordSpace K group ρ,
      Summable (fun n => (weightedCP K (fun a => w (group a)))^[n] X)) :
    IsUnit (1 - wordTransfer K group ρ w) := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  intro X hX
  have hfix : wordTransfer K group ρ w X = X := by
    change X - wordTransfer K group ρ w X = 0 at hX
    exact (sub_eq_zero.mp hX).symm
  have hpow (n : ℕ) : (wordTransfer K group ρ w)^[n] X = X :=
    Function.IsFixedPt.iterate hfix n
  have hlim := (hs X X.property).tendsto_atTop_zero
  have heq (n : ℕ) : (weightedCP K (fun a => w (group a)))^[n]
      (X : Matrix (Fin d) (Fin d) ℂ) = X := by
    rw [← wordTransfer_iterate, hpow]
  simp only [heq] at hlim
  exact Subtype.ext (tendsto_nhds_unique tendsto_const_nhds hlim)

private theorem potential_mem_wordSpace (K : α → Matrix (Fin d) (Fin d) ℂ)
    (group : α → J) (ρ : Matrix (Fin d) (Fin d) ℂ) (w : J → ℝ) :
    (∑' n, (weightedCP K (fun a => w (group a)))^[n] ρ) ∈ realWordSpace K group ρ := by
  apply tsum_mem (realWordSpace K group ρ).closed_of_finiteDimensional
  intro n
  change (weightedCP K (fun a => w (group a)))^[n]
    (wordInitial K group ρ : Matrix (Fin d) (Fin d) ℂ) ∈ _
  rw [← wordTransfer_iterate K group ρ w (wordInitial K group ρ) n]
  exact Subtype.property _

/-- A fixed real basis, chosen without a source parameter. -/
def wordBasis (K : α → Matrix (Fin d) (Fin d) ℂ) (group : α → J)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :=
  Module.finBasis ℝ (realWordSpace K group ρ)

/-- The real continuation matrix in the fixed basis. -/
def wordMatrix (K : α → Matrix (Fin d) (Fin d) ℂ) (group : α → J)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (w : J → ℝ) :=
  LinearMap.toMatrix (wordBasis K group ρ) (wordBasis K group ρ)
    (wordTransfer K group ρ w)

/-- A real event functional on the word space. -/
def eventFunctional (K : α → Matrix (Fin d) (Fin d) ℂ) (group : α → J)
    (ρ F : Matrix (Fin d) (Fin d) ℂ) : realWordSpace K group ρ →ₗ[ℝ] ℝ :=
  (Complex.reCLM.toLinearMap.comp
    (((Matrix.traceLinearMap (Fin d) ℂ ℂ).comp
      (LinearMap.mulLeft ℂ F)).restrictScalars ℝ)).comp
        (realWordSpace K group ρ).subtype

/-- The event row in the same fixed real basis. -/
def wordRow (K : α → Matrix (Fin d) (Fin d) ℂ) (group : α → J)
    (ρ F : Matrix (Fin d) (Fin d) ℂ) :=
  fun i => eventFunctional K group ρ F (wordBasis K group ρ i)

private theorem row_repr (K : α → Matrix (Fin d) (Fin d) ℂ) (group : α → J)
    (ρ F : Matrix (Fin d) (Fin d) ℂ) (X : realWordSpace K group ρ) :
    wordRow K group ρ F ⬝ᵥ (wordBasis K group ρ).repr X = (F * X).trace.re := by
  have h := congrArg (eventFunctional K group ρ F)
    ((wordBasis K group ρ).sum_repr X)
  change wordRow K group ρ F ⬝ᵥ (wordBasis K group ρ).repr X =
    eventFunctional K group ρ F X
  simpa only [map_sum, map_smul, Finset.mul_sum, smul_eq_mul, mul_comm,
    wordRow, dotProduct] using h

/-- The inverse in the fixed real space is the physical Neumann potential,
not an inverse on unreachable ambient directions. -/
private theorem real_word_response_coordinates {Θ : Type*} [TopologicalSpace Θ]
    (K E : α → Matrix (Fin d) (Fin d) ℂ) (hE : ∀ a, (E a).PosSemidef)
    (group : α → J) (w : Θ → J → ℝ) (U : Set Θ)
    (hpos : ∀ θ ∈ U, ∀ j, 0 < w θ j)
    (hcont : ∀ j, ContinuousOn (fun θ => w θ j) U)
    (hcomplete : ∀ θ ∈ U, weightedDual K (fun a => w θ (group a)) 1 +
      ∑ a, (w θ (group a) : ℂ) • E a = 1)
    (θ₀ : Θ) (hθ₀ : θ₀ ∈ U) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef)
    (hterm : Tendsto (fun n => ((weightedCP K (fun a => w θ₀ (group a)))^[n] ρ).trace)
      atTop (𝓝 0)) :
    (Module.finrank ℝ (realWordSpace K group ρ) ≤
      (Module.finrank ℂ (reachableSpace K ρ)) ^ 2 ∧
      (Module.finrank ℂ (reachableSpace K ρ)) ^ 2 ≤ d ^ 2) ∧
    ∀ θ ∈ U,
      (1 - wordMatrix K group ρ (w θ)).det ≠ 0 ∧
      ∀ (F : Matrix (Fin d) (Fin d) ℂ), 0 ≤ F →
        F ≤ 1 - weightedDual K (fun a => w θ (group a)) 1 →
        Summable (fun n => (F * (weightedCP K (fun a => w θ (group a)))^[n] ρ).trace.re) ∧
        (∑' n, (F * (weightedCP K (fun a => w θ (group a)))^[n] ρ).trace.re) =
          wordRow K group ρ F ⬝ᵥ ((1 - wordMatrix K group ρ (w θ))⁻¹ *ᵥ
            (wordBasis K group ρ).repr (wordInitial K group ρ)) ∧
        0 ≤ (∑' n, (F * (weightedCP K (fun a => w θ (group a)))^[n] ρ).trace.re) ∧
        (∑' n, (F * (weightedCP K (fun a => w θ (group a)))^[n] ρ).trace.re) ≤ ρ.trace.re := by
  obtain ⟨_, _, habs, hspan, _⟩ := positive_branch_compact_absorption K E hE
    (fun θ a => w θ (group a)) U (fun θ hθ a => hpos θ hθ (group a))
    (fun a => hcont (group a)) hcomplete θ₀ hθ₀ ρ hρ hterm
  refine ⟨realWordSpace_dimension K group ρ hρ, ?_⟩
  intro θ hθ
  have hs := fun X hX => (hspan θ hθ X
    (realWordSpace_supported_span K group ρ hρ hX)).1
  have hu := word_resolvent_unit K group ρ (w θ) hs
  have hmat : IsUnit (1 - wordMatrix K group ρ (w θ)) := by
    simpa only [wordMatrix, map_sub, LinearMap.toMatrix_one] using
      (LinearMap.isUnit_toMatrix_iff (wordBasis K group ρ)).mpr hu
  have hdet : (1 - wordMatrix K group ρ (w θ)).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hmat)
  refine ⟨hdet, ?_⟩
  intro F hF hFle
  obtain ⟨_, hsum, hpoisson, hresp⟩ := habs θ hθ ρ hρ (initial_support K ρ)
  obtain ⟨hfsum, hfeq, hlo, hhi, _⟩ := hresp F hF hFle
  let R : realWordSpace K group ρ :=
    ⟨∑' n, (weightedCP K (fun a => w θ (group a)))^[n] ρ,
      potential_mem_wordSpace K group ρ (w θ)⟩
  have hsolve : (1 - wordTransfer K group ρ (w θ)) R = wordInitial K group ρ := by
    exact Subtype.ext hpoisson
  have hcoords : (1 - wordMatrix K group ρ (w θ)) *ᵥ (wordBasis K group ρ).repr R =
      (wordBasis K group ρ).repr (wordInitial K group ρ) := by
    have hm := LinearMap.toMatrix_mulVec_repr (wordBasis K group ρ)
      (wordBasis K group ρ) (1 - wordTransfer K group ρ (w θ)) R
    simpa only [map_sub, LinearMap.toMatrix_one, wordMatrix, hsolve] using hm
  have hinv : (1 - wordMatrix K group ρ (w θ))⁻¹ *ᵥ
      (wordBasis K group ρ).repr (wordInitial K group ρ) =
        (wordBasis K group ρ).repr R := by
    rw [← hcoords, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  have hreal := Complex.reCLM.map_tsum hfsum
  have heq : (∑' n, (F * (weightedCP K (fun a => w θ (group a)))^[n] ρ).trace.re) =
      (F * (R : Matrix (Fin d) (Fin d) ℂ)).trace.re := by
    exact (show (∑' n, (F * (weightedCP K (fun a => w θ (group a)))^[n] ρ).trace.re) =
      (∑' n, (F * (weightedCP K (fun a => w θ (group a)))^[n] ρ).trace).re from
        hreal.symm).trans (congrArg Complex.re hfeq)
  exact ⟨Complex.reCLM.summable hfsum, by rw [hinv, row_repr, heq],
    by rw [heq]; exact hlo, by rw [heq]; exact hhi⟩

/-- The event effect uses the same source weights as the continuation. -/
def weightedEventEffect (F : α → Matrix (Fin d) (Fin d) ℂ) (group : α → J)
    (w : J → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ a, (w (group a) : ℂ) • F a

/-- Initial return mass plus the unconditioned sum of all finite event returns. -/
def actualEventResponse (K : α → Matrix (Fin d) (Fin d) ℂ) (group : α → J)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (F : α → Matrix (Fin d) (Fin d) ℂ)
    (γ : ℝ) (w : J → ℝ) : ℝ :=
  γ + ∑' n, (weightedEventEffect F group w *
    (weightedCP K (fun a => w (group a)))^[n] ρ).trace.re

private theorem wordMatrix_affine (K : α → Matrix (Fin d) (Fin d) ℂ)
    (group : α → J) (ρ : Matrix (Fin d) (Fin d) ℂ) (w₀ w₁ : J → ℝ) (t : ℝ) :
    wordMatrix K group ρ (w₀ + t • w₁) =
      wordMatrix K group ρ w₀ + t • wordMatrix K group ρ w₁ := by
  have hh : (weightedCP K (fun a => (w₀ + t • w₁) (group a))).restrictScalars ℝ =
      (weightedCP K (fun a => w₀ (group a))).restrictScalars ℝ +
        t • (weightedCP K (fun a => w₁ (group a))).restrictScalars ℝ := by
    rw [grouped_weightedCP K group (w₀ + t • w₁),
      grouped_weightedCP K group w₀, grouped_weightedCP K group w₁]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  have ht : wordTransfer K group ρ (w₀ + t • w₁) =
      wordTransfer K group ρ w₀ + t • wordTransfer K group ρ w₁ := by
    ext X : 1
    apply Subtype.ext
    exact LinearMap.congr_fun hh X
  simp only [wordMatrix, ht, map_add, map_smul]

private theorem weightedEventEffect_affine (F : α → Matrix (Fin d) (Fin d) ℂ)
    (group : α → J) (w₀ w₁ : J → ℝ) (t : ℝ) :
    weightedEventEffect F group (w₀ + t • w₁) =
      weightedEventEffect F group w₀ + t • weightedEventEffect F group w₁ := by
  unfold weightedEventEffect
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_add,
    Complex.ofReal_mul, add_smul, mul_smul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rfl

private theorem wordRow_affine (K : α → Matrix (Fin d) (Fin d) ℂ)
    (group : α → J) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (F : α → Matrix (Fin d) (Fin d) ℂ) (w₀ w₁ : J → ℝ) (t : ℝ) :
    wordRow K group ρ (weightedEventEffect F group (w₀ + t • w₁)) =
      wordRow K group ρ (weightedEventEffect F group w₀) +
        t • wordRow K group ρ (weightedEventEffect F group w₁) := by
  rw [weightedEventEffect_affine]
  ext i
  simp [wordRow, eventFunctional, Matrix.add_mul, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.smul_re]

private theorem eventEffect_bounds (K E : α → Matrix (Fin d) (Fin d) ℂ)
    (group : α → J) (F : α → Matrix (Fin d) (Fin d) ℂ)
    (hF : ∀ a, 0 ≤ F a) (hFE : ∀ a, F a ≤ E a) (w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j)
    (hcomplete : weightedDual K (fun a => w (group a)) 1 +
      ∑ a, (w (group a) : ℂ) • E a = 1) :
    0 ≤ weightedEventEffect F group w ∧ weightedEventEffect F group w ≤
      1 - weightedDual K (fun a => w (group a)) 1 := by
  have he : 1 - weightedDual K (fun a => w (group a)) 1 =
      ∑ a, (w (group a) : ℂ) • E a := by
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hcomplete.symm)
  refine ⟨Finset.sum_nonneg (fun a _ => smul_nonneg
    (Complex.zero_le_real.mpr (hw (group a))) (hF a)), ?_⟩
  rw [he]
  exact Finset.sum_le_sum fun a _ =>
    smul_le_smul_of_nonneg_left (hFE a) (Complex.zero_le_real.mpr (hw (group a)))

/-- The actual response on any affine source line has a real denominator with
no zero on its physical internal segment, and degrees bounded by the same
world independent CP-word dimension. Initial return mass is included. -/
theorem affine_source_real_rational_response {Θ : Type*} [TopologicalSpace Θ]
    (K E : α → Matrix (Fin d) (Fin d) ℂ) (hE : ∀ a, (E a).PosSemidef)
    (group : α → J) (w : Θ → J → ℝ) (U : Set Θ)
    (hpos : ∀ θ ∈ U, ∀ j, 0 < w θ j)
    (hcont : ∀ j, ContinuousOn (fun θ => w θ j) U)
    (hcomplete : ∀ θ ∈ U, weightedDual K (fun a => w θ (group a)) 1 +
      ∑ a, (w θ (group a) : ℂ) • E a = 1)
    (θ₀ : Θ) (hθ₀ : θ₀ ∈ U) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef)
    (hterm : Tendsto (fun n => ((weightedCP K (fun a => w θ₀ (group a)))^[n] ρ).trace)
      atTop (𝓝 0))
    (F : α → Matrix (Fin d) (Fin d) ℂ) (hF : ∀ a, 0 ≤ F a)
    (hFE : ∀ a, F a ≤ E a) (γ : ℝ) (hγ : 0 ≤ γ) (hmass : γ + ρ.trace.re ≤ 1)
    (line : ℝ → Θ) (w₀ w₁ : J → ℝ) (I : Set ℝ) (hI : IsOpen I)
    (hline : ∀ t ∈ I, line t ∈ U)
    (haffine : ∀ t ∈ I, w (line t) = w₀ + t • w₁) :
    (Module.finrank ℝ (realWordSpace K group ρ) ≤
      (Module.finrank ℂ (reachableSpace K ρ)) ^ 2 ∧
      (Module.finrank ℂ (reachableSpace K ρ)) ^ 2 ≤ d ^ 2) ∧
    ∃ P Q : ℝ[X],
      P.natDegree ≤ Module.finrank ℝ (realWordSpace K group ρ) ∧
      Q.natDegree ≤ Module.finrank ℝ (realWordSpace K group ρ) ∧
      (∀ t ∈ I, Q.eval t ≠ 0 ∧
        actualEventResponse K group ρ F γ (w (line t)) =
          γ + wordRow K group ρ (weightedEventEffect F group (w (line t))) ⬝ᵥ
            ((1 - wordMatrix K group ρ (w (line t)))⁻¹ *ᵥ
              (wordBasis K group ρ).repr (wordInitial K group ρ)) ∧
        actualEventResponse K group ρ F γ (w (line t)) = P.eval t / Q.eval t ∧
        0 ≤ actualEventResponse K group ρ F γ (w (line t)) ∧
        actualEventResponse K group ρ F γ (w (line t)) ≤ 1) ∧
      AnalyticOnNhd ℝ (fun t => actualEventResponse K group ρ F γ (w (line t))) I ∧
      (Module.finrank ℝ (realWordSpace K group ρ) = 0 →
        ∀ v : J → ℝ, actualEventResponse K group ρ F γ v = γ) := by
  obtain ⟨hdim, hcoords⟩ := real_word_response_coordinates K E hE group w U
    hpos hcont hcomplete θ₀ hθ₀ ρ hρ hterm
  let M₀ := wordMatrix K group ρ w₀
  let M₁ := wordMatrix K group ρ w₁
  let ell₀ := wordRow K group ρ (weightedEventEffect F group w₀)
  let ell₁ := wordRow K group ρ (weightedEventEffect F group w₁)
  have hmatrix (t : ℝ) (ht : t ∈ I) :
      1 - wordMatrix K group ρ (w (line t)) = t • (-M₁) + (1 - M₀) := by
    rw [haffine t ht, wordMatrix_affine]
    dsimp [M₀, M₁]
    module
  have hrow (t : ℝ) (ht : t ∈ I) :
      wordRow K group ρ (weightedEventEffect F group (w (line t))) = ell₀ + t • ell₁ := by
    rw [haffine t ht, wordRow_affine]
  obtain ⟨P, Q, hP, hQ, hrat, hanalytic⟩ :=
    D5.S3.Quantum.Measurement.AffineMatrixResponse.affine_matrix_rational_response
      (-M₁) (1 - M₀) ((wordBasis K group ρ).repr (wordInitial K group ρ))
      ell₀ ell₁ γ I (fun t ht => hmatrix t ht ▸ (hcoords (line t) (hline t ht)).1)
  have hactual (t : ℝ) (ht : t ∈ I) :
      actualEventResponse K group ρ F γ (w (line t)) =
        γ + wordRow K group ρ (weightedEventEffect F group (w (line t))) ⬝ᵥ
          ((1 - wordMatrix K group ρ (w (line t)))⁻¹ *ᵥ
            (wordBasis K group ρ).repr (wordInitial K group ρ)) ∧
      actualEventResponse K group ρ F γ (w (line t)) = P.eval t / Q.eval t ∧
      0 ≤ actualEventResponse K group ρ F γ (w (line t)) ∧
      actualEventResponse K group ρ F γ (w (line t)) ≤ 1 := by
    have hb := eventEffect_bounds K E group F hF hFE (w (line t))
      (fun j => (hpos _ (hline t ht) j).le) (hcomplete _ (hline t ht))
    obtain ⟨_, heq, hlo, hhi⟩ := (hcoords (line t) (hline t ht)).2
      (weightedEventEffect F group (w (line t))) hb.1 hb.2
    have he : actualEventResponse K group ρ F γ (w (line t)) =
        γ + wordRow K group ρ (weightedEventEffect F group (w (line t))) ⬝ᵥ
          ((1 - wordMatrix K group ρ (w (line t)))⁻¹ *ᵥ
            (wordBasis K group ρ).repr (wordInitial K group ρ)) := by
      exact congrArg (γ + ·) heq
    refine ⟨he, ?_, add_nonneg hγ hlo, ?_⟩
    · rw [he, hmatrix t ht, hrow t ht]
      exact (hrat t ht).2
    · dsimp [actualEventResponse]
      linarith
  refine ⟨hdim, P, Q, by simpa using hP, by simpa using hQ,
    (fun t ht => ⟨(hrat t ht).1, hactual t ht⟩), ?_, ?_⟩
  · intro t ht
    apply (hanalytic t ht).congr
    filter_upwards [hI.mem_nhds ht] with s hs
    exact (hactual s hs).2.1.symm
  · intro hz v
    haveI : Subsingleton (realWordSpace K group ρ) := Module.finrank_zero_iff.mp hz
    have hzero : ρ = 0 := congrArg Subtype.val
      (Subsingleton.elim (wordInitial K group ρ) 0)
    simp only [actualEventResponse, hzero, ← Module.End.pow_apply, map_zero,
      Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re, tsum_zero, add_zero]

#print axioms affine_source_real_rational_response
end D5.S3.Quantum.Measurement.PositiveBranchReachableResponse
