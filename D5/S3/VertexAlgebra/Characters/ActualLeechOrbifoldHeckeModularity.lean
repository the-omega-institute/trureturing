/- GID: D5/S3/VertexAlgebra/Characters/ActualLeechOrbifoldHeckeModularity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/ActualLeechOrbifoldHeckeModularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Level-one invariance and upper-half-plane holomorphy of the native Hecke sum. -/

import D5.S3.Arith.ModularForms.HeckeCosetTriangularRepresentatives
import D5.S3.VertexAlgebra.Characters.ActualLeechOrbifoldHeckeExpansion
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic

/-! The native unnormalized Hecke sum is the sum over the triangular representatives
of positive determinant. The right permutation of those representatives and the
weight-zero invariance of the native character give level-one invariance. -/

set_option autoImplicit false

noncomputable section

open Matrix UpperHalfPlane ModularForm
open scoped BigOperators Manifold Matrix MatrixGroups ModularForm Topology

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldHeckeModularity

open D5.S3.Arith.ModularForms.HeckeCosetTriangularRepresentatives
open ActualLeechOrbifoldTraceSeries (character)
open ActualLeechOrbifoldMoonshineCharacter (character_eq_j_sub_744)
open ActualLeechOrbifoldHeckeExpansion
  (heckeSum triangularSum triangularPoint coe_triangularPoint
    heckeCoeff heckeCoeff_zero heckeSum_hasSum summable_norm_heckeCoeff)

local notation "Mat₂" => Matrix (Fin 2) (Fin 2) ℤ
local notation "Δ" => ModularForm.discriminant

private theorem character_smul (G : SL(2, ℤ)) (τ : ℍ) :
    character (G • τ) = character τ := by
  have hG : (G : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨G, rfl⟩
  have hE := SlashInvariantForm.slash_action_eqn'' E₄ hG τ
  have hΔ := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hG τ
  change E₄ (G • τ) = _ at hE
  change Δ (G • τ) = denom (G : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * Δ τ at hΔ
  rw [character_eq_j_sub_744, character_eq_j_sub_744, hE, hΔ]
  have hden := denom_ne_zero (G : GL (Fin 2) ℝ) τ
  simp only [show (4 : ℤ) = (4 : ℕ) by rfl, show (12 : ℤ) = (12 : ℕ) by rfl,
    zpow_natCast, mul_pow, ← pow_mul]
  rw [show (4 * 3 : ℕ) = 12 by rfl,
    mul_div_mul_left _ _ (pow_ne_zero 12 hden)]

private theorem character_mdifferentiable : MDiff character := by
  have hE : MDiff (E₄ : ℍ → ℂ) := ModularFormClass.holo E₄
  have hΔ : MDiff Δ := ModularFormClass.holo CuspForm.discriminant
  rw [show character = fun τ : ℍ => E₄ τ ^ (3 : ℕ) / Δ τ - 744 from
    funext character_eq_j_sub_744]
  exact ((hE.pow 3).div hΔ discriminant_ne_zero).sub mdifferentiable_const

private theorem cast_det_pos (A : Mat₂) (hA : 0 < A.det) :
    0 < ((Int.castRingHom ℝ).mapMatrix A).det := by
  rw [← RingHom.map_det]
  change (0 : ℝ) < (A.det : ℝ)
  exact_mod_cast hA

/-- The entrywise real cast of a positive-determinant integral matrix as a unit. -/
private def realGL (A : Mat₂) (hA : 0 < A.det) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero ((Int.castRingHom ℝ).mapMatrix A) (cast_det_pos A hA).ne'

private theorem realGL_det_pos (A : Mat₂) (hA : 0 < A.det) :
    0 < (realGL A hA).det.val := by
  rw [GeneralLinearGroup.val_det_apply]
  exact cast_det_pos A hA

private theorem det_mul_pos {A B : Mat₂} (hA : 0 < A.det) (hB : 0 < B.det) :
    0 < (A * B).det := by
  rw [Matrix.det_mul]
  exact mul_pos hA hB

private theorem realGL_mul (A B : Mat₂) (hA : 0 < A.det) (hB : 0 < B.det) :
    realGL (A * B) (det_mul_pos hA hB) = realGL A hA * realGL B hB := by
  apply Units.ext
  exact map_mul (Int.castRingHom ℝ).mapMatrix A B

private theorem sl_det_pos (G : SL(2, ℤ)) : 0 < (G : Mat₂).det := by
  rw [G.det_coe]
  exact zero_lt_one

private theorem realGL_sl (G : SL(2, ℤ)) :
    realGL (G : Mat₂) (sl_det_pos G) = (G : GL (Fin 2) ℝ) := by
  apply Units.ext
  ext i j
  simp [realGL]

private theorem index_det_pos {N : ℕ} (hN : 0 < N) (r : Index (N : ℤ)) :
    0 < r.matrix.det := by
  rw [r.det_matrix]
  exact_mod_cast hN

/-- The action of a triangular representative through the real Möbius action. -/
def indexPoint {N : ℕ} (hN : 0 < N) (r : Index (N : ℤ)) (τ : ℍ) : ℍ :=
  realGL r.matrix (index_det_pos hN r) • τ

/-- In triangular coordinates the real Möbius action is the native affine map. -/
theorem indexPoint_eq_triangularPoint {N : ℕ} (hN : 0 < N) (r : Index (N : ℤ)) (τ : ℍ) :
    indexPoint hN r τ = triangularPoint r.a.toNat r.d.toNat
      (by have := r.a_pos; omega) (by have := r.d_pos; omega) r.b.toNat τ := by
  apply UpperHalfPlane.ext
  rw [indexPoint, coe_smul_of_det_pos (realGL_det_pos _ _), coe_triangularPoint]
  simp [num, denom, realGL, Index.matrix, ← Int.cast_natCast (R := ℂ),
    Int.toNat_of_nonneg r.a_pos.le, Int.toNat_of_nonneg r.d_pos.le,
    Int.toNat_of_nonneg r.b_nonneg]

private theorem divisor_mul {N : ℕ} (a : {a // a ∈ N.divisors}) :
    a.val * (N / a.val) = N :=
  Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors a.property)

private theorem index_toNat_mul {N : ℕ} (r : Index (N : ℤ)) :
    r.a.toNat * r.d.toNat = N := by
  have h := r.ad
  exact_mod_cast (show (↑r.a.toNat : ℤ) * ↑r.d.toNat = ↑N by
    rwa [Int.toNat_of_nonneg r.a_pos.le, Int.toNat_of_nonneg r.d_pos.le])

private theorem index_toNat_div {N : ℕ} (r : Index (N : ℤ)) :
    N / r.a.toNat = r.d.toNat := by
  have ha : 0 < r.a.toNat := by have := r.a_pos; omega
  exact (congrArg (· / r.a.toNat) (index_toNat_mul r).symm).trans
    (Nat.mul_div_cancel_left _ ha)

private def divisorIndexEquiv {N : ℕ} (hN : 0 < N) :
    (Σ a : {a // a ∈ N.divisors}, Fin (N / a.val)) ≃ Index (N : ℤ) where
  toFun x :=
    { a := x.1.val
      b := x.2.val
      d := (↑(N / x.1.val) : ℤ)
      a_pos := by exact_mod_cast Nat.pos_of_mem_divisors x.1.property
      b_nonneg := Int.natCast_nonneg _
      d_pos := by exact_mod_cast Nat.zero_lt_of_lt x.2.isLt
      b_lt_d := by exact_mod_cast x.2.isLt
      ad := by exact_mod_cast divisor_mul x.1 }
  invFun r :=
    ⟨⟨r.a.toNat, Nat.mem_divisors.mpr ⟨⟨r.d.toNat, (index_toNat_mul r).symm⟩, hN.ne'⟩⟩,
      ⟨r.b.toNat, by
        change r.b.toNat < N / r.a.toNat
        rw [index_toNat_div r]
        exact (Int.toNat_lt_toNat r.d_pos).mpr r.b_lt_d⟩⟩
  left_inv := by rintro ⟨a, b⟩; rfl
  right_inv r := by
    apply Index.ext
    · exact Int.toNat_of_nonneg r.a_pos.le
    · exact Int.toNat_of_nonneg r.b_nonneg
    · change (↑(N / r.a.toNat) : ℤ) = r.d
      rw [index_toNat_div r, Int.toNat_of_nonneg r.d_pos.le]

/-- The native divisor/translate sum is the sum of the native character over the
supplied triangular representatives of determinant N. -/
theorem heckeSum_eq_sum_index {N : ℕ} (hN : 0 < N) (τ : ℍ) :
    heckeSum N τ = ∑ r : Index (N : ℤ), character (indexPoint hN r τ) := by
  classical
  let term (a : {a // a ∈ N.divisors}) (b : ℕ) :=
    character (triangularPoint a.val (N / a.val) (Nat.pos_of_mem_divisors a.property)
      (Nat.div_pos (Nat.le_of_dvd hN (Nat.dvd_of_mem_divisors a.property))
        (Nat.pos_of_mem_divisors a.property)) b τ)
  calc
    heckeSum N τ = ∑ a : {a // a ∈ N.divisors}, ∑ b : Fin (N / a.val), term a b := by
      unfold heckeSum triangularSum
      apply Finset.sum_congr rfl
      intro a _
      exact (Fin.sum_univ_eq_sum_range (term a) _).symm
    _ = ∑ x : Σ a : {a // a ∈ N.divisors}, Fin (N / a.val), term x.1 x.2 :=
      (Fintype.sum_sigma' (fun a (b : Fin (N / a.val)) => term a b)).symm
    _ = _ := by
      rw [← (divisorIndexEquiv hN).sum_comp]
      apply Finset.sum_congr rfl
      intro x _
      rw [indexPoint_eq_triangularPoint]
      rfl

private theorem character_sum_right_mul {N : ℕ} (hN : 0 < N) (G : SL(2, ℤ)) (τ : ℍ) :
    (∑ r : Index (N : ℤ), character (indexPoint hN r (G • τ))) =
      ∑ r : Index (N : ℤ), character (indexPoint hN r τ) := by
  let f (A : Mat₂) : ℂ := if hA : 0 < A.det then character (realGL A hA • τ) else 0
  have hf (L : SL(2, ℤ)) (A : Mat₂) (hA : A.det = (N : ℤ)) :
      f ((L : Mat₂) * A) = f A := by
    have hpos : 0 < A.det := hA ▸ (by exact_mod_cast hN : (0 : ℤ) < N)
    simp only [f, dite_eq_left hpos, dite_eq_left (det_mul_pos (sl_det_pos L) hpos)]
    rw [realGL_mul (L : Mat₂) A (sl_det_pos L) hpos, realGL_sl, mul_smul]
    exact character_smul L _
  have hsum := sum_right_mul_eq (show (0 : ℤ) < N by exact_mod_cast hN) G f hf
  change (∑ r : Index (N : ℤ),
      character (indexPoint hN r ((G : GL (Fin 2) ℝ) • τ))) = _
  simpa only [indexPoint, f, dite_eq_left (index_det_pos hN _),
    dite_eq_left (det_mul_pos (index_det_pos hN _) (sl_det_pos G)),
    realGL_mul _ _ (index_det_pos hN _) (sl_det_pos G), realGL_sl, mul_smul] using hsum

/-- Weight-zero invariance of the actual unnormalized transform under every
element of SL(2, ℤ). -/
theorem heckeSum_smul {N : ℕ} (hN : 0 < N) (G : SL(2, ℤ)) (τ : ℍ) :
    heckeSum N (G • τ) = heckeSum N τ := by
  rw [heckeSum_eq_sum_index hN, heckeSum_eq_sum_index hN]
  exact character_sum_right_mul hN G τ

/-- The transform is holomorphic throughout the upper half-plane. -/
theorem heckeSum_mdifferentiable {N : ℕ} (hN : 0 < N) : MDiff (heckeSum N) := by
  have hsum : heckeSum N = ∑ r : Index (N : ℤ), fun τ => character (indexPoint hN r τ) := by
    funext τ
    rw [Finset.sum_apply]
    exact heckeSum_eq_sum_index hN τ
  rw [hsum]
  exact MDifferentiable.sum fun r _ => character_mdifferentiable.comp
    (mdifferentiable_smul (realGL_det_pos r.matrix (index_det_pos hN r)))

/-- The native transform bundled with its level-one weight-zero slash invariance. -/
def heckeSlashInvariantForm {N : ℕ} (hN : 0 < N) : SlashInvariantForm 𝒮ℒ 0 where
  toFun := heckeSum N
  slash_action_eq' G hG := by
    rcases hG with ⟨G, rfl⟩
    funext τ
    change (heckeSum N ∣[(0 : ℤ)] G) τ = heckeSum N τ
    simpa only [SL_slash_apply, neg_zero, zpow_zero, mul_one] using heckeSum_smul hN G τ

local notation "𝕢" => Function.Periodic.qParam 1

/-- After removing its polar term, the native transform tends to zero at the cusp. -/
theorem heckeSum_sub_pole_isZeroAtImInfty {N : ℕ} (hN : 0 < N) :
    IsZeroAtImInfty (fun τ => heckeSum N τ - (𝕢 τ ^ N)⁻¹) := by
  let p := FormalMultilinearSeries.ofScalars ℂ (heckeCoeff N)
  have hs := summable_norm_heckeCoeff hN (q := (1 / 2 : ℝ)) (by norm_num)
  have hr : (↑(1 / 2 : NNReal) : ENNReal) ≤ p.radius := by
    apply p.le_radius_of_summable_norm
    apply (summable_nat_add_iff 1).mp
    simpa only [p, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hs
  have hp : 0 < p.radius := lt_of_lt_of_le (by norm_num) hr
  have hlimit := (p.hasFPowerSeriesOnBall hp).hasFPowerSeriesAt.continuousAt.tendsto.comp
    (qParam_tendsto_atImInfty (h := 1) one_pos)
  have hzero : p.sum 0 = 0 := by
    change FormalMultilinearSeries.ofScalarsSum (heckeCoeff N) (0 : ℂ) = 0
    simp
  rw [hzero] at hlimit
  change Filter.Tendsto _ atImInfty (𝓝 0)
  refine hlimit.congr fun τ => ?_
  change FormalMultilinearSeries.ofScalarsSum (heckeCoeff N) (𝕢 τ) = _
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  apply HasSum.tsum_eq
  simpa only [Finset.sum_range_one, heckeCoeff_zero, zero_mul, add_zero, smul_eq_mul]
    using (hasSum_nat_add_iff (f := fun n : ℕ => heckeCoeff N n * 𝕢 τ ^ n) 1).mp
      (heckeSum_hasSum hN τ)

/-- The native transform is the unique holomorphic weight-zero level-one function
whose Laurent expansion at infinity has principal part q⁻ᴺ and zero constant term. -/
theorem eq_heckeSum_of_sub_pole_isZeroAtImInfty {N : ℕ} (hN : 0 < N)
    (f : SlashInvariantForm 𝒮ℒ 0) (hf : MDiff (f : ℍ → ℂ))
    (hc : IsZeroAtImInfty (fun τ => f τ - (𝕢 τ ^ N)⁻¹)) :
    (f : ℍ → ℂ) = heckeSum N := by
  have hd : IsZeroAtImInfty (fun τ => f τ - heckeSum N τ) := by
    change Filter.Tendsto _ atImInfty (𝓝 0)
    have h := Filter.Tendsto.sub hc (heckeSum_sub_pole_isZeroAtImInfty hN)
    simpa only [sub_sub_sub_cancel_right, sub_zero] using h
  let g : ModularForm 𝒮ℒ 0 :=
    { toSlashInvariantForm := f - heckeSlashInvariantForm hN
      holo' := hf.sub (heckeSum_mdifferentiable hN)
      bdd_at_cusps' := fun hcusp => (OnePoint.isBoundedAt_iff_forall_SL2Z hcusp).mpr
        fun G _ => by
          rw [SL_slash]
          change IsBoundedAtImInfty
            (((f - heckeSlashInvariantForm hN : SlashInvariantForm 𝒮ℒ 0) : ℍ → ℂ)
              ∣[(0 : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ G)
          have hG : Matrix.SpecialLinearGroup.mapGL ℝ G ∈ 𝒮ℒ := ⟨G, rfl⟩
          rw [SlashInvariantForm.slash_action_eqn (f - heckeSlashInvariantForm hN) _ hG]
          exact hd.isBoundedAtImInfty }
  obtain ⟨c, hconst⟩ := ModularFormClass.levelOne_weight_zero_const g
  change (fun τ => f τ - heckeSum N τ) = Function.const ℍ c at hconst
  rw [hconst] at hd
  have hc0 : c = 0 := tendsto_const_nhds_iff.mp hd
  funext τ
  exact sub_eq_zero.mp (by simpa [hc0] using congrFun hconst τ)

end D5.S3.VertexAlgebra.ActualLeechOrbifoldHeckeModularity
