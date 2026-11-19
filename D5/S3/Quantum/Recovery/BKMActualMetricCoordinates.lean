/- GID: D5/S3/Quantum/Recovery/BKMActualMetricCoordinates
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/BKMActualMetricCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Euclidean coordinates for the faithful finite BKM metric. -/

import D5.S3.Quantum.Recovery.BKMRelativeDensity
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-! # Euclidean coordinates for the faithful finite BKM metric -/

noncomputable section

open Matrix ContinuousLinearMap WithLp
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Kronecker InnerProductSpace
open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.Recovery.BKMRelativeDensity

namespace D5.S3.Quantum.Recovery.BKMActualMetricCoordinates

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "M" => Matrix n n ℂ
local notation "E" => EuclideanSpace ℂ (n × n)

private theorem omegaCoefficient_one : omegaCoefficient (1 : M) = 1 := by
  have hp (t : ℝ) : mpow (1 : M) t = 1 := by
    rw [mpow, ← CFC.rpow_eq_cfc_real (zero_le_one : (0 : M) ≤ 1)]
    exact CFC.one_rpow
  simp [omegaCoefficient, powerCoefficient, hp]

/-- The actual BKM coefficient is faithful on the entire complex matrix space. -/
theorem omegaCoefficient_posDef (c : M) (hc : c.PosDef) :
    (omegaCoefficient c).PosDef := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
    let := hn
    rw [Subsingleton.elim (omegaCoefficient c) 1]
    exact Matrix.PosDef.one
  | inr hn =>
    let := hn
    have hs := hc.isStrictlyPositive
    obtain ⟨r, hr, hrle⟩ := (CFC.exists_pos_algebraMap_le_iff c hs.isSelfAdjoint).2
      (fun x hx => hs.spectrum_pos hx)
    have hcu := IsSelfAdjoint.le_algebraMap_norm_self c hs.isSelfAdjoint
    have hr' : r • (1 : M) ≤ c := by
      simpa only [Algebra.algebraMap_eq_smul_one] using hrle
    have hu' : c ≤ max r ‖c‖ • (1 : M) := by
      have hdiff : 0 ≤ (max r ‖c‖ - ‖c‖) • (1 : M) :=
        (Matrix.PosSemidef.one.smul (sub_nonneg.mpr (le_max_right r ‖c‖))).nonneg
      rw [sub_smul, sub_nonneg] at hdiff
      rw [Algebra.algebraMap_eq_smul_one] at hcu
      exact hcu.trans hdiff
    have hlo := (omegaCoefficient_relative_bounds hc (Matrix.PosDef.one : (1 : M).PosDef)
      hr (le_max_left r ‖c‖) hr' hu').1
    rw [omegaCoefficient_one] at hlo
    have hrpos : IsStrictlyPositive (r • (1 : Matrix (n × n) (n × n) ℂ)) := by
      exact ⟨(Matrix.PosSemidef.one.smul hr.le).nonneg, by
        rw [← Algebra.algebraMap_eq_smul_one]
        exact (isUnit_iff_ne_zero.mpr hr.ne').map (algebraMap ℝ _)⟩
    exact (hrpos.of_le hlo).posDef

/-- The relative coefficient in Euclidean coordinates for the reference density. -/
private def relativeMatrix (a b : M) : Matrix (n × n) (n × n) ℂ :=
  omegaCoefficient b ^ (-(1 / 2) : ℝ) * omegaCoefficient a *
    omegaCoefficient b ^ (-(1 / 2) : ℝ)

local notation "liftMatrix" => Matrix.toEuclideanCLM (n := n × n) (𝕜 := ℂ)

def relativeOperator (a b : M) : E →L[ℂ] E :=
  liftMatrix (relativeMatrix a b)

theorem relativeOperator_selfAdjoint (a b : M) (ha : a.PosDef) :
    IsSelfAdjoint (relativeOperator a b) := by
  have hm : 0 ≤ relativeMatrix a b :=
    conjugate_nonneg_of_nonneg (omegaCoefficient_posDef a ha).posSemidef.nonneg CFC.rpow_nonneg
  exact (IsSelfAdjoint.of_nonneg hm).map liftMatrix

theorem relativeOperator_bounds {a b : M} (ha : a.PosDef) (hb : b.PosDef)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hlo : l • b ≤ a) (hhi : a ≤ u • b) :
    (l : ℂ) • (1 : E →L[ℂ] E) ≤ relativeOperator a b ∧
      relativeOperator a b ≤ (u : ℂ) • (1 : E →L[ℂ] E) := by
  let U := omegaCoefficient b
  let D := U ^ (-(1 / 2) : ℝ)
  have hD : 0 ≤ D := CFC.rpow_nonneg
  have hU := (omegaCoefficient_posDef b hb).isStrictlyPositive
  have hDU : D * U * D = 1 := by
    calc
      D * U * D = D * (U ^ (1 / 2 : ℝ) * U ^ (1 / 2 : ℝ)) * D := by
        rw [← CFC.rpow_add hU.isUnit, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
          CFC.rpow_one _ hU.nonneg]
      _ = (D * U ^ (1 / 2 : ℝ)) * (U ^ (1 / 2 : ℝ) * D) := by simp only [mul_assoc]
      _ = 1 := by
        dsimp [D]
        rw [CFC.rpow_neg_mul_rpow _ hU, CFC.rpow_mul_rpow_neg _ hU, one_mul]
  obtain ⟨hL, hH⟩ := omegaCoefficient_relative_bounds ha hb hl hlu hlo hhi
  have hscale (s : ℝ) : D * (s • U) * D = s • 1 := by
    rw [mul_smul_comm, smul_mul_assoc, hDU]
  have hL' := conjugate_le_conjugate_of_nonneg hL hD
  have hH' := conjugate_le_conjugate_of_nonneg hH hD
  change D * (l • U) * D ≤ relativeMatrix a b at hL'
  change relativeMatrix a b ≤ D * (u • U) * D at hH'
  rw [hscale] at hL' hH'
  have hmap (s : ℝ) :
      liftMatrix (s • (1 : Matrix (n × n) (n × n) ℂ)) =
        (s : ℂ) • (1 : E →L[ℂ] E) := by
    change liftMatrix ((s : ℂ) • _) = _
    rw [map_smul, map_one]
  change _ ≤ liftMatrix (relativeMatrix a b) ∧ liftMatrix (relativeMatrix a b) ≤ _
  rw [← hmap l, ← hmap u]
  exact ⟨map_rel liftMatrix hL', map_rel liftMatrix hH'⟩


private def vectorization : M ≃ₗ[ℂ] E :=
  (LinearEquiv.ofBijective
    { toFun := Matrix.vec
      map_add' := Matrix.vec_add
      map_smul' := Matrix.vec_smul }
    Matrix.vec_bijective).trans (WithLp.linearEquiv 2 ℂ _).symm

private def root (c : M) : Matrix (n × n) (n × n) ℂ :=
  omegaCoefficient c ^ (1 / 2 : ℝ)

private def inverseRoot (c : M) : Matrix (n × n) (n × n) ℂ :=
  omegaCoefficient c ^ (-(1 / 2) : ℝ)

private theorem root_mul_inverseRoot (c : M) (hc : c.PosDef) :
    root c * inverseRoot c = 1 :=
  CFC.rpow_mul_rpow_neg _ (omegaCoefficient_posDef c hc).isStrictlyPositive

private theorem inverseRoot_mul_root (c : M) (hc : c.PosDef) :
    inverseRoot c * root c = 1 :=
  CFC.rpow_neg_mul_rpow _ (omegaCoefficient_posDef c hc).isStrictlyPositive

private def rootEquiv (c : M) (hc : c.PosDef) : E ≃ₗ[ℂ] E :=
  { (liftMatrix (root c)).toLinearMap with
    invFun := liftMatrix (inverseRoot c)
    left_inv := fun x => by
      change (liftMatrix (inverseRoot c) * liftMatrix (root c)) x = x
      rw [← map_mul, inverseRoot_mul_root c hc, map_one, one_apply_eq_self]
    right_inv := fun x => by
      change (liftMatrix (root c) * liftMatrix (inverseRoot c)) x = x
      rw [← map_mul, root_mul_inverseRoot c hc, map_one, one_apply_eq_self] }

/-- The invertible coordinate map sends X to Ω_c^(1/2) vec X. -/
def metricCoordinates (c : M) (hc : c.PosDef) : M ≃L[ℂ] E :=
  (vectorization.trans (rootEquiv c hc)).toContinuousLinearEquiv

/-- The unnormalized observable BKM form. -/
def bkmInner (c X Y : M) : ℂ := (Xᴴ * omega c Y).trace

private theorem inner_coefficient (c : M) (hc : c.PosDef) (X Y : M) :
    ⟪vectorization X, liftMatrix (omegaCoefficient c) (vectorization Y)⟫_ℂ =
      bkmInner c X Y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  change star (vec X) ⬝ᵥ (omegaCoefficient c *ᵥ vec Y) = _
  rw [omegaCoefficient_mulVec c Y hc, Matrix.star_vec_dotProduct_vec]
  rfl

private theorem adjoint_root (b : M) :
    (liftMatrix (root b)).adjoint = liftMatrix (root b) := by
  have hroot : IsSelfAdjoint (root b) := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  exact (hroot.map liftMatrix).star_eq

theorem metricCoordinates_inner (b : M) (hb : b.PosDef) (X Y : M) :
    ⟪metricCoordinates b hb X, metricCoordinates b hb Y⟫_ℂ = bkmInner b X Y := by
  change ⟪liftMatrix (root b) (vectorization X),
    liftMatrix (root b) (vectorization Y)⟫_ℂ = _
  rw [← adjoint_inner_right, adjoint_root]
  change ⟪vectorization X, (liftMatrix (root b) * liftMatrix (root b)) (vectorization Y)⟫_ℂ = _
  rw [← map_mul]
  have hs := (omegaCoefficient_posDef b hb).isStrictlyPositive
  have hsq : root b * root b = omegaCoefficient b := by
    unfold root
    rw [← CFC.rpow_add hs.isUnit, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
      CFC.rpow_one _ hs.nonneg]
  rw [hsq]
  exact inner_coefficient b hb X Y

theorem relativeOperator_inner (a b : M) (ha : a.PosDef) (hb : b.PosDef) (X Y : M) :
    ⟪metricCoordinates b hb X, relativeOperator a b (metricCoordinates b hb Y)⟫_ℂ =
      bkmInner a X Y := by
  change ⟪liftMatrix (root b) (vectorization X),
    liftMatrix (relativeMatrix a b) (liftMatrix (root b) (vectorization Y))⟫_ℂ = _
  rw [← adjoint_inner_right, adjoint_root]
  change ⟪vectorization X,
    (liftMatrix (root b) * (liftMatrix (relativeMatrix a b) * liftMatrix (root b)))
      (vectorization Y)⟫_ℂ = _
  rw [← map_mul, ← map_mul]
  have h : root b * (relativeMatrix a b * root b) = omegaCoefficient a := by
    change root b * ((inverseRoot b * omegaCoefficient a * inverseRoot b) * root b) = _
    rw [mul_assoc (inverseRoot b * omegaCoefficient a), inverseRoot_mul_root b hb, mul_one,
      ← mul_assoc, root_mul_inverseRoot b hb, one_mul]
  rw [h]
  exact inner_coefficient a ha X Y


end D5.S3.Quantum.Recovery.BKMActualMetricCoordinates
