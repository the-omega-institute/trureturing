/- GID: D5/S3/Quantum/Dynamics/NativeReader/Invariants
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/NativeReader/Invariants
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conserved two-point charges of the actual changed auxiliary pulses. -/

import D5.S3.Quantum.Dynamics.NativeReader.Edges
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Conserved charges are derived from the source projections, rather than assumed as certificates. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.Dynamics.NativeReader

open Matrix
open D5.S3.Quantum.Measurement.OneSidedGoldenHistory (x x_properties block block_mul block_star)

theorem sourceQ_idempotent : sourceQ * sourceQ = sourceQ := by
  ext b c
  have h := projection_edge_mulVec false false
    (fun z => projection false (changedAddress false) z (edgeConfig false false c)) b
  change (projection false (changedAddress false) * projection false (changedAddress false))
    (edgeConfig false false b) (edgeConfig false false c) = _ at h
  rw [(projection_laws false (changedAddress false)).2, projection_edge_entry] at h
  simpa only [pairVector, projection_edge_entry, Matrix.mulVec, Matrix.mul_apply, dotProduct] using h.symm

theorem sourceQ_hermitian : sourceQ.IsHermitian := by
  ext b c
  cases b <;> cases c <;> simp [sourceQ, Matrix.conjTranspose_apply]

theorem pairPulse_unitary (t : ℝ) : (pairPulse t).conjTranspose * pairPulse t = 1 := by
  let e : Bool ≃ Fin 2 := Fintype.equivFin Bool
  let f := Matrix.reindexAlgEquiv ℂ ℂ e
  have hq : f sourceQ * f sourceQ = f sourceQ := by
    rw [← map_mul, sourceQ_idempotent]
  have hh : (f sourceQ).IsHermitian := by
    ext b c
    exact congrFun (congrFun sourceQ_hermitian.eq (e.symm b)) (e.symm c)
  have hp : f (pairPulse t) = block (f sourceQ) (unitPhase t) (unitPhase t ^ 2) := by
    simp only [pairPulse, map_smul, map_add, map_one, block, smul_sub, smul_add, smul_smul]
    module
  have hs : f (pairPulse t).conjTranspose = (f (pairPulse t)).conjTranspose := by
    ext b c
    rfl
  apply f.injective
  rw [map_mul, map_one, hs, hp, block_star _ hh, block_mul _ hq]
  simp only [star_pow, unitPhase_star, ← mul_pow]
  simp [block]

theorem pairPulse_commutes (t : ℝ) : Commute sourceQ (pairPulse t) := by
  unfold Commute SemiconjBy pairPulse
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

private theorem quadratic_image (M A : Matrix Bool Bool ℂ) (v : Bool → ℂ) :
    star (M *ᵥ v) ⬝ᵥ (A *ᵥ (M *ᵥ v)) =
      star v ⬝ᵥ ((M.conjTranspose * A * M) *ᵥ v) := by
  simp only [Matrix.star_mulVec, dotProduct_mulVec, vecMul_vecMul, Matrix.mul_assoc]

/-- The opposite coordinate is a; the actual candidate configuration has center !a. -/
def charge (a : Bool) (v : Bool → ℂ) : ℂ :=
  star v ⬝ᵥ (sourceQ *ᵥ v) - sourceQ a a * (star v ⬝ᵥ v)

theorem charge_conserved (a : Bool) (v : Bool → ℂ) (t : ℝ) :
    charge a (pairPulse t *ᵥ v) = charge a v := by
  have hq : (pairPulse t).conjTranspose * sourceQ * pairPulse t = sourceQ := by
    rw [Matrix.mul_assoc, (pairPulse_commutes t).eq, ← Matrix.mul_assoc,
      pairPulse_unitary, Matrix.one_mul]
  have hm : star (pairPulse t *ᵥ v) ⬝ᵥ (pairPulse t *ᵥ v) = star v ⬝ᵥ v := by
    simpa only [Matrix.one_mulVec, Matrix.mul_one, pairPulse_unitary] using
      quadratic_image (pairPulse t) 1 v
  simp only [charge, quadratic_image, hq, Matrix.one_mulVec, hm]

theorem charge_zero_of_current_zero (a : Bool) (v : Bool → ℂ) (hv : v (!a) = 0) :
    charge a v = 0 := by
  cases a <;>
    simp_all [charge, sourceQ, dotProduct, Matrix.mulVec, Fintype.sum_bool] <;> ring

theorem pair_current_nonzero (a : Bool) (v : Bool → ℂ) (h : charge a v ≠ 0) (t : ℝ) :
    (pairPulse t *ᵥ v) (!a) ≠ 0 := by
  intro hz
  exact h ((charge_conserved a v t).symm.trans (charge_zero_of_current_zero a _ hz))

theorem pair_ready (i a : Bool) :
    pairVector i a (readyVector i) = Pi.single (!a) (1 : ℂ) := by
  ext b
  simp only [pairVector, readyVector, Pi.single_apply]
  have he : edgeConfig i a b = readyTail i ↔ b = (!a) := by
    rw [← edge_ready i a]
    exact (edge_injective i a).eq_iff
  simp [he]

theorem reference_charge_nonzero (a : Bool) (c : ℂ) (hc : c ≠ 0) :
    charge a (c • Pi.single (!a) (1 : ℂ)) ≠ 0 := by
  have hd : x ^ 2 < x := by
    simpa only [pow_two, mul_one] using
      mul_lt_mul_of_pos_left x_properties.2.1 x_properties.1
  have hdc : (x : ℂ)^2 - (x : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hd.ne
  have hstar : star c * c ≠ 0 := mul_ne_zero (star_ne_zero.mpr hc) hc
  cases a
  · convert mul_ne_zero hdc hstar using 1 <;>
      simp [charge, sourceQ, Matrix.mulVec, dotProduct, Fintype.sum_bool,
        Pi.single_apply, star_mul] <;> ring
  · convert mul_ne_zero (neg_ne_zero.mpr hdc) hstar using 1 <;>
      simp [charge, sourceQ, Matrix.mulVec, dotProduct, Fintype.sum_bool,
        Pi.single_apply, star_mul] <;> ring

/-- The source-specific invariant is evaluated on the actual finite pulse entrance. -/
def entranceCharge (i a : Bool) (k : ℕ) (lam : ℝ) : ℂ :=
  charge a (pairVector i a (entrance i lam k))

theorem entranceCharge_at_zero (i a : Bool) (k : ℕ) : entranceCharge i a k 0 ≠ 0 := by
  obtain ⟨c, hc, he⟩ := reference_entrance i k
  have hp : pairVector i a (c • readyVector i) = c • pairVector i a (readyVector i) := rfl
  simpa [entranceCharge, he, hp, pair_ready] using reference_charge_nonzero a c hc

theorem entranceCharge_analytic (i a : Bool) (k : ℕ) (t : ℝ) :
    AnalyticAt ℝ (entranceCharge i a k) t := by
  have hv (b : Bool) := entrance_analytic i k (edgeConfig i a b) t
  have hs (b : Bool) : AnalyticAt ℝ (fun lam => star (entrance i lam k (edgeConfig i a b))) t := by
    exact (Complex.conjCLE.analyticAt _).comp (hv b)
  unfold entranceCharge charge pairVector Matrix.mulVec dotProduct
  simp only [Fintype.sum_bool, Pi.star_apply]
  fun_prop

end D5.S3.Quantum.Dynamics.NativeReader
