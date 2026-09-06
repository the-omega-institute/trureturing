/- GID: D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/QuquintWignerCriticalGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=terminal=atom:91bc86ae8d5e84fc1107062a0d552d5ce646c4d56b3d6135a51b12bb315c1691; result=D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.critical_geometry
   digest: Exact ququint Wigner zeros, tangent dimension, and critical gradient. -/

import D5.S3.Constants.PentagonCosines
import D5.S3.Quantum.Magic.QuquintCertificateData
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
open Complex Matrix
open D5.S3.Quantum.Magic.QuquintCertificateData (radical radical_sq radical_quartic radical_bounds)
open scoped BigOperators
set_option maxRecDepth 2000

namespace D5.S3.Quantum.Magic.QuquintWignerCriticalGeometry

abbrev State := EuclideanSpace ℂ (Fin 5)

def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)
def phasePoint (q p : Fin 5) : Matrix (Fin 5) (Fin 5) ℂ := fun x y =>
  if (x : ZMod 5) + (y : ZMod 5) = 2 * (q : ZMod 5) then
    zeta ^ (((p : ZMod 5) * ((x : ZMod 5) - (y : ZMod 5))).val) else 0
def wigner (v : State) (q p : Fin 5) : ℝ :=
  (star (WithLp.ofLp v) ⬝ᵥ (phasePoint q p *ᵥ WithLp.ofLp v)).re / 5
def lOne (v : State) : ℝ := ∑ q, ∑ p, |wigner v q p|
def psi : State := WithLp.toLp 2 ((1 / (Real.sqrt 5 : ℂ)) • ![1, 1, zeta ^ 3, 1, zeta ^ 2])
def zeroPoints : Finset (Fin 5 × Fin 5) :=
  by classical exact Finset.univ.filter fun qp => wigner psi qp.1 qp.2 = 0

private theorem zeta_value : zeta = ⟨(radical ^ 2 - 12) / 8, radical / 4⟩ := by
  have hc : Real.cos (2 * Real.pi / 5) = (radical ^ 2 - 12) / 8 := by
    have h := D5.S3.Constants.PentagonCosines.pentagon_golden_cosines.2.1
    rw [Real.inv_goldenRatio] at h
    change 2 * Real.cos (2 * Real.pi / 5) = -((1 - Real.sqrt 5) / 2) at h
    linarith [radical_sq]
  have hs : Real.sin (2 * Real.pi / 5) = radical / 4 := by
    have h := Real.sin_sq_add_cos_sq (2 * Real.pi / 5)
    have hp : 0 < Real.sin (2 * Real.pi / 5) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    have hr : 0 ≤ radical := Real.sqrt_nonneg _
    rw [hc] at h
    nlinarith [radical_quartic]
  apply Complex.ext
  · simpa [zeta, Complex.exp_re] using hc
  · simpa [zeta, Complex.exp_im] using hs

private def powerTable : Fin 5 → ℂ :=
  ![1, ⟨(radical ^ 2 - 12) / 8, radical / 4⟩,
    ⟨(8 - radical ^ 2) / 8, (radical ^ 3 - 12 * radical) / 16⟩,
    ⟨(8 - radical ^ 2) / 8, (12 * radical - radical ^ 3) / 16⟩,
    ⟨(radical ^ 2 - 12) / 8, -radical / 4⟩]

set_option maxHeartbeats 2000000 in
private theorem zeta_powers (i : Fin 5) : zeta ^ i.val = powerTable i := by
  have h := radical_quartic
  fin_cases i <;> apply Complex.ext <;>
    norm_num [powerTable, zeta_value, pow_succ, Complex.mul_re, Complex.mul_im] <;> grind only

private theorem inv_sqrt_five : (1 / (Real.sqrt 5 : ℂ)) = ((radical ^ 2 - 10) / 10 : ℝ) := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hp : Real.sqrt 5 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hr : (1 / Real.sqrt 5 : ℝ) = (radical ^ 2 - 10) / 10 := by
    rw [div_eq_iff hp, radical_sq]
    nlinarith
  exact_mod_cast hr

private def wignerTable : Matrix (Fin 5) (Fin 5) ℝ :=
  let a := (10 - radical ^ 2) / 50
  let b := (radical ^ 2 - 10) / 50
  let c := radical ^ 2 / 100
  let d := (20 - radical ^ 2) / 100
  !![a,b,c,0,d; a,b,c,0,d; d,a,b,c,0; c,0,d,a,b; d,a,b,c,0]

set_option maxHeartbeats 8000000 in
private theorem wigner_table (q p : Fin 5) : wigner psi q p = wignerTable q p := by
  have h := radical_quartic
  unfold wigner psi
  rw [inv_sqrt_five]
  fin_cases q <;> fin_cases p
  all_goals simp [dotProduct, mulVec, Fin.sum_univ_succ, phasePoint, zeta_value,
      wignerTable, pow_succ, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im,
      ZMod.val, Fin.val, Fin.neg_def]
  all_goals simp [Complex.conj_ofNat, Complex.div_re, Complex.div_im, Complex.mul_re,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.normSq_apply, pow_succ]
  all_goals norm_num at *
  all_goals grind only

theorem zero_points_eq : zeroPoints = {(0,3),(1,3),(2,4),(3,1),(4,4)} := by
  classical
  have h := radical_bounds
  ext qp
  rcases qp with ⟨q,p⟩
  simp only [zeroPoints, Finset.mem_filter, Finset.mem_univ, true_and, wigner_table]
  fin_cases q <;> fin_cases p <;> norm_num [wignerTable, Fin.ext_iff] <;>
    intro h' <;> nlinarith

theorem zero_points_card : zeroPoints.card = 5 := by
  rw [zero_points_eq]
  decide

theorem lOne_psi : lOne psi = 1 + 2 * Real.sqrt 5 / 5 := by
  have h := radical_bounds
  have ha : (10 - radical ^ 2) / 50 < 0 := by linarith
  have hb : 0 < (radical ^ 2 - 10) / 50 := by linarith
  have hc : 0 < radical ^ 2 / 100 := by linarith
  have hd : 0 < (20 - radical ^ 2) / 100 := by linarith
  simp only [lOne, wigner_table]
  norm_num [Fin.sum_univ_succ, wignerTable, abs_of_neg ha,
    abs_of_pos hb, abs_of_pos hc, abs_of_pos hd]
  linarith [radical_sq]

def gradient : Matrix (Fin 5) (Fin 5) ℂ :=
  ∑ q, ∑ p, (SignType.sign (wigner psi q p) : ℂ) • phasePoint q p

private theorem sign_table (q p : Fin 5) : SignType.sign (wigner psi q p) =
    (!![-1,1,1,0,1; -1,1,1,0,1; 1,-1,1,1,0;
      1,0,1,-1,1; 1,-1,1,1,0] : Matrix (Fin 5) (Fin 5) SignType) q p := by
  have h := radical_bounds
  have ha : (10 - radical ^ 2) / 50 < 0 := by linarith
  have hb : 0 < (radical ^ 2 - 10) / 50 := by linarith
  have hc : 0 < radical ^ 2 / 100 := by linarith
  have hd : 0 < (20 - radical ^ 2) / 100 := by linarith
  rw [wigner_table]
  fin_cases q <;> fin_cases p <;> simp [wignerTable,
    sign_neg ha, sign_pos hb, sign_pos hc, sign_pos hd]

set_option maxHeartbeats 8000000 in
theorem gradient_psi : gradient *ᵥ WithLp.ofLp psi =
    (5 * lOne psi : ℂ) • WithLp.ofLp psi := by
  have h := radical_quartic
  rw [lOne_psi]
  have hs : Real.sqrt 5 = (radical ^ 2 - 10) / 2 := by linarith [radical_sq]
  rw [hs]
  unfold gradient
  simp only [sign_table]
  unfold psi
  rw [inv_sqrt_five]
  ext i
  fin_cases i <;> apply Complex.ext
  all_goals simp [dotProduct, mulVec, Fin.sum_univ_succ, phasePoint, zeta_value,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.conj_re, Complex.conj_im, ZMod.val, Fin.val, Fin.neg_def]
  all_goals try simp [Complex.conj_ofNat, Complex.div_re, Complex.div_im, Complex.mul_re,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.normSq_apply, pow_succ]
  all_goals grind only

def tangent : Submodule ℝ State where
  carrier := {v | star (WithLp.ofLp psi) ⬝ᵥ WithLp.ofLp v = 0 ∧
    ∀ qp ∈ zeroPoints,
      (star (WithLp.ofLp psi) ⬝ᵥ (phasePoint qp.1 qp.2 *ᵥ WithLp.ofLp v)).re = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    constructor
    · simpa [dotProduct_add] using congrArg₂ (· + ·) hv.1 hw.1
    · intro qp hqp
      simp only [WithLp.ofLp_add, mulVec_add, dotProduct_add, Complex.add_re,
        hv.2 qp hqp, hw.2 qp hqp, add_zero]
  smul_mem' := by
    intro c v hv
    constructor
    · simp [dotProduct_smul, hv.1]
    · intro qp hqp
      simp [mulVec_smul, dotProduct_smul, hv.2 qp hqp]

def phases : Fin 5 → ℂ := ![1,1,zeta ^ 3,1,zeta ^ 2]

def gauge (u : Fin 10 → ℝ) : State :=
  WithLp.toLp 2 fun i => phases i * ⟨u (Fin.castAdd 5 i), u (Fin.natAdd 5 i)⟩

def basisMatrix : Matrix (Fin 10) (Fin 4) ℝ :=
  !![-1, radical ^ 2 / 4 - 3, -radical ^ 3 / 10 + radical, -radical ^ 3 / 40;
    3 - radical ^ 2 / 4, 3 - radical ^ 2 / 4, 3 * radical ^ 3 / 40 - radical,
      -3 * radical ^ 3 / 40 + radical;
    radical ^ 2 / 4 - 3, -1, radical ^ 3 / 40, radical ^ 3 / 10 - radical;
    1,0,0,0; 0,1,0,0;
    0,0,-1,2 - radical ^ 2 / 4;
    0,0,radical ^ 2 / 4 - 2,radical ^ 2 / 4 - 2;
    0,0,2 - radical ^ 2 / 4,-1;
    0,0,1,0; 0,0,0,1]

private def coordinates (u : Fin 10 → ℝ) : Fin 4 → ℝ := ![u 3,u 4,u 8,u 9]

private def gaugeMap : (Fin 10 → ℝ) →ₗ[ℝ] State where
  toFun := gauge
  map_add' := by
    intro u v
    ext i
    apply Complex.ext <;> simp [gauge, Complex.mul_re, Complex.mul_im] <;> ring
  map_smul' := by
    intro c u
    ext i
    apply Complex.ext <;> simp [gauge, Complex.mul_re, Complex.mul_im] <;> ring

private def constraintMap : State →ₗ[ℝ] (Fin 7 → ℝ) where
  toFun v := Real.sqrt 5 • ![
    (star (WithLp.ofLp psi) ⬝ᵥ WithLp.ofLp v).re,
    (star (WithLp.ofLp psi) ⬝ᵥ WithLp.ofLp v).im,
    (star (WithLp.ofLp psi) ⬝ᵥ (phasePoint 0 3 *ᵥ WithLp.ofLp v)).re,
    (star (WithLp.ofLp psi) ⬝ᵥ (phasePoint 1 3 *ᵥ WithLp.ofLp v)).re,
    (star (WithLp.ofLp psi) ⬝ᵥ (phasePoint 2 4 *ᵥ WithLp.ofLp v)).re,
    (star (WithLp.ofLp psi) ⬝ᵥ (phasePoint 3 1 *ᵥ WithLp.ofLp v)).re,
    (star (WithLp.ofLp psi) ⬝ᵥ (phasePoint 4 4 *ᵥ WithLp.ofLp v)).re]
  map_add' := by
    intro v w
    ext i
    fin_cases i <;> simp [dotProduct_add, mulVec_add, mul_add]
  map_smul' := by
    intro c v
    ext i
    fin_cases i <;> simp [dotProduct_smul, mulVec_smul, mul_left_comm]

private def constraintTable : Matrix (Fin 7) (Fin 10) ℝ :=
  let a := (8 - radical ^ 2) / 8
  let b := (radical ^ 2 - 12) / 8
  let c := (12 * radical - radical ^ 3) / 16
  let d := radical / 4
  !![1,1,1,1,1,0,0,0,0,0; 0,0,0,0,0,1,1,1,1,1;
    1,a,b,b,a,0,c,-d,d,-c; a,1,a,b,b,-c,0,c,-d,d;
    b,a,1,a,b,d,-c,0,c,-d; b,b,a,1,a,-d,d,-c,0,c;
    a,b,b,a,1,c,-d,d,-c,0]

set_option maxHeartbeats 8000000 in
private theorem constraint_table :
    LinearMap.toMatrix' (constraintMap.comp gaugeMap) = constraintTable := by
  have h := radical_quartic
  have hs : Real.sqrt 5 = (radical ^ 2 - 10) / 2 := by linarith [radical_sq]
  ext i j
  rw [LinearMap.toMatrix'_apply]
  simp only [LinearMap.comp_apply]
  fin_cases i <;> fin_cases j
  all_goals simp [constraintMap, gaugeMap, constraintTable, psi, inv_sqrt_five,
    dotProduct, mulVec, Fin.sum_univ_succ, gauge, phases, phasePoint, zeta_value,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.conj_re, Complex.conj_im, ZMod.val, Fin.val, Fin.neg_def, Pi.single_apply]
  all_goals try simp [Complex.conj_ofNat, Complex.div_re, Complex.div_im,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.normSq_apply]
  all_goals rw [hs]
  all_goals grind only

private def selector : Matrix (Fin 4) (Fin 10) ℝ :=
  !![0,0,0,1,0,0,0,0,0,0; 0,0,0,0,1,0,0,0,0,0;
    0,0,0,0,0,0,0,0,1,0; 0,0,0,0,0,0,0,0,0,1]

private def elimination : Matrix (Fin 10) (Fin 7) ℝ :=
  !![1-radical^2/20,radical^3/40-radical/5,3*radical^2/20-7/5,
      radical^2/20-4/5,radical^2/20-6/5,radical^2/20-3/5,0;
    radical^2/10-1,0,2-3*radical^2/20,1-radical^2/20,2-3*radical^2/20,0,0;
    1-radical^2/20,-radical^3/40+radical/5,-3/5,-1/5,radical^2/10-4/5,
      3/5-radical^2/20,0;
    0,0,0,0,0,0,0; 0,0,0,0,0,0,0;
    0,radical^2/20,radical/10,radical^3/40-3*radical/10,
      -radical^3/40+3*radical/10,-radical/10,0;
    0,1-radical^2/10,-radical^3/40+3*radical/10,radical/10,
      radical^3/40-radical/10,radical/5,0;
    0,radical^2/20,radical^3/40-2*radical/5,-radical^3/40+radical/5,
      -radical/5,-radical/10,0;
    0,0,0,0,0,0,0; 0,0,0,0,0,0,0]

set_option maxHeartbeats 8000000 in
private theorem constraint_basis : constraintTable * basisMatrix = 0 := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [constraintTable, basisMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ'] <;> grind only

set_option maxHeartbeats 8000000 in
private theorem selector_basis : selector * basisMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [selector, basisMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ']

set_option maxHeartbeats 8000000 in
private theorem elimination_identity :
    basisMatrix * selector + elimination * constraintTable = 1 := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [constraintTable, basisMatrix, selector, elimination, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val_succ'] <;> grind only

private theorem phases_ne_zero (i : Fin 5) : phases i ≠ 0 := by
  have hz : zeta ≠ 0 := Complex.exp_ne_zero _
  fin_cases i <;> simp [phases, hz]

private def ungauge (v : State) : Fin 10 → ℝ :=
  Fin.append (fun i => (WithLp.ofLp v i / phases i).re)
    (fun i => (WithLp.ofLp v i / phases i).im)

private theorem gauge_ungauge (v : State) : gauge (ungauge v) = v := by
  apply WithLp.ofLp_injective
  funext i
  change phases i * ⟨ungauge v (Fin.castAdd 5 i), ungauge v (Fin.natAdd 5 i)⟩ = _
  rw [ungauge, Fin.append_left, Fin.append_right, Complex.eta]
  exact mul_div_cancel₀ _ (phases_ne_zero i)

private theorem ungauge_gauge (u : Fin 10 → ℝ) : ungauge (gauge u) = u := by
  have h (i : Fin 5) : WithLp.ofLp (gauge u) i / phases i =
      ⟨u (Fin.castAdd 5 i), u (Fin.natAdd 5 i)⟩ := by
    simp [gauge, mul_div_cancel_left₀, phases_ne_zero]
  simpa only [ungauge, h] using (Fin.append_castAdd_natAdd (m := 5) (n := 5) (f := u))

private theorem tangent_iff_constraint (v : State) :
    v ∈ tangent ↔ constraintMap v = 0 := by
  have hs : Real.sqrt 5 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  change (_ ∧ _) ↔ _
  simp only [zero_points_eq, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
    forall_eq, Complex.ext_iff, Complex.zero_re, Complex.zero_im]
  simp [constraintMap, funext_iff, Fin.forall_fin_succ, hs, and_assoc]

private theorem constraint_gauge (u : Fin 10 → ℝ) :
    constraintMap (gauge u) = constraintTable *ᵥ u := by
  rw [← constraint_table, LinearMap.toMatrix'_mulVec]
  rfl

private theorem basis_mem_tangent (a : Fin 4 → ℝ) :
    gauge (basisMatrix *ᵥ a) ∈ tangent := by
  rw [tangent_iff_constraint, constraint_gauge, mulVec_mulVec, constraint_basis]
  simp

private theorem basis_reconstruct (v : tangent) :
    basisMatrix *ᵥ (selector *ᵥ ungauge v) = ungauge v := by
  have hc : constraintTable *ᵥ ungauge v = 0 := by
    rw [← constraint_gauge, gauge_ungauge]
    exact (tangent_iff_constraint v).mp v.property
  have h := congrArg (fun m => m *ᵥ ungauge v) elimination_identity
  simpa only [add_mulVec, ← mulVec_mulVec, hc, mulVec_zero, add_zero,
    one_mulVec] using h

/-- The checked basis and selector give inverse coordinates on the actual tangent space. -/
def tangentEquiv : (Fin 4 → ℝ) ≃ₗ[ℝ] tangent where
  toFun a := ⟨gauge (basisMatrix *ᵥ a), basis_mem_tangent a⟩
  invFun v := selector *ᵥ ungauge v
  left_inv a := by
    change selector *ᵥ ungauge (gauge (basisMatrix *ᵥ a)) = a
    rw [ungauge_gauge, mulVec_mulVec, selector_basis, one_mulVec]
  right_inv v := by
    apply Subtype.ext
    change gauge (basisMatrix *ᵥ (selector *ᵥ ungauge v)) = v
    rw [basis_reconstruct, gauge_ungauge]
  map_add' a b := by
    apply Subtype.ext
    exact (gaugeMap.comp basisMatrix.mulVecLin).map_add a b
  map_smul' c a := by
    apply Subtype.ext
    exact (gaugeMap.comp basisMatrix.mulVecLin).map_smul c a

theorem tangent_finrank : Module.finrank ℝ tangent = 4 := by
  rw [← tangentEquiv.finrank_eq, Module.finrank_fin_fun]

theorem critical_geometry :
    zeroPoints = {(0,3),(1,3),(2,4),(3,1),(4,4)} ∧
      zeroPoints.card = 5 ∧ Module.finrank ℝ tangent = 4 ∧
      lOne psi = 1 + 2 * Real.sqrt 5 / 5 := by
  exact ⟨zero_points_eq, zero_points_card, tangent_finrank, lOne_psi⟩

set_option maxHeartbeats 8000000 in
private theorem phasePoint_hermitian (q p : Fin 5) : (phasePoint q p).IsHermitian := by
  have h := radical_quartic
  ext i j
  fin_cases q <;> fin_cases p <;> fin_cases i <;> fin_cases j
  all_goals simp [phasePoint, Matrix.conjTranspose_apply, zeta_value,
    pow_succ, Complex.mul_re, Complex.mul_im, ZMod.val, Fin.val, Fin.neg_def]
  all_goals apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im] <;> grind only

private theorem hermitian_pair (A : Matrix (Fin 5) (Fin 5) ℂ) (hA : A.IsHermitian)
    (u v : Fin 5 → ℂ) : (star v ⬝ᵥ (A *ᵥ u)).re = (star u ⬝ᵥ (A *ᵥ v)).re := by
  have h : star v ⬝ᵥ (A *ᵥ u) = star (star u ⬝ᵥ (A *ᵥ v)) := by
    rw [← star_dotProduct, star_mulVec, hA, dotProduct_mulVec]
  rw [h]
  rfl

theorem wigner_expand (v : State) (q p : Fin 5) (e : ℝ) :
    wigner (psi + e • v) q p = wigner psi q p +
      e * (2 * (star (WithLp.ofLp psi) ⬝ᵥ
        (phasePoint q p *ᵥ WithLp.ofLp v)).re / 5) + e ^ 2 * wigner v q p := by
  have h := hermitian_pair (phasePoint q p) (phasePoint_hermitian q p)
    (WithLp.ofLp psi) (WithLp.ofLp v)
  simp [wigner, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, Complex.add_re, h]
  ring

theorem gradient_restricted : gradient =
    ∑ qp ∈ (Finset.univ \ zeroPoints),
      (SignType.sign (wigner psi qp.1 qp.2) : ℂ) • phasePoint qp.1 qp.2 := by
  classical
  unfold gradient
  rw [← Fintype.sum_prod_type (fun qp : Fin 5 × Fin 5 =>
    (SignType.sign (wigner psi qp.1 qp.2) : ℂ) • phasePoint qp.1 qp.2)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro qp _ hqp
  have hz : qp ∈ zeroPoints := by simpa using hqp
  have h : wigner psi qp.1 qp.2 = 0 := (Finset.mem_filter.mp hz).2
  simp [h]

private theorem gradient_hermitian : gradient.IsHermitian := by
  change gradientᴴ = gradient
  simp only [gradient, conjTranspose_sum, conjTranspose_smul,
    (phasePoint_hermitian _ _).eq]
  congr 1
  funext q
  congr 1
  funext p
  have hs (s : SignType) : star (s : ℂ) = (s : ℂ) := by cases s <;> simp
  rw [hs]

theorem first_coefficient_zero (v : tangent) :
    ∑ q, ∑ p, (SignType.sign (wigner psi q p) : ℝ) *
      (2 * (star (WithLp.ofLp psi) ⬝ᵥ (phasePoint q p *ᵥ WithLp.ofLp (v : State))).re / 5) = 0 := by
  have h : (star (WithLp.ofLp psi) ⬝ᵥ (gradient *ᵥ WithLp.ofLp (v : State))).re = 0 := by
    rw [← hermitian_pair gradient gradient_hermitian, gradient_psi, dotProduct_smul]
    have hv : star (WithLp.ofLp (v : State)) ⬝ᵥ WithLp.ofLp psi = 0 := by
      rw [star_dotProduct, v.property.1]
      simp
    rw [hv]
    simp
  have hs (s : SignType) : (s : ℂ).re = (s : ℝ) ∧ (s : ℂ).im = 0 := by
    cases s <;> norm_num
  calc
    _ = (2 / 5 : ℝ) * (star (WithLp.ofLp psi) ⬝ᵥ
        (gradient *ᵥ WithLp.ofLp (v : State))).re := by
      simp only [gradient, sum_mulVec, dotProduct_sum, smul_mulVec, dotProduct_smul,
        Complex.re_sum, smul_eq_mul, Complex.mul_re, hs, mul_zero, sub_zero,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = 0 := by rw [h]; ring

theorem first_variation_zero (v : tangent) :
    HasDerivAt (fun e : ℝ => lOne (psi + e • (v : State))) 0 0 := by
  have hd (q p : Fin 5) : HasDerivAt (fun e : ℝ => |wigner (psi + e • (v : State)) q p|)
      ((SignType.sign (wigner psi q p) : ℝ) *
        (2 * (star (WithLp.ofLp psi) ⬝ᵥ (phasePoint q p *ᵥ WithLp.ofLp (v : State))).re / 5)) 0 := by
    by_cases hz : wigner psi q p = 0
    · have hv := v.property.2 (q,p) (by simp [zeroPoints, hz])
      simpa [wigner_expand, hz, hv, abs_mul, abs_sq] using
        ((hasDerivAt_pow 2 (0 : ℝ)).mul_const |wigner v q p|)
    · have hpoly := ((hasDerivAt_const (0 : ℝ) (wigner psi q p)).add
        ((hasDerivAt_id (0 : ℝ)).mul_const
          (2 * (star (WithLp.ofLp psi) ⬝ᵥ (phasePoint q p *ᵥ WithLp.ofLp (v : State))).re / 5))).add
        ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (wigner v q p))
      have hp : HasDerivAt (fun e : ℝ => wigner (psi + e • (v : State)) q p)
          (2 * (star (WithLp.ofLp psi) ⬝ᵥ (phasePoint q p *ᵥ WithLp.ofLp (v : State))).re / 5) 0 := by
        convert! hpoly using 1 <;> simp [wigner_expand, funext_iff, Pi.add_apply]
      convert! (hasDerivAt_abs (by simpa using hz)).comp 0 hp using 1 <;>
        simp [Function.comp_def]
  simpa only [lOne, first_coefficient_zero] using
    (HasDerivAt.fun_sum (u := Finset.univ) fun q _ =>
      HasDerivAt.fun_sum (u := Finset.univ) fun p _ => hd q p)

#print axioms tangent_finrank
#print axioms critical_geometry
#print axioms gradient_psi
#print axioms gradient_restricted
#print axioms first_variation_zero
#print axioms wigner_expand
#print axioms first_coefficient_zero
end D5.S3.Quantum.Magic.QuquintWignerCriticalGeometry
