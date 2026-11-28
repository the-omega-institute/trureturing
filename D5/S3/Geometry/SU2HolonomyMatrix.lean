/- GID: D5/S3/Geometry/SU2HolonomyMatrix
   generality: G
   mirror-B: none(waiver:covered-by-chordal-su2-sharp-bounds-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The first two moments of the weighted holonomy matrix are independent of the gains. -/

import D5.S3.Geometry.QuaternionicRayleigh
import D5.S3.Geometry.UnitQuaternionMetric

/-!
Omega original.

The first two moments of the weighted holonomy matrix are independent of
the gains. Its cubic moment averages the real parts of triangle holonomies.
-/

open scoped Quaternion BigOperators

noncomputable section

namespace Omega.Geometry.HolonomySpectrum

open Finset Real Omega.Geometry.UnitQuaternion

local notation "U" => unitary ℍ[ℝ]

variable {ι : Type*} [Fintype ι]

/-- A skew family of unit-quaternion matrix entries with unit diagonal. -/
structure HolonomyGains (ι : Type*) where
  gain : ι → ι → U
  diag : ∀ i, gain i i = 1
  flip : ∀ i j, gain j i = (gain i j)⁻¹

private theorem coe_inv (u : U) : (↑u⁻¹ : ℍ[ℝ]) = star (u : ℍ[ℝ]) := rfl

/-- The entry in position `i,j` is `√(w i) √(w j)` times the edge gain. -/
def holonomyMatrix (g : HolonomyGains ι) (w : ι → ℝ) : Matrix ι ι ℍ[ℝ] :=
  fun i j => (√(w i) * √(w j)) • (g.gain i j : ℍ[ℝ])

omit [Fintype ι] in
theorem isHermitian_holonomyMatrix (g : HolonomyGains ι) (w : ι → ℝ) :
    (holonomyMatrix g w).IsHermitian := by
  ext i j : 1
  change star (holonomyMatrix g w j i) = holonomyMatrix g w i j
  simp only [holonomyMatrix, Quaternion.star_smul, ← coe_inv, ← g.flip]
  rw [mul_comm]

/-- The diagonal trace is the total vertex weight. -/
theorem holonomy_trace (g : HolonomyGains ι) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) :
    ∑ i, (holonomyMatrix g w i i).re = ∑ i, w i := by
  apply sum_congr rfl
  intro i _
  rw [holonomyMatrix, g.diag]
  change √(w i) * √(w i) * 1 = w i
  rw [mul_one, mul_self_sqrt (hw i)]

omit [Fintype ι] in
private theorem factor_two (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (i j : ι) :
    (√(w i) * √(w j)) * (√(w j) * √(w i)) = w i * w j := by
  have h₁ := mul_self_sqrt (hw i)
  have h₂ := mul_self_sqrt (hw j)
  calc
    _ = (√(w i) * √(w i)) * (√(w j) * √(w j)) := by ring
    _ = _ := by rw [h₁, h₂]

/-- The squared trace is the square of the total weight. -/
theorem holonomy_trace_sq [DecidableEq ι] (g : HolonomyGains ι) {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) :
    ∑ i, ((holonomyMatrix g w ^ 2) i i).re = (∑ i, w i) ^ 2 := by
  rw [pow_two, pow_two, sum_mul]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum, Matrix.mul_apply]
  change (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) _ = _
  rw [map_sum]
  refine sum_congr rfl fun j _ => ?_
  simp only [holonomyMatrix, smul_mul_smul_comm, factor_two _ hw, g.flip i j]
  change (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1))
    ((w i * w j) • (↑(g.gain i j * (g.gain i j)⁻¹) : ℍ[ℝ])) = _
  rw [mul_inv_cancel]
  change w i * w j * 1 = _
  ring

omit [Fintype ι] in
private theorem triple_product (g : HolonomyGains ι) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (i j k : ι) :
    holonomyMatrix g w i j * holonomyMatrix g w j k * holonomyMatrix g w k i =
      (w i * w j * w k) • (↑(g.gain i j * g.gain j k * g.gain k i) : ℍ[ℝ]) := by
  simp only [holonomyMatrix, smul_mul_smul_comm]
  congr 1
  calc
    _ = (√(w i) * √(w i)) * (√(w j) * √(w j)) * (√(w k) * √(w k)) := by ring
    _ = _ := by simp only [mul_self_sqrt (hw _)]

/-- The cubic trace is the sum over oriented triangles with their
simplex weights. This identity includes all triples with repeated indices. -/
theorem holonomy_trace_cube [DecidableEq ι] (g : HolonomyGains ι) {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) :
    ∑ i, ((holonomyMatrix g w ^ 3) i i).re =
      ∑ i, ∑ j, ∑ k, w i * w j * w k *
        (↑(g.gain i j * g.gain j k * g.gain k i) : ℍ[ℝ]).re := by
  rw [show (3 : ℕ) = 2 + 1 by decide, pow_succ, pow_two]
  refine sum_congr rfl fun i _ => ?_
  simp only [Matrix.mul_apply, sum_mul]
  change (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) _ = _
  simp only [map_sum, triple_product g hw]
  rw [sum_comm]
  rfl

omit [Fintype ι] in
theorem cycle_gain_eq_one (g : HolonomyGains ι) {i j k : ι}
    (h : i = j ∨ j = k ∨ i = k) : g.gain i j * g.gain j k * g.gain k i = 1 := by
  rcases h with hij | hjk | hik
  · subst j
    rw [g.diag, one_mul, g.flip i k, mul_inv_cancel]
  · subst k
    rw [g.diag, mul_one, g.flip i j, mul_inv_cancel]
  · subst k
    rw [g.diag, mul_one, g.flip i j, mul_inv_cancel]


open scoped InnerProductSpace

/-- A weighted column of unit-quaternion values. -/
def weightedColumn (w : ι → ℝ) (q : ι → U) : Columns ι :=
  WithLp.toLp 2 fun i => √(w i) • (q i : ℍ[ℝ])

omit [Fintype ι] in
@[simp] theorem weightedColumn_apply (w : ι → ℝ) (q : ι → U) (i : ι) :
    weightedColumn w q i = √(w i) • (q i : ℍ[ℝ]) := rfl

theorem norm_weightedColumn {w : ι → ℝ} (q : ι → U) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) : ‖weightedColumn w q‖ = 1 := by
  have hp : ‖weightedColumn w q‖ ^ 2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [weightedColumn_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg _),
      norm_coe, mul_one, sq_sqrt (hw _), hs]
  nlinarith [norm_nonneg (weightedColumn w q)]

theorem pairing_weightedColumn {w : ι → ℝ} (q r : ι → U) (hw : ∀ i, 0 ≤ w i) :
    pairing (weightedColumn w q) (weightedColumn w r) =
      ∑ i, w i • (↑((q i)⁻¹ * r i) : ℍ[ℝ]) := by
  simp only [pairing, weightedColumn_apply, Quaternion.star_smul, smul_mul_smul_comm,
    mul_self_sqrt (hw _), ← coe_inv]
  rfl

/-- The weighted Rayleigh quotient is the average of the pairwise alignments. -/
theorem rayleigh_weightedColumn (g : HolonomyGains ι) {w : ι → ℝ}
    (q : ι → U) (hw : ∀ i, 0 ≤ w i) :
    ⟪weightedColumn w q, realAction (holonomyMatrix g w) (weightedColumn w q)⟫_ℝ =
      ∑ i, ∑ j, w i * w j * (↑((q i)⁻¹ * g.gain i j * q j) : ℍ[ℝ]).re := by
  rw [real_inner_eq_re_pairing]
  change (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) _ = _
  simp only [pairing, realAction_apply, weightedColumn_apply, Finset.mul_sum,
    map_sum, Quaternion.star_smul, holonomyMatrix, smul_mul_smul_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  have h : √(w i) * ((√(w i) * √(w j)) * √(w j)) = w i * w j := by
    rw [← factor_two w hw i j]
    ring
  rw [h]
  change w i * w j * (star (q i : ℍ[ℝ]) * ((g.gain i j : ℍ[ℝ]) * (q j : ℍ[ℝ]))).re = _
  rw [← mul_assoc]
  rfl

/-- A common lower bound on off-diagonal alignments gives a weighted Rayleigh lower bound
whose diagonal contribution retains the second moment of the weights. -/
theorem rayleigh_weightedColumn_lower (g : HolonomyGains ι) {w : ι → ℝ}
    (q : ι → U) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) {c : ℝ}
    (h : ∀ i j, i ≠ j → c ≤ (↑((q i)⁻¹ * g.gain i j * q j) : ℍ[ℝ]).re) :
    c + (1 - c) * ∑ i, w i ^ 2 ≤
      ⟪weightedColumn w q, realAction (holonomyMatrix g w) (weightedColumn w q)⟫_ℝ := by
  classical
  rw [rayleigh_weightedColumn g q hw]
  let f (i j : ι) := c * (w i * w j) + if i = j then (1 - c) * w i ^ 2 else 0
  have hrow (i : ι) : ∑ j, f i j = c * w i + (1 - c) * w i ^ 2 := by
    simp [f, sum_add_distrib, ← mul_sum, hs]
  calc
    _ = ∑ i, ∑ j, f i j := by simp [hrow, sum_add_distrib, ← mul_sum, hs]
    _ ≤ _ := by
      refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
      by_cases hij : i = j
      · subst j
        simp only [f, g.diag, mul_one, inv_mul_cancel]
        change c * (w i * w i) + (1 - c) * w i ^ 2 ≤ w i * w i * 1
        nlinarith
      · simpa [f, hij, mul_comm c] using mul_le_mul_of_nonneg_left (h i j hij)
          (mul_nonneg (hw _) (hw _))


/-- The contribution of triples with a repeated index is the cubic
inclusion-exclusion correction to the second moment. -/
theorem holonomy_trace_cube_lower [DecidableEq ι] (g : HolonomyGains ι)
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) {c : ℝ}
    (htri : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      c ≤ (↑(g.gain i j * g.gain j k * g.gain k i) : ℍ[ℝ]).re) :
    c + (1 - c) * ∑ i, (3 * w i ^ 2 - 2 * w i ^ 3) ≤
      ∑ i, ((holonomyMatrix g w ^ 3) i i).re := by
  rw [holonomy_trace_cube g hw]
  let term (i j k : ι) := w i * w j * w k *
    (if i = j ∨ j = k ∨ i = k then 1 else c)
  have hle : (∑ i, ∑ j, ∑ k, term i j k) ≤
      ∑ i, ∑ j, ∑ k, w i * w j * w k *
        (↑(g.gain i j * g.gain j k * g.gain k i) : ℍ[ℝ]).re := by
    refine sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun k _ => ?_
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg (hw i) (hw j)) (hw k))
    by_cases h : i = j ∨ j = k ∨ i = k
    · rw [cycle_gain_eq_one g h]
      rw [if_pos h]
      exact le_refl (1 : ℝ)
    · push_neg at h
      simpa only [h.1, h.2.1, h.2.2, or_self, ite_false] using htri i j k h.1 h.2.1 h.2.2
  have hid (i j k : ι) : term i j k =
      c * (w i * w j * w k) + (1 - c) *
        ((if i = j then w i ^ 2 * w k else 0) + (if j = k then w i * w j ^ 2 else 0) +
          (if i = k then w i ^ 2 * w j else 0) - 2 * (if i = j ∧ j = k then w i ^ 3 else 0)) := by
    unfold term
    by_cases hij : i = j
    · subst j
      by_cases hik : i = k
      · subst k
        simp
        ring
      · simp [hik]
        ring
    · by_cases hjk : j = k
      · subst k
        simp [hij]
        ring
      · by_cases hik : i = k
        · subst k
          simp [hij, Ne.symm hij]
          ring
        · simp [hij, hjk, hik]
          ring
  have hsum₁ : (∑ i, ∑ j, ∑ k, if i = j then w i ^ 2 * w k else 0) = ∑ i, w i ^ 2 := by
    refine sum_congr rfl fun i _ => ?_
    rw [sum_comm]
    simp [← mul_sum, hs]
  have hsum₂ : (∑ i, ∑ j, ∑ k, if j = k then w i * w j ^ 2 else 0) = ∑ i, w i ^ 2 := by
    simp [← mul_sum, ← sum_mul, hs]
  have hsum₃ : (∑ i, ∑ j, ∑ k, if i = k then w i ^ 2 * w j else 0) = ∑ i, w i ^ 2 := by
    simp [← mul_sum, hs]
  have hsum₄ : (∑ i, ∑ j, ∑ k, if i = j ∧ j = k then w i ^ 3 else 0) = ∑ i, w i ^ 3 := by
    refine sum_congr rfl fun i _ => ?_
    trans ∑ j, if i = j then w i ^ 3 else 0
    · apply sum_congr rfl
      intro j _
      by_cases h : i = j <;> simp [h]
    · simp
  have he : (∑ i, ∑ j, ∑ k, term i j k) =
      c + (1 - c) * ∑ i, (3 * w i ^ 2 - 2 * w i ^ 3) := by
    simp only [hid, sum_add_distrib, sum_sub_distrib, ← mul_sum,
      hsum₁, hsum₂, hsum₃, hsum₄]
    simp only [hs, mul_one, ← mul_sum]
    ring
  rwa [he] at hle

end Omega.Geometry.HolonomySpectrum
