/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedReplaySoundness
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedReplaySoundness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Replay.existsUnique_zero; instance=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Bounds.row_bounds
   digest: Integer residual, Jacobian and preconditioner bounds imply an exact root certificate. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.ChirpedReplayArithmetic
import D5.S3.Quantum.QuantumChannels.WernerHolevo.ChirpedRootCertificate
import Mathlib.Analysis.Matrix.Normed

namespace ChirpedReplay

open scoped BigOperators Matrix.Norms.Operator

section Rows

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rowWeight (A : Matrix ι ι ℤ) (i : ι) : ℤ := ∑ j, |A i j|

def denominator (D S : ℤ) : ℤ := D * S ^ 2

def stepRow (S : ℤ) (n : ℕ) (A : Matrix ι ι ℤ) (f : ι → ℤ) (i : ι) : ℤ :=
  |∑ j, A i j * f j| + rowWeight A i * (120 * (n : ℤ) * S)

def defectRow (D S : ℤ) (n : ℕ) (A J : Matrix ι ι ℤ) (i : ι) : ℤ :=
  (∑ j, |denominator D S * (if i = j then (1 : ℤ) else 0) - ∑ k, A i k * J k j|) +
    rowWeight A i * (Fintype.card ι : ℤ) * (420 * (n : ℤ) * S)

noncomputable def scaledMatrix (A : Matrix ι ι ℤ) (D : ℤ) : Matrix ι ι ℝ :=
  fun i j => (A i j : ℝ) / (D : ℝ)

noncomputable def preconditioner (A : Matrix ι ι ℤ) (D : ℤ) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  (scaledMatrix A D).mulVecLin.toContinuousLinearMap

private theorem norm_le_of_row_sum_le (B : Matrix ι ι ℝ) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i, ∑ j, |B i j| ≤ b) : ‖B‖ ≤ b := by
  rw [Matrix.linfty_opNorm_def]
  have hs : (Finset.univ.sup fun i : ι => ∑ j : ι, ‖B i j‖₊) ≤ NNReal.mk b hb := by
    apply Finset.sup_le
    intro i _
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_sum, coe_nnnorm, NNReal.coe_mk, Real.norm_eq_abs] using h i
  exact NNReal.coe_le_coe.mpr hs

/-- The weighted error is added to the absolute integer dot product for this row. -/
private theorem affine_row_bound {D S : ℤ} (hD : 0 < D) (hS : 0 < S)
    (a b : ι → ℤ) (x : ι → ℝ) (t B : ℤ)
    (h : ∀ j, |(S : ℝ) ^ 2 * x j - (b j : ℝ)| ≤ (B : ℝ)) :
    |(t : ℝ) - ∑ j, ((a j : ℝ) / (D : ℝ)) * x j| ≤
      ((|denominator D S * t - ∑ j, a j * b j| + (∑ j, |a j|) * B : ℤ) : ℝ) /
        (denominator D S : ℝ) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  have hH : (0 : ℝ) < (denominator D S : ℝ) := by
    simp only [denominator, Int.cast_mul, Int.cast_pow]
    positivity
  let r : ℝ := (t : ℝ) - ∑ j, ((a j : ℝ) / (D : ℝ)) * x j
  let u : ℝ := ((denominator D S * t - ∑ j, a j * b j : ℤ) : ℝ)
  let v : ℝ := ∑ j, (a j : ℝ) * ((S : ℝ) ^ 2 * x j - (b j : ℝ))
  have hsplit : (denominator D S : ℝ) * r = u - v := by
    dsimp only [r, u, v, denominator]
    push_cast
    rw [mul_sub, Finset.mul_sum]
    have hterms :
        (∑ j, ((D : ℝ) * (S : ℝ) ^ 2) * (((a j : ℝ) / (D : ℝ)) * x j)) =
          (∑ j, (a j : ℝ) * (b j : ℝ)) +
            ∑ j, (a j : ℝ) * ((S : ℝ) ^ 2 * x j - (b j : ℝ)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      field_simp <;> ring
    rw [hterms]
    ring
  have hv : |v| ≤ (∑ j, |(a j : ℝ)|) * (B : ℝ) := by
    calc
      _ ≤ ∑ j, |(a j : ℝ) * ((S : ℝ) ^ 2 * x j - (b j : ℝ))| := by
        simpa only [v, Real.norm_eq_abs] using
          (norm_sum_le Finset.univ
            (fun j => (a j : ℝ) * ((S : ℝ) ^ 2 * x j - (b j : ℝ))))
      _ ≤ _ := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun j _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (h j) (abs_nonneg _)
  apply (le_div_iff₀ hH).2
  change |r| * (denominator D S : ℝ) ≤ _
  calc
    _ = |(denominator D S : ℝ) * r| := by rw [abs_mul, abs_of_pos hH, mul_comm]
    _ = |u - v| := by rw [hsplit]
    _ ≤ |u| + |v| := by simpa only [Real.norm_eq_abs] using norm_sub_le u v
    _ ≤ _ := by
      simpa only [Int.cast_add, Int.cast_abs, Int.cast_mul, Int.cast_sum] using
        add_le_add (le_refl |u|) hv

/-- Convert the replay's integer step, defect, and preconditioner row bounds to
the sup norms on the exact continuous linear maps. The entry hypotheses are
cleared of denominators at scale S². -/
theorem clm_bounds_of_rows {D S : ℤ} (hD : 0 < D) (hS : 0 < S) (n : ℕ)
    (A J : Matrix ι ι ℤ) (f : ι → ℤ) (g : ι → ℝ)
    (G : (ι → ℝ) →L[ℝ] (ι → ℝ)) (E Δ M : ℤ)
    (hE : 0 ≤ E) (hΔ : 0 ≤ Δ) (hM : 0 ≤ M)
    (hf : ∀ i, |(S : ℝ) ^ 2 * g i - (f i : ℝ)| ≤ (120 * (n : ℝ) * (S : ℝ)))
    (hJ : ∀ i j, |(S : ℝ) ^ 2 * LinearMap.toMatrix' G.toLinearMap i j - (J i j : ℝ)| ≤
      (420 * (n : ℝ) * (S : ℝ)))
    (he : ∀ i, stepRow S n A f i ≤ E)
    (hδ : ∀ i, defectRow D S n A J i ≤ Δ)
    (hy : ∀ i, rowWeight A i ≤ M) :
    ‖preconditioner A D g‖ ≤ (E : ℝ) / (denominator D S : ℝ) ∧
      ‖ContinuousLinearMap.id ℝ (ι → ℝ) - (preconditioner A D).comp G‖ ≤
        (Δ : ℝ) / (denominator D S : ℝ) ∧
      ‖preconditioner A D‖ ≤ (M : ℝ) / (D : ℝ) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  have hH : (0 : ℝ) < (denominator D S : ℝ) := by
    simp only [denominator, Int.cast_mul, Int.cast_pow]
    positivity
  have hER : (0 : ℝ) ≤ E := by exact_mod_cast hE
  have hΔR : (0 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hMR : (0 : ℝ) ≤ M := by exact_mod_cast hM
  let Y := preconditioner A D
  let B := scaledMatrix A D
  let Gm := LinearMap.toMatrix' G.toLinearMap
  have hYmat : LinearMap.toMatrix' Y.toLinearMap = B := by
    change LinearMap.toMatrix' (Matrix.toLin' B) = B
    exact LinearMap.toMatrix'_toLin' B
  refine ⟨?_, ?_, ?_⟩
  · apply (pi_norm_le_iff_of_nonneg (div_nonneg hER hH.le)).2
    intro i
    change ‖∑ j, ((A i j : ℝ) / (D : ℝ)) * g j‖ ≤ _
    rw [Real.norm_eq_abs]
    have hrow := affine_row_bound hD hS (A i) f g 0 (120 * (n : ℤ) * S)
      (fun j => by exact_mod_cast hf j)
    have hstep : |∑ j, ((A i j : ℝ) / (D : ℝ)) * g j| ≤
        (stepRow S n A f i : ℝ) / (denominator D S : ℝ) := by
      simpa only [Int.cast_zero, zero_sub, mul_zero, abs_neg, stepRow, rowWeight] using hrow
    exact hstep.trans (div_le_div_of_nonneg_right (by exact_mod_cast he i) hH.le)
  · change ‖ContinuousLinearMap.id ℝ (ι → ℝ) - Y.comp G‖ ≤ _
    rw [← Matrix.linfty_opNorm_toMatrix (ContinuousLinearMap.id ℝ (ι → ℝ) - Y.comp G)]
    have hmatrix :
        LinearMap.toMatrix' (ContinuousLinearMap.id ℝ (ι → ℝ) - Y.comp G).toLinearMap =
          1 - B * Gm := by
      change LinearMap.toMatrix'
        (LinearMap.id - Y.toLinearMap.comp G.toLinearMap) = _
      rw [map_sub, LinearMap.toMatrix'_id, LinearMap.toMatrix'_comp, hYmat]
    rw [hmatrix]
    apply norm_le_of_row_sum_le _ (div_nonneg hΔR hH.le)
    intro i
    have hentry (j : ι) :
        |(1 - B * Gm) i j| ≤
          ((|denominator D S * (if i = j then (1 : ℤ) else 0) - ∑ k, A i k * J k j| +
            rowWeight A i * (420 * (n : ℤ) * S) : ℤ) : ℝ) / (denominator D S : ℝ) := by
      have hrow := affine_row_bound hD hS (A i) (fun k => J k j) (fun k => Gm k j)
        (if i = j then 1 else 0) (420 * (n : ℤ) * S)
        (fun k => by exact_mod_cast hJ k j)
      by_cases hij : i = j <;>
        simpa [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply, B, scaledMatrix,
          rowWeight, hij] using hrow
    calc
      _ ≤ ∑ j, ((|denominator D S * (if i = j then (1 : ℤ) else 0) -
          ∑ k, A i k * J k j| + rowWeight A i * (420 * (n : ℤ) * S) : ℤ) : ℝ) /
            (denominator D S : ℝ) := Finset.sum_le_sum fun j _ => hentry j
      _ = (defectRow D S n A J i : ℝ) / (denominator D S : ℝ) := by
        rw [← Finset.sum_div]
        simp only [Int.cast_add, Int.cast_sum, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, defectRow] <;> ring
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hδ i) hH.le
  · have hnorm : ‖B‖ = ‖preconditioner A D‖ := Matrix.linfty_opNorm_eq_opNorm B
    rw [← hnorm]
    apply norm_le_of_row_sum_le _ (div_nonneg hMR hDR.le)
    intro i
    calc
      ∑ j, |B i j| = (rowWeight A i : ℝ) / (D : ℝ) := by
        simp only [B, scaledMatrix, abs_div, abs_of_pos hDR, rowWeight, Int.cast_sum, Int.cast_abs]
        rw [Finset.sum_div]
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hy i) hDR.le

/-- Common dyadic exponent used by Python's `contract`. A dyadic entry is
a pair of integer mantissa and signed exponent. -/
def dyadicExponent (y : Matrix ι ι (ℤ × ℤ)) : ℕ :=
  Finset.univ.sup fun i => Finset.univ.sup fun j => (- (y i j).2).toNat

def dyadicDenominator (y : Matrix ι ι (ℤ × ℤ)) : ℤ := 2 ^ dyadicExponent y

def dyadicNumerators (y : Matrix ι ι (ℤ × ℤ)) : Matrix ι ι ℤ :=
  fun i j => (y i j).1 * 2 ^ ((y i j).2 + (dyadicExponent y : ℤ)).toNat

theorem dyadicDenominator_pos (y : Matrix ι ι (ℤ × ℤ)) : 0 < dyadicDenominator y :=
  pow_pos (by norm_num) _

theorem scaledMatrix_dyadic (y : Matrix ι ι (ℤ × ℤ)) (i j : ι) :
    scaledMatrix (dyadicNumerators y) (dyadicDenominator y) i j =
      ((y i j).1 : ℝ) * (2 : ℝ) ^ (y i j).2 := by
  have hN : (- (y i j).2).toNat ≤ dyadicExponent y :=
    (Finset.le_sup (f := fun j => (-(y i j).2).toNat) (Finset.mem_univ j)).trans
      (Finset.le_sup (f := fun i => Finset.univ.sup fun j => (-(y i j).2).toNat)
        (Finset.mem_univ i))
  have hnonneg : 0 ≤ (y i j).2 + (dyadicExponent y : ℤ) := by omega
  simp only [scaledMatrix, dyadicNumerators, dyadicDenominator, Int.cast_mul, Int.cast_pow,
    Int.cast_ofNat]
  rw [← zpow_natCast, Int.toNat_of_nonneg hnonneg, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
    zpow_natCast, ← mul_assoc, mul_div_cancel_right₀ _ (pow_ne_zero _ (by norm_num))]

end Rows

def radiusDen : ℤ := 2 ^ 30

noncomputable def radius : ℝ := 1 / (radiusDen : ℝ)

def contractionNumerator (Δ M : ℤ) : ℤ := Δ + 16 * M * (scale ^ 2 / radiusDen)

/-- Consumer of the row bounds at the replay scales. The two strict integer
comparisons are exactly the comparisons in `contract`. The derivative and
its drift refer to the exact analytic map on the whole closed ball. -/
theorem existsUnique_zero_of_replay
    {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (A J : Matrix ι ι ℤ) (f : ι → ℤ) (D E Δ M : ℤ)
    (hD : 0 < D) (hE : 0 ≤ E) (hΔ : 0 ≤ Δ) (hM : 0 ≤ M)
    (F : (ι → ℝ) → (ι → ℝ)) (DF : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ))
    (c : ι → ℝ)
    (hf : ∀ i, |(scale : ℝ) ^ 2 * F c i - (f i : ℝ)| ≤ 120 * (n : ℝ) * (scale : ℝ))
    (hJ : ∀ i j, |(scale : ℝ) ^ 2 * LinearMap.toMatrix' (DF c).toLinearMap i j -
        (J i j : ℝ)| ≤ 420 * (n : ℝ) * (scale : ℝ))
    (he : ∀ i, stepRow scale n A f i ≤ E)
    (hδ : ∀ i, defectRow D scale n A J i ≤ Δ)
    (hy : ∀ i, rowWeight A i ≤ M)
    (hk : contractionNumerator Δ M < denominator D scale)
    (hinclude : E * radiusDen + contractionNumerator Δ M < denominator D scale)
    (hder : ∀ x ∈ Metric.closedBall c radius, HasFDerivAt F (DF x) x)
    (hdrift : ∀ x ∈ Metric.closedBall c radius, ‖DF x - DF c‖ ≤ 16 * ‖x - c‖) :
    ∃! x, x ∈ Metric.closedBall c radius ∧ F x = 0 := by
  obtain ⟨hstep, hdefect, hnorm⟩ :=
    clm_bounds_of_rows hD scale_pos n A J f (F c) (DF c) E Δ M hE hΔ hM hf hJ he hδ hy
  let H : ℝ := (denominator D scale : ℝ)
  let K : ℝ := (contractionNumerator Δ M : ℝ)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hH : 0 < H := by
    have hs : (0 : ℝ) < scale := by exact_mod_cast scale_pos
    simp only [H, denominator, Int.cast_mul, Int.cast_pow]
    exact mul_pos hDR (pow_pos hs _)
  have hq : (0 : ℝ) < radiusDen := by norm_num [radiusDen]
  have hr : 0 < radius := one_div_pos.mpr hq
  have hK : 0 ≤ K := by
    have hnonneg : 0 ≤ contractionNumerator Δ M := by
      unfold contractionNumerator
      exact add_nonneg hΔ (mul_nonneg (mul_nonneg (by norm_num) hM)
        (by norm_num [scale, radiusDen]))
    dsimp only [K]
    exact_mod_cast hnonneg
  have hKlt : K < H := by
    dsimp only [K, H]
    exact_mod_cast hk
  have hInc : (E : ℝ) * (radiusDen : ℝ) + K < H := by
    dsimp only [K, H]
    exact_mod_cast hinclude
  let k : NNReal := NNReal.mk (K / H) (div_nonneg hK hH.le)
  have hquot : ((scale ^ 2 / radiusDen : ℤ) : ℝ) = (scale : ℝ) ^ 2 / (radiusDen : ℝ) := by
    norm_num [scale, radiusDen]
  have hKform : K / H = (Δ : ℝ) / H + (M : ℝ) / (D : ℝ) * 16 * radius := by
    simp only [K, contractionNumerator, Int.cast_add, Int.cast_mul, Int.cast_ofNat, hquot,
      H, denominator, Int.cast_pow, radius]
    have hs : (0 : ℝ) < scale := by exact_mod_cast scale_pos
    field_simp <;> ring
  refine ChirpedRootCertificate.existsUnique_zero_closedBall F DF (preconditioner A D) c radius
    ((Δ : ℝ) / H) 16 k hr.le (by norm_num) ((div_lt_one hH).2 hKlt) hder hdefect hdrift ?_ ?_
  · change (Δ : ℝ) / H + ‖preconditioner A D‖ * 16 * radius ≤ K / H
    rw [hKform]
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnorm (by norm_num)) hr.le)
  · change ‖preconditioner A D (F c)‖ + (K / H) * radius ≤ radius
    have hs : (E : ℝ) / H + (K / H) * radius ≤ radius := by
      calc
        _ = (((E : ℝ) * (radiusDen : ℝ) + K) / H) * radius := by
          unfold radius
          field_simp <;> ring
        _ ≤ 1 * radius := mul_le_mul_of_nonneg_right ((div_le_one hH).2 hInc.le) hr.le
        _ = radius := one_mul _
    exact (add_le_add hstep le_rfl).trans hs


inductive Order
  | n69
  | n73

def Order.dimension : Order → ℕ
  | .n69 => 69
  | .n73 => 73

def Order.parameters : Order → ℕ
  | .n69 => 63
  | .n73 => 37

/-- For each retained coordinate, the left arrays already include the replay's
column permutation. Absent parameter derivatives have zero entries. -/
structure CorrelationRows (ι : Type*) (n : ℕ) (K : Type*) where
  left : ι → Fin n → K
  right : ι → Fin n → K
  leftSlope : ι → ι → Fin n → K
  rightSlope : ι → ι → Fin n → K

namespace CorrelationRows

variable {ι : Type*} {n : ℕ}

def residual (R : CorrelationRows ι n IntComplex) (imag : ι → Bool) (i : ι) : ℤ :=
  projectInt (imag i) (correlationInt (R.left i) (R.right i))

def jacobian (R : CorrelationRows ι n IntComplex) (imag : ι → Bool) : Matrix ι ι ℤ :=
  fun i j => projectInt (imag i)
    (correlationInt (R.leftSlope i j) (R.right i) +
      correlationInt (R.left i) (R.rightSlope i j))

noncomputable def exactResidual (R : CorrelationRows ι n ℂ) (imag : ι → Bool) (i : ι) : ℝ :=
  project (imag i) (correlation (R.left i) (R.right i))

noncomputable def exactJacobian (R : CorrelationRows ι n ℂ) (imag : ι → Bool) : Matrix ι ι ℝ :=
  fun i j => project (imag i)
    (correlation (R.leftSlope i j) (R.right i) + correlation (R.left i) (R.rightSlope i j))

structure SeedBounds (R : CorrelationRows ι n IntComplex) (X : CorrelationRows ι n ℂ) : Prop where
  leftError : ∀ i d, ‖IntComplex.decode scale (R.left i d) - X.left i d‖ ≤ 52 / (scale : ℝ)
  rightError : ∀ i d, ‖IntComplex.decode scale (R.right i d) - X.right i d‖ ≤ 52 / (scale : ℝ)
  leftSlopeError : ∀ i j d,
    ‖IntComplex.decode scale (R.leftSlope i j d) - X.leftSlope i j d‖ ≤ 97 / (scale : ℝ)
  rightSlopeError : ∀ i j d,
    ‖IntComplex.decode scale (R.rightSlope i j d) - X.rightSlope i j d‖ ≤ 97 / (scale : ℝ)
  leftNorm : ∀ i d, ‖X.left i d‖ ≤ 1
  rightNorm : ∀ i d, ‖X.right i d‖ ≤ 1
  leftSlopeNorm : ∀ i j d, ‖X.leftSlope i j d‖ ≤ 2
  rightSlopeNorm : ∀ i j d, ‖X.rightSlope i j d‖ ≤ 2

theorem residual_error {R : CorrelationRows ι n IntComplex} {X : CorrelationRows ι n ℂ}
    (h : SeedBounds R X) (imag : ι → Bool) (i : ι) :
    |(scale : ℝ) ^ 2 * X.exactResidual imag i - (R.residual imag i : ℝ)| ≤
      120 * (n : ℝ) * (scale : ℝ) :=
  projected_error (imag i) _ _ 120
    (correlation_value_error _ _ _ _ (h.leftError i) (h.rightError i) (h.leftNorm i) (h.rightNorm i))

theorem jacobian_error {R : CorrelationRows ι n IntComplex} {X : CorrelationRows ι n ℂ}
    (h : SeedBounds R X) (imag : ι → Bool) (i j : ι) :
    |(scale : ℝ) ^ 2 * X.exactJacobian imag i j - (R.jacobian imag i j : ℝ)| ≤
      420 * (n : ℝ) * (scale : ℝ) :=
  projected_error (imag i) _ _ 420
    (correlation_slope_error _ _ _ _ _ _ _ _ (h.leftError i) (h.rightError i)
      (h.leftSlopeError i j) (h.rightSlopeError i j) (h.leftNorm i) (h.rightNorm i)
      (h.leftSlopeNorm i j) (h.rightSlopeNorm i j))

end CorrelationRows

/-- Entry point for either concrete order. The integer residual and Jacobian
are computed from the same seed arrays that supply the approximation proofs. -/
theorem existsUnique_zero_of_seed_replay (o : Order)
    (R : CorrelationRows (Fin o.parameters) o.dimension IntComplex)
    (X : CorrelationRows (Fin o.parameters) o.dimension ℂ)
    (hseed : CorrelationRows.SeedBounds R X) (imag : Fin o.parameters → Bool)
    (y : Matrix (Fin o.parameters) (Fin o.parameters) (ℤ × ℤ))
    (E Δ M : ℤ) (hE : 0 ≤ E) (hΔ : 0 ≤ Δ) (hM : 0 ≤ M)
    (F : (Fin o.parameters → ℝ) → (Fin o.parameters → ℝ))
    (DF : (Fin o.parameters → ℝ) → (Fin o.parameters → ℝ) →L[ℝ] (Fin o.parameters → ℝ))
    (c : Fin o.parameters → ℝ)
    (hvalue : F c = X.exactResidual imag)
    (hslope : LinearMap.toMatrix' (DF c).toLinearMap = X.exactJacobian imag)
    (he : ∀ i, stepRow scale o.dimension (dyadicNumerators y) (R.residual imag) i ≤ E)
    (hδ : ∀ i, defectRow (dyadicDenominator y) scale o.dimension (dyadicNumerators y)
      (R.jacobian imag) i ≤ Δ)
    (hy : ∀ i, rowWeight (dyadicNumerators y) i ≤ M)
    (hk : contractionNumerator Δ M < denominator (dyadicDenominator y) scale)
    (hinclude : E * radiusDen + contractionNumerator Δ M < denominator (dyadicDenominator y) scale)
    (hder : ∀ x ∈ Metric.closedBall c radius, HasFDerivAt F (DF x) x)
    (hdrift : ∀ x ∈ Metric.closedBall c radius, ‖DF x - DF c‖ ≤ 16 * ‖x - c‖) :
    ∃! x, x ∈ Metric.closedBall c radius ∧ F x = 0 := by
  apply existsUnique_zero_of_replay o.dimension (dyadicNumerators y) (R.jacobian imag)
    (R.residual imag) (dyadicDenominator y) E Δ M (dyadicDenominator_pos y)
    hE hΔ hM F DF c ?_ ?_ he hδ hy hk hinclude hder hdrift
  · rw [hvalue]
    exact CorrelationRows.residual_error hseed imag
  · rw [hslope]
    exact CorrelationRows.jacobian_error hseed imag

#print axioms existsUnique_zero_of_seed_replay

end ChirpedReplay
