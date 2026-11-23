/- GID: D5/S3/Quantum/Recovery/LocalCompression/QutritDiagonalResetOptimum
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/LocalCompression/QutritDiagonalResetOptimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact pure Bell-source optimum in the diagonal-reset qutrit compression class. -/

import D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetDistortion

/-! The stationary characteristic polynomial of the matched Bell block. -/

noncomputable section

open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Recovery.LocalCompression.QutritPure
open D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalReset
open D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetDistortion

namespace D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetOptimum

open private explicit_rayleigh from
  D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetDistortion
open private encoder_apply from D5.S3.Quantum.Recovery.LocalCompression.QutritPure

/-- The characteristic polynomial of the matched block at attenuation amplitude `b`. -/
def characteristic (L b : ℝ) : ℝ :=
  L ^ 3 - L ^ 2 - 3 * L - 1 + 2 * (L + 1) * b - 2 * b ^ 3 - (L - 1) * b ^ 4

/-- Solving the stationarity equation in the spectral parameter. -/
def stationaryLambda (b : ℝ) : ℝ :=
  (-4 * b ^ 3 + 6 * b ^ 2 - 2) / (2 - 4 * b ^ 3)

private theorem stationary_denominator_neg {b : ℝ} (hb : 4 / 5 ≤ b) :
    2 - 4 * b ^ 3 < 0 := by
  have hcube : (4 / 5 : ℝ) ^ 3 ≤ b ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hb _
  linarith

private theorem stationary_lambda_gt_one {b : ℝ} (hb : 4 / 5 ≤ b) (hb' : b ≤ 81 / 100) :
    1 < stationaryLambda b := by
  have hsq : b ^ 2 ≤ (81 / 100 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hb' _
  apply (lt_div_iff_of_neg (stationary_denominator_neg hb)).2
  linarith

/-- The zero at the stationary value has a rationally isolated attenuation amplitude.
At that value the characteristic polynomial is negative at every other amplitude in
`[0,1]`. -/
theorem exists_stationary_characteristic :
    ∃ b : ℝ, 0.80680296 < b ∧ b < 0.80680298 ∧
      1 < stationaryLambda b ∧ characteristic (stationaryLambda b) b = 0 ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ b → characteristic (stationaryLambda b) x < 0 := by
  let l : ℝ := 0.80680296
  let u : ℝ := 0.80680298
  let f : ℝ → ℝ := fun b => characteristic (stationaryLambda b) b
  have hlu : l ≤ u := by norm_num [l, u]
  have hl : 0 < f l := by norm_num [f, l, characteristic, stationaryLambda]
  have hu : f u < 0 := by norm_num [f, u, characteristic, stationaryLambda]
  have hcont : ContinuousOn f (Set.Icc l u) := by
    have hstat : ContinuousOn stationaryLambda (Set.Icc l u) := by
      unfold stationaryLambda
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro b hb
      exact (stationary_denominator_neg ((by norm_num [l] : 4 / 5 ≤ l).trans hb.1)).ne
    unfold f characteristic
    fun_prop
  obtain ⟨b, hb, hroot⟩ := intermediate_value_Icc' hlu hcont
    (show (0 : ℝ) ∈ Set.Icc (f u) (f l) from ⟨hu.le, hl.le⟩)
  have hbl : l < b := lt_of_le_of_ne hb.1 fun he => hl.ne' (by simpa only [he] using hroot)
  have hbu : b < u := lt_of_le_of_ne hb.2 fun he => hu.ne (by simpa only [he] using hroot)
  have hlow := (by norm_num [l] : 4 / 5 ≤ l).trans hb.1
  have hhigh := hb.2.trans (by norm_num [u] : u ≤ 81 / 100)
  have hL := stationary_lambda_gt_one hlow hhigh
  have hs : stationaryLambda b * (2 - 4 * b ^ 3) = -4 * b ^ 3 + 6 * b ^ 2 - 2 :=
    div_mul_cancel₀ _ (stationary_denominator_neg hlow).ne
  have hd : 2 * (stationaryLambda b + 1) - 6 * b ^ 2 -
      4 * (stationaryLambda b - 1) * b ^ 3 = 0 := by
    linear_combination hs
  refine ⟨b, hbl, hbu, hL, hroot, ?_⟩
  intro x hx hxb
  have hTaylor :
      characteristic (stationaryLambda b) x =
        -(x - b) ^ 2 * ((stationaryLambda b - 1) * (x ^ 2 + 2 * x * b + 3 * b ^ 2) +
          2 * x + 4 * b) := by
    change characteristic (stationaryLambda b) b = 0 at hroot
    unfold characteristic at hroot ⊢
    linear_combination hroot + (x - b) * hd
  have hx0 := hx.1
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hlow
  have hcoeff : 0 < (stationaryLambda b - 1) * (x ^ 2 + 2 * x * b + 3 * b ^ 2) +
      2 * x + 4 * b := by positivity
  rw [hTaylor]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hxb))) hcoeff

private def shiftedBlock (L b : ℝ) : Matrix Qutrit Qutrit ℝ :=
  L • (1 : Matrix Qutrit Qutrit ℝ) - modelBlock b

private theorem shifted_det (L b : ℝ) : (shiftedBlock L b).det = characteristic L b := by
  rw [Matrix.det_fin_three]
  norm_num [shiftedBlock, modelBlock, Matrix.one_apply, characteristic]
  ring

private theorem shifted_hermitian (L b : ℝ) : (shiftedBlock L b).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shiftedBlock, modelBlock, Matrix.conjTranspose_apply]

private theorem shifted_form (L b : ℝ) (v : Qutrit → ℝ) :
    star v ⬝ᵥ (shiftedBlock L b *ᵥ v) =
      L * (∑ i, v i ^ 2) - quadratic (modelBlock b) v := by
  simp only [shiftedBlock, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, star_trivial]
  congr 1
  · congr 1
    simp [dotProduct, pow_two]
  · simp [quadratic, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

private theorem shifted_psd_at_root {L b : ℝ} (hL : 1 < L) (hb : 4 / 5 ≤ b)
    (hroot : characteristic L b = 0) : (shiftedBlock L b).PosSemidef := by
  let d := L * (L - 1 + b ^ 2) - (1 - b) ^ 2
  have hL0 : 0 < L := by linarith
  have hd : 0 < d := by
    dsimp [d]
    have h : 0 < (L - 1) * (L + b ^ 2) := by positivity
    nlinarith
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (shifted_hermitian L b) fun v => ?_
  have hidentity :
      L * d * (star v ⬝ᵥ (shiftedBlock L b *ᵥ v)) =
        d * (L * v 0 - (1 - b) * v 1 - v 2) ^ 2 +
          (d * v 1 - (L + 1 - b) * v 2) ^ 2 := by
    rw [shifted_form]
    norm_num [quadratic, modelBlock, Fin.sum_univ_three, d]
    unfold characteristic at hroot
    linear_combination L * (v 2) ^ 2 * hroot
  have hsum : 0 ≤ d * (L * v 0 - (1 - b) * v 1 - v 2) ^ 2 +
      (d * v 1 - (L + 1 - b) * v 2) ^ 2 := by positivity
  exact nonneg_of_mul_nonneg_right (hidentity.trans_ge hsum) (mul_pos hL0 hd)

private theorem quadratic_le_of_rayleigh_bound {b L : ℝ}
    (h : ∀ v : Qutrit → ℝ, (∑ i, v i ^ 2) = 1 → quadratic (modelBlock b) v ≤ L)
    (v : Qutrit → ℝ) : quadratic (modelBlock b) v ≤ L * ∑ i, v i ^ 2 := by
  by_cases hv : v = 0
  · simp [hv, quadratic]
  let q : ℝ := ∑ i, v i ^ 2
  have hq : 0 < q := by
    refine lt_of_le_of_ne' (Finset.sum_nonneg (fun i _ => sq_nonneg (v i))) ?_
    intro hz
    exact hv (funext (fun i => (Finset.sum_sq_eq_zero_iff Finset.univ v).mp hz i (Finset.mem_univ i)))
  let r := Real.sqrt q
  have hr : 0 < r := Real.sqrt_pos.2 hq
  have hrq : r ^ 2 = q := Real.sq_sqrt hq.le
  let w : Qutrit → ℝ := fun i => v i / r
  have hw : (∑ i, w i ^ 2) = 1 := by
    simp only [w, div_pow, ← Finset.sum_div]
    change q / r ^ 2 = 1
    rw [hrq, div_self hq.ne']
  have hscale : quadratic (modelBlock b) w = quadratic (modelBlock b) v / r ^ 2 := by
    unfold quadratic
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [w]
    ring
  have hbound := h w hw
  rw [hscale, div_le_iff₀ (sq_pos_of_ne_zero hr.ne'), hrq] at hbound
  exact hbound

private theorem rayleigh_cmp {L b m : ℝ}
    (hmax : IsGreatest {s : ℝ | ∃ v : Qutrit → ℝ, (∑ i, v i ^ 2) = 1 ∧
      quadratic (modelBlock b) v = s} m) :
    (m ≤ L → 0 ≤ characteristic L b) ∧ (m < L → 0 < characteristic L b) := by
  have hbound := quadratic_le_of_rayleigh_bound
    (fun v hv => hmax.2 (show quadratic (modelBlock b) v ∈ _ from ⟨v, hv, rfl⟩))
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · rw [← shifted_det]
    refine (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (shifted_hermitian L b) ?_).det_nonneg
    intro v
    rw [shifted_form, sub_nonneg]
    exact (hbound v).trans (mul_le_mul_of_nonneg_right hm (by positivity))
  · rw [← shifted_det]
    refine (Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨shifted_hermitian L b, ?_⟩).det_pos
    intro v hv
    have hvpos : 0 < ∑ i, v i ^ 2 := by
      refine lt_of_le_of_ne' (by positivity) ?_
      intro hz
      exact hv (funext (fun i => (Finset.sum_sq_eq_zero_iff Finset.univ v).mp hz i (Finset.mem_univ i)))
    rw [shifted_form, sub_pos]
    exact (hbound v).trans_lt (mul_lt_mul_of_pos_right hm hvpos)

private theorem rayleigh_at_root {L b m : ℝ} (hL : 1 < L) (hb : 4 / 5 ≤ b)
    (hroot : characteristic L b = 0)
    (hmax : IsGreatest {s : ℝ | ∃ v : Qutrit → ℝ, (∑ i, v i ^ 2) = 1 ∧
      quadratic (modelBlock b) v = s} m) : m = L := by
  obtain ⟨v, hv, hval⟩ := hmax.1
  have hn := (shifted_psd_at_root hL hb hroot).dotProduct_mulVec_nonneg v
  rw [shifted_form, hv, mul_one, hval, sub_nonneg] at hn
  exact le_antisymm hn (le_of_not_gt fun hm => (rayleigh_cmp hmax).2 hm |>.ne' hroot)

/-- The pure qutrit Bell-source error is attained in the diagonal-reset class.
The attenuating family has a unique minimizing amplitude. -/
theorem pure_diagonal_reset_optimum :
    ∃ (b c : ℝ) (h : b ^ 2 + c ^ 2 = 1),
      0.80680296 < b ∧ b < 0.80680298 ∧ 0 ≤ c ∧
      DiagonalReset encoder 0 ∧
      3 * error ((decoder b c h).comp encoder) = stationaryLambda b ∧
      (∀ (x y : ℝ) (hxy : x ^ 2 + y ^ 2 = 1), x ∈ Set.Icc (0 : ℝ) 1 →
        x ≠ b → error ((decoder b c h).comp encoder) < error ((decoder x y hxy).comp encoder)) ∧
      (∀ (E : QuantumChannel Qutrit Qubit) (D : QuantumChannel Qubit Qutrit) (t : ℝ),
        DiagonalReset E t → error ((decoder b c h).comp encoder) ≤ error (D.comp E)) := by
  obtain ⟨b, hlo, hhi, hL, hroot, hneg⟩ := exists_stationary_characteristic
  have hb : b ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hc : 0 ≤ 1 - b ^ 2 := by nlinarith [mul_nonneg hb.1 (sub_nonneg.mpr hb.2)]
  let c := Real.sqrt (1 - b ^ 2)
  have hbc : b ^ 2 + c ^ 2 = 1 := by rw [Real.sq_sqrt hc]; ring
  have hE : DiagonalReset encoder 0 := by
    refine ⟨le_rfl, zero_le_one, fun X => ?_⟩
    rw [encoder_apply]
    simp
  have hval := rayleigh_at_root hL (by linarith) hroot (explicit_rayleigh b c hbc hb.1 hb.2)
  have hstrict (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hxb : x ≠ b) (m : ℝ)
      (hm : IsGreatest {s : ℝ | ∃ v : Qutrit → ℝ, (∑ i, v i ^ 2) = 1 ∧
        quadratic (modelBlock x) v = s} m) : stationaryLambda b < m :=
    lt_of_not_ge fun hle => (not_le_of_gt (hneg x hx hxb)) ((rayleigh_cmp hm).1 hle)
  refine ⟨b, c, hbc, hlo, hhi, Real.sqrt_nonneg _, hE, hval, ?_, ?_⟩
  · intro x y hxy hx hxb
    have hlt := hstrict x hx hxb _ (explicit_rayleigh x y hxy hx.1 hx.2)
    linarith
  · intro E D t hreset
    obtain ⟨x, y, hxy, hxamp, hx0, hx1, _, hmax, herr⟩ :=
      diagonal_reset_distortion_converse E D t hreset
    clear hxamp
    by_cases he : x = b
    · subst x
      have hsame := rayleigh_at_root hL (by linarith) hroot hmax
      linarith
    · have hlt := hstrict x ⟨hx0, hx1⟩ he _ hmax
      linarith

end D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetOptimum
