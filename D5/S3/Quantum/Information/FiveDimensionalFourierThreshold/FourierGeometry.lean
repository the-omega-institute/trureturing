/- GID: D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact row masses and leverage bounds on centered and critical Fourier masks. -/

import D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.FourierGeometryCore

/-! Individual row masses, weighted amplitude estimates, and the critical affine orbit. -/

open InnerProductSpace QuantumPhaseEstimationGeneral
open D5.S3.Constants.PentagonCosines
open scoped BigOperators ComplexConjugate InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.FiveDimensionalFourierThreshold

private theorem inner_rowProjection_basis (b : OrthonormalBasis Idx ℂ CoordinateFive)
    (j k : Idx) (x : CoordinateFive) :
    ⟪b j, rowProjection (b k) x⟫_ℂ =
      if j = k then ⟪b k, x⟫_ℂ else 0 := by
  simp only [rowProjection_apply, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
  split_ifs <;> simp

private theorem centered_pair_coeff_projection (b : OrthonormalBasis Idx ℂ CoordinateFive)
    {j : Idx} (hj : j ∈ centeredPair) (x : CoordinateFive) :
    ⟪b j, (rowProjection (b 2) + rowProjection (b 3)) x⟫_ℂ = ⟪b j, x⟫_ℂ := by
  simp only [centeredPair, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl <;>
    simp [inner_add_right, inner_rowProjection_basis]

private theorem centeredP_amplitude {j : Idx} (hj : j ∈ centeredPair) (x : CoordinateFive) :
    geometryAmplitude (P x) (.inl j) = geometryAmplitude x (.inl j) := by
  simpa only [P_eq_rows, geometryAmplitude_eq_inner, Sum.elim_inl] using
    centered_pair_coeff_projection coordinateBasisFive hj x

theorem centeredQ_amplitude {j : Idx} (hj : j ∈ centeredPair) (x : CoordinateFive) :
    geometryAmplitude (Q x) (.inr j) = geometryAmplitude x (.inr j) := by
  simpa only [Q_eq_rows, geometryAmplitude_eq_inner, Sum.elim_inr] using
    centered_pair_coeff_projection fourierBasisFive hj x

private theorem rootHalf_norm_sq : ‖rootHalf‖ ^ 2 = (1 / 2 : ℝ) := by
  have h := congrArg Complex.re rootHalf_sq
  simpa only [rootHalf, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    ← Complex.ofReal_pow, Complex.ofReal_re, Complex.div_ofNat_re, Complex.one_re] using h

private theorem centered_pair_norm_std (odd : Bool) {j : Idx} (hj : j ∈ centeredPair) :
    ‖geometryAmplitude (centeredStandard odd) (.inl j)‖ ^ 2 = 1 / 2 := by
  simp only [centeredPair, Finset.mem_insert, Finset.mem_singleton] at hj
  rw [geometryAmplitude_eq_inner, Sum.elim_inl]
  rcases hj with rfl | rfl <;> cases odd <;>
    simp only [centeredStandard, Bool.false_eq_true, ite_true, ite_false, inner_smul_right,
      inner_add_right, orthonormal_iff_ite.mp coordinateBasisFive.orthonormal] <;>
    norm_num [norm_neg, rootHalf_norm_sq]

theorem centered_pair_norm_fourier (odd : Bool) {j : Idx} (hj : j ∈ centeredPair) :
    ‖geometryAmplitude (centeredFourier odd) (.inr j)‖ ^ 2 = 1 / 2 := by
  simp only [centeredPair, Finset.mem_insert, Finset.mem_singleton] at hj
  rw [geometryAmplitude_eq_inner, Sum.elim_inr]
  rcases hj with rfl | rfl <;> cases odd <;>
    simp only [centeredFourier, Bool.false_eq_true, ite_true, ite_false, inner_smul_right,
      inner_add_right, orthonormal_iff_ite.mp fourierBasisFive.orthonormal] <;>
    norm_num [norm_mul, norm_neg, Complex.norm_I, rootHalf_norm_sq]

theorem principalLength_sq_real (five odd plus : Bool) :
    principalLength five odd plus ^ 2 =
      2 * (1 + principalSign plus * principalOverlap five odd) := by
  exact_mod_cast principalLength_sq five odd plus

/-- Each selected Fourier pair row carries one half of the principal ray's Fourier
mass on the pair, in both ranks. -/
theorem centeredRay_fourier_pair_mass (five odd plus : Bool) {j : Idx}
    (hj : j ∈ centeredPair) :
    ‖geometryAmplitude (centeredRay five odd plus) (.inr j)‖ ^ 2 =
      (1 + principalSign plus * principalOverlap five odd) / 4 := by
  have hap :
      geometryAmplitude (principalStandard five odd) (.inr j) =
        (principalOverlap five odd : ℂ) * geometryAmplitude (centeredFourier odd) (.inr j) := by
    rw [← centeredQ_amplitude hj (principalStandard five odd), Q_principal]
    simp only [geometryAmplitude_eq_inner, inner_smul_right]
  have hv :
      geometryAmplitude (centeredRay five odd plus) (.inr j) =
        (principalLength five odd plus : ℂ)⁻¹ *
          (((principalOverlap five odd : ℂ) + (principalSign plus : ℂ)) *
            geometryAmplitude (centeredFourier odd) (.inr j)) := by
    have h := hap
    rw [geometryAmplitude_eq_inner] at h
    simp only [centeredRay, geometryAmplitude_eq_inner, inner_smul_right, inner_add_right, h]
    ring
  rw [hv, ← Complex.ofReal_add, norm_mul, norm_mul, mul_pow, mul_pow,
    centered_pair_norm_fourier odd hj, norm_inv, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, inv_pow, sq_abs, sq_abs, principalLength_sq_real]
  have hn : 1 + principalSign plus * principalOverlap five odd ≠ 0 := by
    have h := principalOverlap_mem five odd
    cases plus <;> simp [principalSign] <;> linarith
  field_simp
  cases plus <;> simp [principalSign] <;> ring

/-- In rank five the computational pair is omitted. Each row of that omitted pair has
the complementary share of the corresponding principal ray. -/
theorem centeredRankFive_ray_standard_pair_mass (odd plus : Bool) {j : Idx}
    (hj : j ∈ centeredPair) :
    ‖geometryAmplitude (centeredRay true odd plus) (.inl j)‖ ^ 2 =
      (1 - principalSign plus * centeredComplementOverlap odd) / 4 := by
  have hp : geometryAmplitude (centeredOutside odd) (.inl j) = 0 := by
    rw [← centeredP_amplitude hj (centeredOutside odd), P_outside]
    simp [geometryAmplitude_eq_inner]
  have hq :
      geometryAmplitude (centeredFourier odd) (.inl j) =
        (centeredOverlap odd : ℂ) * geometryAmplitude (centeredStandard odd) (.inl j) := by
    rw [← centeredP_amplitude hj (centeredFourier odd), P_fourier]
    simp only [geometryAmplitude_eq_inner, inner_smul_right]
  have hv :
      geometryAmplitude (centeredRay true odd plus) (.inl j) =
        (principalLength true odd plus : ℂ)⁻¹ *
          ((principalSign plus : ℂ) * ((centeredOverlap odd : ℂ) *
            geometryAmplitude (centeredStandard odd) (.inl j))) := by
    rw [geometryAmplitude_eq_inner] at hp hq
    simp only [centeredRay, principalStandard, ite_true, geometryAmplitude_eq_inner, inner_smul_right,
      inner_add_right, hp, hq, zero_add]
  rw [hv, norm_mul, norm_mul, norm_mul, mul_pow, mul_pow, mul_pow, centered_pair_norm_std odd hj,
    norm_inv, Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, Real.norm_eq_abs, inv_pow, sq_abs, sq_abs, sq_abs, principalLength_sq_real]
  change (2 * (1 + principalSign plus * centeredComplementOverlap odd))⁻¹ *
      (principalSign plus ^ 2 * (centeredOverlap odd ^ 2 * (1 / 2))) = _
  have hn : 1 + principalSign plus * centeredComplementOverlap odd ≠ 0 := by
    have h₁ := centeredComplementOverlap_pos odd
    have h₂ := centeredComplementOverlap_lt_one odd
    cases plus <;> simp [principalSign] <;> linarith
  field_simp
  cases plus <;> simp [principalSign] <;> nlinarith only [centeredOverlap_sq_add odd]

private theorem zero_entry (j : Idx) :
    ⟪coordinateBasisFive 0, fourierBasisFive j⟫_ℂ = scale 5 ∧
      ⟪fourierBasisFive 0, coordinateBasisFive j⟫_ℂ = scale 5 := by
  have h₀ : residue (0 : Idx) = 0 := by decide
  constructor
  · rw [five_cross_entry, kernel_five_eq_pentagonPhase, h₀, zero_mul,
      AddChar.map_zero_eq_one, mul_one]
  · rw [← inner_conj_symm, five_cross_entry, kernel_five_eq_pentagonPhase, h₀, mul_zero,
      AddChar.map_zero_eq_one, mul_one, scale_conj]

theorem norm_center_coefficient :
    ‖rootHalf * (2 * scale 5)‖ ^ 2 = (2 / 5 : ℝ) := by
  have hs : ‖scale 5‖ ^ 2 = (1 / 5 : ℝ) := by
    rw [scale_five_re, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, sqrt_five_sq]
    norm_num
  rw [norm_mul, norm_mul, mul_pow, mul_pow, rootHalf_norm_sq, hs]
  norm_num

theorem centeredStandard_zero (odd : Bool) :
    geometryAmplitude (centeredStandard odd) (.inl 0) = 0 ∧
      geometryAmplitude (centeredStandard odd) (.inr 0) =
        if odd then 0 else rootHalf * (2 * scale 5) := by
  constructor
  · rw [geometryAmplitude_eq_inner, Sum.elim_inl]
    cases odd <;>
      simp only [centeredStandard, Bool.false_eq_true, ite_true, ite_false, inner_smul_right,
        inner_add_right, orthonormal_iff_ite.mp coordinateBasisFive.orthonormal] <;> norm_num
  · rw [geometryAmplitude_eq_inner, Sum.elim_inr]
    cases odd <;>
      simp only [centeredStandard, inner_add_right, inner_smul_right, (zero_entry _).2,
        Bool.false_eq_true, ite_true, ite_false] <;> ring

private theorem centeredFourier_zero (odd : Bool) :
    geometryAmplitude (centeredFourier odd) (.inl 0) =
      (if odd then 0 else rootHalf * (2 * scale 5)) ∧
      geometryAmplitude (centeredFourier odd) (.inr 0) = 0 := by
  constructor
  · rw [geometryAmplitude_eq_inner, Sum.elim_inl]
    cases odd <;>
      simp only [centeredFourier, inner_add_right, inner_smul_right, (zero_entry _).1,
        Bool.false_eq_true, ite_true, ite_false] <;> ring
  · rw [geometryAmplitude_eq_inner, Sum.elim_inr]
    cases odd <;>
      simp only [centeredFourier, Bool.false_eq_true, ite_true, ite_false, inner_smul_right,
        inner_add_right, orthonormal_iff_ite.mp fourierBasisFive.orthonormal] <;> norm_num

/-- Both odd principal rays have zero center amplitude in each basis. -/
theorem centeredRay_odd_zero (five plus : Bool) :
    geometryAmplitude (centeredRay five true plus) (.inl 0) = 0 ∧
      geometryAmplitude (centeredRay five true plus) (.inr 0) = 0 := by
  have ha := centeredStandard_zero true
  have hb := centeredFourier_zero true
  simp only [geometryAmplitude_eq_inner, ite_true] at ha hb
  cases five <;>
    simp only [geometryAmplitude_eq_inner, centeredRay, principalStandard, ite_true,
      Bool.false_eq_true, ite_false, centeredOutside, inner_smul_right, inner_add_right,
      inner_sub_right, ha.1, ha.2, hb.1, hb.2, mul_zero, add_zero, sub_zero, and_self]

/-- The sum of the reference squared amplitudes on row zero in either basis. -/
def centeredZeroMass : ℝ := (2 / 5) / sharpC ^ 2

theorem centeredZeroMass_eq : centeredZeroMass = (7 - Real.sqrt 5) / 11 := by
  unfold centeredZeroMass
  rw [sharpC_sq]
  have h : 0 < 7 + Real.sqrt (5 : ℝ) := by positivity
  field_simp
  nlinarith only [sqrt_five_sq]

/-- The squared center-row overlaps with both even extreme rays of the rank-five mask. -/
theorem centeredRankFive_ray_zero_mass (plus : Bool) :
    ‖geometryAmplitude (centeredRay true false plus) (.inl 0)‖ ^ 2 =
      (1 + principalSign plus * sharpC) * centeredZeroMass / 2 ∧
    ‖geometryAmplitude (centeredRay true false plus) (.inr 0)‖ ^ 2 =
      (1 - principalSign plus * sharpC) * centeredZeroMass / 2 := by
  obtain ⟨ha₀, ha₁⟩ := centeredStandard_zero false
  obtain ⟨hb₀, hb₁⟩ := centeredFourier_zero false
  simp only [geometryAmplitude_eq_inner, Bool.false_eq_true, ite_false] at ha₀ ha₁ hb₀ hb₁
  let d : ℂ := rootHalf * (2 * scale 5)
  let L : ℝ := principalLength true false plus
  have hstd :
      geometryAmplitude (centeredRay true false plus) (.inl 0) =
        ((L : ℂ)⁻¹ * (((sharpC : ℂ)⁻¹ + (principalSign plus : ℂ)))) * d := by
    simp only [centeredRay, principalStandard, ite_true, centeredOutside, centeredComplementOverlap,
      centeredOverlap, Bool.false_eq_true, ite_false, geometryAmplitude_eq_inner, inner_smul_right,
      inner_add_right, inner_sub_right, ha₀, hb₀, mul_zero, sub_zero, L, d]
    ring
  have hfour :
      geometryAmplitude (centeredRay true false plus) (.inr 0) =
        ((L : ℂ)⁻¹ * (-(sharpC : ℂ)⁻¹ * (sharpB : ℂ))) * d := by
    simp only [centeredRay, principalStandard, ite_true, centeredOutside, centeredComplementOverlap,
      centeredOverlap, Bool.false_eq_true, ite_false, geometryAmplitude_eq_inner, inner_smul_right,
      inner_add_right, inner_sub_right, ha₁, hb₁, mul_zero, zero_sub, add_zero, L, d]
    ring
  have hL : L ^ 2 = 2 * (1 + principalSign plus * sharpC) :=
    principalLength_sq_real true false plus
  have hc : sharpC ≠ 0 := sharpC_pos.ne'
  have hden : 1 + principalSign plus * sharpC ≠ 0 := by
    have h := sharpC_lt_one
    have h' := sharpC_pos
    cases plus <;> simp [principalSign] <;> linarith
  have hd : ‖d‖ ^ 2 = 2 / 5 := norm_center_coefficient
  constructor
  · rw [hstd, ← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_add,
      norm_mul, norm_mul, mul_pow, mul_pow,
      hd, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      sq_abs, inv_pow, hL]
    unfold centeredZeroMass
    field_simp
  · rw [hfour, ← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
      norm_mul, norm_mul, mul_pow, mul_pow, hd, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, inv_pow, hL, mul_pow, neg_pow,
      inv_pow]
    unfold centeredZeroMass
    field_simp
    cases plus <;> simp [principalSign] <;> nlinarith only [sharpB_sq, sharpD_eq]

theorem centered_row_mass_sum (five : Bool) (r : GeometryRow) :
    ∑ i, ‖geometryAmplitude (centeredEigenbasis five i) r‖ ^ 2 = 1 := by
  simp only [geometryAmplitude_eq_inner, (centeredEigenbasis five).sum_sq_norm_inner_left]
  cases r with
  | inl j => simp only [Sum.elim_inl, coordinateBasisFive.norm_eq_one, one_pow]
  | inr j => simp only [Sum.elim_inr, fourierBasisFive.norm_eq_one, one_pow]

/-- The even channel at centered eigenvalue zero carries the rest of the center-row mass. -/
theorem centeredRankFive_middle_zero_mass :
    ‖geometryAmplitude (centeredEigenbasis true none) (.inl 0)‖ ^ 2 = 1 - centeredZeroMass ∧
    ‖geometryAmplitude (centeredEigenbasis true none) (.inr 0)‖ ^ 2 = 1 - centeredZeroMass := by
  have h (r : GeometryRow) := centered_row_mass_sum true r
  simp only [Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool,
    centeredEigenbasis_some] at h
  constructor
  · have h₀ := h (.inl 0)
    rw [(centeredRay_odd_zero true true).1, (centeredRay_odd_zero true false).1,
      (centeredRankFive_ray_zero_mass true).1, (centeredRankFive_ray_zero_mass false).1] at h₀
    simp [principalSign] at h₀
    nlinarith only [h₀]
  · have h₀ := h (.inr 0)
    rw [(centeredRay_odd_zero true true).2, (centeredRay_odd_zero true false).2,
      (centeredRankFive_ray_zero_mass true).2, (centeredRankFive_ray_zero_mass false).2] at h₀
    simp [principalSign] at h₀
    nlinarith only [h₀]

/-- The middle channel has zero weight on the four heavy rows in reflected pairs. -/
theorem centeredRankFive_middle_pair_mass (j : Idx) (hj : j ∈ centeredPair) :
    ‖geometryAmplitude (centeredEigenbasis true none) (.inl j)‖ ^ 2 = 0 ∧
    ‖geometryAmplitude (centeredEigenbasis true none) (.inr j)‖ ^ 2 = 0 := by
  have hs := centered_row_mass_sum true (.inl j)
  have hf := centered_row_mass_sum true (.inr j)
  simp only [Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool,
    centeredEigenbasis_some, centeredRankFive_ray_standard_pair_mass _ _ hj,
    centeredRay_fourier_pair_mass _ _ _ hj, principalSign, Bool.false_eq_true,
    ite_true, ite_false] at hs hf
  exact ⟨by linarith only [hs], by linarith only [hf]⟩

/-- Cauchy–Schwarz with inverse spectral gaps bounds the error in an individual row.
Take `t` to be the non-reference channels and `g` their gaps from the reference eigenvalue. -/
theorem geometryAmplitude_sq_le_weighted {ι : Type*} (t : Finset ι)
    (v : ι → CoordinateFive) (z : ι → ℂ) (g : ι → ℝ)
    (hg : ∀ i ∈ t, 0 < g i) (row : GeometryRow) :
    ‖geometryAmplitude (∑ i ∈ t, z i • v i) row‖ ^ 2 ≤
      (∑ i ∈ t, ‖geometryAmplitude (v i) row‖ ^ 2 / g i) *
        (∑ i ∈ t, g i * ‖z i‖ ^ 2) := by
  let a (i : ι) := ‖geometryAmplitude (v i) row‖ / Real.sqrt (g i)
  let b (i : ι) := Real.sqrt (g i) * ‖z i‖
  have hsum : geometryAmplitude (∑ i ∈ t, z i • v i) row =
      ∑ i ∈ t, z i * geometryAmplitude (v i) row := by
    simp only [geometryAmplitude_eq_inner, inner_sum, inner_smul_right]
  have hnorm : ‖geometryAmplitude (∑ i ∈ t, z i • v i) row‖ ≤ ∑ i ∈ t, a i * b i := by
    rw [hsum]
    refine (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun i hi => ?_)
    rw [norm_mul]
    dsimp [a, b]
    rw [← mul_assoc, div_mul_cancel₀ _ (Real.sqrt_pos.2 (hg i hi)).ne', mul_comm]
  have ha : ∑ i ∈ t, a i ^ 2 = ∑ i ∈ t, ‖geometryAmplitude (v i) row‖ ^ 2 / g i := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [a]
    rw [div_pow, Real.sq_sqrt (hg i hi).le]
  have hb : ∑ i ∈ t, b i ^ 2 = ∑ i ∈ t, g i * ‖z i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [b]
    rw [mul_pow, Real.sq_sqrt (hg i hi).le]
  calc
    _ ≤ (∑ i ∈ t, a i * b i) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hnorm)).2 hnorm
    _ ≤ _ := by rw [← ha, ← hb]; exact Finset.sum_mul_sq_le_sq_mul_sq t a b

private theorem map_centeredPair (u : (ZMod 5)ˣ) (i j : Idx)
    (h : residue i - residue j = -(u : ZMod 5)) :
    ∃ a : ZMod 5, centeredPair.map (affineIndex u a).toEmbedding = {i, j} := by
  let a := residue i - (u : ZMod 5) * 2
  have h2 : residue (2 : Idx) = 2 := by decide
  have h3 : residue (3 : Idx) = 3 := by decide
  have hi : affineIndex u a 2 = i := by
    apply residue.injective
    rw [residue_affineIndex, h2]
    dsimp [a]
    ring
  have hj : affineIndex u a 3 = j := by
    apply residue.injective
    rw [residue_affineIndex, h3]
    dsimp [a]
    linear_combination h
  exact ⟨a, by simp [centeredPair, hi, hj]⟩

/-- A pair of ordered differences with product ±1 lies in the centered critical orbit.
The same witness transports the rank-four mask and the rank-five mask formed by
complementing its standard pair. -/
theorem criticalPairs_affine (i i' j j' : Idx)
    (h : (residue i - residue i') * (residue j - residue j') = 1 ∨
      (residue i - residue i') * (residue j - residue j') = -1) :
    ∃ (u : (ZMod 5)ˣ) (a b : ZMod 5),
      centeredPair.map (affineIndex u a).toEmbedding = {i, i'} ∧
      centeredPair.map (affineIndex u⁻¹ b).toEmbedding = {j, j'} := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let m := residue i - residue i'
  have hm : m ≠ 0 := by
    intro he
    change m * _ = 1 ∨ m * _ = -1 at h
    simp [he] at h
  let u : (ZMod 5)ˣ := Units.mk0 (-m) (neg_ne_zero.mpr hm)
  have hu : (u : ZMod 5) = -m := rfl
  obtain ⟨a, ha⟩ := map_centeredPair u i i' (by rw [hu, neg_neg])
  have huinv : (u : ZMod 5) * ↑(u⁻¹) = 1 := Units.mul_inv u
  change m * _ = 1 ∨ m * _ = -1 at h
  rcases h with h | h
  · have hj : residue j - residue j' = -(↑(u⁻¹) : ZMod 5) := by
      apply mul_left_cancel₀ hm
      rw [h]
      rw [hu, neg_mul] at huinv
      rw [mul_neg, huinv]
    obtain ⟨b, hb⟩ := map_centeredPair u⁻¹ j j' hj
    exact ⟨u, a, b, ha, hb⟩
  · have hj : residue j' - residue j = -(↑(u⁻¹) : ZMod 5) := by
      apply mul_left_cancel₀ hm
      rw [hu, neg_mul] at huinv
      rw [mul_neg, huinv]
      linear_combination -h
    obtain ⟨b, hb⟩ := map_centeredPair u⁻¹ j' j hj
    exact ⟨u, a, b, ha, by simpa [Finset.pair_comm] using hb⟩

theorem affineRows_map_disjSum (u : (ZMod 5)ˣ) (a b : ZMod 5) (I J : Finset Idx) :
    (I.disjSum J).map (affineRows u a b).toEmbedding =
      (I.map (affineIndex u a).toEmbedding).disjSum (J.map (affineIndex u⁻¹ b).toEmbedding) := by
  ext v
  cases v <;> simp [affineRows, Finset.mem_disjSum]

private theorem map_complement {α : Type*} [Fintype α] [DecidableEq α]
    (e : α ≃ α) (s : Finset α) :
    sᶜ.map e.toEmbedding = (s.map e.toEmbedding)ᶜ := by
  ext v
  obtain ⟨v, rfl⟩ := e.surjective v
  simp

/-- Center both critical pairs at once. This gives the rank-four mask, the rank-five mask
with a standard triple, and, by taking the complement, the opposite rank-five orientation. -/
theorem criticalMasks_affine (i i' j j' : Idx)
    (h : (residue i - residue i') * (residue j - residue j') = 1 ∨
      (residue i - residue i') * (residue j - residue j') = -1) :
    ∃ (u : (ZMod 5)ˣ) (a b : ZMod 5),
      centeredRankFour.map (affineRows u a b).toEmbedding =
        ({i, i'} : Finset Idx).disjSum {j, j'} ∧
      centeredRankFive.map (affineRows u a b).toEmbedding =
        ({i, i'} : Finset Idx)ᶜ.disjSum {j, j'} ∧
      centeredRankFiveᶜ.map (affineRows u a b).toEmbedding =
        ({i, i'} : Finset Idx).disjSum ({j, j'} : Finset Idx)ᶜ := by
  obtain ⟨u, a, b, hi, hj⟩ := criticalPairs_affine i i' j j' h
  have h4 : centeredRankFour.map (affineRows u a b).toEmbedding =
      ({i, i'} : Finset Idx).disjSum {j, j'} := by
    rw [centeredRankFour, affineRows_map_disjSum, hi, hj]
  have h5 : centeredRankFive.map (affineRows u a b).toEmbedding =
      ({i, i'} : Finset Idx)ᶜ.disjSum {j, j'} := by
    rw [centeredRankFive, affineRows_map_disjSum, map_complement, hi, hj]
  refine ⟨u, a, b, h4, h5, ?_⟩
  rw [map_complement, h5]
  ext v
  cases v <;> simp only [Finset.mem_compl, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum, not_not]

end D5.S3.Quantum.Information.FiveDimensionalFourierThreshold
