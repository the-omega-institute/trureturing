/- GID: D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Centered masks have exact two-projection spectra and affine covariance. -/

import D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.SharpConstants

/-!
Exact centered mask geometry for the five-point Fourier measurement.
The Fourier amplitudes use the normalized inverse QFT, as in FourierFiveBasis.
-/

open InnerProductSpace QuantumPhaseEstimationGeneral
open D5.S3.Constants.PentagonCosines
open scoped BigOperators ComplexConjugate InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.FiveDimensionalFourierThreshold

abbrev GeometryRow := Idx ⊕ Idx

abbrev residue := ZMod.finEquiv 5

private theorem phase_norm (a : ZMod 5) : ‖pentagonPhase a‖ = 1 := by
  rw [ZMod.stdAddChar_apply, Circle.norm_coe]

theorem phase_neg (a : ZMod 5) : conj (pentagonPhase a) = pentagonPhase (-a) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj]
  simp [ZMod.stdAddChar_apply]

def geometryAmplitude (x : CoordinateFive) : GeometryRow → ℂ :=
  Sum.elim (fun i => x i) (fun j => (fourierRepr 5 (by decide) x) j)

theorem geometryAmplitude_eq_inner (x : CoordinateFive) (i : GeometryRow) :
    geometryAmplitude x i =
      ⟪Sum.elim (fun j => coordinateBasisFive j) (fun j => fourierBasisFive j) i, x⟫_ℂ := by
  cases i with
  | inl j =>
    change x j = ⟪coordinateBasisFive j, x⟫_ℂ
    rw [← OrthonormalBasis.repr_apply_apply, EuclideanSpace.basisFun_repr]
  | inr j =>
    change (fourierRepr 5 (by decide) x) j = ⟪fourierBasisFive j, x⟫_ℂ
    rw [← OrthonormalBasis.repr_apply_apply]
    rfl

theorem inverse_entry (x : CoordinateFive) (j : Idx) :
    geometryAmplitude x (.inr j) =
      scale 5 * ∑ i : Idx, pentagonPhase (-(residue i * residue j)) * x i := by
  change inverseQFT 5 (WithLp.ofLp x) j = _
  simp only [inverseQFT, kernel_five_eq_pentagonPhase, phase_neg, mul_comm (residue j)]

/-- The permutation induced by multiplication by a unit followed by a residue shift. -/
def affineIndex (u : (ZMod 5)ˣ) (a : ZMod 5) : Idx ≃ Idx :=
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  residue.toEquiv.trans
    ((Equiv.mulLeft₀ (u : ZMod 5) (Units.ne_zero u)).trans
      ((Equiv.addRight a).trans residue.symm.toEquiv))

theorem residue_affineIndex (u : (ZMod 5)ˣ) (a : ZMod 5) (i : Idx) :
    ZMod.finEquiv 5 (affineIndex u a i) = (u : ZMod 5) * ZMod.finEquiv 5 i + a := by
  simp [affineIndex, Equiv.mulLeft₀, Equiv.addRight]

/-- A standard residue dilation by a unit induces the reciprocal dilation on Fourier labels. -/
def affineRows (u : (ZMod 5)ˣ) (a b : ZMod 5) : GeometryRow ≃ GeometryRow :=
  Equiv.sumCongr (affineIndex u a) (affineIndex u⁻¹ b)

/-- Apply dilation, then shift the standard coordinates by `a` and modulate by `b`. -/
def affineState (u : (ZMod 5)ˣ) (a b : ZMod 5) : CoordinateFive ≃ₗᵢ[ℂ] CoordinateFive where
  toLinearEquiv :=
    { toFun := fun x => WithLp.toLp 2 fun j =>
        pentagonPhase (b * residue j) * x ((affineIndex u a).symm j)
      invFun := fun x => WithLp.toLp 2 fun i =>
        pentagonPhase (-(b * residue (affineIndex u a i))) * x (affineIndex u a i)
      left_inv := by
        intro x
        ext i
        simp only [Equiv.symm_apply_apply, ← mul_assoc,
          ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
      right_inv := by
        intro x
        ext i
        simp only [Equiv.apply_symm_apply, ← mul_assoc,
          ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]
      map_add' := by intro x y; ext i; simp [PiLp.add_apply, mul_add]
      map_smul' := by intro c x; ext i; simp [PiLp.smul_apply, smul_eq_mul, mul_left_comm] }
  norm_map' := by
    intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    change ‖WithLp.toLp 2 (fun j =>
      pentagonPhase (b * residue j) * x ((affineIndex u a).symm j))‖ ^ 2 = ‖x‖ ^ 2
    simp only [EuclideanSpace.norm_sq_eq, norm_mul, phase_norm, one_mul]
    exact (affineIndex u a).symm.sum_comp (fun i => ‖x i‖ ^ 2)

/-- Both transported amplitudes acquire a row phase, shared by every input state. -/
def affineRowPhase (u : (ZMod 5)ˣ) (a b : ZMod 5) : GeometryRow → ℂ :=
  Sum.elim (fun i => pentagonPhase (b * residue (affineIndex u a i)))
    (fun j => pentagonPhase (-(a * ((↑(u⁻¹) : ZMod 5) * residue j))))

theorem norm_affineRowPhase (u : (ZMod 5)ˣ) (a b : ZMod 5) (i : GeometryRow) :
    ‖affineRowPhase u a b i‖ = 1 := by cases i <;> exact phase_norm _

theorem geometryAmplitude_affine (u : (ZMod 5)ˣ) (a b : ZMod 5)
    (x : CoordinateFive) (i : GeometryRow) :
    geometryAmplitude (affineState u a b x) (affineRows u a b i) =
      affineRowPhase u a b i * geometryAmplitude x i := by
  cases i with
  | inl i =>
    change pentagonPhase (b * residue (affineIndex u a i)) *
      x ((affineIndex u a).symm (affineIndex u a i)) = _
    rw [Equiv.symm_apply_apply]
    rfl
  | inr j =>
    change geometryAmplitude (affineState u a b x) (.inr (affineIndex u⁻¹ b j)) = _
    rw [inverse_entry, inverse_entry]
    change scale 5 *
      (∑ k : Idx, pentagonPhase (-(residue k * residue (affineIndex u⁻¹ b j))) *
        (pentagonPhase (b * residue k) * x ((affineIndex u a).symm k))) =
      pentagonPhase (-(a * ((↑(u⁻¹) : ZMod 5) * residue j))) *
        (scale 5 * ∑ k : Idx, pentagonPhase (-(residue k * residue j)) * x k)
    rw [mul_left_comm _ (scale 5)]
    apply congrArg (scale 5 * ·)
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (affineIndex u a).symm _ _ ?_
    intro k
    obtain ⟨k, rfl⟩ := (affineIndex u a).surjective k
    simp only [Equiv.symm_apply_apply, residue_affineIndex, ← mul_assoc,
      ← AddChar.map_add_eq_mul]
    have hu : (↑u : ZMod 5) * ↑(u⁻¹) = 1 := Units.mul_inv u
    congr 2
    calc
      _ = -((↑u : ZMod 5) * ↑(u⁻¹)) * (residue k * residue j) -
          a * (↑(u⁻¹) * residue j) := by ring
      _ = _ := by rw [hu]; ring

/-- The operator of a selected set of measurement rows. -/
def geometryMask (s : Finset GeometryRow) : CoordinateFive →ₗ[ℂ] CoordinateFive :=
  ∑ i ∈ s, (innerSL ℂ
    (Sum.elim (fun j => coordinateBasisFive j) (fun j => fourierBasisFive j) i)).toLinearMap.smulRight
      (Sum.elim (fun j => coordinateBasisFive j) (fun j => fourierBasisFive j) i)

theorem inner_geometryMask (s : Finset GeometryRow) (x y : CoordinateFive) :
    ⟪x, geometryMask s y⟫_ℂ =
      ∑ i ∈ s, conj (geometryAmplitude x i) * geometryAmplitude y i := by
  simp only [geometryMask, LinearMap.sum_apply, LinearMap.smulRight_apply, ContinuousLinearMap.coe_coe,
    innerSL_apply_apply, inner_sum, inner_smul_right, geometryAmplitude_eq_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_conj_symm, mul_comm]

theorem geometryMask_affine (u : (ZMod 5)ˣ) (a b : ZMod 5) (s : Finset GeometryRow)
    (x : CoordinateFive) :
    geometryMask (s.map (affineRows u a b).toEmbedding) (affineState u a b x) =
      affineState u a b (geometryMask s x) := by
  apply ext_inner_left ℂ
  intro z
  obtain ⟨y, rfl⟩ := (affineState u a b).surjective z
  rw [LinearIsometryEquiv.inner_map_map, inner_geometryMask, inner_geometryMask, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Equiv.toEmbedding_apply, geometryAmplitude_affine, map_mul]
  have hp := Complex.mul_conj (affineRowPhase u a b i)
  rw [Complex.normSq_eq_norm_sq, norm_affineRowPhase, one_pow, Complex.ofReal_one] at hp
  calc
    _ = (affineRowPhase u a b i * conj (affineRowPhase u a b i)) *
      (conj (geometryAmplitude y i) * geometryAmplitude x i) := by ring
    _ = _ := by rw [hp, one_mul]

theorem sqrt_five_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

private theorem pentagonPhase_one_parts :
    (pentagonPhase 1).re = (Real.sqrt 5 - 1) / 4 ∧
      (pentagonPhase 1).im = Real.sin (2 * Real.pi / 5) := by
  have he : pentagonPhase 1 = Complex.exp ((2 * Real.pi / 5 : ℝ) * Complex.I) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    congr 1
    have hv : (1 : ZMod 5).val = 1 := by decide
    rw [hv]
    push_cast
    ring
  rw [he, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have h := pentagon_golden_cosines.2.1
  rw [Real.inv_goldenRatio, Real.goldenConj] at h
  exact ⟨by linarith only [h], rfl⟩

private theorem phase_four : pentagonPhase 4 = conj (pentagonPhase 1) := by
  rw [phase_neg, show -(1 : ZMod 5) = 4 by decide]

theorem scale_five_re : scale 5 = ((Real.sqrt 5)⁻¹ : ℝ) := by
  change ((Real.sqrt (↑(5 : ℕ))) : ℂ)⁻¹ = _
  push_cast
  rfl

private theorem scaled_phase_even :
    scale 5 * (pentagonPhase 4 + pentagonPhase 1) = (sharpB : ℂ) := by
  have hs : 0 < Real.sqrt (5 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hg : 2 < Real.sqrt (5 : ℝ) := by linarith [sharp_sqrt_five_bounds.1]
  have hb : (Real.sqrt 5 - 1) / (2 * Real.sqrt 5) = sharpB := by
    apply (sq_eq_sq₀ (div_nonneg (by linarith) (by positivity) :
      0 ≤ (Real.sqrt 5 - 1) / (2 * Real.sqrt 5)) (Real.sqrt_nonneg _)).1
    change ((Real.sqrt 5 - 1) / (2 * Real.sqrt 5)) ^ 2 = sharpB ^ 2
    rw [sharpB_sq, sharpD]
    field_simp
    nlinarith only [sqrt_five_sq]
  apply Complex.ext
  · rw [phase_four, scale_five_re]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.conj_re, zero_mul, sub_zero, pentagonPhase_one_parts.1]
    rw [← hb]
    field_simp
    ring
  · rw [phase_four, scale_five_re]
    simp [Complex.mul_im]

private theorem scaled_phase_odd :
    Complex.I * (scale 5 * (pentagonPhase 4 - pentagonPhase 1)) = (sharpSigma : ℂ) := by
  have hs : 0 < Real.sqrt (5 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsin : 0 < Real.sin (2 * Real.pi / 5) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hc : Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
    have h := pentagon_golden_cosines.2.1
    rw [Real.inv_goldenRatio, Real.goldenConj] at h
    linarith only [h]
  have hσ : 2 * Real.sin (2 * Real.pi / 5) / Real.sqrt 5 = sharpSigma := by
    apply (sq_eq_sq₀ (by positivity : 0 ≤ 2 * Real.sin (2 * Real.pi / 5) / Real.sqrt 5)
      (Real.sqrt_nonneg _)).1
    change (2 * Real.sin (2 * Real.pi / 5) / Real.sqrt 5) ^ 2 =
      (Real.sqrt ((5 + Real.sqrt 5) / 10)) ^ 2
    rw [Real.sq_sqrt (by positivity)]
    rw [div_pow, sqrt_five_sq]
    have ht := Real.sin_sq_add_cos_sq (2 * Real.pi / 5)
    rw [hc] at ht
    nlinarith only [ht, sqrt_five_sq]
  apply Complex.ext
  · rw [phase_four, scale_five_re, ← hσ]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_im, Complex.conj_im, Complex.mul_im, pentagonPhase_one_parts.2]
    ring
  · rw [phase_four, scale_five_re]
    simp [Complex.mul_im, Complex.mul_re]

/-- The pair shared by the two bases of the centered representatives. -/
def centeredPair : Finset Idx := {2, 3}

/-- The two selected pairs of the rank-four centered mask. -/
def centeredRankFour : Finset GeometryRow :=
  centeredPair.disjSum centeredPair

/-- The computational triple and Fourier pair of the rank-five centered mask. -/
def centeredRankFive : Finset GeometryRow :=
  centeredPairᶜ.disjSum centeredPair

def rootHalf : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

theorem rootHalf_sq : rootHalf ^ 2 = (1 / 2 : ℂ) := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold rootHalf
  calc
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ 2 = ↑(((Real.sqrt 2)⁻¹) ^ 2) := by push_cast; rfl
    _ = ↑((1 / 2 : ℝ)) := by rw [inv_pow, h, one_div]
    _ = (1 / 2 : ℂ) := by norm_num

private theorem conj_rootHalf : conj rootHalf = rootHalf := by simp [rootHalf]

/-- The symmetric and antisymmetric computational vectors of the selected pair. -/
def centeredStandard (odd : Bool) : CoordinateFive :=
  rootHalf • (coordinateBasisFive 2 +
    (if odd then (-1 : ℂ) else 1) • coordinateBasisFive 3)

/-- The corresponding Fourier vectors, phased so that both principal overlaps are positive. -/
def centeredFourier (odd : Bool) : CoordinateFive :=
  ((if odd then Complex.I else 1) * rootHalf) • (fourierBasisFive 2 +
    (if odd then (-1 : ℂ) else 1) • fourierBasisFive 3)

def centeredOverlap (odd : Bool) : ℝ := if odd then sharpSigma else sharpB

def centeredComplementOverlap (odd : Bool) : ℝ := if odd then sharpH else sharpC

theorem centeredOverlap_sq_add (odd : Bool) :
    centeredOverlap odd ^ 2 + centeredComplementOverlap odd ^ 2 = 1 := by
  cases odd
  · simp [centeredOverlap, centeredComplementOverlap, sharpB_sq, sharpD_eq]
  · simpa [centeredOverlap, centeredComplementOverlap, add_comm] using sharp_h_sigma_sq

theorem centeredComplementOverlap_pos (odd : Bool) :
    0 < centeredComplementOverlap odd := by
  cases odd
  · exact sharpC_pos
  · exact lt_trans (by norm_num) sharp_h_bounds.1

private theorem centeredOverlap_mem (odd : Bool) :
    0 < centeredOverlap odd ∧ centeredOverlap odd < 1 := by
  cases odd
  · exact ⟨lt_trans (by norm_num) sharp_b_bounds.1, lt_trans sharp_b_bounds.2 (by norm_num)⟩
  · exact ⟨lt_trans (by norm_num) sharp_sigma_bounds.1, lt_trans sharp_sigma_bounds.2 (by norm_num)⟩

theorem centeredComplementOverlap_lt_one (odd : Bool) :
    centeredComplementOverlap odd < 1 := by
  cases odd
  · exact sharpC_lt_one
  · exact lt_trans sharp_h_bounds.2 (by norm_num)

theorem centeredStandard_orthonormal : Orthonormal ℂ centeredStandard := by
  rw [orthonormal_iff_ite]
  intro i j
  cases i <;> cases j <;>
    simp only [centeredStandard, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
      orthonormal_iff_ite.mp coordinateBasisFive.orthonormal, conj_rootHalf, Bool.false_eq_true,
      Bool.true_eq_false, ite_true, ite_false, map_one, map_neg] <;>
    norm_num <;> linear_combination 2 * rootHalf_sq

private theorem centeredFourier_orthonormal : Orthonormal ℂ centeredFourier := by
  rw [orthonormal_iff_ite]
  intro i j
  cases i <;> cases j <;>
    simp only [centeredFourier, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
      orthonormal_iff_ite.mp fourierBasisFive.orthonormal, conj_rootHalf, Bool.false_eq_true,
      Bool.true_eq_false, ite_true, ite_false, map_one, map_neg, map_mul, Complex.conj_I] <;>
    norm_num <;> ring_nf <;>
    simp [rootHalf_sq, show Complex.I ^ 2 = -1 by simpa only [pow_two] using Complex.I_mul_I]

private theorem centered_cross_entries :
    ⟪coordinateBasisFive 2, fourierBasisFive 2⟫_ℂ = scale 5 * pentagonPhase 4 ∧
    ⟪coordinateBasisFive 2, fourierBasisFive 3⟫_ℂ = scale 5 * pentagonPhase 1 ∧
    ⟪coordinateBasisFive 3, fourierBasisFive 2⟫_ℂ = scale 5 * pentagonPhase 1 ∧
    ⟪coordinateBasisFive 3, fourierBasisFive 3⟫_ℂ = scale 5 * pentagonPhase 4 := by
  simp only [five_cross_entry, kernel_five_eq_pentagonPhase]
  exact ⟨congrArg (fun a => scale 5 * pentagonPhase a) (by decide),
    congrArg (fun a => scale 5 * pentagonPhase a) (by decide),
    congrArg (fun a => scale 5 * pentagonPhase a) (by decide),
    congrArg (fun a => scale 5 * pentagonPhase a) (by decide)⟩

theorem inner_centeredStandard_fourier (i j : Bool) :
    ⟪centeredStandard i, centeredFourier j⟫_ℂ =
      if i = j then (centeredOverlap i : ℂ) else 0 := by
  obtain ⟨haa, hab, hba, hbb⟩ := centered_cross_entries
  cases i <;> cases j <;>
    simp only [centeredStandard, centeredFourier, centeredOverlap, inner_smul_left, inner_smul_right,
      inner_add_left, inner_add_right, conj_rootHalf, haa, hab, hba, hbb, Bool.false_eq_true,
      Bool.true_eq_false, ite_true, ite_false, map_one, map_neg] <;>
    first
    | linear_combination scaled_phase_even +
        (2 * scale 5 * (pentagonPhase 4 + pentagonPhase 1)) * rootHalf_sq
    | linear_combination scaled_phase_odd +
        (2 * Complex.I * scale 5 * (pentagonPhase 4 - pentagonPhase 1)) * rootHalf_sq
    | ring

private theorem inner_centeredFourier_standard (i j : Bool) :
    ⟪centeredFourier i, centeredStandard j⟫_ℂ =
      if j = i then (centeredOverlap j : ℂ) else 0 := by
  rw [← inner_conj_symm, inner_centeredStandard_fourier]
  split_ifs <;> simp

def rowProjection (p : CoordinateFive) : CoordinateFive →ₗ[ℂ] CoordinateFive :=
  (rankOne ℂ p p).toLinearMap

theorem rowProjection_apply (p x : CoordinateFive) :
    rowProjection p x = ⟪p, x⟫_ℂ • p := rfl

private def pairProjection (p : Bool → CoordinateFive) : CoordinateFive →ₗ[ℂ] CoordinateFive :=
  ∑ i, rowProjection (p i)

private theorem pairProjection_apply (p : Bool → CoordinateFive) (x : CoordinateFive) :
    pairProjection p x = ∑ i, ⟪p i, x⟫_ℂ • p i := by
  simp only [pairProjection, LinearMap.sum_apply, rowProjection_apply]

def P := pairProjection centeredStandard
def Q := pairProjection centeredFourier

private theorem P_standard (i : Bool) : P (centeredStandard i) = centeredStandard i := by
  simp [P, pairProjection_apply, orthonormal_iff_ite.mp centeredStandard_orthonormal,
    ite_smul, Finset.sum_ite_eq']

private theorem Q_fourier (i : Bool) : Q (centeredFourier i) = centeredFourier i := by
  simp [Q, pairProjection_apply, orthonormal_iff_ite.mp centeredFourier_orthonormal,
    ite_smul, Finset.sum_ite_eq']

theorem P_fourier (i : Bool) :
    P (centeredFourier i) = (centeredOverlap i : ℂ) • centeredStandard i := by
  simp [P, pairProjection_apply, inner_centeredStandard_fourier, ite_smul, Finset.sum_ite_eq']

theorem Q_standard (i : Bool) :
    Q (centeredStandard i) = (centeredOverlap i : ℂ) • centeredFourier i := by
  simp [Q, pairProjection_apply, inner_centeredFourier_standard, ite_smul, Finset.sum_ite_eq]

private theorem scaled_signed_pair (x y : CoordinateFive) (c : ℂ) (hc : conj c * c = 1) :
    rowProjection (rootHalf • (x + y)) +
      rowProjection ((c * rootHalf) • (x + (-1 : ℂ) • y)) =
      rowProjection x + rowProjection y := by
  ext z : 1
  simp only [LinearMap.add_apply, rowProjection_apply, inner_smul_left, inner_add_left,
    conj_rootHalf, map_mul, map_neg, map_one]
  match_scalars
  · linear_combination (rootHalf ^ 2 * (⟪x, z⟫_ℂ - ⟪y, z⟫_ℂ)) * hc +
      (2 * ⟪x, z⟫_ℂ) * rootHalf_sq
  · linear_combination (rootHalf ^ 2 * (⟪y, z⟫_ℂ - ⟪x, z⟫_ℂ)) * hc +
      (2 * ⟪y, z⟫_ℂ) * rootHalf_sq

theorem P_eq_rows : P = rowProjection (coordinateBasisFive 2) +
    rowProjection (coordinateBasisFive 3) := by
  unfold P pairProjection
  rw [Fintype.sum_bool]
  rw [add_comm]
  simpa only [centeredStandard, Bool.false_eq_true, ite_false, ite_true, one_smul, one_mul] using
    scaled_signed_pair (coordinateBasisFive 2) (coordinateBasisFive 3) 1 (by simp)

theorem Q_eq_rows : Q = rowProjection (fourierBasisFive 2) +
    rowProjection (fourierBasisFive 3) := by
  unfold Q pairProjection
  rw [Fintype.sum_bool]
  rw [add_comm]
  simpa only [centeredFourier, Bool.false_eq_true, ite_false, ite_true, one_smul, one_mul] using
    scaled_signed_pair (fourierBasisFive 2) (fourierBasisFive 3) Complex.I
      (by simp [Complex.conj_I, Complex.I_mul_I])

private theorem geometryMask_disjSum (I J : Finset Idx) :
    geometryMask (I.disjSum J) =
      (∑ i ∈ I, rowProjection (coordinateBasisFive i)) +
        (∑ j ∈ J, rowProjection (fourierBasisFive j)) := by
  unfold geometryMask
  rw [Finset.sum_disjSum]
  rfl

theorem centeredRankFour_eq : geometryMask centeredRankFour = P + Q := by
  rw [centeredRankFour, geometryMask_disjSum, P_eq_rows, Q_eq_rows]
  simp [centeredPair, Finset.sum_pair (by decide : (2 : Idx) ≠ 3)]

private theorem sum_coordinate_projection :
    (∑ i : Idx, rowProjection (coordinateBasisFive i)) = LinearMap.id := by
  ext x : 1
  simpa only [LinearMap.sum_apply, rowProjection_apply, LinearMap.id_apply] using
    coordinateBasisFive.sum_repr' x

private theorem centeredRankFive_eq : geometryMask centeredRankFive = LinearMap.id - P + Q := by
  rw [centeredRankFive, geometryMask_disjSum, P_eq_rows, Q_eq_rows]
  have hc := Finset.sum_compl_add_sum centeredPair
    (fun i => rowProjection (coordinateBasisFive i))
  rw [sum_coordinate_projection] at hc
  rw [eq_sub_of_add_eq hc]
  simp [centeredPair, Finset.sum_pair (by decide : (2 : Idx) ≠ 3)]

/-- The normalized component of the Fourier principal vector outside the computational pair. -/
def centeredOutside (i : Bool) : CoordinateFive :=
  ((centeredComplementOverlap i : ℂ)⁻¹) •
    (centeredFourier i - (centeredOverlap i : ℂ) • centeredStandard i)

private theorem complementOverlap_ne (i : Bool) : (centeredComplementOverlap i : ℂ) ≠ 0 := by
  exact_mod_cast (centeredComplementOverlap_pos i).ne'

private theorem centered_sq_add_complex (i : Bool) :
    (centeredOverlap i : ℂ) ^ 2 + (centeredComplementOverlap i : ℂ) ^ 2 = 1 := by
  exact_mod_cast centeredOverlap_sq_add i

theorem P_outside (i : Bool) : P (centeredOutside i) = 0 := by
  simp [centeredOutside, P_fourier, P_standard]

private theorem Q_outside (i : Bool) :
    Q (centeredOutside i) = (centeredComplementOverlap i : ℂ) • centeredFourier i := by
  have h := complementOverlap_ne i
  have hcoef : (centeredComplementOverlap i : ℂ)⁻¹ * (1 - (centeredOverlap i : ℂ)^2) =
      (centeredComplementOverlap i : ℂ) := by
    field_simp
    linear_combination -centered_sq_add_complex i
  simp only [centeredOutside, map_smul, map_sub, Q_fourier, Q_standard]
  rw [smul_smul, ← pow_two]
  conv_lhs =>
    arg 2
    arg 1
    rw [← one_smul ℂ (centeredFourier i)]
  rw [← sub_smul, smul_smul, hcoef]

private theorem outside_decomp (i : Bool) :
    centeredFourier i - (centeredOverlap i : ℂ) • centeredStandard i =
      (centeredComplementOverlap i : ℂ) • centeredOutside i := by
  simp [centeredOutside, smul_smul, mul_inv_cancel₀ (complementOverlap_ne i)]

private theorem inner_centeredOutside_fourier (i j : Bool) :
    ⟪centeredOutside i, centeredFourier j⟫_ℂ =
      if i = j then (centeredComplementOverlap i : ℂ) else 0 := by
  simp only [centeredOutside, inner_smul_left, inner_sub_left, map_inv₀, Complex.conj_ofReal,
    orthonormal_iff_ite.mp centeredFourier_orthonormal, inner_centeredStandard_fourier]
  split_ifs with h
  · field_simp [complementOverlap_ne i]
    linear_combination -centered_sq_add_complex i
  · ring

private theorem inner_centeredOutside_standard (i j : Bool) :
    ⟪centeredOutside i, centeredStandard j⟫_ℂ = 0 := by
  simp only [centeredOutside, inner_smul_left, inner_sub_left, map_inv₀, Complex.conj_ofReal,
    orthonormal_iff_ite.mp centeredStandard_orthonormal, inner_centeredFourier_standard]
  by_cases h : i = j
  · subst j
    simp
  · simp [h, Ne.symm h]

private theorem centeredOutside_orthonormal : Orthonormal ℂ centeredOutside := by
  rw [orthonormal_iff_ite]
  intro i j
  conv_lhs =>
    arg 3
    unfold centeredOutside
  simp only [inner_smul_right, inner_sub_right, inner_centeredOutside_fourier,
    inner_centeredOutside_standard, mul_zero, sub_zero]
  split_ifs with h
  · subst j
    exact inv_mul_cancel₀ (complementOverlap_ne i)
  · exact mul_zero _

def centeredMask (five : Bool) : Finset GeometryRow :=
  if five then centeredRankFive else centeredRankFour

private def standardProjection (five : Bool) : CoordinateFive →ₗ[ℂ] CoordinateFive :=
  if five then LinearMap.id - P else P

private theorem centeredMask_eq (five : Bool) :
    geometryMask (centeredMask five) = standardProjection five + Q := by
  cases five
  · exact centeredRankFour_eq
  · exact centeredRankFive_eq

def principalStandard (five odd : Bool) : CoordinateFive :=
  if five then centeredOutside odd else centeredStandard odd

def principalOverlap (five odd : Bool) : ℝ :=
  if five then centeredComplementOverlap odd else centeredOverlap odd

theorem principalOverlap_mem (five odd : Bool) :
    0 < principalOverlap five odd ∧ principalOverlap five odd < 1 := by
  cases five
  · exact centeredOverlap_mem odd
  · exact ⟨centeredComplementOverlap_pos odd, centeredComplementOverlap_lt_one odd⟩

private theorem principalStandard_orthonormal (five : Bool) :
    Orthonormal ℂ (principalStandard five) := by
  cases five
  · exact centeredStandard_orthonormal
  · exact centeredOutside_orthonormal

private theorem principal_inner (five i j : Bool) :
    ⟪principalStandard five i, centeredFourier j⟫_ℂ =
      if i = j then (principalOverlap five i : ℂ) else 0 := by
  cases five
  · exact inner_centeredStandard_fourier i j
  · exact inner_centeredOutside_fourier i j

private theorem principal_inner_flip (five i j : Bool) :
    ⟪centeredFourier i, principalStandard five j⟫_ℂ =
      if j = i then (principalOverlap five j : ℂ) else 0 := by
  rw [← inner_conj_symm, principal_inner]
  split_ifs <;> simp

private theorem standardProjection_principal (five i : Bool) :
    standardProjection five (principalStandard five i) = principalStandard five i := by
  cases five
  · exact P_standard i
  · change centeredOutside i - P (centeredOutside i) = centeredOutside i
    rw [P_outside, sub_zero]

private theorem standardProjection_fourier (five i : Bool) :
    standardProjection five (centeredFourier i) =
      (principalOverlap five i : ℂ) • principalStandard five i := by
  cases five
  · exact P_fourier i
  · change centeredFourier i - P (centeredFourier i) = _
    rw [P_fourier]
    exact outside_decomp i

theorem Q_principal (five i : Bool) :
    Q (principalStandard five i) = (principalOverlap five i : ℂ) • centeredFourier i := by
  cases five
  · exact Q_standard i
  · exact Q_outside i

def principalSign (plus : Bool) : ℝ := if plus then 1 else -1

/-- The norm of the sum or difference of the two unit principal vectors. -/
def principalLength (five odd plus : Bool) : ℝ :=
  Real.sqrt (2 * (1 + principalSign plus * principalOverlap five odd))

theorem principalLength_pos (five odd plus : Bool) : 0 < principalLength five odd plus := by
  apply Real.sqrt_pos.2
  have hr := principalOverlap_mem five odd
  cases plus <;> simp [principalSign] <;> linarith

theorem principalLength_sq (five odd plus : Bool) :
    (principalLength five odd plus : ℂ) ^ 2 =
      2 * (1 + (principalSign plus : ℂ) * (principalOverlap five odd : ℂ)) := by
  have h : 0 ≤ 2 * (1 + principalSign plus * principalOverlap five odd) := by
    have hr := principalOverlap_mem five odd
    cases plus <;> simp [principalSign] <;> linarith
  exact_mod_cast Real.sq_sqrt h

/-- Normalized even or odd principal ray. The final flag selects the upper eigenvalue. -/
def centeredRay (five odd plus : Bool) : CoordinateFive :=
  ((principalLength five odd plus : ℂ)⁻¹) •
    (principalStandard five odd + (principalSign plus : ℂ) • centeredFourier odd)

private theorem centeredRay_orthonormal (five : Bool) :
    Orthonormal ℂ (fun i : Bool × Bool => centeredRay five i.1 i.2) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i, s⟩ ⟨j, t⟩
  by_cases hij : i = j
  · subst j
    have hne (u : Bool) : (principalLength five i u : ℂ) ≠ 0 := by
      exact_mod_cast (principalLength_pos five i u).ne'
    cases s <;> cases t <;>
      simp only [centeredRay, principalSign, inner_smul_left, inner_smul_right, inner_add_left,
        inner_add_right, map_inv₀, Complex.conj_ofReal,
        orthonormal_iff_ite.mp (principalStandard_orthonormal five),
        orthonormal_iff_ite.mp centeredFourier_orthonormal, principal_inner, principal_inner_flip,
        Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, Complex.ofReal_one,
        Complex.ofReal_neg, map_one, map_neg, Prod.mk.injEq, true_and]
    · field_simp [hne]
      have h := principalLength_sq five i false
      simp [principalSign] at h
      linear_combination -h
    · ring
    · ring
    · field_simp [hne]
      have h := principalLength_sq five i true
      simp [principalSign] at h
      linear_combination -h
  · have hp : (i, s) ≠ (j, t) := fun h => hij (congrArg Prod.fst h)
    simp only [centeredRay, hp, hij, Ne.symm hij, inner_smul_left, inner_smul_right, inner_add_left,
      inner_add_right, orthonormal_iff_ite.mp (principalStandard_orthonormal five),
      orthonormal_iff_ite.mp centeredFourier_orthonormal, principal_inner, principal_inner_flip,
      ite_false, mul_zero, add_zero]

private theorem centeredRay_eigen (five i plus : Bool) :
    geometryMask (centeredMask five) (centeredRay five i plus) =
      ((1 + principalSign plus * principalOverlap five i : ℝ) : ℂ) • centeredRay five i plus := by
  rw [centeredMask_eq, centeredRay]
  simp only [map_smul, map_add, LinearMap.add_apply, standardProjection_principal,
    standardProjection_fourier, Q_principal, Q_fourier, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_mul]
  cases plus <;> simp only [principalSign, Bool.false_eq_true, ite_false, ite_true,
    Complex.ofReal_one, Complex.ofReal_neg] <;> module

/-- The difference of the standard and Fourier projections on the centered mask. -/
def centeredProjectionDifference (five : Bool) : CoordinateFive →ₗ[ℂ] CoordinateFive :=
  standardProjection five - Q

/-- The factor coupling the two rays in each principal plane. -/
def centeredCoupling (five odd : Bool) : ℝ :=
  if five then centeredOverlap odd else centeredComplementOverlap odd

private theorem centeredCoupling_pos (five odd : Bool) : 0 < centeredCoupling five odd := by
  cases five
  · exact centeredComplementOverlap_pos odd
  · exact (centeredOverlap_mem odd).1

private theorem principalLength_ratio (five odd plus : Bool) :
    (1 + principalSign plus * principalOverlap five odd) * principalLength five odd (!plus) =
      centeredCoupling five odd * principalLength five odd plus := by
  have hs (b : Bool) :
      0 < 1 + principalSign b * principalOverlap five odd := by
    have h := principalOverlap_mem five odd
    cases b <;> simp [principalSign] <;> linarith
  have hsq (b : Bool) : principalLength five odd b ^ 2 =
      2 * (1 + principalSign b * principalOverlap five odd) :=
    Real.sq_sqrt (mul_nonneg (by norm_num) (hs b).le)
  have hadd := centeredOverlap_sq_add odd
  have hprod :
      (1 + principalSign plus * principalOverlap five odd) *
        (1 + principalSign (!plus) * principalOverlap five odd) = centeredCoupling five odd ^ 2 := by
    cases five <;> cases plus <;>
      simp [principalSign, principalOverlap, centeredCoupling] <;> nlinarith only [hadd]
  apply (sq_eq_sq₀ (mul_pos (hs plus) (principalLength_pos five odd (!plus))).le
    (mul_pos (centeredCoupling_pos five odd) (principalLength_pos five odd plus)).le).1
  rw [mul_pow, mul_pow, hsq, hsq]
  calc
    _ = 2 * (1 + principalSign plus * principalOverlap five odd) *
        ((1 + principalSign plus * principalOverlap five odd) *
          (1 + principalSign (!plus) * principalOverlap five odd)) := by ring
    _ = _ := by rw [hprod]; ring

theorem centeredProjectionDifference_ray (five odd plus : Bool) :
    centeredProjectionDifference five (centeredRay five odd plus) =
      (centeredCoupling five odd : ℂ) • centeredRay five odd (!plus) := by
  let L (s : Bool) : ℂ := principalLength five odd s
  have hL (s : Bool) : L s ≠ 0 := by
    dsimp [L]
    exact_mod_cast (principalLength_pos five odd s).ne'
  have hratio : (1 + (principalSign plus : ℂ) * (principalOverlap five odd : ℂ)) * L (!plus) =
      (centeredCoupling five odd : ℂ) * L plus := by
    dsimp [L]
    exact_mod_cast principalLength_ratio five odd plus
  have halg :
      (L plus)⁻¹ * (1 + (principalSign plus : ℂ) * (principalOverlap five odd : ℂ)) =
        (centeredCoupling five odd : ℂ) * (L (!plus))⁻¹ := by
    field_simp [hL]
    linear_combination hratio
  simp only [centeredProjectionDifference, centeredRay, map_smul, map_add, LinearMap.sub_apply,
    standardProjection_principal, standardProjection_fourier, Q_principal, Q_fourier]
  change (L plus)⁻¹ •
    (principalStandard five odd - (principalOverlap five odd : ℂ) • centeredFourier odd +
      (principalSign plus : ℂ) •
        ((principalOverlap five odd : ℂ) • principalStandard five odd - centeredFourier odd)) =
    (centeredCoupling five odd : ℂ) • (L (!plus))⁻¹ •
      (principalStandard five odd + (principalSign (!plus) : ℂ) • centeredFourier odd)
  rw [smul_smul, ← halg, ← smul_smul]
  congr 1
  cases plus <;>
    simp only [principalSign, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ite_true, ite_false, Complex.ofReal_one, Complex.ofReal_neg] <;> module

/-- The two principal channels and a fifth vector perpendicular to both channels. -/
abbrev CenteredEigenIndex := Option (Bool × Bool)

private theorem centeredBasis_exists (five : Bool) :
    ∃ b : OrthonormalBasis CenteredEigenIndex ℂ CoordinateFive,
      ∀ i s : Bool, b (some (i, s)) = centeredRay five i s := by
  let S : Set CenteredEigenIndex := Set.range some
  let v : CenteredEigenIndex → CoordinateFive :=
    fun k => Option.elim k 0 (fun i => centeredRay five i.1 i.2)
  have hcard : Module.finrank ℂ CoordinateFive = Fintype.card CenteredEigenIndex := by
    rw [finrank_euclideanSpace]
    decide
  have hv : Orthonormal ℂ (S.domRestrict v) := by
    let f : S → Bool × Bool := fun x => Option.get x.1 (by
      obtain ⟨k, hk⟩ := x.2
      rw [← hk]
      rfl)
    have hf : Function.Injective f := by
      rintro ⟨x, ⟨i, rfl⟩⟩ ⟨y, ⟨j, rfl⟩⟩ h
      change i = j at h
      subst j
      rfl
    convert (centeredRay_orthonormal five).comp f hf using 1
    funext x
    obtain ⟨k, hk⟩ := x.2
    cases x with
    | mk x hx =>
      dsimp at hk
      subst x
      rfl
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq hcard
  exact ⟨b, fun i s => hb (some (i, s)) ⟨(i, s), rfl⟩⟩

/-- An orthonormal eigenbasis with positive principal phases in the four two-projection channels. -/
def centeredEigenbasis (five : Bool) : OrthonormalBasis CenteredEigenIndex ℂ CoordinateFive :=
  (centeredBasis_exists five).choose

theorem centeredEigenbasis_some (five i s : Bool) :
    centeredEigenbasis five (some (i, s)) = centeredRay five i s :=
  (centeredBasis_exists five).choose_spec i s

private theorem inner_centered_kernel (five i : Bool) :
    ⟪principalStandard five i, centeredEigenbasis five none⟫_ℂ = 0 ∧
      ⟪centeredFourier i, centeredEigenbasis five none⟫_ℂ = 0 := by
  have h (s : Bool) : ⟪centeredRay five i s, centeredEigenbasis five none⟫_ℂ = 0 := by
    rw [← centeredEigenbasis_some]
    exact (centeredEigenbasis five).orthonormal.inner_eq_zero (by simp)
  have hsign (s : Bool) :
      ⟪principalStandard five i, centeredEigenbasis five none⟫_ℂ +
        (principalSign s : ℂ) * ⟪centeredFourier i, centeredEigenbasis five none⟫_ℂ = 0 := by
    have hn : (principalLength five i s : ℂ) ≠ 0 := by
      exact_mod_cast (principalLength_pos five i s).ne'
    simpa only [centeredRay, inner_smul_left, inner_add_left, map_inv₀, Complex.conj_ofReal,
      mul_eq_zero, inv_eq_zero, hn, false_or] using h s
  have hp := hsign true
  have hm := hsign false
  simp [principalSign] at hp hm
  exact ⟨by linear_combination (hp + hm) / 2, by linear_combination (hp - hm) / 2⟩

def centeredEigenvalue (five : Bool) : CenteredEigenIndex → ℝ
  | none => if five then 1 else 0
  | some (odd, plus) => 1 + principalSign plus * principalOverlap five odd

/-- Exact eigenvalues of the rank-four projection sum and the rank-five projection sum. -/
theorem centeredEigenbasis_apply (five : Bool) (i : CenteredEigenIndex) :
    geometryMask (centeredMask five) (centeredEigenbasis five i) =
      (centeredEigenvalue five i : ℂ) • centeredEigenbasis five i := by
  cases i with
  | some i =>
    rcases i with ⟨odd, plus⟩
    rw [centeredEigenbasis_some]
    exact centeredRay_eigen five odd plus
  | none =>
    have hq : Q (centeredEigenbasis five none) = 0 := by
      simp [Q, pairProjection_apply, (inner_centered_kernel five _).2]
    have hp (i : Bool) :
        ⟪centeredStandard i, centeredEigenbasis five none⟫_ℂ = 0 := by
      cases five
      · exact (inner_centered_kernel false i).1
      · have h := (inner_centered_kernel true i).1
        change ⟪centeredOutside i, centeredEigenbasis true none⟫_ℂ = 0 at h
        have hn : (centeredOverlap i : ℂ) ≠ 0 := by
          exact_mod_cast (centeredOverlap_mem i).1.ne'
        simpa only [centeredOutside, inner_smul_left, inner_sub_left, complementOverlap_ne i,
          (inner_centered_kernel true i).2, hn, map_inv₀, Complex.conj_ofReal, mul_eq_zero,
          inv_eq_zero, false_or, zero_sub, neg_eq_zero] using h
    have hp' : P (centeredEigenbasis five none) = 0 := by
      simp [P, pairProjection_apply, hp]
    rw [centeredMask_eq, LinearMap.add_apply, hq, add_zero]
    cases five
    · simpa [standardProjection, centeredEigenvalue] using hp'
    · simp [standardProjection, centeredEigenvalue, hp']

/-- The exact orthonormal eigenbasis on any translated, modulated and dilated centered mask. -/
theorem affine_centeredEigenbasis_apply (five : Bool) (i : CenteredEigenIndex)
    (u : (ZMod 5)ˣ) (a b : ZMod 5) :
    geometryMask ((centeredMask five).map (affineRows u a b).toEmbedding)
      (affineState u a b (centeredEigenbasis five i)) =
      (centeredEigenvalue five i : ℂ) • affineState u a b (centeredEigenbasis five i) := by
  rw [geometryMask_affine, centeredEigenbasis_apply]
  exact (affineState u a b).map_smul _ _

/-- The measured mass is the Rayleigh form of the actual two-basis mask. -/
theorem geometryMask_mass (s : Finset GeometryRow) (x : CoordinateFive) :
    (⟪x, geometryMask s x⟫_ℂ).re =
      maskMass (basisLaw coordinateBasisFive fourierBasisFive x) s := by
  rw [inner_geometryMask]
  unfold maskMass
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq,
    geometryAmplitude_eq_inner]
  cases i <;> rfl

/-- Row weights and both scalar coefficients can travel unchanged with the row labels.
This applies to the phase-sensitive residual as well as to the Born law. -/
theorem geometryRowEnergy_affine (u : (ZMod 5)ˣ) (a b : ZMod 5)
    (x y : CoordinateFive) (i : GeometryRow) (α β : ℂ) :
    ‖α * geometryAmplitude (affineState u a b x) (affineRows u a b i) -
      β * geometryAmplitude (affineState u a b y) (affineRows u a b i)‖ ^ 2 =
    ‖α * geometryAmplitude x i - β * geometryAmplitude y i‖ ^ 2 := by
  rw [geometryAmplitude_affine, geometryAmplitude_affine]
  rw [show α * (affineRowPhase u a b i * geometryAmplitude x i) -
      β * (affineRowPhase u a b i * geometryAmplitude y i) =
    affineRowPhase u a b i * (α * geometryAmplitude x i - β * geometryAmplitude y i) by ring]
  rw [norm_mul, norm_affineRowPhase, one_mul]

theorem geometryMask_compl (s : Finset GeometryRow) :
    geometryMask sᶜ = (2 : ℂ) • LinearMap.id - geometryMask s := by
  have hfull : geometryMask Finset.univ = (2 : ℂ) • LinearMap.id := by
    rw [show (Finset.univ : Finset GeometryRow) = Finset.univ.disjSum Finset.univ by
      ext i; cases i <;> simp, geometryMask_disjSum, sum_coordinate_projection]
    have hf : (∑ i : Idx, rowProjection (fourierBasisFive i)) = LinearMap.id := by
      ext x : 1
      simpa only [LinearMap.sum_apply, rowProjection_apply, LinearMap.id_apply] using
        fourierBasisFive.sum_repr' x
    rw [hf]
    module
  have h := Finset.sum_compl_add_sum s (fun i : GeometryRow =>
    (innerSL ℂ (Sum.elim (fun j => coordinateBasisFive j) (fun j => fourierBasisFive j) i)).toLinearMap.smulRight
      (Sum.elim (fun j => coordinateBasisFive j) (fun j => fourierBasisFive j) i))
  change geometryMask sᶜ + geometryMask s = geometryMask Finset.univ at h
  rw [hfull] at h
  exact eq_sub_of_add_eq h

/-- Complementing a transported mask retains the eigenvectors and reverses the centered
eigenvalues. This gives the rank-five orientation with a standard pair and Fourier triple. -/
theorem affine_centeredEigenbasis_compl_apply (five : Bool) (i : CenteredEigenIndex)
    (u : (ZMod 5)ˣ) (a b : ZMod 5) :
    geometryMask (((centeredMask five).map (affineRows u a b).toEmbedding)ᶜ)
      (affineState u a b (centeredEigenbasis five i)) =
      (2 - (centeredEigenvalue five i : ℂ)) • affineState u a b (centeredEigenbasis five i) := by
  rw [geometryMask_compl, LinearMap.sub_apply, affine_centeredEigenbasis_apply]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, sub_smul]

/-- The mass of a centered mask is the exact diagonal form in its orthonormal eigenbasis. -/
theorem centeredMask_mass_spectral (five : Bool) (x : CoordinateFive) :
    maskMass (basisLaw coordinateBasisFive fourierBasisFive x) (centeredMask five) =
      ∑ i, centeredEigenvalue five i * ‖⟪centeredEigenbasis five i, x⟫_ℂ‖ ^ 2 := by
  rw [← geometryMask_mass, ← (centeredEigenbasis five).sum_repr' x, map_sum, inner_sum,
    Complex.re_sum]
  have hx : (∑ i, ⟪centeredEigenbasis five i, x⟫_ℂ • centeredEigenbasis five i) = x :=
    (centeredEigenbasis five).sum_repr' x
  simp only [hx]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, centeredEigenbasis_apply, inner_smul_right, inner_smul_right, ← inner_conj_symm x]
  rw [show ⟪centeredEigenbasis five i, x⟫_ℂ *
      (↑(centeredEigenvalue five i) * conj ⟪centeredEigenbasis five i, x⟫_ℂ) =
    ↑(centeredEigenvalue five i) *
      (⟪centeredEigenbasis five i, x⟫_ℂ * conj ⟪centeredEigenbasis five i, x⟫_ℂ) by ring]
  rw [Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

end D5.S3.Quantum.Information.FiveDimensionalFourierThreshold
