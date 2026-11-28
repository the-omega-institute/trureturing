import D5.S3.Quantum.QuantumChannels.CouplingWassersteinTriangleRefutation
import D5.S3.Quantum.Analysis.NullConeGravity.PureGNSExtensionSectors
import D5.S3.Quantum.Foundation.FiniteHermitianTraceDuality

/-!
# Equality in trace-ground coupling transport

Beatty and Stilck França, arXiv:2402.16477v2, Eqs. (62) and (81).
Preregistration: https://github.com/the-omega-institute/trureturing/issues/35123
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000

noncomputable section

namespace D5.S3.Quantum.QuantumChannels.CouplingWassersteinEquality

open Matrix
open scoped ComplexOrder
open CouplingWassersteinTriangleRefutation (UnitVector ground Plan cost wasserstein)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity pure_state_handshake)

variable {n : ℕ}

private abbrev ip (x y : Fin n → ℂ) : ℂ := star x ⬝ᵥ y

private theorem ip_self (x : UnitVector n) : ip x.val x.val = 1 := by
  simp only [ip, dotProduct, Pi.star_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_sum, x.property, Complex.ofReal_one]

private theorem unit_of_ip {x : Fin n → ℂ} (h : ip x x = 1) :
    ∑ i, Complex.normSq (x i) = 1 := by
  simpa only [ip, dotProduct, Pi.star_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_sum, Complex.ofReal_eq_one] using h

private theorem ip_conj (x y : Fin n → ℂ) : star (ip x y) = ip y x := by
  simp [ip, dotProduct, Pi.star_apply, mul_comm]

private theorem ip_sub (x y z : Fin n → ℂ) : ip x (y - z) = ip x y - ip x z :=
  dotProduct_sub _ _ _

private theorem sub_ip (x y z : Fin n → ℂ) : ip (x - y) z = ip x z - ip y z := by
  rw [ip, star_sub, sub_dotProduct]

private theorem ip_smul (c : ℂ) (x y : Fin n → ℂ) : ip x (c • y) = c * ip x y :=
  dotProduct_smul _ _ _

private theorem smul_ip (c : ℂ) (x y : Fin n → ℂ) : ip (c • x) y = star c * ip x y := by
  rw [ip, star_smul, smul_dotProduct]
  rfl

private theorem overlap_le_one (x y : UnitVector n) : ‖ip x.val y.val‖ ≤ 1 := by
  let x' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x.val
  let y' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 y.val
  have hx : ‖x'‖ = 1 := by
    rw [EuclideanSpace.norm_eq, show (∑ i, ‖x' i‖ ^ 2) = 1 by
      simpa only [x', ← Complex.normSq_eq_norm_sq] using x.property, Real.sqrt_one]
  have hy : ‖y'‖ = 1 := by
    rw [EuclideanSpace.norm_eq, show (∑ i, ‖y' i‖ ^ 2) = 1 by
      simpa only [y', ← Complex.normSq_eq_norm_sq] using y.property, Real.sqrt_one]
  have hinner : ip x.val y.val = inner ℂ x' y' := by
    rw [ip, dotProduct_comm]
    rfl
  rw [hinner]
  simpa only [hx, hy, mul_one] using norm_inner_le_norm x' y'

private theorem ground_sq (x y : UnitVector n) :
    ground x y ^ 2 = 1 - ‖ip x.val y.val‖ ^ 2 := by
  change Real.sqrt (1 - Complex.normSq (ip x.val y.val)) ^ 2 = _
  rw [Complex.normSq_eq_norm_sq, Real.sq_sqrt]
  nlinarith [overlap_le_one x y, norm_nonneg (ip x.val y.val)]

private theorem ground_nonneg (x y : UnitVector n) : 0 ≤ ground x y := Real.sqrt_nonneg _

private theorem ground_le_one (x y : UnitVector n) : ground x y ≤ 1 := by
  nlinarith [ground_sq x y, ground_nonneg x y, sq_nonneg ‖ip x.val y.val‖]

private theorem rankOneDensity_phase (d : ℂ) (hd : ‖d‖ = 1) (y : Fin n → ℂ) :
    rankOneDensity (d • y) = rankOneDensity y := by
  have h : d * star d = 1 := by
    rw [Complex.star_def, Complex.mul_conj', hd]
    norm_num
  ext i j
  simp only [rankOneDensity, vecMulVec_apply, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul]
  calc
    (d * y i) * (star (y j) * star d) = (d * star d) * (y i * star (y j)) := by ring
    _ = _ := by rw [h, one_mul]

private theorem align_phase (x y : UnitVector n) :
    ∃ y' : UnitVector n, rankOneDensity y'.val = rankOneDensity y.val ∧
      ip x.val y'.val = (‖ip x.val y.val‖ : ℂ) := by
  let z := ip x.val y.val
  by_cases hz : z = 0
  · exact ⟨y, rfl, by change z = (‖z‖ : ℂ); simp [hz]⟩
  let d := star z / (‖z‖ : ℂ)
  have hd : ‖d‖ = 1 := by
    simp [d, norm_ne_zero_iff.mpr hz]
  have hd' : star d * d = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hd]
    norm_num
  refine ⟨⟨d • y.val, unit_of_ip (by rw [smul_ip, ip_smul, ip_self, mul_one, hd'])⟩,
    rankOneDensity_phase d hd _, ?_⟩
  change ip x.val (d • y.val) = (‖z‖ : ℂ)
  rw [ip_smul]
  change star z / (‖z‖ : ℂ) * z = _
  rw [div_mul_eq_mul_div, Complex.star_def, Complex.conj_mul']
  field_simp [norm_ne_zero_iff.mpr hz]

private def upper (t : ℝ) : ℝ := Real.sqrt ((1 + t) / 2)
private def lower (t : ℝ) : ℝ := Real.sqrt ((1 - t) / 2)

private theorem amplitudes {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    upper t ^ 2 + lower t ^ 2 = 1 ∧ upper t ^ 2 - lower t ^ 2 = t := by
  have ha : upper t ^ 2 = (1 + t) / 2 := Real.sq_sqrt (by linarith)
  have hb : lower t ^ 2 = (1 - t) / 2 := Real.sq_sqrt (by linarith)
  constructor <;> linarith

private theorem amplitude_overlap (x y : UnitVector n) :
    2 * upper (ground x y) * lower (ground x y) = ‖ip x.val y.val‖ := by
  let t := ground x y
  have ha : upper t ^ 2 = (1 + t) / 2 := Real.sq_sqrt (by linarith [ground_nonneg x y])
  have hb : lower t ^ 2 = (1 - t) / 2 := Real.sq_sqrt (by linarith [ground_le_one x y])
  have hnonneg : 0 ≤ 2 * upper t * lower t :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  apply (sq_eq_sq₀ hnonneg (norm_nonneg _)).mp
  calc
    (2 * upper t * lower t) ^ 2 = 4 * upper t ^ 2 * lower t ^ 2 := by ring
    _ = ‖ip x.val y.val‖ ^ 2 := by rw [ha, hb]; nlinarith [ground_sq x y]

/-- Swapped amplitudes in a common pair of rays give a diagonal difference. -/
private theorem swapped_difference (u v : Fin n → ℂ) {a b t : ℝ}
    (ht : a ^ 2 - b ^ 2 = t) :
    rankOneDensity ((a : ℂ) • u + (b : ℂ) • v) -
      rankOneDensity ((b : ℂ) • u + (a : ℂ) • v) =
      (t : ℂ) • (rankOneDensity u - rankOneDensity v) := by
  have h : (a : ℂ) ^ 2 - (b : ℂ) ^ 2 = (t : ℂ) := by exact_mod_cast ht
  ext i j
  simp only [rankOneDensity, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, star_add, star_mul, Complex.star_def, Complex.conj_ofReal]
  linear_combination (u i * (starRingEnd ℂ) (u j) - v i * (starRingEnd ℂ) (v j)) * h

private theorem swapped_representation (x y : UnitVector n)
    (hne : rankOneDensity x.val ≠ rankOneDensity y.val) :
    0 < ground x y ∧ ∃ u v : UnitVector n, ip u.val v.val = 0 ∧
      rankOneDensity x.val =
        rankOneDensity ((upper (ground x y) : ℂ) • u.val + (lower (ground x y) : ℂ) • v.val) ∧
      rankOneDensity y.val =
        rankOneDensity ((lower (ground x y) : ℂ) • u.val + (upper (ground x y) : ℂ) • v.val) := by
  obtain ⟨y', hy', hxy⟩ := align_phase x y
  let t := ground x y
  have ht : 0 < t := by
    refine lt_of_le_of_ne (ground_nonneg x y) ?_
    intro hz
    have hc : ‖ip x.val y.val‖ = 1 := by
      have hs := ground_sq x y
      change t ^ 2 = _ at hs
      rw [← hz] at hs
      nlinarith [norm_nonneg (ip x.val y.val)]
    have he : x.val - y'.val = 0 := by
      apply dotProduct_star_self_eq_zero.mp
      change ip (x.val - y'.val) (x.val - y'.val) = 0
      have hyx := ip_conj x.val y'.val
      rw [hxy, hc] at hyx
      rw [sub_ip, ip_sub, ip_sub, ip_self, ip_self, hxy, hc, ← hyx]
      simp
    exact hne ((congrArg rankOneDensity (sub_eq_zero.mp he)).trans hy')
  refine ⟨ht, ?_⟩
  let a := upper t
  let b := lower t
  have hs : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by
    exact_mod_cast (amplitudes (le_of_lt ht) (ground_le_one x y)).1
  have hd : (a : ℂ) ^ 2 - (b : ℂ) ^ 2 = (t : ℂ) := by
    exact_mod_cast (amplitudes (le_of_lt ht) (ground_le_one x y)).2
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hc : ip x.val y'.val = 2 * (a : ℂ) * (b : ℂ) := by
    rw [hxy]
    exact_mod_cast (amplitude_overlap x y).symm
  have hc' : ip y'.val x.val = 2 * (a : ℂ) * (b : ℂ) := by
    rw [← ip_conj, hc]
    simp
  let u := ((t : ℂ)⁻¹) • ((a : ℂ) • x.val - (b : ℂ) • y'.val)
  let v := ((t : ℂ)⁻¹) • ((a : ℂ) • y'.val - (b : ℂ) • x.val)
  have hu : ip u u = 1 := by
    simp only [u, smul_ip, ip_smul, sub_ip, ip_sub, ip_self, hc, hc',
      star_inv₀, Complex.star_def, Complex.conj_ofReal]
    field_simp
    linear_combination hd * ((a : ℂ) ^ 2 - (b : ℂ) ^ 2 + (t : ℂ)) -
      hs * ((a : ℂ) ^ 2 + (b : ℂ) ^ 2)
  have hv : ip v v = 1 := by
    simp only [v, smul_ip, ip_smul, sub_ip, ip_sub, ip_self, hc, hc',
      star_inv₀, Complex.star_def, Complex.conj_ofReal]
    field_simp
    linear_combination hd * ((a : ℂ) ^ 2 - (b : ℂ) ^ 2 + (t : ℂ)) -
      hs * ((a : ℂ) ^ 2 + (b : ℂ) ^ 2)
  have huv : ip u v = 0 := by
    simp only [u, v, smul_ip, ip_smul, sub_ip, ip_sub, ip_self, hc, hc',
      star_inv₀, Complex.star_def, Complex.conj_ofReal]
    field_simp
    linear_combination (2 * (a : ℂ) * (b : ℂ)) * hs
  have hx : (a : ℂ) • u + (b : ℂ) • v = x.val := by
    funext i
    simp only [u, v, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination x.val i * hd
  have hy : (b : ℂ) • u + (a : ℂ) • v = y'.val := by
    funext i
    simp only [u, v, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination y'.val i * hd
  refine ⟨⟨u, unit_of_ip hu⟩, ⟨v, unit_of_ip hv⟩, huv, ?_, ?_⟩
  · rw [show ((upper t : ℂ) • u + (lower t : ℂ) • v) = x.val from hx]
  · rw [show ((lower t : ℂ) • u + (upper t : ℂ) • v) = y'.val from hy, hy']

private def pairing (H A : Matrix (Fin n) (Fin n) ℂ) : ℝ := (H * A).trace.re / 2

private theorem re_nonneg_zero_iff {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.PosSemidef) (u : Fin n → ℂ) :
    0 ≤ (ip u (M *ᵥ u)).re ∧ ((ip u (M *ᵥ u)).re = 0 ↔ M *ᵥ u = 0) := by
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg u)
  refine ⟨hre, ?_⟩
  rw [← hM.dotProduct_mulVec_zero_iff]
  exact ⟨fun h => Complex.ext h him.symm, fun h => congrArg Complex.re h⟩

private theorem spectral_pairing (H : Matrix (Fin n) (Fin n) ℂ)
    (hminus : (1 - H).PosSemidef) (hplus : (1 + H).PosSemidef)
    (u v : UnitVector n) {t : ℝ} (ht : 0 < t) :
    let A := (t : ℂ) • (rankOneDensity u.val - rankOneDensity v.val)
    pairing H A ≤ t ∧
      (pairing H A = t ↔ H *ᵥ u.val = u.val ∧ H *ᵥ v.val = -v.val) := by
  dsimp only
  have hminus' := re_nonneg_zero_iff hminus u.val
  have hplus' := re_nonneg_zero_iff hplus v.val
  let qu := (ip u.val ((1 - H) *ᵥ u.val)).re
  let qv := (ip v.val ((1 + H) *ᵥ v.val)).re
  have hslack : t - pairing H ((t : ℂ) • (rankOneDensity u.val - rankOneDensity v.val)) =
      (t / 2) * (qu + qv) := by
    unfold pairing qu qv
    rw [Matrix.mul_smul, trace_smul, mul_sub, trace_sub, smul_eq_mul,
      ← (pure_state_handshake u.val (ip_self u) H).2.2,
      ← (pure_state_handshake v.val (ip_self v) H).2.2]
    simp only [sub_mulVec, add_mulVec, one_mulVec, ip_sub, ip_self, dotProduct_add,
      Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, zero_mul, sub_zero, ip]
    ring
  change 0 ≤ qu ∧ (qu = 0 ↔ _) at hminus'
  change 0 ≤ qv ∧ (qv = 0 ↔ _) at hplus'
  have hu : qu = 0 ↔ H *ᵥ u.val = u.val := by
    rw [hminus'.2, sub_mulVec, one_mulVec, sub_eq_zero, eq_comm]
  have hv : qv = 0 ↔ H *ᵥ v.val = -v.val := by
    rw [hplus'.2, add_mulVec, one_mulVec, add_comm, add_eq_zero_iff_eq_neg]
  have ht' : 0 < t / 2 := by positivity
  refine ⟨by linarith [mul_nonneg ht'.le (add_nonneg hminus'.1 hplus'.1)], ?_⟩
  constructor
  · intro h
    have hz : (t / 2) * (qu + qv) = 0 := by linarith
    have hsum := (mul_eq_zero.mp hz).resolve_left ht'.ne'
    exact ⟨hu.mp (by linarith [hminus'.1, hplus'.1]), hv.mp (by linarith [hminus'.1, hplus'.1])⟩
  · rintro ⟨hu', hv'⟩
    rw [hu.mpr hu', hv.mpr hv', add_zero, mul_zero] at hslack
    linarith

/-- Equality against a fixed Hermitian contraction precisely requires shared swapped
amplitudes on its two extremal eigenspaces. -/
theorem fixed_pair_equality (x y : UnitVector n)
    (hne : rankOneDensity x.val ≠ rankOneDensity y.val)
    (H : Matrix (Fin n) (Fin n) ℂ) (hminus : (1 - H).PosSemidef)
    (hplus : (1 + H).PosSemidef) :
    let t := ground x y
    let A := rankOneDensity x.val - rankOneDensity y.val
    0 < t ∧ t ≤ 1 ∧ pairing H A ≤ t ∧
      (pairing H A = t ↔
        ∃ u v : UnitVector n, ip u.val v.val = 0 ∧ H *ᵥ u.val = u.val ∧
          H *ᵥ v.val = -v.val ∧
          rankOneDensity x.val =
            rankOneDensity ((upper t : ℂ) • u.val + (lower t : ℂ) • v.val) ∧
          rankOneDensity y.val =
            rankOneDensity ((lower t : ℂ) • u.val + (upper t : ℂ) • v.val)) := by
  dsimp only
  obtain ⟨ht, u, v, huv, hx, hy⟩ := swapped_representation x y hne
  have ht' := ground_le_one x y
  have hd := (amplitudes ht.le ht').2
  have hA : rankOneDensity x.val - rankOneDensity y.val =
      (ground x y : ℂ) • (rankOneDensity u.val - rankOneDensity v.val) :=
    (congrArg₂ (· - ·) hx hy).trans (swapped_difference u.val v.val hd)
  refine ⟨ht, ht', ?_, ?_⟩
  · rw [hA]
    exact (spectral_pairing H hminus hplus u v ht).1
  · constructor
    · intro h
      rw [hA] at h
      obtain ⟨hu, hv⟩ := (spectral_pairing H hminus hplus u v ht).2.mp h
      exact ⟨u, v, huv, hu, hv, hx, hy⟩
    · rintro ⟨u', v', _, hu', hv', hx', hy'⟩
      have hA' : rankOneDensity x.val - rankOneDensity y.val =
          (ground x y : ℂ) • (rankOneDensity u'.val - rankOneDensity v'.val) :=
        (congrArg₂ (· - ·) hx' hy').trans (swapped_difference u'.val v'.val hd)
      rw [hA']
      exact (spectral_pairing H hminus hplus u' v' ht).2.mpr ⟨hu', hv'⟩


private def phaseX : UnitVector 2 :=
  ⟨![4 / 5, (3 / 5) * Complex.I], by
    norm_num [Fin.sum_univ_two, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]⟩

private def phaseY (c : ℂ) (hc : Complex.normSq c = 16 / 25) : UnitVector 2 :=
  ⟨![3 / 5, c], by
    have hc' : c.re * c.re + c.im * c.im = 16 / 25 := hc
    norm_num [Fin.sum_univ_two, Complex.normSq_apply, hc']⟩

private def sharedY : UnitVector 2 :=
  phaseY ((4 / 5) * Complex.I) (by
    norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im])

private def oppositeY : UnitVector 2 :=
  phaseY (-((4 / 5) * Complex.I)) (by
    norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im])

private def phaseH : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1, -1]

private theorem phase_pairing (c : ℂ) (hc : Complex.normSq c = 16 / 25) :
    pairing phaseH (rankOneDensity phaseX.val - rankOneDensity (phaseY c hc).val) = 7 / 25 := by
  have hc' : c.re * c.re + c.im * c.im = 16 / 25 := hc
  unfold pairing phaseH trace
  simp only [Fin.sum_univ_two, diag_apply, diagonal_mul, Matrix.sub_apply, rankOneDensity,
    vecMulVec_apply, Pi.star_apply, phaseX, phaseY, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_ofNat]; linarith

/-- At the same diagonal test, flipping one relative phase changes the exact slack. -/
theorem phase_diagnostic :
    ground phaseX sharedY = 7 / 25 ∧
    pairing phaseH (rankOneDensity phaseX.val - rankOneDensity sharedY.val) = 7 / 25 ∧
    ground phaseX oppositeY = 1 ∧
    pairing phaseH (rankOneDensity phaseX.val - rankOneDensity oppositeY.val) = 7 / 25 := by
  refine ⟨?_, phase_pairing _ _, ?_, phase_pairing _ _⟩
  · norm_num [ground, phaseX, sharedY, phaseY, Fin.sum_univ_two,
      Complex.normSq_apply, Complex.star_def, Complex.conj_ofNat, Complex.mul_re,
      Complex.mul_im, Real.sqrt_div]
  · norm_num [ground, phaseX, oppositeY, phaseY, Fin.sum_univ_two,
      Complex.normSq_apply, Complex.star_def, Complex.conj_ofNat, Complex.mul_re, Complex.mul_im]

#print axioms fixed_pair_equality
#print axioms phase_diagnostic

end D5.S3.Quantum.QuantumChannels.CouplingWassersteinEquality
