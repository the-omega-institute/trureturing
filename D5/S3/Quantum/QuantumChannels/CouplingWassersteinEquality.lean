import D5.S3.Quantum.GleasonComplexRepresentation
import D5.S3.Quantum.QuantumChannels.CouplingWassersteinTriangleRefutation
import D5.S3.Quantum.Foundation.TrigonometricMomentGap
import D5.S3.Quantum.Foundation.FiniteHermitianTraceDuality

/-!
# Equality in trace-ground coupling transport

Beatty and Stilck França, arXiv:2402.16477v2, Eqs. (62) and (81).
Preregistration: https://github.com/the-omega-institute/trureturing/issues/35123
-/

set_option autoImplicit false
set_option Elab.async false

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
  simp only [rankOneDensity, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply,
    Pi.star_apply, Pi.add_apply,
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

private theorem ground_eq_zero_of_density_eq (x y : UnitVector n)
    (h : rankOneDensity x.val = rankOneDensity y.val) : ground x y = 0 := by
  have hy : rankOneDensity y.val *ᵥ y.val = y.val := by
    rw [rankOneDensity, vecMulVec_mulVec, op_smul_eq_smul]
    change ip y.val y.val • y.val = y.val
    rw [ip_self, one_smul]
  have hx : ip x.val y.val • x.val = y.val := by
    rw [← h, rankOneDensity, vecMulVec_mulVec, op_smul_eq_smul] at hy
    exact hy
  have hh : ip (ip x.val y.val • x.val) (ip x.val y.val • x.val) = 1 :=
    (congrArg₂ ip hx hx).trans (ip_self y)
  rw [smul_ip, ip_smul, ip_self, mul_one] at hh
  have hh' : (Complex.normSq (ip x.val y.val) : ℂ) = 1 := by
    simpa only [Complex.star_def, Complex.normSq_eq_conj_mul_self] using hh
  have hs : Complex.normSq (ip x.val y.val) = 1 := by exact_mod_cast hh'
  change Real.sqrt (1 - Complex.normSq (ip x.val y.val)) = 0
  simp [hs]

private theorem atom_pairing_le (H : Matrix (Fin n) (Fin n) ℂ)
    (hminus : (1 - H).PosSemidef) (hplus : (1 + H).PosSemidef) (x y : UnitVector n) :
    pairing H (rankOneDensity x.val - rankOneDensity y.val) ≤ ground x y := by
  by_cases h : rankOneDensity x.val = rankOneDensity y.val
  · simp [h, pairing, ground_eq_zero_of_density_eq x y h]
  · exact (fixed_pair_equality x y h H hminus hplus).2.2.1

private theorem hasSum_cost {ρ σ : Matrix (Fin n) (Fin n) ℂ} (Q : Plan ρ σ) :
    HasSum (fun j => Q.weight j * ground (Q.source j) (Q.target j)) (cost Q) := by
  apply Summable.hasSum
  exact Summable.of_nonneg_of_le
    (fun j => mul_nonneg (Q.nonneg j) (ground_nonneg _ _))
    (fun j => mul_le_of_le_one_right (Q.nonneg j) (ground_le_one _ _)) Q.mass.summable

private def pairingMap (H : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ where
  toFun := pairing H
  map_add' A B := by simp [pairing, mul_add, trace_add, add_div]
  map_smul' r A := by
    simp [pairing, trace_smul, Complex.real_smul, mul_div_assoc]
  cont := by unfold pairing trace; fun_prop

private theorem hasSum_pairing {ρ σ : Matrix (Fin n) (Fin n) ℂ}
    (Q : Plan ρ σ) (H : Matrix (Fin n) (Fin n) ℂ) :
    HasSum (fun j => Q.weight j *
      pairing H (rankOneDensity (Q.source j).val - rankOneDensity (Q.target j).val))
      (pairing H (ρ - σ)) := by
  have h := (Q.left.sub Q.right).mapL (pairingMap H)
  change HasSum _ (pairing H (ρ - σ)) at h
  convert h using 1
  funext j
  rw [← smul_sub]
  change _ = pairing H _
  simp [pairing, trace_smul, mul_div_assoc]

/-- For an arbitrary countable plan the weighted atom slacks are nonnegative
and sum to its cost minus the marginal pairing. -/
theorem countable_plan_slack {ρ σ : Matrix (Fin n) (Fin n) ℂ} (Q : Plan ρ σ)
    (H : Matrix (Fin n) (Fin n) ℂ) (hminus : (1 - H).PosSemidef)
    (hplus : (1 + H).PosSemidef) :
    let slack := fun j => Q.weight j *
      (ground (Q.source j) (Q.target j) -
        pairing H (rankOneDensity (Q.source j).val - rankOneDensity (Q.target j).val))
    (∀ j, 0 ≤ slack j) ∧ HasSum slack (cost Q - pairing H (ρ - σ)) := by
  dsimp only
  refine ⟨fun j => mul_nonneg (Q.nonneg j)
    (sub_nonneg.mpr (atom_pairing_le H hminus hplus _ _)), ?_⟩
  simpa only [mul_sub] using (hasSum_cost Q).sub (hasSum_pairing Q H)

/-- A countable plan attains the fixed test bound exactly when all of its
positive-weight atoms attain their individual bounds. -/
theorem countable_plan_equality {ρ σ : Matrix (Fin n) (Fin n) ℂ} (Q : Plan ρ σ)
    (H : Matrix (Fin n) (Fin n) ℂ) (hminus : (1 - H).PosSemidef)
    (hplus : (1 + H).PosSemidef) :
    cost Q = pairing H (ρ - σ) ↔
      ∀ j, 0 < Q.weight j →
        pairing H (rankOneDensity (Q.source j).val - rankOneDensity (Q.target j).val) =
          ground (Q.source j) (Q.target j) := by
  obtain ⟨hpos, hsum⟩ := countable_plan_slack Q H hminus hplus
  constructor
  · intro h j hj
    rw [h, sub_self] at hsum
    have hz := le_antisymm (le_hasSum hsum j (fun i _ => hpos i)) (hpos j)
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hj.ne')).symm
  · intro h
    have he : ∀ j, Q.weight j *
        (ground (Q.source j) (Q.target j) -
          pairing H (rankOneDensity (Q.source j).val - rankOneDensity (Q.target j).val)) = 0 := by
      intro j
      rcases (Q.nonneg j).eq_or_lt with hj | hj
      · simp [← hj]
      · rw [h j hj, sub_self, mul_zero]
    simp only [he] at hsum
    exact sub_eq_zero.mp (hsum.unique hasSum_zero)

open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Foundation.FiniteHermitianTraceDuality (exists_hermitian_traceNorm_test)

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- The trace-norm lower bound holds for every admissible countable plan. -/
theorem traceNorm_le_countable_cost {ρ σ : Matrix (Fin n) (Fin n) ℂ}
    (Q : Plan ρ σ) (hΔ : (ρ - σ).IsHermitian) :
    traceNorm (ρ - σ) / 2 ≤ cost Q := by
  obtain ⟨H, hH, hnorm, htrace⟩ := exists_hermitian_traceNorm_test (ρ - σ) hΔ
  have hu : H ≤ 1 := hH.isSelfAdjoint.le_algebraMap_norm_self H |>.trans (by
    simpa using (algebraMap_mono (Matrix (Fin n) (Fin n) ℂ) hnorm))
  have hl : -H ≤ 1 := hH.neg.isSelfAdjoint.le_algebraMap_norm_self (-H) |>.trans (by
    simpa using (algebraMap_mono (Matrix (Fin n) (Fin n) ℂ) hnorm))
  have hs := countable_plan_slack Q H (sub_nonneg.mpr hu).posSemidef
    (by simpa [sub_neg_eq_add] using (sub_nonneg.mpr hl).posSemidef)
  have hn := hs.2.tsum_eq ▸ tsum_nonneg hs.1
  rw [sub_nonneg] at hn
  simpa [pairing, htrace] using hn

/-- The same lower bound passes to the original infimum whenever its cost set is inhabited. -/
theorem traceNorm_le_wasserstein {ρ σ : Matrix (Fin n) (Fin n) ℂ}
    (hplan : Nonempty (Plan ρ σ)) (hΔ : (ρ - σ).IsHermitian) :
    traceNorm (ρ - σ) / 2 ≤ wasserstein ρ σ := by
  apply le_csInf
  · obtain ⟨Q⟩ := hplan
    exact ⟨cost Q, Q, rfl⟩
  · rintro _ ⟨Q, rfl⟩
    exact traceNorm_le_countable_cost Q hΔ

/-- Countable barycenters are limits of finite convex combinations formed by
placing the leftover mass on one fixed point. -/
private theorem countable_barycenter_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hc : IsClosed S) (hv : Convex ℝ S) (z₀ : E) (hz₀ : z₀ ∈ S)
    (z : ℕ → E) (hz : ∀ j, z j ∈ S)
    (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) (hm : HasSum w 1)
    {p : E} (hp : HasSum (fun j => w j • z j) p) : p ∈ S := by
  classical
  let rest (k : ℕ) := 1 - ∑ j ∈ Finset.range k, w j
  let approximant (k : ℕ) := (∑ j ∈ Finset.range k, w j • z j) + rest k • z₀
  have hrest : Filter.Tendsto rest Filter.atTop (nhds 0) := by
    simpa [rest] using (tendsto_const_nhds (x := (1 : ℝ))).sub hm.tendsto_sum_nat
  have hlim : Filter.Tendsto approximant Filter.atTop (nhds p) := by
    simpa [approximant] using hp.tendsto_sum_nat.add (hrest.smul (tendsto_const_nhds (x := z₀)))
  refine hc.mem_of_tendsto hlim (Filter.Eventually.of_forall fun k => ?_)
  let w' (i : ℕ) := if i < k then w i else rest k
  let z' (i : ℕ) := if i < k then z i else z₀
  have hw' : ∀ j ∈ Finset.range k, w' j = w j :=
    fun j hj => ite_eq_left (Finset.mem_range.mp hj)
  have hz' : ∀ j ∈ Finset.range k, z' j = z j :=
    fun j hj => ite_eq_left (Finset.mem_range.mp hj)
  have hmass : ∑ j ∈ Finset.range (k + 1), w' j = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_congr rfl hw']
    simp [w', rest]
  have hmem := hv.sum_mem (t := Finset.range (k + 1)) (w := w') (z := z')
    (fun j _ => by
      by_cases hj : j < k
      · simpa [w', hj] using hw j
      · simpa [w', hj, rest] using
          sub_nonneg.mpr (sum_le_hasSum (Finset.range k) (fun i _ => hw i) hm))
    hmass (fun j _ => by
      by_cases hj : j < k
      · simpa [z', hj] using hz j
      · simpa [z', hj] using hz₀)
  have hsum : (∑ j ∈ Finset.range (k + 1), w' j • z' j) = approximant k := by
    rw [Finset.sum_range_succ, Finset.sum_congr rfl (fun j hj => by rw [hw' j hj, hz' j hj])]
    simp [w', z', approximant]
  exact hsum ▸ hmem

open scoped Matrix.Norms.Elementwise

private abbrev TransportMoment (n : ℕ) :=
  Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × ℝ

private def pureMoment (x y : UnitVector n) : TransportMoment n :=
  (rankOneDensity x.val, rankOneDensity y.val, ground x y)

private def pureMoments (n : ℕ) : Set (TransportMoment n) :=
  Set.range (fun xy : UnitVector n × UnitVector n => pureMoment xy.1 xy.2)

/-- The marginals and cost of an arbitrary countable plan lie in the
closure of the convex hull of the pure-pair moment graph. -/
theorem countable_plan_mem_closure {ρ σ : Matrix (Fin n) (Fin n) ℂ} (Q : Plan ρ σ) :
    ((ρ, σ, cost Q) : TransportMoment n) ∈ closure (convexHull ℝ (pureMoments n)) := by
  let z := fun j => pureMoment (Q.source j) (Q.target j)
  have hz (j : ℕ) : z j ∈ closure (convexHull ℝ (pureMoments n)) :=
    subset_closure (subset_convexHull ℝ _ ⟨(Q.source j, Q.target j), rfl⟩)
  have hp : HasSum (fun j => Q.weight j • z j) (ρ, σ, cost Q) := by
    simpa [z, pureMoment, Complex.real_smul, smul_eq_mul] using
      Q.left.prodMk (Q.right.prodMk (hasSum_cost Q))
  exact countable_barycenter_mem isClosed_closure (convex_convexHull ℝ _).closure
    (z 0) (hz 0) z hz Q.weight Q.nonneg Q.mass hp

/-- Realize a finite weighted family by extending its weights by zero in the
original countable plan. The added coordinates use a fixed unit vector. -/
private theorem finite_realization {ι : Type} [Fintype ι]
    (padding : UnitVector n) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hm : ∑ i, w i = 1)
    (x y : ι → UnitVector n) :
    ∃ Q : Plan (∑ i, (w i : ℂ) • rankOneDensity (x i).val)
        (∑ i, (w i : ℂ) • rankOneDensity (y i).val),
      (∃ s : Finset ℕ, ∀ j ∉ s, Q.weight j = 0) ∧
      cost Q = ∑ i, w i * ground (x i) (y i) := by
  classical
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  let w' := Function.extend e w 0
  let x' := Function.extend e x (fun _ => padding)
  let y' := Function.extend e y (fun _ => padding)
  have w_zero (j : ℕ) (hj : j ∉ Set.range e) : w' j = 0 :=
    Function.extend_apply' _ _ _ hj
  have extend_sum {E : Type} [AddCommMonoid E] [TopologicalSpace E] (f : ι → E)
      (g : ℕ → E) (heq : ∀ i, g (e i) = f i) (hzero : ∀ j ∉ Set.range e, g j = 0) :
      HasSum g (∑ i, f i) := by
    apply (he.hasSum_iff hzero).mp
    exact (hasSum_fintype f).congr_fun heq
  have mass : HasSum w' 1 := by
    rw [← hm]
    exact extend_sum w w' (he.extend_apply _ _) w_zero
  have marginal (a : ι → UnitVector n) :
      HasSum (fun j => (w' j : ℂ) • rankOneDensity (Function.extend e a (fun _ => padding) j).val)
        (∑ i, (w i : ℂ) • rankOneDensity (a i).val) := by
    apply extend_sum
    · intro i
      simp [w', he.extend_apply]
    · intro j hj
      simp [w_zero j hj]
  let Q : Plan (∑ i, (w i : ℂ) • rankOneDensity (x i).val)
      (∑ i, (w i : ℂ) • rankOneDensity (y i).val) :=
    ⟨w', fun j => by
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hj
        simpa [w', he.extend_apply] using hw i
      · simp [w_zero j hj],
      x', y', marginal x, marginal y, mass⟩
  refine ⟨Q, ⟨Finset.univ.image e, fun j hj => w_zero j (by simpa [Set.mem_range] using hj)⟩, ?_⟩
  have hs : HasSum (fun j => w' j * ground (x' j) (y' j)) (∑ i, w i * ground (x i) (y i)) := by
    apply extend_sum
    · intro i
      simp [w', x', y', he.extend_apply]
    · intro j hj
      simp [w_zero j hj]
  exact hs.tsum_eq

/-- A point of the finite convex hull gives an actual finitely supported
countable plan with the specified marginals and cost. -/
theorem convexHull_realized_as_plan {ρ σ : Matrix (Fin n) (Fin n) ℂ} {c : ℝ}
    (padding : UnitVector n) (h : ((ρ, σ, c) : TransportMoment n) ∈ convexHull ℝ (pureMoments n)) :
    ∃ Q : Plan ρ σ, (∃ s : Finset ℕ, ∀ j ∉ s, Q.weight j = 0) ∧ cost Q = c := by
  classical
  obtain ⟨ι, _, w, z, hw, hm, hz, hp⟩ := mem_convexHull_iff_exists_fintype.mp h
  have hz' (i : ι) : ∃ x y : UnitVector n, pureMoment x y = z i := by
    obtain ⟨xy, hxy⟩ := hz i
    exact ⟨xy.1, xy.2, hxy⟩
  choose x y hxy using hz'
  simp only [← hxy] at hp
  have hl : ∑ i, (w i : ℂ) • rankOneDensity (x i).val = ρ := by
    simpa [pureMoment, Prod.fst_sum, Complex.real_smul] using congrArg Prod.fst hp
  have hr : ∑ i, (w i : ℂ) • rankOneDensity (y i).val = σ := by
    simpa [pureMoment, Prod.fst_sum, Prod.snd_sum, Complex.real_smul] using
      congrArg (fun p : TransportMoment n => p.2.1) hp
  have hc : ∑ i, w i * ground (x i) (y i) = c := by
    simpa [pureMoment, Prod.snd_sum, smul_eq_mul] using
      congrArg (fun p : TransportMoment n => p.2.2) hp
  rw [← hl, ← hr, ← hc]
  exact finite_realization padding w hw hm x y

/-- Compactness of the pure-pair hull gives finite attainment for the original
countable-plan infimum as soon as a single admissible plan exists. -/
theorem finite_attainment_of_compact_hull {ρ σ : Matrix (Fin n) (Fin n) ℂ}
    (Q₀ : Plan ρ σ) (hcompact : IsCompact (convexHull ℝ (pureMoments n))) :
    ∃ Q : Plan ρ σ, (∃ s : Finset ℕ, ∀ j ∉ s, Q.weight j = 0) ∧ cost Q = wasserstein ρ σ := by
  let fiber : Set (TransportMoment n) := {p | p.1 = ρ ∧ p.2.1 = σ}
  let K := convexHull ℝ (pureMoments n) ∩ fiber
  let f : TransportMoment n → ℝ := fun p => p.2.2
  have hclosed : IsClosed fiber :=
    (isClosed_eq continuous_fst continuous_const).inter
      (isClosed_eq (continuous_fst.comp continuous_snd) continuous_const)
  have hK : IsCompact K := hcompact.inter_right hclosed
  have hmem (Q : Plan ρ σ) : ((ρ, σ, cost Q) : TransportMoment n) ∈ K := by
    refine ⟨?_, rfl, rfl⟩
    simpa only [hcompact.isClosed.closure_eq] using countable_plan_mem_closure Q
  obtain ⟨⟨p, q, c⟩, ⟨hull, hp, hq⟩, hmin⟩ :=
    hK.exists_isMinOn ⟨_, hmem Q₀⟩ (continuous_snd.comp continuous_snd).continuousOn
  change p = ρ at hp
  change q = σ at hq
  subst p
  subst q
  obtain ⟨Q, hfin, hcost⟩ := convexHull_realized_as_plan (Q₀.source 0) hull
  have hle (P : Plan ρ σ) : c ≤ cost P := hmin (hmem P)
  have hval : wasserstein ρ σ = c := by
    apply le_antisymm
    · exact csInf_le ⟨c, by rintro _ ⟨P, rfl⟩; exact hle P⟩ ⟨Q, hcost⟩
    · exact le_csInf ⟨c, Q, hcost⟩ (by rintro _ ⟨P, rfl⟩; exact hle P)
  exact ⟨Q, hfin, hcost.trans hval.symm⟩

local instance : TopologicalSpace (UnitVector n) :=
  inferInstanceAs (TopologicalSpace {v : Fin n → ℂ // ∑ i, Complex.normSq (v i) = 1})

private theorem unitVector_compact : CompactSpace (UnitVector n) := by
  let S : Set (Fin n → ℂ) := {v | ∑ i, Complex.normSq (v i) = 1}
  change CompactSpace S
  apply isCompact_iff_compactSpace.mp
  have hc : Continuous fun v : Fin n → ℂ => ∑ i, Complex.normSq (v i) :=
    continuous_finsetSum _ fun i _ => Complex.continuous_normSq.comp (continuous_apply i)
  have hclosed : IsClosed S := isClosed_eq hc continuous_const
  have hcompact : IsCompact (Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hcompact.of_isClosed_subset hclosed ?_
  intro v hv i _
  have hs : ∑ j, Complex.normSq (v j) = 1 := hv
  have hi := Finset.single_le_sum (f := fun j => Complex.normSq (v j))
    (fun j _ => Complex.normSq_nonneg (v j)) (Finset.mem_univ i)
  rw [hs, Complex.normSq_eq_norm_sq] at hi
  exact Metric.mem_closedBall.mpr (by rw [dist_zero_right]; nlinarith [norm_nonneg (v i)])

private theorem continuous_pureMoment :
    Continuous (fun xy : UnitVector n × UnitVector n => pureMoment xy.1 xy.2) := by
  have hρ : Continuous fun x : UnitVector n => rankOneDensity x.val := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [rankOneDensity, vecMulVec_apply, Pi.star_apply]
    exact ((continuous_apply i).comp continuous_subtype_val).mul
      ((continuous_apply j).comp continuous_subtype_val).star
  have hground : Continuous fun xy : UnitVector n × UnitVector n => ground xy.1 xy.2 := by
    unfold ground
    apply Real.continuous_sqrt.comp
    apply continuous_const.sub
    apply Complex.continuous_normSq.comp
    exact continuous_finsetSum _ fun i _ =>
      (((continuous_apply i).comp continuous_subtype_val).comp continuous_fst).star.mul
        (((continuous_apply i).comp continuous_subtype_val).comp continuous_snd)
  exact (hρ.comp continuous_fst).prodMk ((hρ.comp continuous_snd).prodMk hground)

private theorem pureMoments_compact : IsCompact (pureMoments n) := by
  have : CompactSpace (UnitVector n) := unitVector_compact
  exact isCompact_range continuous_pureMoment

open D5.S3.Quantum.Foundation.TrigonometricMomentGap (compact_hull)

/-- Every inhabited plan space has a finitely supported minimizer of its
original countable-plan infimum. -/
theorem finite_attainment {ρ σ : Matrix (Fin n) (Fin n) ℂ} (Q₀ : Plan ρ σ) :
    ∃ Q : Plan ρ σ, (∃ s : Finset ℕ, ∀ j ∉ s, Q.weight j = 0) ∧ cost Q = wasserstein ρ σ :=
  finite_attainment_of_compact_hull Q₀
    (compact_hull pureMoments_compact ⟨_, ⟨(Q₀.source 0, Q₀.target 0), rfl⟩⟩)

private def spectralVector {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (i : Fin n) :
    UnitVector n :=
  ⟨(hA.eigenvectorBasis i).ofLp, unit_of_ip (by
    change (star (hA.eigenvectorBasis i).ofLp ⬝ᵥ (hA.eigenvectorBasis i).ofLp) = 1
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
      hA.eigenvectorBasis.orthonormal.norm_eq_one i]
    norm_num)⟩

/-- Spectral decompositions of both marginals yield an admissible product plan. -/
theorem plan_nonempty_of_density (hn : 0 < n) {ρ σ : Matrix (Fin n) (Fin n) ℂ}
    (hρ : ρ.PosSemidef) (hρtr : ρ.trace = 1)
    (hσ : σ.PosSemidef) (hσtr : σ.trace = 1) : Nonempty (Plan ρ σ) := by
  let r := hρ.isHermitian.eigenvalues
  let s := hσ.isHermitian.eigenvalues
  let w (ij : Fin n × Fin n) := r ij.1 * s ij.2
  let x (ij : Fin n × Fin n) := spectralVector hρ.isHermitian ij.1
  let y (ij : Fin n × Fin n) := spectralVector hσ.isHermitian ij.2
  have hr : ∑ i, r i = 1 := by
    have h := hρ.isHermitian.trace_eq_sum_eigenvalues
    rw [hρtr] at h
    simpa [Complex.re_sum, r, s] using (congrArg Complex.re h).symm
  have hs : ∑ i, s i = 1 := by
    have h := hσ.isHermitian.trace_eq_sum_eigenvalues
    rw [hσtr] at h
    simpa [Complex.re_sum, r, s] using (congrArg Complex.re h).symm
  have hw (ij : Fin n × Fin n) : 0 ≤ w ij :=
    mul_nonneg (hρ.eigenvalues_nonneg ij.1) (hσ.eigenvalues_nonneg ij.2)
  have hm : ∑ ij, w ij = 1 := by
    rw [Fintype.sum_prod_type]
    simp [w, ← Finset.mul_sum, hs, hr]
  have hl : ∑ ij, (w ij : ℂ) • rankOneDensity (x ij).val = ρ := by
    rw [Fintype.sum_prod_type]
    simp only [w, x, Complex.ofReal_mul, mul_comm (↑(r _) : ℂ), mul_smul,
      ← Finset.sum_smul, ← Complex.ofReal_sum, hs, Complex.ofReal_one, one_smul]
    simpa [r, spectralVector, rankOneDensity, Gleason.rankOne, Complex.real_smul] using
      hρ.isHermitian.eq_sum_eigenvalues_smul_rankOne.symm
  have hright : ∑ ij, (w ij : ℂ) • rankOneDensity (y ij).val = σ := by
    rw [Fintype.sum_prod_type_right]
    simp only [w, y, Complex.ofReal_mul, mul_smul,
      ← Finset.sum_smul, ← Complex.ofReal_sum, hr, Complex.ofReal_one, one_smul]
    simpa [s, spectralVector, rankOneDensity, Gleason.rankOne, Complex.real_smul] using
      hσ.isHermitian.eq_sum_eigenvalues_smul_rankOne.symm
  obtain ⟨Q, _, _⟩ := finite_realization (spectralVector hρ.isHermitian ⟨0, hn⟩) w hw hm x y
  exact ⟨hl ▸ hright ▸ Q⟩

/-- The original countable-plan infimum of two finite-dimensional density
matrices is attained by a finitely supported plan. -/
theorem finite_attainment_of_density (hn : 0 < n) {ρ σ : Matrix (Fin n) (Fin n) ℂ}
    (hρ : ρ.PosSemidef) (hρtr : ρ.trace = 1)
    (hσ : σ.PosSemidef) (hσtr : σ.trace = 1) :
    ∃ Q : Plan ρ σ, (∃ s : Finset ℕ, ∀ j ∉ s, Q.weight j = 0) ∧ cost Q = wasserstein ρ σ := by
  obtain ⟨Q⟩ := plan_nonempty_of_density hn hρ hρtr hσ hσtr
  exact finite_attainment Q

/-- An atom that saturates a fixed test is stationary or has swapped amplitudes
in its two extremal eigenspaces. -/
private def SaturatedAtom (H : Matrix (Fin n) (Fin n) ℂ) (x y : UnitVector n) : Prop :=
  rankOneDensity x.val = rankOneDensity y.val ∨
    ∃ u v : UnitVector n, ip u.val v.val = 0 ∧ H *ᵥ u.val = u.val ∧ H *ᵥ v.val = -v.val ∧
      rankOneDensity x.val =
        rankOneDensity ((upper (ground x y) : ℂ) • u.val + (lower (ground x y) : ℂ) • v.val) ∧
      rankOneDensity y.val =
        rankOneDensity ((lower (ground x y) : ℂ) • u.val + (upper (ground x y) : ℂ) • v.val)

private theorem atom_saturates_iff (H : Matrix (Fin n) (Fin n) ℂ)
    (hminus : (1 - H).PosSemidef) (hplus : (1 + H).PosSemidef) (x y : UnitVector n) :
    pairing H (rankOneDensity x.val - rankOneDensity y.val) = ground x y ↔
      SaturatedAtom H x y := by
  by_cases h : rankOneDensity x.val = rankOneDensity y.val
  · simp [SaturatedAtom, h, pairing, ground_eq_zero_of_density_eq x y h]
  · simpa [SaturatedAtom, h] using (fixed_pair_equality x y h H hminus hplus).2.2.2

/-- A fixed test is sharp for the countable-plan infimum precisely when some
finitely supported plan uses only saturating positive-weight atoms. -/
theorem wasserstein_eq_pairing_iff {ρ σ : Matrix (Fin n) (Fin n) ℂ}
    (Q₀ : Plan ρ σ) (H : Matrix (Fin n) (Fin n) ℂ)
    (hminus : (1 - H).PosSemidef) (hplus : (1 + H).PosSemidef) :
    wasserstein ρ σ = pairing H (ρ - σ) ↔
      ∃ Q : Plan ρ σ, (∃ s : Finset ℕ, ∀ j ∉ s, Q.weight j = 0) ∧
        ∀ j, 0 < Q.weight j → SaturatedAtom H (Q.source j) (Q.target j) := by
  constructor
  · intro h
    obtain ⟨Q, hfin, hc⟩ := finite_attainment Q₀
    have hat := (countable_plan_equality Q H hminus hplus).mp (hc.trans h)
    exact ⟨Q, hfin, fun j hj =>
      (atom_saturates_iff H hminus hplus _ _).mp (hat j hj)⟩
  · rintro ⟨Q, _, hsat⟩
    have hc := (countable_plan_equality Q H hminus hplus).mpr (fun j hj =>
      (atom_saturates_iff H hminus hplus _ _).mpr (hsat j hj))
    have hl (P : Plan ρ σ) : pairing H (ρ - σ) ≤ cost P := by
      obtain ⟨hn, hs⟩ := countable_plan_slack P H hminus hplus
      exact sub_nonneg.mp (hs.tsum_eq ▸ tsum_nonneg hn)
    exact le_antisymm
      (csInf_le ⟨_, by rintro _ ⟨P, rfl⟩; exact hl P⟩ ⟨Q, hc⟩)
      (le_csInf ⟨cost Q, Q, rfl⟩ (by rintro _ ⟨P, rfl⟩; exact hl P))

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

end D5.S3.Quantum.QuantumChannels.CouplingWassersteinEquality
