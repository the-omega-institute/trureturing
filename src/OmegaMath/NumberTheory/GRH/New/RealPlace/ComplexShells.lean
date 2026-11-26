import OmegaMath.NumberTheory.GRH.New.RealPlace.LocalTheorem
import OmegaMath.NumberTheory.GRH.New.RealPlace.ComplexGauge
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Real-place Bessel integrals: band limits, energy and open-cell bound (see
New.Filling.FillingData).

This file: Summing the local theorem over shells at C; explicit band bound for forms. -/

noncomputable section


open MeasureTheory Size Fintype Real Level Shape ENNReal Finset Gauge RealPlaceSizes
variable {j s : ℕ} {𝔰 : Shape} {I : Type} [Fintype I] (F : C(𝔰.G₁, EuclideanSpace ℂ I))
  {p q : ℕ → ℂˣ} {ρ L t ε b : ℝ} {rep F₀ n W}

/-- A pair (F₀, F) of a Bessel function and its cut satisfying `IsCutPair` b n, with numerical
conditions: ρ a fixed power of b, |κ| = s + 3(ϱ+1) + 2, and lower bounds on ρ, s, |κ|, ϱ, b. -/
structure IsCutBessel rep ρ s b F₀ n extends IsCutPair b n rep (·.rec F₀ F), RealPlaceSizes 𝔰 ρ s b

namespace IsCutBessel

variable {F} (hF : IsCutBessel F rep ρ s b F₀ n) (hj : j ≤ 𝔰.ϱ)

/-- The number (vol U(k)/vol U(r))/(λ|I|)², with k, r the ranks of X₀ and the whole space, and λ
= `RealPlaceSizes.haarRatio` the ratio of 𝖬 to the Haar measure of G₁. -/
def formConst := volU 𝔰.k / volU 𝔰.r / (hF.haarRatio.toReal * card I) ^ 2

lemma isCut_complexLevel : hF.complexLevel.IsCut F := have h := hF.isBesselFunction .cut
  ⟨⟨h.1, by simpa using h.2⟩,
    (_root_.exists_norm_le_of_besselSize_le <| hF.rho_eq ▸ hF.inCut_of_ne_zero _ ·)⟩

lemma volumeExponent_eq : hF.complexLevel.volumeExponent =
  s := by simp [Level.volumeExponent, hF.k_eq]

/-- For F satisfying `IsCutBessel`, some L ≥ ρ makes p, q heads of length j for the gauge of size
L, and L^K ≤ R^{(K+6)(2j+1)}·𝗁(p)𝗁(q), 𝗁 = `headWeight` K j, for every R ≥ ρ bounding all
|p₁⋯p_l|, |q₁⋯q_l|, l ≤ j. -/
lemma exists_gauge_isHead j p q K : ∃ L, ∃ h : ρ ≤ L, (hF.gauge h).IsHead j p ∧ (hF.gauge h).IsHead
  j q ∧ ∀ R ≥ ρ, (∀ l ≤ j, ‖(∏ a ∈ range l, p a).1‖ ≤ R ∧ ‖(∏ a ∈ range l, q a).1‖ ≤ R) →
  L ^ K ≤ R ^ ((K + 6) * (2 * j + 1)) * (headWeight K j p * headWeight K j q) := by
  have n {L B R} {x : ℂˣ} (c : L ^ K ≤ B) (h : ‖x.1‖ ≤ R) (_ : 1 ≤ L) (_ : 1 ≤ R) :
      max L ‖x.1‖⁻¹ ^ K ≤ B * (R ^ (K + 6) * dampedPower K ‖x.1‖⁻¹) := by
    grw [dampedPower, ← c, max_def, min_def]
    split_ifs <;> simp [field, pow_add] <;> (try grw [h]) <;> bound
  simp [IsHead, RealPlaceSizes.gauge, headWeight, -Units.coe_prod]
  refine' j.rec ⟨ρ, by simp; grw [← le_self_add]; bound [hF.ten_le]⟩
    fun j ⟨L, a, b, h, c⟩ ↦ ⟨_, _, _, _, fun R r z ↦ (n (n (c R r _) (z _ .refl).1 ..) (z _
    .refl).2 ..).trans_eq (by simp [prod_range_succ]; ring)⟩ <;> clear n <;> grind [hF.ten_le]

include hj

/-- Let F be cut, j ≤ ϱ, p, q heads for L ≥ ρ, W Bessel, supported on points near at j, ‖W‖₂² ≤
ε²|I|, ε ≥ 0, t ≥ 1, f ≤ `Level.formMajorant`, and f² ≤ (π^kρ^{24k}t^{−s})²`Gauge.selfNormProduct`
if t > 1. Then `IsCutBessel.formConst`·κ_j∫ f d𝖬 ≤ ΘL^{10⁹(ϱ+1)⁴}ρ^{24k}t^{9.9·10⁶(ϱ+1)³−s}ε, with k
= rank X₀, κ_j = `Level.headDensity`, Θ = `Shape.bandConst`. -/
lemma formConst_mul_lintegral_le [Nonempty I] (hW : Place.IsBessel W 1)
  (hε : ∫⁻ y, ‖W y‖ₑ ^ 2 ∂besselQuotMeasure ≤ .ofReal ε ^ 2 * card I) (ε0 : 0 ≤ ε) {hL : ρ ≤
  L} (hp : (hF.gauge hL).IsHead j p) (hq : (hF.gauge hL).IsHead j q) (hs : ∀ {y}, W y ≠ 0 →
  hF.complexLevel.IsNear j y) {f} (ht : 1 ≤ t) (hf : f ≤ hF.complexLevel.formMajorant j p q F W)
  (h : ∀ {x}, 1 < t → f x ^ 2 ≤ .ofReal ((π * ρ ^ 24) ^ 𝔰.k / t ^ s) ^ 2 *
  (hF.gauge hL).selfNormProduct j p q F W x) : ‖(hF.formConst : ℂ)‖ₑ * (hF.complexLevel.headDensity
  j p q * ∫⁻ x, f x ∂hF.complexLevel.groupMeasure) ≤ .ofReal (𝔰.bandConst * L ^ (10 ^ 9 * 𝔰.n ^ 4) *
  ρ ^ (24 * 𝔰.k) * t ^ (9900000 * 𝔰.n ^ 3) / t ^ s * ε) := by
  obtain ⟨⟨l, _, _⟩ : 2 ≤ L ∧ 1 ≤ ρ ∧ 1 ≤ L, c, _, ⟨_, _⟩, -, N, -⟩ := by bound [hF.ten_le],
    hF.isCut_complexLevel, one_le_two.trans two_le_pi, hF.haarRatio_spec
  let T i := t * L ^ (11 * 𝔰.n * i)
  have o i a b (h : a ≤ 11 * 𝔰.n * i * b := by lia) : L ^ a ≤ T i ^ b := by
    grw [h, pow_mul, ← one_mul (L ^ _), ht]
  have g i b := hL.trans (pow_one L ▸ o (.succ i) 1 (.succ b))
  grw [← mul_one (ENNReal.ofReal _), ← setLIntegral_univ, ← Set.iUnion_eq_univ_iff (f := fun i ↦
    (hF.gauge (g i (99 * 𝔰.ϱ + 98))).positionsOfSize).2 fun x ↦
    (pow_unbounded_of_one_lt _ (by linarith)).imp
    fun i e ↦ ⟨⟨⟩, fun _ _ ↦ (norm_apply_le_l2_opNorm ..).trans (e.le.trans ((o _ i _).trans_eq
    (pow_mul ..)))⟩, ← iUnion_disjointed, lintegral_iUnion_le, ← tsum_two_zpow_neg_add_one]
  simp [← ENNReal.tsum_mul_left, disjointed]; gcongr 1 with i; grw [lintegral_positions_le _ _ c hW
    hj hq (Θ := .ofReal ε * (hF.haarRatio * card I) ^ 2) ?_ sdiff_le (e := .ofReal
    ((π * ρ ^ 24) ^ 𝔰.k * ρ ^ (9999 * 𝔰.n) / T i ^ s)) fun x m ↦ ?_]
  have := @toReal_ne_zero
  simp (disch := finiteness) [RealPlaceSizes.gauge, floorModulus, ← toReal_le_toReal,
    *, T, formConst, bandConst, volU, field,
    mul_pow, ← pow_mul, abs_of_nonneg, ENNReal.zpow_sub, ENNReal.zpow_neg]
  nth_grw 1 [tsub_le_self, l, l, hL, ← hF.mul_cube_lt_s]; ring_nf; gcongr <;> omega
  repeat grw [Level.pairingNorm, (ofReal_norm _).ge, norm_inner_le_norm]
  simp +contextual [mul_pow, lintegral_mul_const, N, hW.2, c.law, -upperMeasure, enorm_smul,
    ← ofReal_norm (wave _), hW.stronglyMeasurable.enorm.pow, c.stronglyMeasurable.enorm.pow]
  grw [hε, hF.lintegral_sq_cut_le]; ring_nf; rfl
  by_cases i = 0 ∧ 1 < t; grw [h] <;> bound
  grw [hf x, formMajorant_sq_le _ c hW hj hp ⟨⟩
    (by grw [hF.gauge.floorMassLe_one ⟨j, by lia⟩ hasFibreBound_floorQuadric ·, volume_le]) (σ :=
    volume (Metric.ball (0 : ℂ) (T i)⁻¹)) (by bound) hs fun z _ a b d ↦ ?_, hF.volumeExponent_eq]
  gcongr; simp (disch := finiteness) [RealPlaceSizes.gauge,
    ← toReal_le_toReal]; ring_nf; gcongr <;> grind [RealPlaceSizes]
  cases i; simp_all [T, ht.antisymm', ← NNReal.coe_lt_one, not_lt_of_ge]
  contrapose m
  simpa using fun _ ↦ ⟨_, le_rfl, ⟨⟩, by simpa [RealPlaceSizes.gauge, HasMatSize] using!
    ((hF.gauge (g _ 0)).hasMatSize_sub_one_of_floorValues _ hj hp hq (by
    simpa [RealPlaceSizes.gauge] using fun _ _ ↦
      (o _ _ 1).trans') ((c.2 (by aesop)).imp fun u ⟨h, j⟩ ↦ ⟨h, (c.2 (by aesop)).imp fun v ⟨k, l⟩ ↦
    ⟨k, j, l, by simpa using (hasMatSize_box _ l).sub (hasMatSize_box _ j)⟩⟩)
    b d fun a h ↦ (Set.not_subset.1 (m ⟨a, h, measure_mono ·⟩)).elim fun c ⟨d, r⟩ ↦ ⟨.mk0 c
    (r <| by simp [·]; bound), d, by simp [RealPlaceSizes.gauge] at r ⊢; grw [← r, inv_inv]⟩)⟩

/-- If F satisfies `IsCutBessel`, j ≤ ϱ and p, q are sequences in ℂ^×, the majorant 𝓘_j⁺
(`Level.formMajorant`, both functions equal to F) has finite integral over G₁ for the measure 𝖬
of the level. -/
lemma lintegral_formMajorant_ne_top [Nonempty I] : ∫⁻ x, hF.complexLevel.formMajorant j p q F F x
  ∂hF.complexLevel.groupMeasure ≠ ∞ := (hF.exists_gauge_isHead j p q 0).elim fun _ ⟨_, a, b, _⟩ z ↦
  (z ▸ hF.formConst_mul_lintegral_le hj hF.isCut_complexLevel.1 (by simp [hF.lintegral_sq_cut_le])
  zero_le_one a b hF.isCut_complexLevel.isNear_of_ne_zero le_rfl le_rfl (by simp)).not_gt
  (by simp [headDensity, formConst, prod_eq_zero_iff, toReal_ne_zero, ne_of_gt, haarRatio_spec])

/-- For a cut F, j ≤ ϱ, |ω| ≤ 1: if `Level.formModulus`² ≤ (π/|y|)^{2(k−1)}·`Gauge.selfNormProduct`
at all positions in every gauge with head p, then |`IsCutBessel.formConst`·𝓘_j(p, q; ω)| ≤ Θ
b^{2000n⁹} ℓ_{k−n⁷}(1/|y|) 𝗁(p)𝗁(q), with ℓ = `dampedPower`, 𝗁 = `headWeight` n⁶ j, n = ϱ+1. -/
lemma norm_floorForm_le [Nonempty I]
    (y : ℂˣ) {ω} (hω : ∀ x, ‖ω x‖ ≤ 1) (h : ∀ Γ : Gauge hF.complexLevel,
  Γ.IsHead j p → ∀ {x}, hF.complexLevel.formModulus j p q F x ω ^ 2 ≤
  (complexPlace.c / complexPlace.md y) ^ card {i // i ≠ 𝔰.k₀} * Γ.selfNormProduct j p q F F x) :
  ‖hF.formConst * hF.complexLevel.floorForm j p q F ω‖ ≤ 𝔰.bandConst * b ^ (2000 * 𝔰.n ^ 9) *
  dampedPower (𝔰.k - 𝔰.n ^ 7) ‖y.1‖⁻¹ * (headWeight (𝔰.n ^ 6) j p * headWeight (𝔰.n ^ 6) j q) := by
  obtain ⟨⟨_, _, hp, hq, Z⟩, c, _, _, _, ⟨_, N⟩, K, k⟩ := hF.exists_gauge_isHead j p q (𝔰.n ^ 6),
    hF.isCut_complexLevel, hF.ten_le, y.norm_pos, hF.two_le_b,
    exists_add_of_le hF.ten_pow_le_varrho, exists_add_of_le hF.pow_seven_le_k
  grw [← ofReal_le_ofReal_iff, ofReal_norm, enorm_mul, enorm_floorForm_le]
  obtain z | Z := not_or_of_imp (Z (ρ ^ (9 * 𝔰.n)) (by bound))
  have := (formMajorant_sq_le _ c c.1 hj hp (x := ·) ⟨⟩ (σ := 0) (by tauto) le_top
    c.isNear_of_ne_zero fun _ _ _ u v ↦ z.elim fun l m ↦ ⟨minors_mem_ofSize hF.gauge.hasMatSize_box
    hj u (c.isNear_of_ne_zero (by aesop)).choose_spec l m, minors_mem_ofSize hF.gauge.hasMatSize_box
    hj v (c.isNear_of_ne_zero (by aesop)).choose_spec l m⟩)
  simp_all [hF.volumeExponent_eq, hF.mul_cube_lt_s.ne_zero,
    (c.formModulus_le_formMajorant _).antisymm]
  let t := 1 ⊔ ρ ^ 24 * ‖y.1‖
  grw [hF.formConst_mul_lintegral_le hj c.1 (by simp [hF.lintegral_sq_cut_le]) zero_le_one hp hq
    c.isNear_of_ne_zero le_sup_left (fun _ ↦ c.formModulus_le_formMajorant hω) fun m ↦ ?_,
    (?_ : _ * _ ≤ 𝔰.n ^ 6), Z, ← (?_ : 9900000 * 𝔰.n ^ 3 + (K + 6) ≤ s), hj, dampedPower, k,
    ← (by simp [field, t] : ρ ^ 24 / t ≤ _⁻¹), ← (by simp [field, t]; bound : t⁻¹ ≤ 1 ⊓ _)]
  gcongr 1; simp [field, pow_add, div_pow, hF.rho_eq]; ring_nf
  simp [mul_assoc, ← pow_add]; gcongr
  any_goals first | clear Z; delta headWeight dampedPower bandConst volU; positivity
                  | rw [hF.k_eq, Shape.n, N] at *; lia | bound
  grw [h _ hp, hF.volumeExponent_eq.ge.trans tsub_le_self, max_eq_right (by grind)]
  gcongr 1
  simp (disch := finiteness) [← ofReal_norm, ← toReal_le_toReal, div_pow, field]
  ring_nf; repeat bound [two_le_pi]
