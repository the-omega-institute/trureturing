/- GID: D5/S3/Arith/Robin/PriceRecord/FixedLayerRigidity
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/FixedLayerRigidity
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: []
   utility: none
   digest: Fixed prime layers of actual positive-price predecessor records. -/

import D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure
import D5.S3.Arith.ExponentExchange.PriceRecordPrimeBlockTail
import D5.S3.Arith.Robin.EulerLayerRootCorrection
import D5.S3.Arith.GoldenResourceObjectiveFactorization
import D5.S3.Arith.GoldenLayerMarginalDecay
import D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
import D5.S3.Arith.Robin.PrimeValuation5040Bridge
import Mathlib.Data.Nat.Squarefree

/-! Uniform fixed prime-layer ratios for full positive-price predecessor records,
using actual finite prime exchanges and fixed relative prime windows. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity

open Finset Filter
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLayerMarginalDecay
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (price_record_prime_structure)
open scoped Topology Chebyshev
open scoped BigOperators
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenResourceObjectiveFactorization
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open D5.S3.Arith.Robin.PrimeValuation5040Bridge (primeBlock_factorization)
open D5.S3.Factorization.PrimePowers.FiniteCrtJoin (primePowerProduct)

/-- Last prime whose actual valuation reaches the given layer, with empty value one. -/
def layerPrime (m j : ℕ) : ℕ :=
  max 1 ((m.primeFactors.filter fun p => j ≤ m.factorization p).sup id)

theorem layer_prime_mem {m j : ℕ} (hQ : 1 < layerPrime m j) :
    layerPrime m j ∈ m.primeFactors ∧ j ≤ m.factorization (layerPrime m j) := by
  classical
  let S := m.primeFactors.filter fun p => j ≤ m.factorization p
  have hS : S.Nonempty := by
    by_contra hn
    have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hmax : layerPrime m j = 1 := by
      change max 1 (S.sup id) = 1
      rw [he]
      simp
    omega
  obtain ⟨q, hq, hsup⟩ := Finset.exists_mem_eq_sup S hS id
  have hqprime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
  have hmax : layerPrime m j = q := by
    change max 1 (S.sup id) = q
    rw [hsup]
    exact max_eq_right hqprime.one_lt.le
  rw [hmax]
  exact Finset.mem_filter.mp hq

theorem valuation_below_layer_prime {m j q : ℕ} (hq : q.Prime)
    (hanti : ∀ p r : ℕ, p.Prime → r.Prime → p < r →
      m.factorization r ≤ m.factorization p)
    (hqQ : q ≤ layerPrime m j) : j ≤ m.factorization q := by
  have hQ : 1 < layerPrime m j := hq.one_lt.trans_le hqQ
  obtain ⟨hmem, hjQ⟩ := layer_prime_mem hQ
  by_cases heq : q = layerPrime m j
  · simpa only [heq] using hjQ
  · exact hjQ.trans (hanti q (layerPrime m j) hq
      (Nat.prime_of_mem_primeFactors hmem) (lt_of_le_of_ne hqQ heq))

theorem valuation_above_layer_prime {m j q : ℕ} (hm : 0 < m)
    (hj : 1 ≤ j) (hq : q.Prime) (hQq : layerPrime m j < q) : m.factorization q < j := by
  classical
  by_contra! hval
  have hqmem : q ∈ m.primeFactors := hq.mem_primeFactors
    ((hq.dvd_iff_one_le_factorization hm.ne').mpr (hj.trans hval)) hm.ne'
  have hmem : q ∈ m.primeFactors.filter (fun p => j ≤ m.factorization p) :=
    Finset.mem_filter.mpr ⟨hqmem, hval⟩
  have hle : q ≤ layerPrime m j := (Finset.le_sup (f := id) hmem).trans (le_max_right _ _)
  exact hQq.not_ge hle

private theorem layer_gain_antitone {p a b : ℕ} (hp : p.Prime)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    goldenLayerMarginal p b * Real.log p ≤ goldenLayerMarginal p a * Real.log p := by
  by_cases heq : a = b
  · simp only [heq, le_refl]
  · exact mul_le_mul_of_nonneg_right
      (golden_layer_strict_decrease hp ha (lt_of_le_of_ne hab heq)).le hp.log_pos.le

private theorem layer_gain_upper {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    goldenLayerMarginal p a * Real.log p ≤ (p : ℝ)⁻¹ ^ a :=
  (le_div_iff₀ hp.log_pos).mp (golden_layer_marginal_le_inv_pow hp ha)

private theorem scaled_power_ratio_tendsto_zero (A B alpha beta : ℝ)
    (r s : ℕ) (hneg : alpha * s - beta * r < 0) :
    Tendsto (fun x : ℝ => (A * x ^ alpha) ^ s / (B * x ^ beta) ^ r)
      atTop (𝓝 0) := by
  have hlim : Tendsto
      (fun x : ℝ => (A ^ s / B ^ r) * x ^ (alpha * s - beta * r))
      atTop (𝓝 0) := by
    simpa only [neg_neg, mul_zero] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr hneg)).const_mul (A ^ s / B ^ r)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  symm
  rw [mul_pow, mul_pow, ← Real.rpow_natCast (x ^ alpha) s,
    ← Real.rpow_mul hx.le, ← Real.rpow_natCast (x ^ beta) r,
    ← Real.rpow_mul hx.le, Real.rpow_sub hx]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem theta_relative_scale {C : ℝ} (hC : 0 < C) :
    Tendsto (fun x : ℝ => Chebyshev.theta (C * x) / x) atTop (𝓝 C) := by
  have h := (EulerLayerRootCorrection.prime_number_limits.2.comp
    (tendsto_id.const_mul_atTop hC)).mul_const C
  simp only [one_mul, Function.comp_def, id_eq] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp [ne_of_gt hC, ne_of_gt hx]

private theorem eventually_prime_in_relative_window {A B : ℝ}
    (hA : 0 < A) (hAB : A < B) : ∀ᶠ x : ℝ in atTop, ∃ q : ℕ,
      q.Prime ∧ A * x < (q : ℝ) ∧ (q : ℝ) ≤ B * x := by
  have hB : 0 < B := hA.trans hAB
  have hdiff : Tendsto
      (fun x : ℝ => Chebyshev.theta (B * x) / x -
        Chebyshev.theta (A * x) / x) atTop (𝓝 (B - A)) :=
    (theta_relative_scale hB).sub (theta_relative_scale hA)
  have hpos := hdiff.eventually (eventually_gt_nhds (sub_pos.mpr hAB))
  filter_upwards [hpos, eventually_gt_atTop (0 : ℝ)] with x htheta hx
  have hthetaless : Chebyshev.theta (A * x) < Chebyshev.theta (B * x) := by
    have hquot : Chebyshev.theta (A * x) / x <
        Chebyshev.theta (B * x) / x := by linarith
    exact (div_lt_div_iff_of_pos_right hx).mp hquot
  classical
  by_contra! hnone
  have hsub : Nat.primesLE ⌊B * x⌋₊ ⊆ Nat.primesLE ⌊A * x⌋₊ := by
    intro q hq
    obtain ⟨hqB, hprime⟩ := Nat.mem_primesLE.mp hq
    have hqBx : (q : ℝ) ≤ B * x := (Nat.le_floor_iff (mul_nonneg hB.le hx.le)).mp hqB
    have hqAx : (q : ℝ) ≤ A * x := by
      by_contra! hlt
      exact (hnone q hprime hlt).not_ge hqBx
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor hqAx, hprime⟩
  have htheta_le : Chebyshev.theta (B * x) ≤ Chebyshev.theta (A * x) := by
    rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun q _ _ => Real.log_natCast_nonneg q)
  exact hthetaless.not_ge htheta_le

private theorem fixed_cardinality_prime_window {A B : ℝ}
    (hA : 0 < A) (hAB : A < B) (N : ℕ) : ∃ Y : ℝ, ∀ x : ℝ, Y ≤ x → ∃ S : Finset ℕ,
      S.card = N ∧ ∀ q ∈ S,
        q.Prime ∧ A * x < (q : ℝ) ∧ (q : ℝ) ≤ B * x := by
  classical
  induction N generalizing A B with
  | zero =>
      exact ⟨0, fun _ _ => ⟨∅, rfl, by simp⟩⟩
  | succ N ih =>
      let C : ℝ := (A + B) / 2
      have hAC : A < C := by dsimp [C]; linarith
      have hCB : C < B := by dsimp [C]; linarith
      have hC : 0 < C := hA.trans hAC
      obtain ⟨Y₁, hY₁⟩ := ih hA hAC
      obtain ⟨Y₂, hY₂⟩ := eventually_atTop.mp (eventually_prime_in_relative_window hC hCB)
      refine ⟨max 1 (max Y₁ Y₂), ?_⟩
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le (by norm_num)
        ((le_max_left 1 (max Y₁ Y₂)).trans hx)
      have hx₁ : Y₁ ≤ x := ((le_max_left Y₁ Y₂).trans (le_max_right 1 (max Y₁ Y₂))).trans hx
      have hx₂ : Y₂ ≤ x := ((le_max_right Y₁ Y₂).trans (le_max_right 1 (max Y₁ Y₂))).trans hx
      obtain ⟨S, hcard, hS⟩ := hY₁ x hx₁
      obtain ⟨q, hq, hqC, hqB⟩ := hY₂ x hx₂
      have hqS : q ∉ S := by
        intro hmem
        exact hqC.not_ge (hS q hmem).2.2
      refine ⟨insert q S, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hqS, hcard]
      · intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · exact ⟨hq, (mul_lt_mul_of_pos_right hAC hx0).trans hqC, hqB⟩
        · obtain ⟨hpprime, hpA, hpC⟩ := hS p hp
          exact ⟨hpprime, hpA, hpC.trans (mul_le_mul_of_nonneg_right hCB.le hx0.le)⟩

abbrev gain (p a : ℕ) : ℝ := goldenLayerMarginal p a * Real.log p

def LowerGainSupply : Prop := ∀ p a : ℕ, p.Prime → 1 ≤ a →
    (1 - (p : ℝ)⁻¹) * (p : ℝ)⁻¹ ^ a ≤ gain p a

def ExchangeSupply (m : ℕ) (lambda : ℝ) : Prop := ∀ D U : Finset ℕ, Disjoint D U →
    (∀ p ∈ D, p.Prime ∧ p ∣ m) → (∀ q ∈ U, q.Prime) →
    (∏ q ∈ U, q) < (∏ p ∈ D, p) →
    (∑ q ∈ U, gain q (m.factorization q + 1)) +
      lambda * (Real.log ((∏ p ∈ D, p : ℕ) : ℝ) -
        Real.log ((∏ q ∈ U, q : ℕ) : ℝ)) <
        ∑ p ∈ D, gain p (m.factorization p)

theorem gain_lower_window (hlower : LowerGainSupply)
    {p a k : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hak : a ≤ k)
    {Z W : ℝ} (hZ : 1 < Z) (hZp : Z ≤ p) (hpW : (p : ℝ) ≤ W) : (1 - Z⁻¹) * W⁻¹ ^ k ≤ gain p a := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hZ0 : 0 < Z := by linarith
  have hW0 : 0 < W := hp0.trans_le hpW
  have hinvZ : (p : ℝ)⁻¹ ≤ Z⁻¹ := (inv_le_inv₀ hp0 hZ0).mpr hZp
  have hinvW : W⁻¹ ≤ (p : ℝ)⁻¹ := (inv_le_inv₀ hW0 hp0).mpr hpW
  have hZinv : Z⁻¹ ≤ 1 := (inv_le_one₀ hZ0).mpr hZ.le
  have hproduct : (1 - Z⁻¹) * W⁻¹ ^ k ≤
      (1 - (p : ℝ)⁻¹) * (p : ℝ)⁻¹ ^ k :=
    mul_le_mul (by linarith) (pow_le_pow_left₀ (inv_nonneg.mpr hW0.le) hinvW k)
      (pow_nonneg (inv_nonneg.mpr hW0.le) _) (by linarith)
  exact hproduct.trans ((hlower p k hp (ha.trans hak)).trans
    (layer_gain_antitone hp ha hak))

theorem gain_upper_window {p a k : ℕ} (hp : p.Prime)
    (hk : 1 ≤ k) (hka : k ≤ a) {Z : ℝ} (hZ : 0 < Z) (hZp : Z ≤ p) : gain p a ≤ Z⁻¹ ^ k := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  exact (layer_gain_antitone hp hk hka).trans ((layer_gain_upper hp hk).trans
    (pow_le_pow_left₀ (inv_nonneg.mpr hp0.le)
      ((inv_le_inv₀ hp0 hZ).mpr hZp) k))

private theorem scaled_inverse_power {P C R : ℝ} {j : ℕ}
    (hP : 0 < P) (hC : 0 < C) (hR : R ^ j = P) : P * ((C * R)⁻¹) ^ j = (C ^ j)⁻¹ := by
  rw [inv_pow, mul_pow, hR]
  field_simp [hP.ne', (pow_pos hC j).ne']

theorem finite_products_lt {D U : Finset ℕ} {r s : ℕ} {L W : ℝ}
    (hDcard : D.card = r) (hUcard : U.card = s) (hL : 0 < L)
    (hD : ∀ p ∈ D, L ≤ (p : ℝ)) (hU : ∀ q ∈ U, (q : ℝ) ≤ W)
    (hratio : W ^ s / L ^ r < 1) : (∏ q ∈ U, q) < (∏ p ∈ D, p) := by
  have hupper : (∏ q ∈ U, (q : ℝ)) ≤ W ^ s := by
    calc
      _ ≤ ∏ _q ∈ U, W := Finset.prod_le_prod₀ (fun q _ => Nat.cast_nonneg q) hU
      _ = W ^ s := by simp [hUcard]
  have hlower : L ^ r ≤ ∏ p ∈ D, (p : ℝ) := by
    calc
      _ = ∏ _p ∈ D, L := by simp [hDcard]
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hL.le) hD
  have hlt : (∏ q ∈ U, (q : ℝ)) < ∏ p ∈ D, (p : ℝ) :=
    hupper.trans_lt (((div_lt_one (pow_pos hL r)).mp hratio).trans_le hlower)
  have hcast : ((∏ q ∈ U, q : ℕ) : ℝ) < ((∏ p ∈ D, p : ℕ) : ℝ) := by simpa only [Nat.cast_prod] using hlt
  exact_mod_cast hcast

theorem exchange_forbids_scaled_gain_bounds {m : ℕ} {lambda P l u : ℝ}
    (hcert : ExchangeSupply m lambda) (hlambda : 0 < lambda) (hP : 0 < P)
    (D U : Finset ℕ) (hdis : Disjoint D U)
    (hD : ∀ p ∈ D, p.Prime ∧ p ∣ m) (hU : ∀ q ∈ U, q.Prime)
    (hprod : (∏ q ∈ U, q) < (∏ p ∈ D, p))
    (hupper : ∀ p ∈ D, P * gain p (m.factorization p) ≤ l)
    (hlower : ∀ q ∈ U, u ≤ P * gain q (m.factorization q + 1))
    (hmargin : (D.card : ℝ) * l < (U.card : ℝ) * u) : False := by
  have hcert' := hcert D U hdis hD hU hprod
  have hUpos : (0 : ℝ) < (∏ q ∈ U, q) := by exact_mod_cast Finset.prod_pos (fun q hq => (hU q hq).pos)
  have hlog : 0 ≤ lambda *
      (Real.log ((∏ p ∈ D, p : ℕ) : ℝ) - Real.log ((∏ q ∈ U, q : ℕ) : ℝ)) :=
    mul_nonneg hlambda.le (sub_nonneg.mpr
      (Real.log_le_log hUpos (by exact_mod_cast hprod.le)))
  have hsum : (∑ q ∈ U, gain q (m.factorization q + 1)) <
      ∑ p ∈ D, gain p (m.factorization p) := by linarith
  have hscaled := mul_lt_mul_of_pos_left hsum hP
  rw [Finset.mul_sum, Finset.mul_sum] at hscaled
  have hlo := Finset.sum_le_sum hlower
  have hhi := Finset.sum_le_sum hupper
  simp only [Finset.sum_const, nsmul_eq_mul] at hlo hhi
  linarith

private theorem fixed_window_lower_barrier (hlower : LowerGainSupply)
    {j r : ℕ} (hj : 2 ≤ j) (hr : 1 ≤ r)
    {A B c : ℝ} (hA : 0 < A) (hAB : A < B) (hc : 0 < c) (hc1 : c < 1)
    (hmargin : (r : ℝ) / c < ((j * r - 1 : ℕ) : ℝ) / B ^ j) :
    ∃ P₀ : ℝ, 0 < P₀ ∧ ∀ m : ℕ, 0 < m → ∀ lambda : ℝ, 0 < lambda →
      ExchangeSupply m lambda → m.primeFactors = Nat.primesLE (largestPrime m) →
      P₀ ≤ (largestPrime m : ℝ) →
      A * (largestPrime m : ℝ) ^ ((j : ℝ)⁻¹) < (layerPrime m j : ℝ) := by
  classical
  let s : ℕ := j * r - 1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hj1 : (1 : ℝ) < j := by exact_mod_cast (show 1 < j by omega)
  have hinvj : 0 < (j : ℝ)⁻¹ := inv_pos.mpr hj0
  have hinvj1 : (j : ℝ)⁻¹ < 1 := (inv_lt_one₀ hj0).mpr hj1
  have hs : (s : ℝ) = (j : ℝ) * r - 1 := by
    dsimp [s]
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))), Nat.cast_mul, Nat.cast_one]
  have hneg : (j : ℝ)⁻¹ * s - 1 * (r : ℝ) < 0 := by
    have heq : (j : ℝ)⁻¹ * s - 1 * (r : ℝ) = -(j : ℝ)⁻¹ := by
      rw [hs]
      field_simp [hj0.ne']
      ring
    rw [heq]
    exact neg_neg_of_pos hinvj
  have hB : 0 < B := hA.trans hAB
  obtain ⟨Yq, hYq⟩ := fixed_cardinality_prime_window hA hAB s
  obtain ⟨Yp, hYp⟩ := fixed_cardinality_prime_window hc hc1 r
  have hroot : Tendsto (fun P : ℝ => P ^ ((j : ℝ)⁻¹)) atTop atTop := tendsto_rpow_atTop hinvj
  have hsep := scaled_power_ratio_tendsto_zero B c ((j : ℝ)⁻¹) 1 1 1
    (by simpa using sub_neg.mpr hinvj1)
  simp only [pow_one, Real.rpow_one] at hsep
  have hratio := scaled_power_ratio_tendsto_zero B c ((j : ℝ)⁻¹) 1 r s hneg
  simp only [Real.rpow_one] at hratio
  have hinv : Tendsto (fun P : ℝ => (A * P ^ ((j : ℝ)⁻¹))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (hroot.const_mul_atTop hA)
  have hgain : Tendsto
      (fun P : ℝ => ((s : ℝ) / B ^ j) * (1 - (A * P ^ ((j : ℝ)⁻¹))⁻¹))
      atTop (𝓝 ((s : ℝ) / B ^ j)) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hinv).const_mul
      ((s : ℝ) / B ^ j)
  have hgood : ∀ᶠ P : ℝ in atTop, ∀ m : ℕ, 0 < m → ∀ lambda : ℝ,
      0 < lambda → ExchangeSupply m lambda →
      m.primeFactors = Nat.primesLE (largestPrime m) →
      (largestPrime m : ℝ) = P → A * P ^ ((j : ℝ)⁻¹) < (layerPrime m j : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      hroot.eventually (eventually_ge_atTop Yq), eventually_ge_atTop Yp,
      (hroot.const_mul_atTop hA).eventually (eventually_gt_atTop (1 : ℝ)),
      hsep.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
      hratio.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
      hgain.eventually (eventually_gt_nhds hmargin)] with P hP hqth hpth hAroot hsep' hratio' hgain'
    intro m hm lambda hlambda hcert hsupport hPeq
    let R : ℝ := P ^ ((j : ℝ)⁻¹)
    have hR : 0 < R := Real.rpow_pos_of_pos hP _
    have hRpow : R ^ j = P := Real.rpow_inv_natCast_pow hP.le (by omega)
    have hseparate : B * R < c * P := (div_lt_one (mul_pos hc hP)).mp hsep'
    obtain ⟨U, hUcard, hU⟩ := hYq R hqth
    obtain ⟨D, hDcard, hD⟩ := hYp P hpth
    by_contra! hcut
    have hdis : Disjoint D U := Finset.disjoint_left.mpr (by
      intro p hpD hpU
      have hlo := (hD p hpD).2.1
      have hhi := (hU p hpU).2.2
      linarith)
    have hdonors : ∀ p ∈ D, p.Prime ∧ p ∣ m := by
      intro p hp
      obtain ⟨hpprime, _, hpP⟩ := hD p hp
      simp only [one_mul] at hpP
      have hpnat : p ≤ largestPrime m := by exact_mod_cast (hpP.trans_eq hPeq.symm)
      refine ⟨hpprime, Nat.dvd_of_mem_primeFactors ?_⟩
      rw [hsupport]
      exact Nat.mem_primesLE.mpr ⟨hpnat, hpprime⟩
    have hprod : (∏ q ∈ U, q) < (∏ p ∈ D, p) := finite_products_lt hDcard hUcard (mul_pos hc hP)
        (fun p hp => (hD p hp).2.1.le) (fun q hq => (hU q hq).2.2) hratio'
    have hupper : ∀ p ∈ D, P * gain p (m.factorization p) ≤ c⁻¹ := by
      intro p hp
      have hpprime := (hdonors p hp).1
      have hval : 1 ≤ m.factorization p :=
        (hpprime.dvd_iff_one_le_factorization hm.ne').mp (hdonors p hp).2
      have hbound := gain_upper_window hpprime (by norm_num : 1 ≤ 1) hval
        (mul_pos hc hP) (hD p hp).2.1.le
      have hscale : P * (c * P)⁻¹ ^ (1 : ℕ) = c⁻¹ := by
        simpa using scaled_inverse_power hP hc (j := 1) (R := P) (by simp)
      exact (mul_le_mul_of_nonneg_left hbound hP.le).trans_eq hscale
    have hlower' : ∀ q ∈ U,
        (1 - (A * R)⁻¹) * (B ^ j)⁻¹ ≤ P * gain q (m.factorization q + 1) := by
      intro q hq
      obtain ⟨hqprime, hqA, hqB⟩ := hU q hq
      have hQq : layerPrime m j < q := by exact_mod_cast (hcut.trans_lt hqA)
      have hval := valuation_above_layer_prime hm (by omega : 1 ≤ j) hqprime hQq
      have hbound := gain_lower_window hlower hqprime
        (by omega : 1 ≤ m.factorization q + 1) (by omega : m.factorization q + 1 ≤ j)
        hAroot hqA.le hqB
      have hscale := scaled_inverse_power hP hB hRpow
      calc
        _ = (1 - (A * R)⁻¹) * (P * (B * R)⁻¹ ^ j) := by rw [hscale]
        _ = P * ((1 - (A * R)⁻¹) * (B * R)⁻¹ ^ j) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hbound hP.le
    apply exchange_forbids_scaled_gain_bounds hcert hlambda hP D U hdis hdonors
      (fun q hq => (hU q hq).1) hprod hupper hlower'
    rw [hDcard, hUcard]
    simpa only [R, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hgain'
  obtain ⟨T, hT⟩ := eventually_atTop.mp hgood
  refine ⟨max 1 T, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro m hm lambda hlambda hcert hsupport hP
  exact hT (largestPrime m : ℝ) ((le_max_right 1 T).trans hP)
    m hm lambda hlambda hcert hsupport rfl

private theorem fixed_window_upper_barrier (hlower : LowerGainSupply)
    {j r : ℕ} (hj : 2 ≤ j) (hr : 1 ≤ r)
    {A B d : ℝ} (hA : 0 < A) (hAB : A < B) (hd : 1 < d)
    (hmargin : ((j * r + 1 : ℕ) : ℝ) / A ^ j < (r : ℝ) / d) :
    ∃ P₀ : ℝ, 0 < P₀ ∧ ∀ m : ℕ, 0 < m → ∀ lambda : ℝ, 0 < lambda →
      ExchangeSupply m lambda →
      (∀ p q : ℕ, p.Prime → q.Prime → p < q →
        m.factorization q ≤ m.factorization p) →
      m.primeFactors = Nat.primesLE (largestPrime m) →
      P₀ ≤ (largestPrime m : ℝ) →
      (layerPrime m j : ℝ) < B * (largestPrime m : ℝ) ^ ((j : ℝ)⁻¹) := by
  classical
  let s : ℕ := j * r + 1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hj1 : (1 : ℝ) < j := by exact_mod_cast (show 1 < j by omega)
  have hinvj : 0 < (j : ℝ)⁻¹ := inv_pos.mpr hj0
  have hinvj1 : (j : ℝ)⁻¹ < 1 := (inv_lt_one₀ hj0).mpr hj1
  have hs : (s : ℝ) = (j : ℝ) * r + 1 := by simp [s]
  have hneg : 1 * (r : ℝ) - (j : ℝ)⁻¹ * s < 0 := by
    have heq : 1 * (r : ℝ) - (j : ℝ)⁻¹ * s = -(j : ℝ)⁻¹ := by
      rw [hs]
      field_simp [hj0.ne']
      ring
    rw [heq]
    exact neg_neg_of_pos hinvj
  have hB : 0 < B := hA.trans hAB
  have hd0 : 0 < d := by linarith
  obtain ⟨Yq, hYq⟩ := fixed_cardinality_prime_window hA hAB s
  obtain ⟨Yp, hYp⟩ := fixed_cardinality_prime_window (by norm_num : (0 : ℝ) < 1) hd r
  have hroot : Tendsto (fun P : ℝ => P ^ ((j : ℝ)⁻¹)) atTop atTop := tendsto_rpow_atTop hinvj
  have hsep := scaled_power_ratio_tendsto_zero B 1 ((j : ℝ)⁻¹) 1 1 1
    (by simpa using sub_neg.mpr hinvj1)
  simp only [pow_one, Real.rpow_one, one_mul] at hsep
  have hratio := scaled_power_ratio_tendsto_zero d A 1 ((j : ℝ)⁻¹) s r hneg
  simp only [Real.rpow_one] at hratio
  have hgain : Tendsto
      (fun P : ℝ => ((r : ℝ) / d) * (1 - P⁻¹))
      atTop (𝓝 ((r : ℝ) / d)) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_inv_atTop_zero : Tendsto (fun P : ℝ => P⁻¹) atTop (𝓝 0))).const_mul
        ((r : ℝ) / d)
  have hgood : ∀ᶠ P : ℝ in atTop, ∀ m : ℕ, 0 < m → ∀ lambda : ℝ,
      0 < lambda → ExchangeSupply m lambda →
      (∀ p q : ℕ, p.Prime → q.Prime → p < q →
        m.factorization q ≤ m.factorization p) →
      m.primeFactors = Nat.primesLE (largestPrime m) →
      (largestPrime m : ℝ) = P → (layerPrime m j : ℝ) < B * P ^ ((j : ℝ)⁻¹) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      hroot.eventually (eventually_ge_atTop Yq), eventually_ge_atTop Yp,
      hsep.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
      hratio.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
      hgain.eventually (eventually_gt_nhds hmargin)] with P hP1 hqth hpth hsep' hratio' hgain'
    intro m hm lambda hlambda hcert hanti hsupport hPeq
    have hP : 0 < P := by linarith
    let R : ℝ := P ^ ((j : ℝ)⁻¹)
    have hR : 0 < R := Real.rpow_pos_of_pos hP _
    have hRpow : R ^ j = P := Real.rpow_inv_natCast_pow hP.le (by omega)
    have hseparate : B * R < P := (div_lt_one hP).mp hsep'
    obtain ⟨D, hDcard, hD⟩ := hYq R hqth
    obtain ⟨U, hUcard, hU⟩ := hYp P hpth
    by_contra! hcut
    have hdis : Disjoint D U := Finset.disjoint_left.mpr (by
      intro p hpD hpU
      have hlo := (hU p hpU).2.1
      have hhi := (hD p hpD).2.2
      simp only [one_mul] at hlo
      linarith)
    have hvalD : ∀ q ∈ D, j ≤ m.factorization q := by
      intro q hq
      have hqQ : q ≤ layerPrime m j := by exact_mod_cast ((hD q hq).2.2.trans hcut)
      exact valuation_below_layer_prime (hD q hq).1 hanti hqQ
    have hdonors : ∀ q ∈ D, q.Prime ∧ q ∣ m := by
      intro q hq
      refine ⟨(hD q hq).1, ((hD q hq).1.dvd_iff_one_le_factorization hm.ne').mpr ?_⟩
      exact (show 1 ≤ j by omega).trans (hvalD q hq)
    have hprod : (∏ p ∈ U, p) < (∏ q ∈ D, q) := finite_products_lt hDcard hUcard (mul_pos hA hR)
        (fun q hq => (hD q hq).2.1.le) (fun p hp => (hU p hp).2.2) hratio'
    have hupper : ∀ q ∈ D, P * gain q (m.factorization q) ≤ (A ^ j)⁻¹ := by
      intro q hq
      have hbound := gain_upper_window (hD q hq).1 (by omega : 1 ≤ j) (hvalD q hq)
        (mul_pos hA hR) (hD q hq).2.1.le
      exact (mul_le_mul_of_nonneg_left hbound hP.le).trans_eq
        (scaled_inverse_power hP hA hRpow)
    have hlower' : ∀ p ∈ U,
        (1 - P⁻¹) * d⁻¹ ≤ P * gain p (m.factorization p + 1) := by
      intro p hp
      obtain ⟨hpprime, hpP, hpd⟩ := hU p hp
      simp only [one_mul] at hpP
      have hpnot : p ∉ m.primeFactors := by
        rw [hsupport]
        intro hmem
        have hple := (Nat.mem_primesLE.mp hmem).1
        have hpleR : (p : ℝ) ≤ (largestPrime m : ℝ) := by exact_mod_cast hple
        rw [hPeq] at hpleR
        exact hpP.not_ge hpleR
      have hpval : m.factorization p = 0 := by
        apply Finsupp.notMem_support_iff.mp
        simpa only [Nat.support_factorization] using hpnot
      rw [hpval, zero_add]
      have hbound := gain_lower_window hlower hpprime (by norm_num : 1 ≤ 1)
        (by norm_num : 1 ≤ 1) hP1 hpP.le hpd
      have hscale : P * (d * P)⁻¹ ^ (1 : ℕ) = d⁻¹ := by
        simpa using scaled_inverse_power hP hd0 (j := 1) (R := P) (by simp)
      calc
        _ = (1 - P⁻¹) * (P * (d * P)⁻¹ ^ (1 : ℕ)) := by rw [hscale]
        _ = P * ((1 - P⁻¹) * (d * P)⁻¹ ^ (1 : ℕ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hbound hP.le
    apply exchange_forbids_scaled_gain_bounds hcert hlambda hP D U hdis hdonors
      (fun p hp => (hU p hp).1) hprod hupper hlower'
    rw [hDcard, hUcard]
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hgain'
  obtain ⟨T, hT⟩ := eventually_atTop.mp hgood
  refine ⟨max 1 T, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro m hm lambda hlambda hcert hanti hsupport hP
  exact hT (largestPrime m : ℝ) ((le_max_right 1 T).trans hP)
    m hm lambda hlambda hcert hanti hsupport rfl

theorem golden_layer_gain_lower {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    (1 - (p : ℝ)⁻¹) * (p : ℝ)⁻¹ ^ a ≤
      goldenLayerMarginal p a * Real.log p := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpInvPos : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hpPos
  have hpInvLt : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hpPos).mpr (by exact_mod_cast hp.one_lt)
  let x : ℝ := (p : ℝ)⁻¹
  let r : ℝ := x ^ a
  have hx : 0 < x := hpInvPos
  have hxl : x < 1 := hpInvLt
  have hr : 0 < r := pow_pos hx _
  have hr1 : r < 1 := pow_lt_one₀ hx.le hxl (by omega)
  have hden : 0 < 1 - r := sub_pos.mpr hr1
  have hnum : 0 < 1 - r * x := by
    have hpow : r * x = x ^ (a + 1) := by rw [show r = x ^ a by rfl, ← pow_succ]
    rw [hpow]
    exact sub_pos.mpr (pow_lt_one₀ hx.le hxl (by omega))
  have hratio : 0 < (1 - r * x) / (1 - r) := div_pos hnum hden
  have hlog := Real.one_sub_inv_le_log_of_pos hratio
  have hnum_le_one : 1 - r * x ≤ 1 := by
    have : 0 ≤ r * x := mul_nonneg hr.le hx.le
    linarith
  have hleft : r * (1 - x) ≤ r * (1 - x) / (1 - r * x) := by
    apply (le_div_iff₀ hnum).2
    have hnonneg : 0 ≤ r * (1 - x) := mul_nonneg hr.le (sub_nonneg.mpr hxl.le)
    nlinarith
  have hinv : 1 - ((1 - r * x) / (1 - r))⁻¹ = r * (1 - x) / (1 - r * x) := by
    field_simp
    ring
  have hcore : r * (1 - x) ≤ Real.log ((1 - r * x) / (1 - r)) := by
    rw [hinv] at hlog
    exact hleft.trans hlog
  have hlogp : 0 < Real.log (p : ℝ) := hp.log_pos
  unfold goldenLayerMarginal
  rw [div_mul_cancel₀ _ hlogp.ne']
  simpa [x, r, pow_succ, mul_comm, ← inv_pow] using hcore

private theorem local_insert_delta (lambda : ℝ) {p a : ℕ} (hp : p.Prime) :
    goldenPrimeLocalObjective lambda p (a + 1) -
        goldenPrimeLocalObjective lambda p a =
      (goldenLayerMarginal p (a + 1) - lambda) * Real.log p := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpLog : 0 < Real.log (p : ℝ) := hp.log_pos
  have hpInvPos : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hpPos
  have hpInvLt : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hpPos).mpr (by exact_mod_cast hp.one_lt)
  have ha : 0 < 1 - (p : ℝ)⁻¹ ^ (a + 1) := sub_pos.mpr (pow_lt_one₀ hpInvPos.le hpInvLt (by omega))
  have hb : 0 < 1 - (p : ℝ)⁻¹ ^ (a + 1 + 1) :=
    sub_pos.mpr (pow_lt_one₀ hpInvPos.le hpInvLt (by omega))
  unfold goldenPrimeLocalObjective goldenLayerMarginal
  rw [Real.log_div hb.ne' (sub_pos.mpr hpInvLt).ne',
    Real.log_div ha.ne' (sub_pos.mpr hpInvLt).ne', Real.log_div hb.ne' ha.ne']
  push_cast
  field_simp [hpLog.ne']
  ring

private theorem prime_product_factorization {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (p : ℕ) : (∏ q ∈ S, q).factorization p = if p ∈ S then 1 else 0 := by
  simpa [primePowerProduct] using
    (primeBlock_factorization hS (fun _ => 1) p)

private theorem objective_exchange_delta (lambda : ℝ) {m : ℕ}
    (hm : 0 < m) (D U : Finset ℕ)
    (hD : ∀ p ∈ D, p.Prime) (hU : ∀ q ∈ U, q.Prime)
    (hDvd : ∀ p ∈ D, p ∣ m) (hDU : Disjoint D U) : let d : ℕ := ∏ p ∈ D, p
    let u : ℕ := ∏ q ∈ U, q
    let n : ℕ := (m / d) * u
    goldenResourceObjective lambda n - goldenResourceObjective lambda m =
      (∑ q ∈ U,
          goldenLayerMarginal q (m.factorization q + 1) * Real.log q) -
        (∑ p ∈ D,
          goldenLayerMarginal p (m.factorization p) * Real.log p) +
        lambda * (Real.log d - Real.log u) := by
  classical
  dsimp
  let d : ℕ := ∏ p ∈ D, p
  let u : ℕ := ∏ q ∈ U, q
  let r : ℕ := m / d
  let n : ℕ := r * u
  have hDmem : D ⊆ m.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hD p hp, hDvd p hp, hm.ne'⟩
  have hdvd : d ∣ m := by
    dsimp [d]
    exact (Finset.prod_dvd_prod_of_subset D m.primeFactors id hDmem).trans
      (Nat.prod_primeFactors_dvd m)
  have hdpos : 0 < d := by
    dsimp [d]
    exact Finset.prod_pos (fun p hp => (hD p hp).pos)
  have hupos : 0 < u := by
    dsimp [u]
    exact Finset.prod_pos (fun q hq => (hU q hq).pos)
  have hrpos : 0 < r := Nat.div_pos (Nat.le_of_dvd hm hdvd) hdpos
  have hd0 : d ≠ 0 := hdpos.ne'
  have hu0 : u ≠ 0 := hupos.ne'
  have hr0 : r ≠ 0 := hrpos.ne'
  have hmd : r * d = m := by exact Nat.div_mul_cancel hdvd
  have hdfac (p : ℕ) : d.factorization p = if p ∈ D then 1 else 0 := by exact prime_product_factorization hD p
  have hufac (p : ℕ) : u.factorization p = if p ∈ U then 1 else 0 := by exact prime_product_factorization hU p
  have hmf (p : ℕ) : m.factorization p =
      r.factorization p + if p ∈ D then 1 else 0 := by
    rw [← hmd, Nat.factorization_mul hr0 hd0, Finsupp.add_apply, hdfac]
  have hnf (p : ℕ) : n.factorization p =
      r.factorization p + if p ∈ U then 1 else 0 := by
    rw [show n = r * u by rfl, Nat.factorization_mul hr0 hu0,
      Finsupp.add_apply, hufac]
  have hrdvd : r ∣ m := by exact Nat.div_dvd_of_dvd hdvd
  have hrsupp : r.primeFactors ⊆ m.primeFactors := Nat.primeFactors_mono hrdvd hm.ne'
  have huFactors : u.primeFactors = U := by
    dsimp [u]
    exact Nat.primeFactors_prod hU
  have hnsupp : n.primeFactors ⊆ m.primeFactors ∪ U := by
    rw [show n = r * u by rfl, Nat.primeFactors_mul hr0 hu0, huFactors]
    exact union_subset (hrsupp.trans subset_union_left) subset_union_right
  let s : Finset ℕ := m.primeFactors ∪ U
  have hnsupp' : n.primeFactors ⊆ s := by simpa [s] using hnsupp
  have hsum : goldenResourceObjective lambda n - goldenResourceObjective lambda m =
        ∑ p ∈ s,
          (goldenPrimeLocalObjective lambda p (n.factorization p) -
            goldenPrimeLocalObjective lambda p (m.factorization p)) := by
    have hnpos : 0 < n := Nat.mul_pos hrpos hupos
    rw [golden_resource_objective_sum_on lambda (Nat.one_le_iff_ne_zero.mpr hnpos.ne') s hnsupp',
      golden_resource_objective_sum_on lambda (Nat.one_le_iff_ne_zero.mpr hm.ne') s subset_union_left,
      ← Finset.sum_sub_distrib]
  let f : ℕ → ℝ := fun p =>
    goldenPrimeLocalObjective lambda p (n.factorization p) -
      goldenPrimeLocalObjective lambda p (m.factorization p)
  have hDUsub : D ∪ U ⊆ s := by
    intro p hp
    simp only [mem_union] at hp
    change p ∈ m.primeFactors ∪ U
    rcases hp with hpD | hpU
    · exact Finset.mem_union.mpr (Or.inl (hDmem hpD))
    · exact Finset.mem_union.mpr (Or.inr hpU)
  have hzero (p : ℕ) (hp : p ∈ s) (hpD : p ∉ D) (hpU : p ∉ U) : f p = 0 := by
    dsimp [f]
    rw [hnf, hmf, if_neg hpU, if_neg hpD]
    simp
  have hsumSupport : (∑ p ∈ D ∪ U, f p) = ∑ p ∈ s, f p := by
    apply Finset.sum_subset hDUsub
    intro p hpS hpDU
    rcases not_or.mp (by simpa only [mem_union] using hpDU) with ⟨hpD, hpU⟩
    exact hzero p hpS hpD hpU
  have hsumDU : (∑ p ∈ s, f p) = (∑ p ∈ D, f p) + (∑ p ∈ U, f p) := by rw [← hsumSupport, Finset.sum_union hDU]
  have hDterm (p : ℕ) (hp : p ∈ D) : goldenPrimeLocalObjective lambda p (n.factorization p) -
          goldenPrimeLocalObjective lambda p (m.factorization p) =
        -(goldenLayerMarginal p (m.factorization p) * Real.log p) +
          lambda * Real.log p := by
    have hpU : p ∉ U := by exact fun hp' => (Finset.disjoint_left.1 hDU hp hp').elim
    have hmf' : m.factorization p = r.factorization p + 1 := by simpa [hp] using hmf p
    have hnf' : n.factorization p = r.factorization p := by simpa [hpU] using hnf p
    rw [hnf', hmf']
    have hi := local_insert_delta lambda (hD p hp)
      (a := r.factorization p)
    nlinarith [hi]
  have hUterm (q : ℕ) (hq : q ∈ U) : goldenPrimeLocalObjective lambda q (n.factorization q) -
          goldenPrimeLocalObjective lambda q (m.factorization q) =
        goldenLayerMarginal q (m.factorization q + 1) * Real.log q -
          lambda * Real.log q := by
    have hqD : q ∉ D := by exact fun hp' => (Finset.disjoint_left.1 hDU hp' hq).elim
    have hmf' : m.factorization q = r.factorization q := by simpa [hqD] using hmf q
    have hnf' : n.factorization q = r.factorization q + 1 := by simpa [hq] using hnf q
    rw [hnf', hmf']
    convert local_insert_delta lambda (hU q hq) (a := r.factorization q) using 1 <;> ring
  rw [hsum, hsumDU]
  change
    (D.sum (fun p =>
        goldenPrimeLocalObjective lambda p (n.factorization p) -
          goldenPrimeLocalObjective lambda p (m.factorization p))) +
      (U.sum (fun q =>
        goldenPrimeLocalObjective lambda q (n.factorization q) -
          goldenPrimeLocalObjective lambda q (m.factorization q))) = _
  have hDsum : D.sum (fun p =>
          goldenPrimeLocalObjective lambda p (n.factorization p) -
            goldenPrimeLocalObjective lambda p (m.factorization p)) =
        D.sum (fun p =>
          -(goldenLayerMarginal p (m.factorization p) * Real.log p) +
            lambda * Real.log p) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact hDterm p hp
  have hUsum : U.sum (fun q =>
          goldenPrimeLocalObjective lambda q (n.factorization q) -
            goldenPrimeLocalObjective lambda q (m.factorization q)) =
        U.sum (fun q =>
          goldenLayerMarginal q (m.factorization q + 1) * Real.log q -
            lambda * Real.log q) := by
    apply Finset.sum_congr rfl
    intro q hq
    exact hUterm q hq
  rw [hDsum, hUsum]
  have hlogD : Real.log (d : ℝ) = ∑ p ∈ D, Real.log p := by
    rw [show (d : ℝ) = ∏ p ∈ D, (p : ℝ) by simp [d],
      Real.log_prod (fun p hp => by exact_mod_cast (hD p hp).ne_zero)]
  have hlogU : Real.log (u : ℝ) = ∑ q ∈ U, Real.log q := by
    rw [show (u : ℝ) = ∏ q ∈ U, (q : ℝ) by simp [u],
      Real.log_prod (fun q hq => by exact_mod_cast (hU q hq).ne_zero)]
  rw [hlogD, hlogU]
  have hDlin : D.sum (fun p =>
        -(goldenLayerMarginal p (m.factorization p) * Real.log p) +
          lambda * Real.log p) =
        -(D.sum (fun p =>
          goldenLayerMarginal p (m.factorization p) * Real.log p)) +
          lambda * (D.sum (fun p => Real.log p)) := by
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  have hUlin : U.sum (fun q =>
        goldenLayerMarginal q (m.factorization q + 1) * Real.log q -
          lambda * Real.log q) =
        (U.sum (fun q =>
          goldenLayerMarginal q (m.factorization q + 1) * Real.log q)) -
          lambda * (U.sum (fun q => Real.log q)) := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hDlin, hUlin]
  ring

theorem signed_exchange_certificate (lambda : ℝ) {m : ℕ}
    (hm : 0 < m)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m)
    (D U : Finset ℕ)
    (hD : ∀ p ∈ D, p.Prime) (hU : ∀ q ∈ U, q.Prime)
    (hDvd : ∀ p ∈ D, p ∣ m) (hDU : Disjoint D U)
    (hprod : (∏ q ∈ U, q) < ∏ p ∈ D, p) : let d : ℕ := ∏ p ∈ D, p
    let u : ℕ := ∏ q ∈ U, q
    let n : ℕ := (m / d) * u
    0 < n ∧ n < m ∧
      (∑ q ∈ U,
          goldenLayerMarginal q (m.factorization q + 1) * Real.log q) +
          lambda * (Real.log d - Real.log u) <
        ∑ p ∈ D,
          goldenLayerMarginal p (m.factorization p) * Real.log p := by
  classical
  dsimp
  let d : ℕ := ∏ p ∈ D, p
  let u : ℕ := ∏ q ∈ U, q
  let r : ℕ := m / d
  let n : ℕ := r * u
  have hDmem : D ⊆ m.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hD p hp, hDvd p hp, hm.ne'⟩
  have hdvd : d ∣ m := by
    dsimp [d]
    exact (Finset.prod_dvd_prod_of_subset D m.primeFactors id hDmem).trans
      (Nat.prod_primeFactors_dvd m)
  have hdpos : 0 < d := by
    dsimp [d]
    exact Finset.prod_pos (fun p hp => (hD p hp).pos)
  have hupos : 0 < u := by
    dsimp [u]
    exact Finset.prod_pos (fun q hq => (hU q hq).pos)
  have hrpos : 0 < r := Nat.div_pos (Nat.le_of_dvd hm hdvd) hdpos
  have hnpos : 0 < n := Nat.mul_pos hrpos hupos
  have hnm : n < m := by
    rw [show m = r * d by exact (Nat.div_mul_cancel hdvd).symm]
    exact Nat.mul_lt_mul_of_pos_left hprod hrpos
  have hdelta := objective_exchange_delta lambda hm D U hD hU hDvd hDU
  have hdelta' : goldenResourceObjective lambda n - goldenResourceObjective lambda m =
        (∑ q ∈ U,
            goldenLayerMarginal q (m.factorization q + 1) * Real.log q) -
          (∑ p ∈ D,
            goldenLayerMarginal p (m.factorization p) * Real.log p) +
          lambda * (Real.log d - Real.log u) := by simpa [d, u, r, n] using hdelta
  have hrec := hrecord n hnpos hnm
  have hcert : (∑ q ∈ U,
          goldenLayerMarginal q (m.factorization q + 1) * Real.log q) +
          lambda * (Real.log d - Real.log u) <
        ∑ p ∈ D,
          goldenLayerMarginal p (m.factorization p) * Real.log p := by linarith [hrec, hdelta']
  exact ⟨hnpos, hnm, hcert⟩

private def FullPredecessorRecord (m : ℕ) (lambda : ℝ) : Prop := ∀ n : ℕ, 0 < n → n < m →
    goldenResourceObjective lambda n < goldenResourceObjective lambda m

private def LowerBarrierSupply (L : ℕ → ℕ → ℕ) : Prop := ∀ (j r : ℕ), 2 ≤ j → 1 ≤ r → ∀ (A B c : ℝ),
    0 < A → A < B → 0 < c → c < 1 →
    (r : ℝ) / c < ((j * r - 1 : ℕ) : ℝ) / B ^ j →
    ∃ T : ℝ, 0 < T ∧
      ∀ (m : ℕ), 2 ≤ m → ∀ (lambda : ℝ), 0 < lambda →
        FullPredecessorRecord m lambda →
        T ≤ (largestPrime m : ℝ) →
          A * (largestPrime m : ℝ) ^ ((j : ℝ)⁻¹) < (L m j : ℝ)

private def UpperBarrierSupply (L : ℕ → ℕ → ℕ) : Prop := ∀ (j r : ℕ), 2 ≤ j → 1 ≤ r → ∀ (A B d : ℝ),
    0 < A → A < B → 1 < d →
    ((j * r + 1 : ℕ) : ℝ) / A ^ j < (r : ℝ) / d →
    ∃ T : ℝ, 0 < T ∧
      ∀ (m : ℕ), 2 ≤ m → ∀ (lambda : ℝ), 0 < lambda →
        FullPredecessorRecord m lambda →
        T ≤ (largestPrime m : ℝ) →
          (L m j : ℝ) < B * (largestPrime m : ℝ) ^ ((j : ℝ)⁻¹)

private theorem lower_window_parameters {j : ℕ} (hj : 2 ≤ j)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hej : epsilon < j) : ∃ A B c : ℝ, ∃ r s : ℕ,
      0 < A ∧ A < B ∧ 0 < c ∧ c < 1 ∧ 1 ≤ r ∧ s = j * r - 1 ∧
      (j : ℝ) - epsilon < A ^ j ∧ (r : ℝ) / c < (s : ℝ) / B ^ j := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hjne : j ≠ 0 := by omega
  let x : ℝ := j - 3 * epsilon / 4
  let y : ℝ := j - epsilon / 2
  have hx : 0 < x := by dsimp [x]; linarith
  have hy : 0 < y := by dsimp [y]; linarith
  have hxy : x < y := by dsimp [x, y]; linarith
  let A : ℝ := x ^ ((j : ℝ)⁻¹)
  let B : ℝ := y ^ ((j : ℝ)⁻¹)
  have hA : 0 < A := Real.rpow_pos_of_pos hx _
  have hAB : A < B := Real.rpow_lt_rpow hx.le hxy (inv_pos.mpr hjpos)
  have hApow : A ^ j = x := Real.rpow_inv_natCast_pow hx.le hjne
  have hBpow : B ^ j = y := Real.rpow_inv_natCast_pow hy.le hjne
  obtain ⟨r, hrR⟩ := exists_nat_gt (max (1 : ℝ) (2 / epsilon))
  have hr1 : (1 : ℝ) < r := (le_max_left _ _).trans_lt hrR
  have hr : 1 ≤ r := by exact_mod_cast hr1.le
  have hrpos : (0 : ℝ) < r := lt_trans zero_lt_one hr1
  have hbig : 1 < (r : ℝ) * epsilon / 2 := by
    have h := (div_lt_iff₀ hepsilon).mp ((le_max_right _ _).trans_lt hrR)
    nlinarith
  let s : ℕ := j * r - 1
  have hjr : 2 ≤ j * r := by simpa using Nat.mul_le_mul hj hr
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hscast : (s : ℝ) = (j : ℝ) * r - 1 := by
    dsimp [s]
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  have hgap : y * r < s := by dsimp [y]; nlinarith
  let k : ℝ := y * r / s
  have hkpos : 0 < k := div_pos (mul_pos hy hrpos) hspos
  have hk1 : k < 1 := (div_lt_one hspos).mpr hgap
  let c : ℝ := (k + 1) / 2
  have hcpos : 0 < c := by dsimp [c]; linarith
  have hc1 : c < 1 := by dsimp [c]; linarith
  have hkc : k < c := by dsimp [c]; linarith
  have hkprod : k * s = y * r := div_mul_cancel₀ _ hspos.ne'
  refine ⟨A, B, c, r, s, hA, hAB, hcpos, hc1, hr, rfl, ?_, ?_⟩
  · rw [hApow]
    dsimp [x]
    linarith
  · rw [hBpow]
    apply (div_lt_div_iff₀ hcpos hy).mpr
    have h := mul_lt_mul_of_pos_right hkc hspos
    rw [hkprod] at h
    nlinarith

private theorem upper_window_parameters {j : ℕ} (hj : 2 ≤ j)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) : ∃ A B d : ℝ, ∃ r s : ℕ,
      0 < A ∧ A < B ∧ 1 < d ∧ 1 ≤ r ∧ s = j * r + 1 ∧
      B ^ j < (j : ℝ) + epsilon ∧ (s : ℝ) / A ^ j < (r : ℝ) / d := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hjne : j ≠ 0 := by omega
  let x : ℝ := j + epsilon / 3
  let y : ℝ := j + 2 * epsilon / 3
  have hx : 0 < x := by dsimp [x]; linarith
  have hy : 0 < y := by dsimp [y]; linarith
  have hxy : x < y := by dsimp [x, y]; linarith
  let A : ℝ := x ^ ((j : ℝ)⁻¹)
  let B : ℝ := y ^ ((j : ℝ)⁻¹)
  have hA : 0 < A := Real.rpow_pos_of_pos hx _
  have hAB : A < B := Real.rpow_lt_rpow hx.le hxy (inv_pos.mpr hjpos)
  have hApow : A ^ j = x := Real.rpow_inv_natCast_pow hx.le hjne
  have hBpow : B ^ j = y := Real.rpow_inv_natCast_pow hy.le hjne
  obtain ⟨r, hrR⟩ := exists_nat_gt (max (1 : ℝ) (3 / epsilon))
  have hr1 : (1 : ℝ) < r := (le_max_left _ _).trans_lt hrR
  have hr : 1 ≤ r := by exact_mod_cast hr1.le
  have hrpos : (0 : ℝ) < r := lt_trans zero_lt_one hr1
  have hbig : 1 < (r : ℝ) * epsilon / 3 := by
    have h := (div_lt_iff₀ hepsilon).mp ((le_max_right _ _).trans_lt hrR)
    nlinarith
  let s : ℕ := j * r + 1
  have hspos : (0 : ℝ) < s := by positivity
  have hscast : (s : ℝ) = (j : ℝ) * r + 1 := by dsimp [s]; push_cast; rfl
  have hgap : (s : ℝ) < x * r := by dsimp [x]; nlinarith
  let k : ℝ := x * r / s
  have hk1 : 1 < k := (one_lt_div hspos).mpr hgap
  let d : ℝ := (1 + k) / 2
  have hd1 : 1 < d := by dsimp [d]; linarith
  have hdk : d < k := by dsimp [d]; linarith
  have hkprod : k * s = x * r := div_mul_cancel₀ _ hspos.ne'
  refine ⟨A, B, d, r, s, hA, hAB, hd1, hr, rfl, ?_, ?_⟩
  · rw [hBpow]
    dsimp [y]
    linarith
  · rw [hApow]
    apply (div_lt_div_iff₀ hx (lt_trans zero_lt_one hd1)).mpr
    have h := mul_lt_mul_of_pos_right hdk hspos
    rw [hkprod] at h
    nlinarith

private theorem rigidity_from_window_barriers (L : ℕ → ℕ → ℕ)
    (lower : LowerBarrierSupply L) (upper : UpperBarrierSupply L) :
    ∀ j : ℕ, 2 ≤ j → ∀ epsilon : ℝ, 0 < epsilon →
      ∃ T : ℝ, 0 < T ∧
        ∀ (m : ℕ), 2 ≤ m → ∀ (lambda : ℝ), 0 < lambda →
          FullPredecessorRecord m lambda →
          T ≤ (largestPrime m : ℝ) →
            |(L m j : ℝ) ^ j / (largestPrime m : ℝ) - (j : ℝ)| < epsilon := by
  intro j hj epsilon hepsilon
  let delta : ℝ := min (epsilon / 2) ((j : ℝ) / 2)
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hdelta : 0 < delta := lt_min (by positivity) (by positivity)
  have hdelta_j : delta < (j : ℝ) := by exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨Al, Bl, cl, rl, sl, hAl, hAlBl, hcl, hcl1, hrl, hsl,
      hAlpow, hmarginl⟩ := lower_window_parameters hj hdelta hdelta_j
  obtain ⟨Tl, hTl, hlower⟩ := lower j rl hj hrl Al Bl cl hAl hAlBl hcl hcl1
    (by simpa [hsl] using hmarginl)
  obtain ⟨Au, Bu, du, ru, su, hAu, hAuBu, hdu, hru, hsu,
      hBupow, hmarginu⟩ := upper_window_parameters hj hepsilon
  obtain ⟨Tu, hTu, hupper⟩ := upper j ru hj hru Au Bu du hAu hAuBu hdu
    (by simpa [hsu] using hmarginu)
  have hBu : 0 < Bu := hAu.trans hAuBu
  refine ⟨max 1 (max Tl Tu), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro m hm lambda hlam hrecord hT
  have hP1 : (1 : ℝ) ≤ (largestPrime m : ℝ) := (le_max_left 1 (max Tl Tu)).trans hT
  have hP : 0 < (largestPrime m : ℝ) := lt_of_lt_of_le (by norm_num) hP1
  let P : ℝ := largestPrime m
  let R : ℝ := P ^ ((j : ℝ)⁻¹)
  have hR : 0 < R := Real.rpow_pos_of_pos hP _
  have hRpow : R ^ j = P := Real.rpow_inv_natCast_pow hP.le (by omega)
  have hTlP : Tl ≤ (largestPrime m : ℝ) :=
    (le_max_left Tl Tu).trans ((le_max_right 1 (max Tl Tu)).trans hT)
  have hTuP : Tu ≤ (largestPrime m : ℝ) :=
    (le_max_right Tl Tu).trans ((le_max_right 1 (max Tl Tu)).trans hT)
  have hlow := hlower m hm lambda hlam hrecord hTlP
  have hupp := hupper m hm lambda hlam hrecord hTuP
  have hAR : 0 < Al * (largestPrime m : ℝ) ^ ((j : ℝ)⁻¹) := by simpa [R, P] using mul_pos hAl hR
  have hLpos : 0 < (L m j : ℝ) := hAR.trans hlow
  have hpowlow : (Al * R) ^ j < (L m j : ℝ) ^ j :=
    pow_lt_pow_left₀ hlow (mul_pos hAl hR).le (by omega)
  have hpowupp : (L m j : ℝ) ^ j < (Bu * R) ^ j := pow_lt_pow_left₀ hupp hLpos.le (by omega)
  have hAlratio : Al ^ j < (L m j : ℝ) ^ j / P := by
    have h := hpowlow
    rw [mul_pow, hRpow] at h
    exact (lt_div_iff₀ hP).mpr h
  have hBuratio : (L m j : ℝ) ^ j / P < Bu ^ j := by
    have h := hpowupp
    rw [mul_pow, hRpow] at h
    exact (div_lt_iff₀ hP).mpr h
  have hratio_lower : (j : ℝ) - delta <
      (L m j : ℝ) ^ j / P := hAlpow.trans hAlratio
  have hratio_upper : (L m j : ℝ) ^ j / P < (j : ℝ) + epsilon := hBuratio.trans hBupow
  have hratio_nonneg : 0 ≤ (L m j : ℝ) ^ j / P :=
    div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hP.le
  have hdelta_eps : delta < epsilon := by
    calc
      delta ≤ epsilon / 2 := min_le_left _ _
      _ < epsilon := by linarith
  change |(L m j : ℝ) ^ j / P - (j : ℝ)| < epsilon
  rw [abs_lt]
  constructor
  · linarith [hratio_lower]
  · exact sub_lt_iff_lt_add'.mpr hratio_upper

/-- Each fixed prime-layer ratio tends uniformly to its layer index over all
full predecessor records at a positive price. -/
theorem price_record_fixed_layer_rigidity (j : ℕ) (hj : 2 ≤ j)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ T : ℝ, 0 < T ∧ ∀ m : ℕ, 2 ≤ m → ∀ lambda : ℝ, 0 < lambda →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
      T ≤ (largestPrime m : ℝ) →
      |(layerPrime m j : ℝ) ^ j / (largestPrime m : ℝ) - (j : ℝ)| < epsilon := by
  have lowerGain : LowerGainSupply := by
    intro p a hp ha
    exact golden_layer_gain_lower hp ha
  have exchange (m : ℕ) (lambda : ℝ) (hm : 0 < m)
      (hrecord : ∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) :
      ExchangeSupply m lambda := by
    intro D U hdis hD hU hprod
    have hcert := signed_exchange_certificate lambda hm hrecord D U
      (fun p hp => (hD p hp).1) hU (fun p hp => (hD p hp).2) hdis hprod
    exact hcert.2.2
  have lower : LowerBarrierSupply layerPrime := by
    intro j r hj hr A B c hA hAB hc hc1 hmargin
    obtain ⟨T, hT, hbarrier⟩ := fixed_window_lower_barrier lowerGain hj hr hA hAB hc hc1 hmargin
    refine ⟨T, hT, ?_⟩
    intro m hm lambda hlambda hrecord hP
    have hstructure := price_record_prime_structure hm hlambda hrecord
    exact hbarrier m (by omega) lambda hlambda
      (exchange m lambda (by omega) hrecord) hstructure.2 hP
  have upper : UpperBarrierSupply layerPrime := by
    intro j r hj hr A B d hA hAB hd hmargin
    obtain ⟨T, hT, hbarrier⟩ := fixed_window_upper_barrier lowerGain hj hr hA hAB hd hmargin
    refine ⟨T, hT, ?_⟩
    intro m hm lambda hlambda hrecord hP
    have hstructure := price_record_prime_structure hm hlambda hrecord
    exact hbarrier m (by omega) lambda hlambda
      (exchange m lambda (by omega) hrecord) hstructure.1 hstructure.2 hP
  exact rigidity_from_window_barriers layerPrime lower upper j hj epsilon hepsilon

#print axioms price_record_fixed_layer_rigidity

end D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
