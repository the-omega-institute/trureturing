/- GID: D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization
   mirror-E: none(waiver:elementary-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Uniform BHP boundary-price localization on full original records. -/
/- proof_shape: content
admission_basis: escape-witness
utility: none. The actual-record construction is an unbounded conditional
mathematical argument. All prime counts, valuations and fees retain their
original hypotheses; the prescribed full bank and RH remain open. -/
import D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization

open Finset Filter Real
open scoped Topology BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (price_record_prime_structure)
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
  (layerPrime valuation_below_layer_prime valuation_above_layer_prime
   signed_exchange_certificate)
open D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity
  (record_ratio_limit coarse_scale_limits)
open D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
  (powerSum powerSumDerivative beta logarithmicSlope powerSum_hasDerivAt
   powerSum_pos gain_pos beta_pos beta_nat beta_le_inv_pow_log)

/-- Full recordhood includes EVERY positive smaller integer, with no support cap. -/
private theorem actual_boundary_price_from_count_and_first_pools (j : ℕ) (hj : 2 ≤ j) :
    ∃ T : ℝ, 0 < T ∧ ∀ C c X : ℝ, 0 < C → 0 < c → 2 ≤ X →
      (∀ x : ℝ, X ≤ x →
        c * x ^ bhpExponent / log x ≤ ((primesIn (x - C * x ^ bhpExponent) x).card : ℝ) ∧
        c * x ^ bhpExponent / log x ≤ ((primesIn x (x + C * x ^ bhpExponent)).card : ℝ)) →
      ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
      T ≤ (largestPrime m : ℝ) →
      let P : ℝ := largestPrime m
      let Q : ℝ := layerPrime m j
      let K : ℕ := comparisonCount j P
      let w : ℝ := C * Q ^ bhpExponent
      X ≤ Q → (K : ℝ) + 1 ≤ c * Q ^ bhpExponent / log Q →
      w ≤ Q / 2 → (layerPrime m (j + 1) : ℝ) < Q - w →
      Q + w ≤ (layerPrime m (j - 1) : ℝ) →
      ∀ v : ℝ, 0 ≤ v → v ≤ P / 2 → ∀ FirstLo FirstHi : Finset ℕ,
      FirstLo.card = K → FirstHi.card = K →
      (∀ p ∈ FirstLo, p.Prime ∧ P - v ≤ (p : ℝ) ∧ (p : ℝ) ≤ P) →
      (∀ p ∈ FirstHi, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ P + v) →
      |beta j Q - beta 1 P| ≤
        priceLip j (Q / 2) * w + priceLip 1 (P / 2) * v +
          (8 * (j : ℝ) / (K : ℝ)) * (beta 1 P + priceLip 1 (P / 2) * v) := by
  obtain ⟨T, hT, hfinite⟩ := actual_boundary_price_from_pools j hj
  refine ⟨T, hT, ?_⟩
  intro C c X hC hc hX hcount m hm mu hmu hrecord hlarge
  dsimp only
  intro hXQ hcapacity hwidth hbelow habove v hv hvP FirstLo FirstHi hFLc hFUc hFL hFU
  obtain ⟨Lo, Hi, hLoc, hHic, hLo, hHi⟩ := counted_higher_pools hcount hXQ hcapacity
  have hw : 0 ≤ C * (layerPrime m j : ℝ) ^ bhpExponent :=
    mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  apply hfinite m hm mu hmu hrecord hlarge _ v hw hwidth hv hvP
    Lo Hi FirstLo FirstHi hLoc hHic hFLc hFUc
  · intro p hp
    have hh := hLo p hp
    refine ⟨hh.1, hh.2.1, hh.2.2, ?_⟩
    exact_mod_cast (hbelow.trans_le hh.2.1)
  · intro p hp
    have hh := hHi p hp
    refine ⟨hh.1, hh.2.1, hh.2.2, ?_⟩
    exact_mod_cast (hh.2.2.trans habove)
  · exact hFL
  · exact hFU

/- Direct count route at the first boundary.  These are the only first-pool
constructors retained.  The same two-sided count is used at P here and at the
actual higher boundary Q in `actual_boundary_price_from_count_and_first_pools`.
All numerical thresholds precede the original full record and its price. -/
private theorem priceExponent_pos {j : ℕ} (hj : 2 ≤ j) : 0 < priceExponent j := by
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  unfold priceExponent
  positivity

private theorem priceExponent_le {j : ℕ} (hj : 2 ≤ j) : priceExponent j ≤ 19 / 80 := by
  have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj
  unfold priceExponent
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 40 * j) (by norm_num)).mpr
  nlinarith

private theorem count_bounds {j : ℕ} (hj : 2 ≤ j) {P : ℝ} (hP : 1 ≤ P) :
    P ^ priceExponent j ≤ (comparisonCount j P : ℝ) ∧
      (comparisonCount j P : ℝ) ≤ 2 * P ^ priceExponent j := by
  have hp : 0 ≤ P ^ priceExponent j := Real.rpow_nonneg (by linarith) _
  have hp1 : 1 ≤ P ^ priceExponent j := by
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hP
      (priceExponent_pos hj).le
  exact ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one hp).le.trans (by linarith)⟩

/-- Consumed numerical helper. The logarithmic capacity follows directly from
the PINNED `_root_.isLittleO_log_rpow_atTop`, with positive exponent theta-gamma.
The radius bound uses the PINNED `tendsto_rpow_neg_atTop` at 19/40. -/
private theorem uniform_first_count_capacity_and_radius (j : ℕ) (hj : 2 ≤ j)
    (C c X : ℝ) (hC : 0 < C) (hc : 0 < c) :
    ∃ T : ℝ, 0 < T ∧ ∀ P : ℝ, T ≤ P →
      4 ≤ P ∧ X ≤ P ∧
      0 ≤ C * P ^ bhpExponent ∧ C * P ^ bhpExponent ≤ P / 2 ∧
      (comparisonCount j P : ℝ) + 1 ≤ c * P ^ bhpExponent / log P := by
  have hgamma := priceExponent_pos hj
  have hdiff : 0 < bhpExponent - priceExponent j := by
    have hle := priceExponent_le hj
    norm_num [bhpExponent] at *
    linarith
  have hlog : Tendsto (fun P : ℝ => log P / P ^ (bhpExponent - priceExponent j))
      atTop (𝓝 0) :=
    (_root_.isLittleO_log_rpow_atTop hdiff).tendsto_div_nhds_zero
  have hsmall : Tendsto (fun P : ℝ => C * P ^ (-(19 / 40 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 19 / 40)).const_mul C
  have hevent : ∀ᶠ P : ℝ in atTop,
      4 ≤ P ∧ X ≤ P ∧
      0 ≤ C * P ^ bhpExponent ∧ C * P ^ bhpExponent ≤ P / 2 ∧
      (comparisonCount j P : ℝ) + 1 ≤ c * P ^ bhpExponent / log P := by
    filter_upwards [eventually_ge_atTop (4 : ℝ), eventually_ge_atTop X,
      hlog.eventually (eventually_lt_nhds (show (0 : ℝ) < c / 3 by positivity)),
      hsmall.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with P hP hXP htail hrad
    have hP0 : 0 < P := by linarith
    have hlogP : 0 < log P := Real.log_pos (by linarith : 1 < P)
    have hpow0 : 0 < P ^ priceExponent j := Real.rpow_pos_of_pos hP0 _
    have hpow1 : 1 ≤ P ^ priceExponent j := by
      calc
        1 = P ^ (0 : ℝ) := (Real.rpow_zero P).symm
        _ ≤ P ^ priceExponent j :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hgamma.le
    have hceil : (comparisonCount j P : ℝ) < P ^ priceExponent j + 1 := by
      exact Nat.ceil_lt_add_one hpow0.le
    have hK : (comparisonCount j P : ℝ) + 1 ≤ 3 * P ^ priceExponent j := by
      linarith
    have htail' : log P ≤ (c / 3) * P ^ (bhpExponent - priceExponent j) :=
      (div_le_iff₀ (Real.rpow_pos_of_pos hP0 _)).mp htail.le
    have hproduct : P ^ priceExponent j * P ^ (bhpExponent - priceExponent j) =
        P ^ bhpExponent := by
      rw [← Real.rpow_add hP0]
      congr 1
      ring
    have hcapacity : 3 * P ^ priceExponent j ≤ c * P ^ bhpExponent / log P := by
      apply (le_div_iff₀ hlogP).mpr
      calc
        3 * P ^ priceExponent j * log P = 3 * (P ^ priceExponent j * log P) := by ring
        _ ≤ 3 * (P ^ priceExponent j *
            ((c / 3) * P ^ (bhpExponent - priceExponent j))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left htail' hpow0.le) (by norm_num)
        _ = c * (P ^ priceExponent j * P ^ (bhpExponent - priceExponent j)) := by ring
        _ = c * P ^ bhpExponent := by rw [hproduct]
    have hradius : C * P ^ bhpExponent / P ≤ (1 / 2 : ℝ) := by
      have he : bhpExponent - 1 = -(19 / 40 : ℝ) := by norm_num [bhpExponent]
      rw [mul_div_assoc, ← Real.rpow_sub_one hP0.ne', he]
      exact hrad.le
    exact ⟨hP, hXP, mul_nonneg hC.le (Real.rpow_nonneg hP0.le _),
      by linarith [(div_le_iff₀ hP0).mp hradius], hK.trans hcapacity⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  refine ⟨max 4 T, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) (le_max_left _ _), ?_⟩
  intro P hP
  exact hT P ((le_max_right _ _).trans hP)

/-- Reusable, consumed count-to-first-pools helper. `hcount` is exactly the
witness telescope of the EXISTING `BHPShortIntervalCount`, at every real x.
It is used at x=P. The existing subset-card proof `counted_higher_pools`
erases P from the upper CLOSED interval, paying at most one prime. No
primality assumption on the natural centre P is needed, so this also applies
to the actual prime `largestPrime m`. Constants precede P, m and mu. -/
theorem uniform_counted_first_pools (j : ℕ) (hj : 2 ≤ j)
    (C c X : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hcount : ∀ x : ℝ, X ≤ x →
      c * x ^ bhpExponent / log x ≤
        ((primesIn (x - C * x ^ bhpExponent) x).card : ℝ) ∧
      c * x ^ bhpExponent / log x ≤
        ((primesIn x (x + C * x ^ bhpExponent)).card : ℝ)) :
    ∃ T : ℝ, 0 < T ∧ ∀ P : ℕ, T ≤ (P : ℝ) →
      4 ≤ (P : ℝ) ∧
      0 ≤ C * (P : ℝ) ^ bhpExponent ∧
      C * (P : ℝ) ^ bhpExponent ≤ (P : ℝ) / 2 ∧
      ∃ FirstLo FirstHi : Finset ℕ,
        FirstLo.card = comparisonCount j P ∧ FirstHi.card = comparisonCount j P ∧
        (∀ p ∈ FirstLo, p.Prime ∧
          (P : ℝ) - C * (P : ℝ) ^ bhpExponent ≤ (p : ℝ) ∧ (p : ℝ) ≤ P) ∧
        (∀ p ∈ FirstHi, p.Prime ∧
          (P : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (P : ℝ) + C * (P : ℝ) ^ bhpExponent) := by
  obtain ⟨T, hT, hscalar⟩ := uniform_first_count_capacity_and_radius j hj C c X hC hc
  refine ⟨T, hT, ?_⟩
  intro P hP
  obtain ⟨hP4, hXP, hv, hvP, hcapacity⟩ := hscalar P hP
  obtain ⟨FirstLo, FirstHi, hLo, hHi, hLoP, hHiP⟩ :=
    counted_higher_pools hcount hXP hcapacity
  exact ⟨hP4, hv, hvP, FirstLo, FirstHi, hLo, hHi, hLoP, hHiP⟩

private theorem largestPrime_prime {m : ℕ} (hm : 2 ≤ m) : (largestPrime m).Prime := by
  classical
  obtain ⟨p, hp, he⟩ := exists_mem_eq_sup m.primeFactors
    (Nat.nonempty_primeFactors.mpr (by omega)) id
  have hP : largestPrime m = p := he
  rw [hP]
  exact Nat.prime_of_mem_primeFactors hp

private theorem layerPrime_one {m : ℕ} (hm : 2 ≤ m) :
    layerPrime m 1 = largestPrime m := by
  classical
  have hf : m.primeFactors.filter (fun p => 1 ≤ m.factorization p) = m.primeFactors := by
    apply filter_eq_self.mpr
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd (by omega)
      (Nat.dvd_of_mem_primeFactors hp)
  unfold layerPrime
  rw [hf]
  exact max_eq_right (largestPrime_prime hm).one_lt.le

/- The following three analytic lemmas use only the frozen fixed-layer ratio.
Their filters need not be nontrivial: uniform thresholds are recovered on the
space of ALL records, not along a selected family of records. -/
private theorem layer_scale_limit {α : Type*} {l : Filter α}
    (P Q : α → ℝ) (j : ℕ) (hj : 2 ≤ j) (hQ : ∀ x, 0 ≤ Q x)
    (hP : Tendsto P l atTop)
    (hR : Tendsto (fun x => Q x ^ j / P x) l (𝓝 (j : ℝ))) :
    Tendsto (fun x => Q x / P x ^ ((j : ℝ)⁻¹))
      l (𝓝 ((j : ℝ) ^ ((j : ℝ)⁻¹))) := by
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hh := hR.rpow_const (p := (j : ℝ)⁻¹) (Or.inl hj0.ne')
  apply hh.congr'
  filter_upwards [hP.eventually_gt_atTop 0] with x hx
  rw [Real.div_rpow (pow_nonneg (hQ x) _) hx.le]
  rw [Real.pow_rpow_inv_natCast (hQ x) (by omega : j ≠ 0)]

private theorem separated_scale_limit {α : Type*} {l : Filter α}
    (P U V : α → ℝ) {a b c d : ℝ} (hab : a < b) (hd : d ≠ 0)
    (hP : Tendsto P l atTop)
    (hU : Tendsto (fun x => U x / P x ^ a) l (𝓝 c))
    (hV : Tendsto (fun x => V x / P x ^ b) l (𝓝 d)) :
    Tendsto (fun x => U x / V x) l (𝓝 0) := by
  have hz : Tendsto (fun x => P x ^ (a - b)) l (𝓝 0) := by
    have he : -(b - a) = a - b := by ring
    simpa only [Function.comp_def, he] using
      (_root_.tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp hP
  have hh := (hU.div hV hd).mul hz
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [hP.eventually_gt_atTop 0, hV.eventually_ne hd] with x hx hv
  have hv0 : V x ≠ 0 := by
    intro he
    apply hv
    simp [he]
  dsimp only [Pi.div_apply]
  rw [Real.rpow_sub hx]
  field_simp [hv0, (Real.rpow_pos_of_pos hx a).ne', (Real.rpow_pos_of_pos hx b).ne']
  <;> ring

private theorem count_capacity_limit {α : Type*} {l : Filter α}
    (P Q : α → ℝ) (j : ℕ) (hj : 2 ≤ j) (hQnonneg : ∀ x, 0 ≤ Q x)
    (hP : Tendsto P l atTop)
    (hR : Tendsto (fun x => Q x ^ j / P x) l (𝓝 (j : ℝ))) :
    Tendsto (fun x => P x ^ priceExponent j * log (Q x) / Q x ^ bhpExponent)
      l (𝓝 0) := by
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  let a : ℝ := (j : ℝ)⁻¹
  let d : ℝ := a * bhpExponent - priceExponent j
  have hd : 0 < d := by
    have he : d = 1 / (20 * (j : ℝ)) := by
      dsimp [d, a, bhpExponent, priceExponent]
      rw [inv_eq_one_div]
      field_simp [hj0.ne'] <;> ring
    rw [he]
    positivity
  have hscale := layer_scale_limit P Q j hj hQnonneg hP hR
  have hlog := (coarse_scale_limits P Q j hj hQnonneg hP hR).2.1
  have hQ := (coarse_scale_limits P Q j hj hQnonneg hP hR).1
  have hc : (j : ℝ) ^ ((j : ℝ)⁻¹) ≠ 0 := (Real.rpow_pos_of_pos hj0 _).ne'
  have hc' : ((j : ℝ) ^ ((j : ℝ)⁻¹)) ^ bhpExponent ≠ 0 :=
    (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hj0 _) _).ne'
  have hz := (_root_.isLittleO_log_rpow_atTop hd).tendsto_div_nhds_zero.comp hP
  have hh := (hlog.div (hscale.rpow_const (Or.inl hc)) hc').mul hz
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [hP.eventually_gt_atTop 1, hQ.eventually_gt_atTop 1] with x hp hq
  have hp0 : 0 < P x := by linarith
  have hq0 : 0 < Q x := by linarith
  have hpA := Real.rpow_pos_of_pos hp0 a
  have hpD := Real.rpow_pos_of_pos hp0 d
  have hqB := Real.rpow_pos_of_pos hq0 bhpExponent
  have he : (P x ^ a) ^ bhpExponent = P x ^ d * P x ^ priceExponent j := by
    rw [← Real.rpow_mul hp0.le, ← Real.rpow_add hp0]
    dsimp [d]
    congr 1 <;> ring
  dsimp [Function.comp_def]
  change (log (Q x) / log (P x)) /
    ((Q x / P x ^ a) ^ bhpExponent) * (log (P x) / P x ^ d) = _
  rw [Real.div_rpow hq0.le hpA.le, he]
  field_simp [hpA.ne', hpD.ne', hqB.ne',
    (Real.rpow_pos_of_pos hp0 (priceExponent j)).ne', (Real.log_pos hp).ne']
  <;> ring

private theorem higher_width_limit {α : Type*} {l : Filter α}
    (Q : α → ℝ) (hQ : Tendsto Q l atTop) (C : ℝ) :
    Tendsto (fun x => C * Q x ^ bhpExponent / Q x) l (𝓝 0) := by
  have hh := ((_root_.tendsto_rpow_neg_atTop
    (by norm_num [bhpExponent] : 0 < 1 - bhpExponent)).comp hQ).const_mul C
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [hQ.eventually_gt_atTop 0] with x hx
  have he : -(1 - bhpExponent) = bhpExponent - 1 := by ring
  dsimp only [Function.comp_def]
  rw [he, Real.rpow_sub hx, Real.rpow_one]
  ring

/-- M2: actual higher-layer capacity and both adjacent support separations,
uniformly over all original full records.  The j=2 upper support is identified
with the SAME integer's largest prime, by `layerPrime_one` above. -/
theorem uniform_higher_geometry (j : ℕ) (hj : 2 ≤ j)
    (C c X : ℝ) (hC : 0 < C) (hc : 0 < c) :
    ∃ T : ℝ, 0 < T ∧ ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu →
      FullRecord m mu → T ≤ (largestPrime m : ℝ) →
      let P : ℝ := largestPrime m
      let Q : ℝ := layerPrime m j
      let K : ℕ := comparisonCount j P
      let w : ℝ := C * Q ^ bhpExponent
      X ≤ Q ∧ (K : ℝ) + 1 ≤ c * Q ^ bhpExponent / log Q ∧
        w ≤ Q / 2 ∧ (layerPrime m (j + 1) : ℝ) < Q - w ∧
        Q + w ≤ (layerPrime m (j - 1) : ℝ) ∧ P ≤ Q ^ j := by
  let S := {v : ℕ × ℝ // 2 ≤ v.1 ∧ 0 < v.2 ∧ FullRecord v.1 v.2}
  let m : S → ℕ := fun x => x.1.1
  let mu : S → ℝ := fun x => x.1.2
  let P : S → ℝ := fun x => largestPrime (m x)
  let Q : S → ℝ := fun x => layerPrime (m x) j
  let U : S → ℝ := fun x => layerPrime (m x) (j + 1)
  let V : S → ℝ := fun x => layerPrime (m x) (j - 1)
  let l : Filter S := comap P atTop
  have hP : Tendsto P l atTop := tendsto_comap
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hj1 : (1 : ℝ) < j := by exact_mod_cast (show 1 < j by omega)
  have hR := record_ratio_limit m mu (fun x => x.2.1) (fun x => x.2.2.1)
    (fun x => x.2.2.2) j hj hP
  have hRU := record_ratio_limit m mu (fun x => x.2.1) (fun x => x.2.2.1)
    (fun x => x.2.2.2) (j + 1) (by omega) hP
  have hQnonneg : ∀ x, 0 ≤ Q x := fun _ => Nat.cast_nonneg _
  have hQ := (coarse_scale_limits P Q j hj hQnonneg hP hR).1
  have hscaleQ := layer_scale_limit P Q j hj hQnonneg hP hR
  have hscaleU := layer_scale_limit P U (j + 1) (by omega)
    (fun _ => Nat.cast_nonneg _) hP hRU
  have hsepU : Tendsto (fun x => U x / Q x) l (𝓝 0) := by
    apply separated_scale_limit P U Q
      (by simpa only [one_div] using
        one_div_lt_one_div_of_lt hj0 (show (j : ℝ) < (j + 1 : ℕ) by push_cast; linarith))
      (Real.rpow_pos_of_pos hj0 _).ne' hP hscaleU hscaleQ
  have hsepV : Tendsto (fun x => Q x / V x) l (𝓝 0) := by
    by_cases he : j = 2
    · subst j
      have hv : V = P := by
        funext x
        change (layerPrime (m x) 1 : ℝ) = (largestPrime (m x) : ℝ)
        exact_mod_cast layerPrime_one x.2.1
      rw [hv]
      exact (coarse_scale_limits P Q 2 (by norm_num) hQnonneg hP hR).2.2
    · have hjm : 2 ≤ j - 1 := by omega
      have hjm0 : 0 < ((j - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < j - 1 by omega)
      have hRV := record_ratio_limit m mu (fun x => x.2.1) (fun x => x.2.2.1)
        (fun x => x.2.2.2) (j - 1) hjm hP
      have hscaleV := layer_scale_limit P V (j - 1) hjm
        (fun _ => Nat.cast_nonneg _) hP hRV
      have hjlt : ((j - 1 : ℕ) : ℝ) < (j : ℝ) := by
        exact_mod_cast (Nat.sub_lt (by omega : 0 < j) (by norm_num : 0 < 1))
      apply separated_scale_limit P Q V
        (by simpa only [one_div] using one_div_lt_one_div_of_lt hjm0 hjlt)
        (Real.rpow_pos_of_pos hjm0 _).ne' hP hscaleQ hscaleV
  have hwidth := higher_width_limit Q hQ C
  have hcapacity := count_capacity_limit P Q j hj hQnonneg hP hR
  have hbelow : Tendsto (fun x => (U x + C * Q x ^ bhpExponent) / Q x) l (𝓝 0) := by
    simpa only [add_div, add_zero] using hsepU.add hwidth
  have habove : Tendsto (fun x => (Q x + C * Q x ^ bhpExponent) / V x) l (𝓝 0) := by
    have hh := ((tendsto_const_nhds (x := (1 : ℝ))).add hwidth).mul hsepV
    simp only [add_zero, mul_zero] at hh
    apply hh.congr'
    filter_upwards [hQ.eventually_gt_atTop 0] with x hx
    by_cases hv : V x = 0
    · simp [hv]
    · field_simp [hx.ne', hv] <;> ring
  have he : ∀ᶠ x in l,
      X ≤ Q x ∧ ((comparisonCount j (P x) : ℝ) + 1 ≤
        c * Q x ^ bhpExponent / log (Q x)) ∧
      C * Q x ^ bhpExponent ≤ Q x / 2 ∧
      U x < Q x - C * Q x ^ bhpExponent ∧
      Q x + C * Q x ^ bhpExponent ≤ V x ∧ P x ≤ Q x ^ j := by
    filter_upwards [hQ.eventually_ge_atTop X, hQ.eventually_gt_atTop 1,
      hP.eventually_ge_atTop 1,
      hwidth.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hcapacity.eventually (eventually_lt_nhds (show (0 : ℝ) < c / 3 by positivity)),
      hbelow.eventually (eventually_lt_nhds zero_lt_one),
      habove.eventually (eventually_lt_nhds zero_lt_one),
      hR.eventually (eventually_gt_nhds hj1)] with x hx hq hp hw hcapa hlo hup hratio
    have hq0 : 0 < Q x := by linarith
    have hp0 : 0 < P x := by linarith
    have hlq : 0 < log (Q x) := Real.log_pos hq
    have hpB : 0 < Q x ^ bhpExponent := Real.rpow_pos_of_pos hq0 _
    have hcount := (count_bounds hj hp).2
    have hpγ1 : 1 ≤ P x ^ priceExponent j := by
      simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hp (priceExponent_pos hj).le
    have hcap' := (div_lt_iff₀ hpB).mp hcapa
    have hfirst : (comparisonCount j (P x) : ℝ) + 1 ≤
        c * Q x ^ bhpExponent / log (Q x) := by
      apply (le_div_iff₀ hlq).mpr
      have hK3 : (comparisonCount j (P x) : ℝ) + 1 ≤ 3 * P x ^ priceExponent j := by
        linarith
      have hh := mul_le_mul_of_nonneg_right hK3 hlq.le
      nlinarith
    have hv0 : 0 < V x := by
      have : 1 ≤ layerPrime (m x) (j - 1) := le_max_left _ _
      dsimp [V]
      exact_mod_cast (show 0 < layerPrime (m x) (j - 1) by omega)
    have hw' := (div_lt_iff₀ hq0).mp hw
    have hlo' := (div_lt_iff₀ hq0).mp hlo
    have hup' := (div_lt_iff₀ hv0).mp hup
    have hr' := (lt_div_iff₀ hp0).mp hratio
    exact ⟨hx, hfirst, by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_comap.mp he)
  refine ⟨max T 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro n hn nu hnu hrec hlarge
  let x : S := ⟨(n, nu), hn, hnu, hrec⟩
  exact hT (largestPrime n : ℝ) ((le_max_left T 1).trans hlarge) x rfl

/- Explicit normalization: no boundary-price estimate occurs in these premises.
Only Q^j >= P and the already supplied coarse logarithmic scale are used. -/
theorem first_beta_lower {P : ℝ} (hP : 2 ≤ P) :
    1 / (P * log P) ≤ 2 * beta 1 P := by
  have hp0 : 0 < P := by linarith
  have hlp : 0 < log P := Real.log_pos (by linarith)
  have hh := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + 1 / P by positivity)
  have he : 1 - (1 + 1 / P)⁻¹ = 1 / (P + 1) := by
    field_simp [hp0.ne', (show P + 1 ≠ 0 by positivity)] <;> ring
  rw [he] at hh
  have hsmall : 1 / (2 * P) ≤ 1 / (P + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hgain : 1 / (2 * P) ≤ HigherLayerLogSlope.gain 1 P := by
    simpa [HigherLayerLogSlope.gain, powerSum] using hsmall.trans hh
  have h := div_le_div_of_nonneg_right hgain hlp.le
  change 1 / (2 * P) / log P ≤ beta 1 P at h
  have he' : 1 / (P * log P) = 2 * (1 / (2 * P) / log P) := by
    field_simp [hp0.ne', hlp.ne'] <;> ring
  rw [he']
  linarith

theorem priceLip_half_bound (j : ℕ) {P Q D : ℝ}
    (hP : 1 < P) (hQ : 4 ≤ Q) (hD : 0 < D)
    (hlog : log P / D ≤ log (Q / 2)) :
    priceLip j (Q / 2) ≤
      (((j : ℝ) + 2) * (2 : ℝ) ^ (j + 1) * D) / (Q ^ (j + 1) * log P) := by
  have hq0 : 0 < Q := by linarith
  have hLQ : 0 < log (Q / 2) := Real.log_pos (by linarith)
  have hLP : 0 < log P := Real.log_pos hP
  have he : priceLip j (Q / 2) =
      (((j : ℝ) + 2) * (2 : ℝ) ^ (j + 1)) / (Q ^ (j + 1) * log (Q / 2)) := by
    unfold priceLip
    rw [div_pow, pow_succ Q, pow_succ (2 : ℝ)]
    field_simp [hq0.ne', hLQ.ne'] <;> ring
  rw [he]
  calc
    _ ≤ (((j : ℝ) + 2) * (2 : ℝ) ^ (j + 1)) /
        (Q ^ (j + 1) * (log P / D)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hlog (pow_nonneg hq0.le _)
    _ = _ := by field_simp [hD.ne', hLP.ne', hq0.ne'] <;> ring

private def higherCostConstant (j : ℕ) : ℝ :=
  ((j : ℝ) + 2) * (2 : ℝ) ^ (j + 1) * (4 * (j : ℝ))

private def firstCostConstant (A : ℝ) : ℝ := 192 * A * (2 : ℝ) ^ bhpExponent

private def totalCostConstant (j : ℕ) (A C : ℝ) : ℝ :=
  2 * C * higherCostConstant j + firstCostConstant A +
    8 * (j : ℝ) * (1 + firstCostConstant A)

/-- M3, a scalar bound on the literal cost expression, with the exact ceil count.
In particular no localization, pools, normalized error premise, or asymptotic
claim at a growing layer is an input to this normalization. -/
private theorem normalized_cost_bound (j : ℕ) (hj : 2 ≤ j)
    {A C P Q : ℝ} (hA : 0 < A) (hC : 0 < C) (hP : 4 ≤ P) (hQ : 4 ≤ Q)
    (hPQ : P ≤ Q ^ j) (hlog : log P / (4 * (j : ℝ)) ≤ log (Q / 2)) :
    let K := comparisonCount j P
    let w := C * Q ^ bhpExponent
    let v := 2 * A * (K : ℝ) * (2 * P) ^ bhpExponent
    priceLip j (Q / 2) * w + priceLip 1 (P / 2) * v +
      (8 * (j : ℝ) / (K : ℝ)) * (beta 1 P + priceLip 1 (P / 2) * v) ≤
        totalCostConstant j A C * beta 1 P * P ^ (-priceExponent j) := by
  dsimp only
  let K := comparisonCount j P
  let t := P ^ (-priceExponent j)
  let lambda := beta 1 P
  let Bj := higherCostConstant j
  let E := firstCostConstant A
  let v := 2 * A * (K : ℝ) * (2 * P) ^ bhpExponent
  have hp0 : 0 < P := by linarith
  have hq0 : 0 < Q := by linarith
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hLP : 0 < log P := Real.log_pos (by linarith)
  have hγ := priceExponent_pos hj
  have ht0 : 0 < t := Real.rpow_pos_of_pos hp0 _
  have ht1 : t ≤ 1 := by
    dsimp [t]
    simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ P by linarith)
      (show -priceExponent j ≤ 0 by linarith)
  have hlam : 0 < lambda := beta_pos (by linarith) (by norm_num)
  have hBj : 0 ≤ Bj := by dsimp [Bj, higherCostConstant]; positivity
  have hE : 0 ≤ E := by dsimp [E, firstCostConstant]; positivity
  have hbase : 1 / (P * log P) ≤ 2 * lambda := first_beta_lower (by linarith)
  have hQexp : Q ^ (bhpExponent - 1) ≤ t := by
    have hh := Real.rpow_le_rpow_of_nonpos hp0 hPQ (neg_nonpos.mpr hγ.le)
    have he : (Q ^ j) ^ (-priceExponent j) = Q ^ (bhpExponent - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
      congr 1
      dsimp [priceExponent, bhpExponent]
      field_simp [hj0.ne'] <;> ring
    rwa [he] at hh
  have hQpow : Q ^ bhpExponent = Q ^ (bhpExponent - 1) * Q := by
    calc
      _ = Q ^ ((bhpExponent - 1) + 1) := by congr 1 <;> ring
      _ = _ := by rw [Real.rpow_add hq0, Real.rpow_one]
  have hhigh : priceLip j (Q / 2) * (C * Q ^ bhpExponent) ≤
      (2 * C * Bj) * lambda * t := by
    have hLip := priceLip_half_bound j (by linarith : 1 < P) hQ
      (by positivity : 0 < 4 * (j : ℝ)) hlog
    change priceLip j (Q / 2) ≤ Bj / (Q ^ (j + 1) * log P) at hLip
    calc
      _ ≤ Bj / (Q ^ (j + 1) * log P) * (C * Q ^ bhpExponent) := by
        exact mul_le_mul_of_nonneg_right hLip (by positivity)
      _ = (C * Bj) * (1 / (Q ^ j * log P)) * Q ^ (bhpExponent - 1) := by
        rw [hQpow, pow_succ]
        field_simp [hq0.ne', hLP.ne'] <;> ring
      _ ≤ (C * Bj) * (1 / (P * log P)) * t := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le hBj)
          exact one_div_le_one_div_of_le (by positivity)
            (mul_le_mul_of_nonneg_right hPQ hLP.le)
        · exact hQexp
        · positivity
        · positivity
      _ ≤ (C * Bj) * (2 * lambda) * t := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbase (mul_nonneg hC.le hBj)) ht0.le
      _ = _ := by ring
  have hlogP : log P / 2 ≤ log (P / 2) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hP
    have he : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [he] at hh
    rw [Real.log_div hp0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    linarith
  have hLip1 : priceLip 1 (P / 2) ≤ 24 / (P ^ 2 * log P) := by
    have hh := priceLip_half_bound 1 (by linarith : 1 < P) hP
      (by norm_num : (0 : ℝ) < 2) hlogP
    norm_num at hh
    exact hh
  have hv : v ≤ (4 * A * (2 : ℝ) ^ bhpExponent) * P ^ (priceExponent j + bhpExponent) := by
    calc
      _ ≤ 2 * A * (2 * P ^ priceExponent j) * (2 * P) ^ bhpExponent := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (count_bounds hj (by linarith)).2 (by positivity))
          (Real.rpow_nonneg (by positivity) _)
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hp0.le,
          Real.rpow_add hp0]
        ring
  have hPexp : P ^ (priceExponent j + bhpExponent - 1) ≤ t := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    have := priceExponent_le hj
    change priceExponent j + (21 / 40 : ℝ) - 1 ≤ -priceExponent j
    linarith
  have hPpow : P ^ (priceExponent j + bhpExponent) =
      P ^ (priceExponent j + bhpExponent - 1) * P := by
    calc
      _ = P ^ ((priceExponent j + bhpExponent - 1) + 1) := by congr 1 <;> ring
      _ = _ := by rw [Real.rpow_add hp0, Real.rpow_one]
  have hfirst : priceLip 1 (P / 2) * v ≤ E * lambda * t := by
    calc
      _ ≤ (24 / (P ^ 2 * log P)) *
          ((4 * A * (2 : ℝ) ^ bhpExponent) * P ^ (priceExponent j + bhpExponent)) := by
        apply mul_le_mul hLip1 hv
        · dsimp [v]; positivity
        · positivity
      _ = (96 * A * (2 : ℝ) ^ bhpExponent) * (1 / (P * log P)) *
          P ^ (priceExponent j + bhpExponent - 1) := by
        rw [hPpow]
        field_simp [hp0.ne', hLP.ne'] <;> ring
      _ ≤ (96 * A * (2 : ℝ) ^ bhpExponent) * (2 * lambda) * t := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hbase (by positivity)
        · exact hPexp
        · positivity
        · positivity
      _ = E * lambda * t := by dsimp [E, firstCostConstant]; ring
  have hK0 : 0 < (K : ℝ) := by
    have hh : 0 < K := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hp0 _)
    exact_mod_cast hh
  have hKinv : 1 / (K : ℝ) ≤ t := by
    have hh := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hp0 _)
      (count_bounds hj (by linarith)).1
    simpa [t, Real.rpow_neg hp0.le, one_div] using hh
  have hfirst' : priceLip 1 (P / 2) * v ≤ E * lambda := by
    exact hfirst.trans (mul_le_of_le_one_right (mul_nonneg hE hlam.le) ht1)
  have h8 : 8 * (j : ℝ) / (K : ℝ) ≤ 8 * (j : ℝ) * t := by
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      mul_le_mul_of_nonneg_left hKinv (show 0 ≤ 8 * (j : ℝ) by positivity)
  have hover : (8 * (j : ℝ) / (K : ℝ)) * (lambda + priceLip 1 (P / 2) * v) ≤
      (8 * (j : ℝ) * (1 + E)) * lambda * t := by
    have hsum : lambda + priceLip 1 (P / 2) * v ≤ lambda * (1 + E) := by
      nlinarith
    calc
      _ ≤ (8 * (j : ℝ) * t) * (lambda * (1 + E)) := by
        apply mul_le_mul h8 hsum
        · have hv0 : 0 ≤ v := by dsimp [v]; positivity
          have := mul_nonneg (priceLip_nonneg 1 (by linarith : 2 ≤ P / 2)) hv0
          linarith
        · positivity
      _ = _ := by ring
  change priceLip j (Q / 2) * (C * Q ^ bhpExponent) + priceLip 1 (P / 2) * v +
    (8 * (j : ℝ) / (K : ℝ)) * (lambda + priceLip 1 (P / 2) * v) ≤
      totalCostConstant j A C * lambda * t
  have he : totalCostConstant j A C * lambda * t =
      (2 * C * Bj) * lambda * t + E * lambda * t +
        (8 * (j : ℝ) * (1 + E)) * lambda * t := by
    dsimp [totalCostConstant, Bj, E]
    ring
  rw [he]
  linarith

/-- M4: the full original endpoint, using only the count supplier in its proof.
The maximum-gap premise remains in `BHPBoundaryPriceClaim` with its exact
original meaning. j is fixed before the uniform constant and threshold;
mu remains the original arbitrary positive record price throughout. -/
theorem bhp_boundary_price_localization : BHPBoundaryPriceClaim := by
  intro _hmaximum hcounted
  obtain ⟨C, c, Xc, hC, hc, hXc, hcount⟩ := hcounted
  intro j hj
  obtain ⟨Tf, hTf, hfinite⟩ := actual_boundary_price_from_count_and_first_pools j hj
  obtain ⟨Tg, hTg, hgeometry⟩ := uniform_higher_geometry j hj C c Xc hC hc
  obtain ⟨Tp, hTp, hpools⟩ := uniform_counted_first_pools j hj C c Xc hC hc hcount
  obtain ⟨Tc, hTc, hcoarse⟩ := uniform_coarse_geometry j hj
  let T := max (max Tf Tg) (max Tp Tc)
  have hconstant : 0 < totalCostConstant j C C := by
    have hj0 : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
    dsimp [totalCostConstant, higherCostConstant, firstCostConstant]
    positivity
  refine ⟨totalCostConstant j C C, T, hconstant, ?_, ?_⟩
  · exact hTf.trans_le ((le_max_left Tf Tg).trans (le_max_left _ _))
  intro m hm mu hmu hrecord hlarge
  have hf : Tf ≤ (largestPrime m : ℝ) :=
    ((le_max_left Tf Tg).trans (le_max_left _ _)).trans hlarge
  have hg : Tg ≤ (largestPrime m : ℝ) :=
    ((le_max_right Tf Tg).trans (le_max_left _ _)).trans hlarge
  have hp : Tp ≤ (largestPrime m : ℝ) :=
    ((le_max_left Tp Tc).trans (le_max_right _ _)).trans hlarge
  have ht : Tc ≤ (largestPrime m : ℝ) :=
    ((le_max_right Tp Tc).trans (le_max_right _ _)).trans hlarge
  obtain ⟨hXQ, hcapacity, hwidth, hbelow, habove, hpower⟩ :=
    hgeometry m hm mu hmu hrecord hg
  obtain ⟨_hP4first, hv, hvP, FirstLo, FirstHi, hFLc, hFUc, hFL, hFU⟩ :=
    hpools (largestPrime m) hp
  obtain ⟨hP4, hQ4, _hQP, _hQ2P, hlog⟩ := hcoarse m hm mu hmu hrecord ht
  let P : ℝ := largestPrime m
  let Q : ℝ := layerPrime m j
  let K : ℕ := comparisonCount j P
  let v : ℝ := C * P ^ bhpExponent
  let V : ℝ := 2 * C * (K : ℝ) * (2 * P) ^ bhpExponent
  have hbound : |beta j Q - beta 1 P| ≤
      priceLip j (Q / 2) * (C * Q ^ bhpExponent) + priceLip 1 (P / 2) * v +
        (8 * (j : ℝ) / (K : ℝ)) * (beta 1 P + priceLip 1 (P / 2) * v) :=
    hfinite C c Xc hC hc hXc hcount m hm mu hmu hrecord hf
      hXQ hcapacity hwidth hbelow habove v hv hvP
      FirstLo FirstHi hFLc hFUc hFL hFU
  have hP0 : 0 < P := by change 0 < (largestPrime m : ℝ); linarith
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by
    have hKpos : 0 < K := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hP0 _)
    exact_mod_cast (show 1 ≤ K by omega)
  have hvV : v ≤ V := by
    have hpow : P ^ bhpExponent ≤ (2 * P) ^ bhpExponent :=
      Real.rpow_le_rpow hP0.le (by linarith) (by norm_num [bhpExponent])
    calc
      v ≤ C * (2 * P) ^ bhpExponent := mul_le_mul_of_nonneg_left hpow hC.le
      _ ≤ (2 * C * (K : ℝ)) * (2 * P) ^ bhpExponent := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
        nlinarith
      _ = V := rfl
  have herror : priceLip 1 (P / 2) * v ≤ priceLip 1 (P / 2) * V :=
    mul_le_mul_of_nonneg_left hvV (priceLip_nonneg 1 (by
      change 2 ≤ (largestPrime m : ℝ) / 2
      linarith))
  have hcost :
      priceLip j (Q / 2) * (C * Q ^ bhpExponent) + priceLip 1 (P / 2) * v +
        (8 * (j : ℝ) / (K : ℝ)) * (beta 1 P + priceLip 1 (P / 2) * v) ≤
      totalCostConstant j C C * beta 1 P * P ^ (-priceExponent j) := by
    calc
      _ ≤ priceLip j (Q / 2) * (C * Q ^ bhpExponent) + priceLip 1 (P / 2) * V +
          (8 * (j : ℝ) / (K : ℝ)) * (beta 1 P + priceLip 1 (P / 2) * V) :=
        add_le_add (add_le_add_right herror _)
          (mul_le_mul_of_nonneg_left (add_le_add_right herror _) (by positivity))
      _ ≤ _ := normalized_cost_bound j hj hC hC hP4 hQ4 hpower hlog
  exact hbound.trans hcost

end D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
