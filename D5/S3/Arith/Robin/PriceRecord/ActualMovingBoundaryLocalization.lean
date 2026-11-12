/- GID: D5/S3/Arith/Robin/PriceRecord/ActualMovingBoundaryLocalization
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualMovingBoundaryLocalization
   mirror-E: none(waiver:finite-quantitative-analysis)
   anchors: []
   utility: none
   digest: One-sided displaced-root localization at the original full record. -/
import D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
import D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
import D5.S3.Arith.Robin.PriceRecord.HigherLayerInsertionRegret
import D5.S3.Arith.Robin.PriceRecord.ActualHigherLayerQuantitativeBudgetRepair

/-! Finite one-sided localization without exact probe valuations. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualMovingBoundaryLocalization
open Finset Real
open scoped BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (price_record_prime_structure)
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
open D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
open D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
open D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff

/- The finite exchanges below precede any adjacent-layer separation. Insertion
above Q_j uses v_p(m)+1<=j; deletion below Q_j uses j<=v_p(m).
Recordhood is always at the original mu, including the signed strict mass gap. -/

private theorem marginal_antitone {p a b : ℕ} (hp : p.Prime)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    goldenLayerMarginal p b ≤ goldenLayerMarginal p a := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact (golden_layer_strict_decrease hp ha hlt).le

private theorem insertion_bound {m j p : ℕ} (hm : 0 < m) (hj : 2 ≤ j)
    (hp : p.Prime) (hQp : layerPrime m j < p) {r : ℝ}
    (hr : 2 ≤ r) (hpr : (p : ℝ) ≤ r) :
    beta j r ≤ goldenLayerMarginal p (m.factorization p + 1) := by
  have hv := valuation_above_layer_prime hm (by omega : 1 ≤ j) hp hQp
  have hreal : 2 ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hb := (beta_strictAntiOn hj).antitoneOn hreal hr hpr
  rw [beta_nat hp (by omega : 1 ≤ j)] at hb
  exact hb.trans (marginal_antitone hp (by omega) (by omega))

private theorem deletion_bound {m j p : ℕ} (hj : 2 ≤ j)
    (hp : p.Prime)
    (hanti : ∀ q r : ℕ, q.Prime → r.Prime → q < r →
      m.factorization r ≤ m.factorization q)
    (hpQ : p ≤ layerPrime m j) {r : ℝ} (hr : 2 ≤ r) (hrp : r ≤ (p : ℝ)) :
    goldenLayerMarginal p (m.factorization p) ≤ beta j r := by
  have hv := valuation_below_layer_prime hp hanti hpQ
  have hreal : 2 ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hb := (beta_strictAntiOn hj).antitoneOn hr hreal hrp
  rw [beta_nat hp (by omega : 1 ≤ j)] at hb
  exact (marginal_antitone hp (by omega) hv).trans hb

private theorem lower_probe_exchange {m j : ℕ} {mu lambda e W a r : ℝ}
    (hm : 0 < m) (hj : 2 ≤ j) (hrecord : FullRecord m mu)
    (First S : Finset ℕ)
    (hFirst : ∀ p ∈ First, p.Prime ∧ p ∣ m ∧
      log (p : ℝ) ≤ W ∧ beta 1 (p : ℝ) ≤ (1 + e) * lambda)
    (hS : ∀ p ∈ S, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ r)
    (hdis : Disjoint First S) (hr : 2 ≤ r)
    (hN : 0 ≤ logMass S) (hfull : logMass S < logMass First)
    (hQa : (layerPrime m j : ℝ) < a) :
    ∃ D ⊆ First, logMass S < logMass D ∧ logMass D ≤ logMass S + W ∧
      beta j r * logMass S < (1 + e) * lambda * logMass D -
        mu * (logMass D - logMass S) := by
  obtain ⟨D, hDF, hND, hDN⟩ := subset_just_above First (fun p => log (p : ℝ))
    hN (fun p hp => (hFirst p hp).2.2.1) hfull
  refine ⟨D, hDF, hND, hDN, ?_⟩
  apply exchange_mass_bound hm hrecord D S
    (fun p hp => (hFirst p (hDF hp)).1) (fun p hp => (hS p hp).1)
    (fun p hp => (hFirst p (hDF hp)).2.1) (hdis.mono_left hDF) hND
  · unfold logMass
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hf := hFirst p (hDF hp)
    have hv : 1 ≤ m.factorization p :=
      (hf.1.dvd_iff_one_le_factorization hm.ne').mp hf.2.1
    have hb := marginal_antitone hf.1 (by norm_num : 1 ≤ 1) hv
    rw [← beta_nat hf.1 (by norm_num : 1 ≤ 1)] at hb
    exact mul_le_mul_of_nonneg_right (hb.trans hf.2.2.2) (log_natCast_nonneg p)
  · unfold logMass
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hs := hS p hp
    have hQp : layerPrime m j < p := by exact_mod_cast hQa.trans_le hs.2.1
    exact mul_le_mul_of_nonneg_right
      (insertion_bound hm hj hs.1 hQp hr hs.2.2) (log_natCast_nonneg p)

private theorem upper_probe_exchange {m j : ℕ} {mu lambda e W r b : ℝ}
    (hm : 0 < m) (hj : 2 ≤ j) (hrecord : FullRecord m mu)
    (hanti : ∀ q t : ℕ, q.Prime → t.Prime → q < t →
      m.factorization t ≤ m.factorization q)
    (First S : Finset ℕ)
    (hFirst : ∀ p ∈ First, p.Prime ∧ m.factorization p = 0 ∧
      log (p : ℝ) ≤ W ∧ (1 - e) * lambda ≤ beta 1 (p : ℝ))
    (hS : ∀ p ∈ S, p.Prime ∧ r ≤ (p : ℝ) ∧ (p : ℝ) ≤ b)
    (hdis : Disjoint S First) (hr : 2 ≤ r)
    (hN : 0 < logMass S) (hfull : logMass S ≤ logMass First)
    (hbQ : b ≤ (layerPrime m j : ℝ)) :
    ∃ U ⊆ First, logMass U < logMass S ∧ logMass S ≤ logMass U + W ∧
      (1 - e) * lambda * logMass U < beta j r * logMass S -
        mu * (logMass S - logMass U) := by
  obtain ⟨U, hUF, hUN, hNU⟩ := subset_just_below First (fun p => log (p : ℝ))
    hN (fun p hp => (hFirst p hp).2.2.1) hfull
  have hpQ : ∀ p ∈ S, p ≤ layerPrime m j := by
    intro p hp
    exact_mod_cast (hS p hp).2.2.trans hbQ
  have hdiv : ∀ p ∈ S, p ∣ m := by
    intro p hp
    have hv := valuation_below_layer_prime (hS p hp).1 hanti (hpQ p hp)
    exact ((hS p hp).1.dvd_iff_one_le_factorization hm.ne').mpr
      ((by omega : 1 ≤ j).trans hv)
  refine ⟨U, hUF, hUN, hNU, ?_⟩
  apply exchange_mass_bound hm hrecord S U (fun p hp => (hS p hp).1)
    (fun p hp => (hFirst p (hUF hp)).1) hdiv (hdis.mono_right hUF) hUN
  · unfold logMass
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_right
      (deletion_bound hj (hS p hp).1 hanti (hpQ p hp) hr (hS p hp).2.1)
      (log_natCast_nonneg p)
  · unfold logMass
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hf := hFirst p (hUF hp)
    rw [hf.2.1, zero_add, ← beta_nat hf.1 (by norm_num : 1 ≤ 1)]
    exact mul_le_mul_of_nonneg_right hf.2.2.2 (log_natCast_nonneg p)

/- proof_shape: content
admission_basis: escape-witness
escape_witness: displaced_root_boundary_squeeze: two different strict
predecessors of the same original record rule out both displaced probe pools.
The finite pool conditions below are not an eventual count theorem. -/
/-- Finite one-sided squeeze. All prices are tied to beta(1,largestPrime m),
while both strict predecessors use the original positive mu. No equality of
actual exponents or adjacent-layer geometry is assumed. -/
theorem displaced_root_boundary_squeeze {m j : ℕ} {mu lambda rho rm rp a b e q W : ℝ}
    (hm : 2 ≤ m) (hmu : 0 < mu) (hrecord : FullRecord m mu) (hj : 2 ≤ j)
    (_hLambda : lambda = beta 1 (largestPrime m : ℝ))
    (hrho : 2 ≤ rho) (hroot : beta j rho = lambda)
    (hrm : 2 ≤ rm) (hmrho : rm ≤ rho) (hrhop : rho ≤ rp)
    (he : 0 ≤ e) (he1 : e ≤ 1) (hq : 0 ≤ q)
    (FirstLo FirstHi Sm Sp : Finset ℕ)
    (hFL : ∀ p ∈ FirstLo, p.Prime ∧ p ≤ largestPrime m ∧
      log (p : ℝ) ≤ W ∧ |beta 1 (p : ℝ) - lambda| ≤ e * lambda)
    (hFU : ∀ p ∈ FirstHi, p.Prime ∧ largestPrime m < p ∧
      log (p : ℝ) ≤ W ∧ |beta 1 (p : ℝ) - lambda| ≤ e * lambda)
    (hSm : ∀ p ∈ Sm, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ rm)
    (hSp : ∀ p ∈ Sp, p.Prime ∧ rp ≤ (p : ℝ) ∧ (p : ℝ) ≤ b)
    (hdisM : Disjoint FirstLo Sm) (hdisP : Disjoint Sp FirstHi)
    (hNm : 0 < logMass Sm) (hNp : 0 < logMass Sp)
    (hfullM : logMass Sm < logMass FirstLo) (hfullP : logMass Sp ≤ logMass FirstHi)
    (hWM : W ≤ q * logMass Sm) (hWP : W ≤ q * logMass Sp)
    (hsepM : e + q ≤ (j : ℝ) / 3 * log (rho / rm))
    (hsepP : e + q ≤ (j : ℝ) / 6 * log (rp / rho))
    (hsmallP : (j : ℝ) / 3 * log (rp / rho) ≤ 1) :
    a ≤ (layerPrime m j : ℝ) ∧ (layerPrime m j : ℝ) < b := by
  have hm0 : 0 < m := by omega
  have hlam : 0 < lambda := hroot ▸ beta_pos hrho (by omega : 1 ≤ j)
  obtain ⟨hanti, hsupport⟩ := price_record_prime_structure hm hmu hrecord
  have hFirstLo : ∀ p ∈ FirstLo, p.Prime ∧ p ∣ m ∧
      log (p : ℝ) ≤ W ∧ beta 1 (p : ℝ) ≤ (1 + e) * lambda := by
    intro p hp
    have hf := hFL p hp
    have hmem : p ∈ m.primeFactors := by
      rw [hsupport]
      exact Nat.mem_primesLE.mpr ⟨hf.2.1, hf.1⟩
    refine ⟨hf.1, Nat.dvd_of_mem_primeFactors hmem, hf.2.2.1, ?_⟩
    have hh := (abs_le.mp hf.2.2.2).2
    nlinarith only [hh]
  have hFirstHi : ∀ p ∈ FirstHi, p.Prime ∧ m.factorization p = 0 ∧
      log (p : ℝ) ≤ W ∧ (1 - e) * lambda ≤ beta 1 (p : ℝ) := by
    intro p hp
    have hf := hFU p hp
    have hnot : ¬p ∣ m := by
      intro hd
      have hh : p ∈ m.primeFactors := hf.1.mem_primeFactors hd hm0.ne'
      rw [hsupport] at hh
      exact hf.2.1.not_ge (Nat.mem_primesLE.mp hh).1
    refine ⟨hf.1, Nat.factorization_eq_zero_of_not_dvd hnot, hf.2.2.1, ?_⟩
    have hh := (abs_le.mp hf.2.2.2).1
    nlinarith only [hh]
  constructor
  · by_contra! hbad
    obtain ⟨D, _, hND, hDN, hex⟩ := lower_probe_exchange hm0 hj hrecord
      FirstLo Sm hFirstLo hSm hdisM hrm hNm.le hfullM hbad
    have hgap : 0 < mu * (logMass D - logMass Sm) :=
      mul_pos hmu (sub_pos.mpr hND)
    have hcost : 0 ≤ (1 + e) * lambda := by positivity
    have hD : logMass D ≤ (1 + q) * logMass Sm := by linarith
    have hprod := mul_le_mul_of_nonneg_left hD hcost
    have hbound : beta j rm / lambda < (1 + e) * (1 + q) := by
      apply (div_lt_iff₀ hlam).mpr
      have hh : beta j rm * logMass Sm <
          ((1 + e) * (1 + q) * lambda) * logMass Sm := by
        nlinarith only [hex, hgap, hprod]
      exact (mul_lt_mul_iff_left₀ hNm).mp hh
    have hlog := log_lt_log (div_pos (beta_pos hrm (by omega)) hlam) hbound
    have hepos : 0 < 1 + e := by linarith
    have hqpos : 0 < 1 + q := by linarith
    rw [log_mul hepos.ne' hqpos.ne'] at hlog
    have hlogE := log_le_sub_one_of_pos hepos
    have hlogQ := log_le_sub_one_of_pos hqpos
    have hslope := log_beta_drop hj hrm hmrho
    rw [hroot] at hslope
    linarith
  · by_contra! hbad
    obtain ⟨U, _, hUN, hNU, hex⟩ := upper_probe_exchange hm0 hj hrecord hanti
      FirstHi Sp hFirstHi hSp hdisP (hrho.trans hrhop) hNp hfullP hbad
    have hgap : 0 < mu * (logMass Sp - logMass U) :=
      mul_pos hmu (sub_pos.mpr hUN)
    have hcost : 0 ≤ (1 - e) * lambda := mul_nonneg (by linarith) hlam.le
    have hU : (1 - q) * logMass Sp ≤ logMass U := by linarith
    have hprod := mul_le_mul_of_nonneg_left hU hcost
    have hratio : (1 - e) * (1 - q) < beta j rp / lambda := by
      apply (lt_div_iff₀ hlam).mpr
      have hh : ((1 - e) * (1 - q) * lambda) * logMass Sp <
          beta j rp * logMass Sp := by
        nlinarith only [hex, hgap, hprod]
      exact (mul_lt_mul_iff_left₀ hNp).mp hh
    have herr : 1 - beta j rp / lambda < e + q := by
      nlinarith [mul_nonneg he hq]
    have hbp := beta_pos (hrho.trans hrhop) (by omega : 1 ≤ j)
    have hslope := log_beta_drop hj hrho hrhop
    rw [hroot] at hslope
    have hlog := log_le_sub_one_of_pos (div_pos hlam hbp)
    have hmul : ((j : ℝ) / 3 * log (rp / rho)) * (beta j rp / lambda) ≤
        1 - beta j rp / lambda := by
      have h := mul_le_mul_of_nonneg_right (hslope.trans hlog)
        (div_pos hbp hlam).le
      have hid : (lambda / beta j rp - 1) * (beta j rp / lambda) =
          1 - beta j rp / lambda := by field_simp
      rwa [hid] at h
    have hnonneg : 0 ≤ (j : ℝ) / 3 * log (rp / rho) := by
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hl : 0 ≤ log (rp / rho) := log_nonneg
        ((one_le_div (by linarith : 0 < rho)).mpr hrhop)
      positivity
    have hhalf : (j : ℝ) / 6 * log (rp / rho) ≤ 1 - beta j rp / lambda := by
      by_cases hz : 1 / 2 ≤ beta j rp / lambda
      · nlinarith
      · push Not at hz
        linarith
    linarith

private theorem counted_probe_pools {K : ℕ} {C c X rm rp : ℝ}
    (hcount : ∀ x : ℝ, X ≤ x →
      c * x ^ bhpExponent / log x ≤
        ((primesIn (x - C * x ^ bhpExponent) x).card : ℝ) ∧
      c * x ^ bhpExponent / log x ≤
        ((primesIn x (x + C * x ^ bhpExponent)).card : ℝ))
    (hXm : X ≤ rm) (hXp : X ≤ rp)
    (hcapM : (K : ℝ) ≤ c * rm ^ bhpExponent / log rm)
    (hcapP : (K : ℝ) ≤ c * rp ^ bhpExponent / log rp) :
    ∃ Sm Sp : Finset ℕ, Sm.card = K ∧ Sp.card = K ∧
      (∀ p ∈ Sm, p.Prime ∧ rm - C * rm ^ bhpExponent ≤ (p : ℝ) ∧ (p : ℝ) ≤ rm) ∧
      (∀ p ∈ Sp, p.Prime ∧ rp ≤ (p : ℝ) ∧ (p : ℝ) ≤ rp + C * rp ^ bhpExponent) := by
  classical
  have hM : K ≤ (primesIn (rm - C * rm ^ bhpExponent) rm).card := by
    exact_mod_cast hcapM.trans (hcount rm hXm).1
  have hP : K ≤ (primesIn rp (rp + C * rp ^ bhpExponent)).card := by
    exact_mod_cast hcapP.trans (hcount rp hXp).2
  obtain ⟨Sm, hm, hmc⟩ := exists_subset_card_eq hM
  obtain ⟨Sp, hp, hpc⟩ := exists_subset_card_eq hP
  exact ⟨Sm, Sp, hmc, hpc,
    fun p h => (mem_filter.mp (hm h)).2,
    fun p h => (mem_filter.mp (hp h)).2⟩

private theorem logMass_bounds (S : Finset ℕ) {lo hi : ℝ}
    (h : ∀ p ∈ S, lo ≤ log (p : ℝ) ∧ log (p : ℝ) ≤ hi) :
    (S.card : ℝ) * lo ≤ logMass S ∧ logMass S ≤ (S.card : ℝ) * hi := by
  constructor
  · simpa [logMass] using sum_le_sum (s := S) (fun p hp => (h p hp).1)
  · simpa [logMass] using sum_le_sum (s := S) (fun p hp => (h p hp).2)

/-- Counted finite displaced-root squeeze. The native count law is used at
three actual centers P, rm and rp. Its first upper CLOSED interval loses the
endpoint P; the probe intervals retain their endpoints. Only explicit scalar
conditions remain for the eventual moving-index threshold. -/
theorem counted_displaced_root_boundary_squeeze {m j K : ℕ}
    {mu C c X P rho rm rp e q Z : ℝ}
    (hm : 2 ≤ m) (hmu : 0 < mu) (hrecord : FullRecord m mu) (hj : 2 ≤ j)
    (hK : 1 ≤ K) (hPdef : P = (largestPrime m : ℝ)) (hP : 4 ≤ P)
    (hC : 0 < C) (hX : 2 ≤ X)
    (hcount : ∀ x : ℝ, X ≤ x →
      c * x ^ bhpExponent / log x ≤
        ((primesIn (x - C * x ^ bhpExponent) x).card : ℝ) ∧
      c * x ^ bhpExponent / log x ≤
        ((primesIn x (x + C * x ^ bhpExponent)).card : ℝ))
    (hXP : X ≤ P) (hXm : X ≤ rm) (hXp : X ≤ rp)
    (hcapP : (K : ℝ) + 1 ≤ c * P ^ bhpExponent / log P)
    (hcapM : (K : ℝ) ≤ c * rm ^ bhpExponent / log rm)
    (hcapR : (K : ℝ) ≤ c * rp ^ bhpExponent / log rp)
    (hwidth : C * P ^ bhpExponent ≤ P / 2)
    (hrho : 2 ≤ rho) (hroot : beta j rho = beta 1 P)
    (hrm : 2 ≤ rm - C * rm ^ bhpExponent)
    (hmrho : rm ≤ rho) (hrhop : rho ≤ rp)
    (hprefix : rp + C * rp ^ bhpExponent < P - C * P ^ bhpExponent)
    (he : 0 ≤ e) (he1 : e ≤ 1) (hq : 0 ≤ q)
    (hprice : priceLip 1 (P / 2) * (C * P ^ bhpExponent) ≤ e * beta 1 P)
    (hZ : 0 < Z) (hZM : Z ≤ log (rm - C * rm ^ bhpExponent))
    (hZP : Z ≤ log rp) (hbudget : 2 * log P ≤ q * ((K : ℝ) * Z))
    (hsepM : e + q ≤ (j : ℝ) / 3 * log (rho / rm))
    (hsepP : e + q ≤ (j : ℝ) / 6 * log (rp / rho))
    (hsmallP : (j : ℝ) / 3 * log (rp / rho) ≤ 1) :
    rm - C * rm ^ bhpExponent ≤ (layerPrime m j : ℝ) ∧
      (layerPrime m j : ℝ) < rp + C * rp ^ bhpExponent := by
  classical
  have hP0 : 0 < P := by linarith
  have hv : 0 < C * P ^ bhpExponent := mul_pos hC (rpow_pos_of_pos hP0 _)
  have hrm0 : 0 < rm := by linarith [hX.trans hXm]
  have hwm : 0 < C * rm ^ bhpExponent := mul_pos hC (rpow_pos_of_pos hrm0 _)
  have hrm2 : 2 ≤ rm := by linarith
  have hrp2 : 2 ≤ rp := hrho.trans hrhop
  have hwp : 0 < C * rp ^ bhpExponent :=
    mul_pos hC (rpow_pos_of_pos (by linarith : 0 < rp) _)
  have hhalf : 2 ≤ P / 2 := by linarith
  have hleft : 0 < P - C * P ^ bhpExponent := by linarith
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hKP : (largestPrime m : ℝ) = P := hPdef.symm
  obtain ⟨FL, FU, hcFL, hcFU, hFL, hFU⟩ := counted_higher_pools
    hcount (N := largestPrime m) (K := K) (by simpa [hKP] using hXP)
    (by simpa [hKP] using hcapP)
  simp only [hKP] at hFL hFU
  obtain ⟨Sm, Sp, hcSm, hcSp, hSm, hSp⟩ := counted_probe_pools hcount hXm hXp hcapM hcapR
  have hlogP : 0 < log P := log_pos (by linarith)
  have hlog2 : log 2 ≤ log P := log_le_log (by norm_num) (by linarith)
  have hlogUpper : log (P + C * P ^ bhpExponent) ≤ 2 * log P := by
    have hh := log_le_log (by positivity : 0 < P + C * P ^ bhpExponent)
      (show P + C * P ^ bhpExponent ≤ 2 * P by linarith)
    rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) hP0.ne'] at hh
    linarith
  have hBand : ∀ p : ℕ, P - C * P ^ bhpExponent ≤ (p : ℝ) →
      (p : ℝ) ≤ P + C * P ^ bhpExponent →
      log (p : ℝ) ≤ 2 * log P ∧ |beta 1 (p : ℝ) - beta 1 P| ≤ e * beta 1 P := by
    intro p hlo hhi
    have hphalf : P / 2 ≤ (p : ℝ) := by linarith
    have hp0 : (0 : ℝ) < p := by linarith
    refine ⟨(log_le_log hp0 hhi).trans hlogUpper, ?_⟩
    have hdist : |(p : ℝ) - P| ≤ C * P ^ bhpExponent :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    exact (price_variation (by norm_num : 1 ≤ 1) hhalf (by linarith : P / 2 ≤ P)
      hphalf).trans ((mul_le_mul_of_nonneg_left hdist (priceLip_nonneg 1 hhalf)).trans hprice)
  have hmBounds := logMass_bounds Sm (lo := Z) (hi := log rm) (by
    intro p hp
    have hh := hSm p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hh.1.pos
    exact ⟨hZM.trans (log_le_log (by linarith) hh.2.1), log_le_log hp0 hh.2.2⟩)
  have hpBounds := logMass_bounds Sp (lo := Z) (hi := log (rp + C * rp ^ bhpExponent)) (by
    intro p hp
    have hh := hSp p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hh.1.pos
    exact ⟨hZP.trans (log_le_log (by linarith) hh.2.1), log_le_log hp0 hh.2.2⟩)
  have hfL := (logMass_bounds FL (lo := log (P - C * P ^ bhpExponent))
    (hi := 2 * log P) (by
      intro p hp
      have hh := hFL p hp
      exact ⟨log_le_log hleft hh.2.1,
        (hBand p hh.2.1 (by linarith [hh.2.2])).1⟩)).1
  have hfU := (logMass_bounds FU (lo := log (P - C * P ^ bhpExponent))
    (hi := 2 * log P) (by
      intro p hp
      have hh := hFU p hp
      exact ⟨log_le_log hleft (by linarith [hh.2.1]),
        (hBand p (by linarith [hh.2.1]) hh.2.2).1⟩)).1
  rw [hcSm] at hmBounds
  rw [hcSp] at hpBounds
  rw [hcFL] at hfL
  rw [hcFU] at hfU
  have hfullM : logMass Sm < logMass FL := by
    have hl := log_lt_log hrm0 (show rm < P - C * P ^ bhpExponent by linarith)
    exact hmBounds.2.trans_lt ((mul_lt_mul_of_pos_left hl hK0).trans_le hfL)
  have hfullP : logMass Sp ≤ logMass FU := by
    have hl := log_lt_log (by linarith : 0 < rp + C * rp ^ bhpExponent) hprefix
    exact hpBounds.2.trans ((mul_lt_mul_of_pos_left hl hK0).le.trans hfU)
  apply displaced_root_boundary_squeeze hm hmu hrecord hj
    (lambda := beta 1 P) (rho := rho) (rm := rm) (rp := rp)
    (e := e) (q := q) (W := 2 * log P)
    (by rw [hPdef]) hrho hroot hrm2 hmrho hrhop he he1 hq FL FU Sm Sp
  · intro p hp
    have hh := hFL p hp
    have hple : p ≤ largestPrime m := by exact_mod_cast (hh.2.2.trans_eq hPdef)
    exact ⟨hh.1, hple, hBand p hh.2.1 (by linarith [hh.2.2])⟩
  · intro p hp
    have hh := hFU p hp
    have hplt : largestPrime m < p := by exact_mod_cast (hPdef ▸ hh.2.1)
    exact ⟨hh.1, hplt, hBand p (by linarith [hh.2.1]) hh.2.2⟩
  · exact hSm
  · exact hSp
  · apply disjoint_left.mpr
    intro p hpL hpM
    linarith [(hFL p hpL).2.1, (hSm p hpM).2.2]
  · apply disjoint_left.mpr
    intro p hpS hpU
    linarith [(hSp p hpS).2.2, (hFU p hpU).2.1]
  · exact (mul_pos hK0 hZ).trans_le hmBounds.1
  · exact (mul_pos hK0 hZ).trans_le hpBounds.1
  · exact hfullM
  · exact hfullP
  · exact hbudget.trans (mul_le_mul_of_nonneg_left hmBounds.1 hq)
  · exact hbudget.trans (mul_le_mul_of_nonneg_left hpBounds.1 hq)
  · exact hsepM
  · exact hsepP
  · exact hsmallP

private theorem window_log_bounds {r w : ℝ} (hr : 0 < r)
    (hw : 0 ≤ w) (hhalf : w ≤ r / 2) :
    log r - 2 * (w / r) ≤ log (r - w) ∧
      log (r + w) ≤ log r + 2 * (w / r) := by
  have hminus : 0 < r - w := by linarith
  have hplus : 0 < r + w := by linarith
  constructor
  · have hh := log_le_sub_one_of_pos (div_pos hr hminus)
    rw [log_div hr.ne' hminus.ne'] at hh
    have hbound : r / (r - w) - 1 ≤ 2 * (w / r) := by
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ hminus).mpr
      field_simp [hr.ne']
      nlinarith [mul_nonneg hw (show 0 ≤ r - 2 * w by linarith)]
    linarith
  · have hh := log_le_sub_one_of_pos (div_pos hplus hr)
    rw [log_div hplus.ne' hr.ne'] at hh
    have hid : (r + w) / r - 1 = w / r := by field_simp; ring
    rw [hid] at hh
    have hn : 0 ≤ w / r := div_nonneg hw hr.le
    linarith

set_option maxHeartbeats 800000 in
-- The full finite supplier telescope and its three-center construction require extra elaboration steps.
/-- Literal-cutoff logarithmic localization from explicit finite count and
smallness conditions. This is the finite core, not a growing-index eventual
threshold assertion. The error constant has no layer-index factor. -/
theorem counted_displaced_cutoff_log_localization {m j K : ℕ}
    {mu C c X P rho rm rp e q Z H t : ℝ}
    (hm : 2 ≤ m) (hmu : 0 < mu) (hrecord : FullRecord m mu) (hj : 2 ≤ j)
    (hK : 1 ≤ K) (hPdef : P = (largestPrime m : ℝ)) (hP : 4 ≤ P)
    (hC : 0 < C) (hX : 2 ≤ X) (hH : 0 < H)
    (htdef : t = P ^ (-priceExponent j))
    (hrhodef : rho = cutoff j (beta 1 P)) (hactive : beta 1 P < beta j 2)
    (hrmdef : rm = rho * exp (-(H * t))) (hrpdef : rp = rho * exp (H * t))
    (hcount : ∀ x : ℝ, X ≤ x →
      c * x ^ bhpExponent / log x ≤
        ((primesIn (x - C * x ^ bhpExponent) x).card : ℝ) ∧
      c * x ^ bhpExponent / log x ≤
        ((primesIn x (x + C * x ^ bhpExponent)).card : ℝ))
    (hXP : X ≤ P) (hXm : X ≤ rm) (hXp : X ≤ rp)
    (hcapP : (K : ℝ) + 1 ≤ c * P ^ bhpExponent / log P)
    (hcapM : (K : ℝ) ≤ c * rm ^ bhpExponent / log rm)
    (hcapR : (K : ℝ) ≤ c * rp ^ bhpExponent / log rp)
    (hwidth : C * P ^ bhpExponent ≤ P / 2)
    (hrm : 2 ≤ rm - C * rm ^ bhpExponent)
    (hprefix : rp + C * rp ^ bhpExponent < P - C * P ^ bhpExponent)
    (he : 0 ≤ e) (he1 : e ≤ 1) (hq : 0 ≤ q)
    (hprice : priceLip 1 (P / 2) * (C * P ^ bhpExponent) ≤ e * beta 1 P)
    (hZ : 0 < Z) (hZM : Z ≤ log (rm - C * rm ^ bhpExponent))
    (hZP : Z ≤ log rp) (hbudget : 2 * log P ≤ q * ((K : ℝ) * Z))
    (hseparate : e + q ≤ (j : ℝ) / 6 * (H * t))
    (hsmall : (j : ℝ) / 3 * (H * t) ≤ 1)
    (hwm : C * rm ^ bhpExponent / rm ≤ 4 * C * t)
    (hwp : C * rp ^ bhpExponent / rp ≤ 4 * C * t)
    (hshort : 4 * C * t ≤ 1 / 2) :
    2 < cutoff j (beta 1 P) ∧ 0 < layerPrime m j ∧
      |log (layerPrime m j : ℝ) - log (cutoff j (beta 1 P))| ≤
        (H + 16 * C) * P ^ (-priceExponent j) := by
  have hP0 : 0 < P := by linarith
  have ht : 0 < t := htdef ▸ rpow_pos_of_pos hP0 _
  have hht : 0 < H * t := mul_pos hH ht
  have hlam := beta_pos (by linarith : 2 ≤ P) (by norm_num : 1 ≤ 1)
  have hs := cutoff_spec hj hlam
  have hcut := hs.2.2.2.mp hactive
  have hrho : 2 < rho := hrhodef ▸ hcut
  have hroot : beta j rho = beta 1 P := hrhodef ▸ hs.2.2.1 hcut
  have hrho0 : 0 < rho := by linarith
  have hrm0 : 0 < rm := hrmdef ▸ mul_pos hrho0 (exp_pos _)
  have hrp0 : 0 < rp := hrpdef ▸ mul_pos hrho0 (exp_pos _)
  have hlogM : log rm = log rho - H * t := by
    rw [hrmdef, log_mul hrho0.ne' (exp_pos _).ne', log_exp]
    ring
  have hlogP : log rp = log rho + H * t := by
    rw [hrpdef, log_mul hrho0.ne' (exp_pos _).ne', log_exp]
  have hmrho : rm ≤ rho := (log_le_log_iff hrm0 hrho0).mp (by linarith)
  have hrhop : rho ≤ rp := (log_le_log_iff hrho0 hrp0).mp (by linarith)
  have hlogRatioM : log (rho / rm) = H * t := by
    rw [log_div hrho0.ne' hrm0.ne', hlogM]
    ring
  have hlogRatioP : log (rp / rho) = H * t := by
    rw [log_div hrp0.ne' hrho0.ne', hlogP]
    ring
  have hsepM : e + q ≤ (j : ℝ) / 3 * log (rho / rm) := by
    rw [hlogRatioM]
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  have hbracket := counted_displaced_root_boundary_squeeze hm hmu hrecord hj hK
    hPdef hP hC hX hcount hXP hXm hXp hcapP hcapM hcapR hwidth hrho.le hroot
    hrm hmrho hrhop hprefix he he1 hq hprice hZ hZM hZP hbudget hsepM
    (by rwa [hlogRatioP]) (by rwa [hlogRatioP])
  have hwm0 : 0 ≤ C * rm ^ bhpExponent :=
    mul_nonneg hC.le (rpow_pos_of_pos hrm0 _).le
  have hwp0 : 0 ≤ C * rp ^ bhpExponent :=
    mul_nonneg hC.le (rpow_pos_of_pos hrp0 _).le
  have hhalfM : C * rm ^ bhpExponent ≤ rm / 2 := by
    have hh := (div_le_iff₀ hrm0).mp (hwm.trans hshort)
    linarith
  have hhalfP : C * rp ^ bhpExponent ≤ rp / 2 := by
    have hh := (div_le_iff₀ hrp0).mp (hwp.trans hshort)
    linarith
  have hwinM := (window_log_bounds hrm0 hwm0 hhalfM).1
  have hwinP := (window_log_bounds hrp0 hwp0 hhalfP).2
  have hQ2 : 2 ≤ (layerPrime m j : ℝ) := hrm.trans hbracket.1
  have hQ0 : (0 : ℝ) < layerPrime m j := by linarith
  have hlogLo := log_le_log (by linarith : 0 < rm - C * rm ^ bhpExponent) hbracket.1
  have hlogHi := log_le_log hQ0 hbracket.2.le
  refine ⟨hcut, by exact_mod_cast hQ0, ?_⟩
  rw [← hrhodef, ← htdef]
  apply abs_le.mpr
  constructor <;> nlinarith [mul_pos hC ht]

/-- Product and logarithmic bounds at the literal first-layer price. All
constants are uniform in the natural layer index. -/
theorem literal_root_geometry {j : ℕ} {P rho : ℝ} (hj : 2 ≤ j)
    (hP : 4 ≤ log P) (hP0 : 0 < P) (hrho : 2 ≤ rho)
    (hroot : beta j rho = beta 1 P)
    (hlog : log (2 * log P / log 2) ≤ log P / 4) :
    P * log P / 2 ≤ rho ^ j * log rho ∧
      rho ^ j * log rho ≤ 2 * P * log P ∧
      log P - log 2 ≤ (j : ℝ) * log rho ∧
      (j : ℝ) * log rho ≤ 5 * log P / 4 := by
  have hP2 : 2 ≤ P := by
    by_contra! h
    have hh := log_le_log hP0 h.le
    have h2 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hr0 : 0 < rho := by linarith
  have hx : 0 < log P := by linarith
  have hy : 0 < log rho := log_pos (by linarith)
  have hjr : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hb := ActualHigherLayerQuantitativeBudgetRepair.uniform_beta_and_slope hj hrho
  have hfirst := first_beta_lower hP2
  have hfirstup := beta_le_inv_pow_log hP2 (by norm_num : 1 ≤ 1)
  rw [pow_one] at hfirstup
  rw [hroot] at hb
  have hprod : 0 < rho ^ j * log rho := mul_pos (pow_pos hr0 j) hy
  have hPx : 0 < P * log P := mul_pos hP0 hx
  have hlo : P * log P / 2 ≤ rho ^ j * log rho := by
    have hh := (one_div_le_one_div (by positivity : 0 < 2 * rho ^ j * log rho)
      hPx).mp (hb.1.trans hfirstup)
    linarith
  have hhi : rho ^ j * log rho ≤ 2 * P * log P := by
    have hh := hfirst.trans (mul_le_mul_of_nonneg_left hb.2.1 (by norm_num : (0 : ℝ) ≤ 2))
    have he : 2 * (1 / (rho ^ j * log rho)) = 1 / (rho ^ j * log rho / 2) := by ring
    rw [he] at hh
    have hh' := (one_div_le_one_div hPx (by positivity : 0 < rho ^ j * log rho / 2)).mp hh
    linarith
  have hll := log_le_log (div_pos hPx (by norm_num)) hlo
  have hlu := log_le_log hprod hhi
  rw [log_div hPx.ne' (by norm_num : (2 : ℝ) ≠ 0), log_mul hP0.ne' hx.ne',
    log_mul (pow_pos hr0 j).ne' hy.ne', log_pow] at hll
  rw [log_mul (pow_pos hr0 j).ne' hy.ne', log_pow,
    log_mul (by positivity : (2 * P : ℝ) ≠ 0) hx.ne',
    log_mul (by norm_num : (2 : ℝ) ≠ 0) hP0.ne'] at hlu
  have h2 : log 2 ≤ 1 := by
    have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hyx : log rho ≤ log P := by
    by_contra! h
    have hh := log_le_log hx h.le
    have hm := mul_le_mul_of_nonneg_right hjr hy.le
    linarith
  have hlow : log P - log 2 ≤ (j : ℝ) * log rho := by
    have hh := log_le_log hy hyx
    linarith
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hlogy := log_le_log hlog2 (log_le_log (by norm_num : (0 : ℝ) < 2) hrho)
  have hid : log (2 * log P / log 2) = log 2 + log (log P) - log (log 2) := by
    rw [log_div (by positivity : (2 * log P : ℝ) ≠ 0) hlog2.ne',
      log_mul (by norm_num : (2 : ℝ) ≠ 0) hx.ne']
  rw [hid] at hlog
  exact ⟨hlo, hhi, hlow, by linarith⟩

/-- Uniform activation at the literal beta(1,P), with no reference-price
substitution. The index restriction is a scalar consequence of the window. -/
theorem literal_cutoff_active {j : ℕ} {P : ℝ} (hj : 2 ≤ j)
    (hP0 : 0 < P) (hP : 4 ≤ log P) (hjx : (j : ℝ) ≤ log P / 4) :
    beta 1 P < beta j 2 := by
  have h2 : 0 < log 2 := log_pos (by norm_num)
  have h21 : log 2 ≤ 1 := by
    have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog2 : log (log 2) ≤ 0 := by
    simpa using log_le_log h2 h21
  have hden : 0 < 2 * (2 : ℝ) ^ j * log 2 := by positivity
  have hlogden : log (2 * (2 : ℝ) ^ j * log 2) < log P := by
    rw [log_mul (by positivity : (2 * (2 : ℝ) ^ j) ≠ 0) h2.ne',
      log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (2 : ℝ) ^ j ≠ 0), log_pow]
    have hh := mul_le_mul_of_nonneg_left h21 (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
    linarith
  have hdP : 2 * (2 : ℝ) ^ j * log 2 < P := (log_lt_log_iff hden hP0).mp hlogden
  have hP2 : 2 ≤ P := by
    by_contra! h
    have hh := log_le_log hP0 h.le
    linarith
  have hPprod : P ≤ P * log P := by nlinarith
  have hi := one_div_lt_one_div_of_lt hden (hdP.trans_le hPprod)
  have hb := ActualHigherLayerQuantitativeBudgetRepair.uniform_beta_and_slope hj
    (by norm_num : (2 : ℝ) ≤ 2)
  have hf := beta_le_inv_pow_log hP2 (by norm_num : 1 ≤ 1)
  rw [pow_one] at hf
  exact (hf.trans_lt hi).trans_le hb.1

/-- Displaced roots retain the uniform logarithmic scale and BHP relative
width. The estimate uses the literal root product, not a higher-layer
Lipschitz constant. -/
theorem literal_displaced_probe_geometry {j : ℕ} {P rho H : ℝ}
    (hj : 2 ≤ j) (hP0 : 0 < P) (hP : 4 ≤ log P) (hrho : 2 ≤ rho)
    (hroot : beta j rho = beta 1 P)
    (hlog : log (2 * log P / log 2) ≤ log P / 4)
    (hH : 0 < H) (hsmall : H * P ^ (-priceExponent j) ≤ 1) :
    let t := P ^ (-priceExponent j)
    let rm := rho * exp (-(H * t))
    let rp := rho * exp (H * t)
    log P / (j : ℝ) - 2 ≤ log rm ∧
      log P / (j : ℝ) - 1 ≤ log rp ∧
      log rp ≤ 5 * log P / (4 * (j : ℝ)) + 1 ∧
      rm ^ bhpExponent / rm ≤ 4 * t ∧
      rp ^ bhpExponent / rp ≤ 4 * t := by
  dsimp only
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hr0 : 0 < rho := by linarith
  have ht : 0 < P ^ (-priceExponent j) := rpow_pos_of_pos hP0 _
  have hh0 : 0 ≤ H * P ^ (-priceExponent j) := (mul_pos hH ht).le
  have hgeo := literal_root_geometry hj hP hP0 hrho hroot hlog
  have h2 : log 2 ≤ 1 := by
    have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlo : log P / (j : ℝ) - 1 ≤ log rho := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hj0).mpr
    nlinarith [hgeo.2.2.1]
  have hhi : log rho ≤ 5 * log P / (4 * (j : ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * (j : ℝ))).mpr
    nlinarith [hgeo.2.2.2]
  have hrm0 : 0 < rho * exp (-(H * P ^ (-priceExponent j))) := by positivity
  have hrp0 : 0 < rho * exp (H * P ^ (-priceExponent j)) := by positivity
  have hlogm : log (rho * exp (-(H * P ^ (-priceExponent j)))) =
      log rho - H * P ^ (-priceExponent j) := by
    rw [log_mul hr0.ne' (exp_pos _).ne', log_exp]; ring
  have hlogp : log (rho * exp (H * P ^ (-priceExponent j))) =
      log rho + H * P ^ (-priceExponent j) := by
    rw [log_mul hr0.ne' (exp_pos _).ne', log_exp]
  have hmlo : log P / (j : ℝ) - 2 ≤
      log (rho * exp (-(H * P ^ (-priceExponent j)))) := by rw [hlogm]; linarith
  have hplo : log P / (j : ℝ) - 1 ≤
      log (rho * exp (H * P ^ (-priceExponent j))) := by rw [hlogp]; linarith
  have hphi : log (rho * exp (H * P ^ (-priceExponent j))) ≤
      5 * log P / (4 * (j : ℝ)) + 1 := by rw [hlogp]; linarith
  have htform : P ^ (-priceExponent j) = exp (-(19 / 40 : ℝ) * log P / j) := by
    rw [rpow_def_of_pos hP0]
    congr 1
    unfold priceExponent
    ring
  have hwidth : ∀ r : ℝ, 0 < r → log P / (j : ℝ) - 2 ≤ log r →
      r ^ bhpExponent / r ≤ 4 * P ^ (-priceExponent j) := by
    intro r hr hl
    have hid : r ^ bhpExponent / r = exp (-(19 / 40 : ℝ) * log r) := by
      rw [rpow_def_of_pos hr, ← exp_log hr, ← exp_sub]
      congr 1
      norm_num [bhpExponent]
      <;> ring
    rw [hid, htform]
    calc
      exp (-(19 / 40 : ℝ) * log r) ≤
          exp (1 + (-(19 / 40 : ℝ) * log P / j)) := by
        apply exp_le_exp.mpr
        calc
          -(19 / 40 : ℝ) * log r ≤ -(19 / 40 : ℝ) * (log P / j - 2) :=
            mul_le_mul_of_nonpos_left hl (by norm_num)
          _ ≤ 1 + (-(19 / 40 : ℝ) * log P / j) := by ring_nf; norm_num
      _ = exp 1 * exp (-(19 / 40 : ℝ) * log P / j) := exp_add _ _
      _ ≤ 4 * exp (-(19 / 40 : ℝ) * log P / j) :=
        mul_le_mul_of_nonneg_right (by linarith [exp_one_lt_d9]) (exp_pos _).le
  exact ⟨hmlo, hplo, hphi, hwidth _ hrm0 hmlo, hwidth _ hrp0 (by linarith)⟩

open Filter Asymptotics
open scoped Topology

/-- A simultaneous lower bound on x/u throughout the growing window. The
threshold precedes every real u in the window, rather than each fixed index. -/
theorem moving_window_log_scale {delta A : ℝ} (hdelta : 0 < delta) (hA : 0 < A) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ log x ∧ 0 < x ∧
      ∀ u : ℝ, 0 < u → u ≤ delta * x / (log x) ^ 2 + 1 →
        A * log x ≤ x / u := by
  have hratio : Tendsto (fun x : ℝ => log x / x) atTop (𝓝 0) :=
    isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlim : Tendsto (fun x : ℝ => A * (delta / log x + log x / x))
      atTop (𝓝 0) := by
    convert ((tendsto_const_nhds.div_atTop tendsto_log_atTop).add hratio).const_mul A using 1
    simp
  filter_upwards [hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    tendsto_log_atTop.eventually_ge_atTop 1, eventually_gt_atTop (0 : ℝ)]
    with x hsmall hx hx0
  refine ⟨hx, hx0, ?_⟩
  intro u hu hule
  have hl : 0 < log x := by linarith
  have hid : (delta * x / (log x) ^ 2 + 1) * log x / x =
      delta / log x + log x / x := by
    field_simp
    <;> ring
  rw [← hid] at hsmall
  have hfull : A * (delta * x / (log x) ^ 2 + 1) * log x ≤ x := by
    have hh : A * ((delta * x / (log x) ^ 2 + 1) * log x / x) =
        (A * (delta * x / (log x) ^ 2 + 1) * log x) / x := by ring
    rw [hh] at hsmall
    simpa only [one_mul] using ((div_lt_iff₀ hx0).mp hsmall).le
  apply (le_div_iff₀ hu).mpr
  have hh := mul_le_mul_of_nonneg_left hule (mul_nonneg hA.le hl.le)
  nlinarith

/-- Every fixed polynomial is dominated uniformly on the whole moving
window. This is not a collection of fixed-index asymptotic limits. -/
theorem moving_window_exp_small {delta a : ℝ} (hdelta : 0 < delta) (ha : 0 < a)
    (k : ℕ) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧
      ∀ u : ℝ, 0 < u → u ≤ delta * x / (log x) ^ 2 + 1 →
        x ^ k * exp (-a * x / u) ≤ 1 / x := by
  have hA : 0 < ((k : ℝ) + 1) / a := by positivity
  filter_upwards [moving_window_log_scale hdelta hA,
    eventually_ge_atTop (1 : ℝ)] with x hx hx1
  refine ⟨hx1, ?_⟩
  intro u hu hule
  have hz := hx.2.2 u hu hule
  have hh := mul_le_mul_of_nonneg_left hz ha.le
  have hid : a * (((k : ℝ) + 1) / a * log x) = ((k : ℝ) + 1) * log x := by
    field_simp
  rw [hid] at hh
  have he : exp (-a * x / u) ≤ exp (-((k : ℝ) + 1) * log x) := by
    apply exp_le_exp.mpr
    calc
      -a * x / u = -(a * (x / u)) := by ring
      _ ≤ -((k : ℝ) + 1) * log x := by linarith only [hh]
  have heq : exp (-((k : ℝ) + 1) * log x) = (x ^ (k + 1))⁻¹ := by
    rw [neg_mul, exp_neg, ← Nat.cast_add_one, exp_nat_mul, exp_log hx.2.1]
  rw [heq] at he
  calc
    x ^ k * exp (-a * x / u) ≤ x ^ k * (x ^ (k + 1))⁻¹ :=
      mul_le_mul_of_nonneg_left he (pow_nonneg hx.2.1.le _)
    _ = 1 / x := by rw [pow_succ]; field_simp

private theorem first_price_error_bound {P C : ℝ}
    (hP0 : 0 < P) (hP : 4 ≤ log P) (hC : 0 < C) :
    priceLip 1 (P / 2) * (C * P ^ bhpExponent) ≤
      (48 * C * P ^ (-priceExponent 1)) * beta 1 P := by
  have h2 : log 2 ≤ 1 := by
    have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hP4 : 4 ≤ P := by
    have hh := log_le_self hP0.le
    linarith
  have hx : 0 < log P := by linarith
  have hlog : log P / 2 ≤ log (P / 2) := by
    rw [log_div hP0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    linarith
  have hlip := priceLip_half_bound 1 (by linarith : 1 < P) hP4
    (by norm_num : (0 : ℝ) < 2) hlog
  norm_num at hlip
  have hb := first_beta_lower (by linarith : 2 ≤ P)
  have hid : P ^ bhpExponent = P * P ^ (-priceExponent 1) := by
    calc
      _ = P ^ ((1 : ℝ) + -priceExponent 1) := by norm_num [bhpExponent, priceExponent]
      _ = P ^ (1 : ℝ) * P ^ (-priceExponent 1) := rpow_add hP0 _ _
      _ = _ := by rw [rpow_one]
  calc
    _ ≤ (24 / (P ^ 2 * log P)) * (C * P ^ bhpExponent) :=
      mul_le_mul_of_nonneg_right hlip (by positivity)
    _ = 24 * C * P ^ (-priceExponent 1) * (1 / (P * log P)) := by
      rw [hid]
      field_simp
      <;> ring
    _ ≤ 24 * C * P ^ (-priceExponent 1) * (2 * beta 1 P) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

private theorem exchange_error_margin {j : ℕ} {P C : ℝ} (hj : 2 ≤ j)
    (hP : 1 ≤ P) (hC : 0 < C) :
    48 * C * P ^ (-priceExponent 1) +
        8 * (j : ℝ) / (comparisonCount j P : ℝ) ≤
      (j : ℝ) / 6 * ((1024 * (1 + C)) * P ^ (-priceExponent j)) := by
  have hP0 : 0 < P := by linarith
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have ht : 0 < P ^ (-priceExponent j) := rpow_pos_of_pos hP0 _
  have hg : 0 < P ^ priceExponent j := rpow_pos_of_pos hP0 _
  have hKlow : P ^ priceExponent j ≤ (comparisonCount j P : ℝ) := Nat.le_ceil _
  have hK0 : (0 : ℝ) < comparisonCount j P := hg.trans_le hKlow
  have hinv : 1 / (comparisonCount j P : ℝ) ≤ P ^ (-priceExponent j) := by
    rw [rpow_neg hP0.le, one_div]
    exact inv_anti₀ hg hKlow
  have hgamma : -priceExponent 1 ≤ -priceExponent j := by
    unfold priceExponent
    norm_num
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 40 * j)).mpr
    nlinarith
  have ht1 : P ^ (-priceExponent 1) ≤ P ^ (-priceExponent j) :=
    rpow_le_rpow_of_exponent_le hP hgamma
  have he := mul_le_mul_of_nonneg_left ht1 (show 0 ≤ 48 * C by positivity)
  have hq := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 8 * (j : ℝ) by positivity)
  have hCjt := mul_le_mul_of_nonneg_right hj2 (mul_nonneg hC.le ht.le)
  have hjt : 0 ≤ (j : ℝ) * P ^ (-priceExponent j) := by positivity
  simp only [mul_one_div] at hq
  nlinarith

private theorem probe_count_capacity {j : ℕ} {P r c : ℝ} (hj : 2 ≤ j)
    (hP : 1 < P) (hr : 0 < r) (hc : 0 < c)
    (hz : 4 ≤ log P / (j : ℝ))
    (hlo : log P / (j : ℝ) - 2 ≤ log r)
    (hhi : log r ≤ 2 * (log P / (j : ℝ)))
    (hcap : 4 * (log P / (j : ℝ)) * exp (-(log P / (j : ℝ)) / 20) ≤
      c * exp (-(21 / 20 : ℝ))) :
    (comparisonCount j P : ℝ) ≤ c * r ^ bhpExponent / log r := by
  have hP0 : 0 < P := by linarith
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hx : 0 < log P := log_pos hP
  have hlr : 0 < log r := by linarith
  have hg : 0 < priceExponent j := by unfold priceExponent; positivity
  have hpow1 : 1 ≤ P ^ priceExponent j := one_le_rpow hP.le hg.le
  have hceil : (comparisonCount j P : ℝ) ≤ 2 * P ^ priceExponent j := by
    have hh := Nat.ceil_lt_add_one (rpow_nonneg hP0.le (priceExponent j))
    change (comparisonCount j P : ℝ) < _ at hh
    linarith
  have hform : P ^ priceExponent j = exp ((19 / 40 : ℝ) * (log P / j)) := by
    rw [rpow_def_of_pos hP0]; congr 1; unfold priceExponent; ring
  have hscaled := mul_le_mul_of_nonneg_right hcap
    (exp_pos ((21 / 40 : ℝ) * (log P / j))).le
  have hleft : 4 * (log P / (j : ℝ)) * exp (-(log P / (j : ℝ)) / 20) *
      exp ((21 / 40 : ℝ) * (log P / j)) =
      4 * (log P / (j : ℝ)) * exp ((19 / 40 : ℝ) * (log P / j)) := by
    rw [mul_assoc, ← exp_add]; congr 2; ring
  have hright : c * exp (-(21 / 20 : ℝ)) * exp ((21 / 40 : ℝ) * (log P / j)) =
      c * exp ((21 / 40 : ℝ) * (log P / j - 2)) := by
    rw [mul_assoc, ← exp_add]; congr 2; ring
  rw [hleft, hright] at hscaled
  have hrpow : exp ((21 / 40 : ℝ) * (log P / j - 2)) ≤ r ^ bhpExponent := by
    rw [rpow_def_of_pos hr]
    apply exp_le_exp.mpr
    norm_num [bhpExponent]
    <;> linarith
  apply (le_div_iff₀ hlr).mpr
  calc
    _ ≤ (2 * P ^ priceExponent j) * (2 * (log P / (j : ℝ))) :=
      mul_le_mul hceil hhi (by positivity) (by positivity)
    _ = 4 * (log P / (j : ℝ)) * exp ((19 / 40 : ℝ) * (log P / j)) := by rw [hform]; ring
    _ ≤ c * exp ((21 / 40 : ℝ) * (log P / j - 2)) := hscaled
    _ ≤ _ := mul_le_mul_of_nonneg_left hrpow hc.le

private theorem first_count_capacity {j : ℕ} {P c : ℝ} (hj : 2 ≤ j)
    (hP : 1 < P) (hc : 0 < c)
    (hcap : 3 * log P * exp (-(23 / 80 : ℝ) * log P) ≤ c) :
    (comparisonCount j P : ℝ) + 1 ≤ c * P ^ bhpExponent / log P := by
  have hP0 : 0 < P := by linarith
  have hx : 0 < log P := log_pos hP
  have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hg : 0 < priceExponent j := by unfold priceExponent; positivity
  have hpow1 : 1 ≤ P ^ priceExponent j := one_le_rpow hP.le hg.le
  have hceil := Nat.ceil_lt_add_one (rpow_nonneg hP0.le (priceExponent j))
  change (comparisonCount j P : ℝ) < _ at hceil
  have hgamma : priceExponent j ≤ 19 / 80 := by
    unfold priceExponent
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 40 * j) (by norm_num)).mpr
    nlinarith
  have hpow : P ^ priceExponent j ≤ exp ((19 / 80 : ℝ) * log P) := by
    rw [rpow_def_of_pos hP0]
    exact exp_le_exp.mpr (by nlinarith)
  have hK : (comparisonCount j P : ℝ) + 1 ≤ 3 * exp ((19 / 80 : ℝ) * log P) := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_right hcap
    (rpow_pos_of_pos hP0 bhpExponent).le
  have hid : 3 * log P * exp (-(23 / 80 : ℝ) * log P) * P ^ bhpExponent =
      (3 * exp ((19 / 80 : ℝ) * log P)) * log P := by
    rw [rpow_def_of_pos hP0, mul_assoc, ← exp_add]
    have hh : -(23 / 80 : ℝ) * log P + log P * bhpExponent =
        (19 / 80 : ℝ) * log P := by norm_num [bhpExponent]; <;> ring
    rw [hh]; ring
  rw [hid] at hscaled
  apply (le_div_iff₀ hx).mpr
  exact (mul_le_mul_of_nonneg_right hK hx.le).trans hscaled

set_option maxHeartbeats 800000 in
-- The simultaneous threshold keeps all finite exchange conditions in one telescope.
/-- One threshold before the original record, its original price and the
moving index. Only the real-center count supplier is used; the independently
typed maximum-gap premise is retained. -/
theorem bhp_uniform_moving_boundary_localization
    (_hgap : BHPMaximumGap) (hcount : BHPShortIntervalCount) :
    ∃ B : ℝ, 0 < B ∧ ∀ delta : ℝ, 0 < delta →
      ∃ T : ℝ, 0 < T ∧ ∀ m : ℕ, 2 ≤ m →
        ∀ mu : ℝ, 0 < mu → FullRecord m mu →
          T ≤ (largestPrime m : ℝ) →
          ∀ j : ℕ, 2 ≤ j →
            (j : ℝ) ≤ delta * log (largestPrime m : ℝ) /
              (log (log (largestPrime m : ℝ))) ^ 2 + 1 →
            2 < cutoff j (beta 1 (largestPrime m : ℝ)) ∧
              0 < layerPrime m j ∧
              |log (layerPrime m j : ℝ) -
                log (cutoff j (beta 1 (largestPrime m : ℝ)))| ≤
                B * (largestPrime m : ℝ) ^ (-priceExponent j) := by
  obtain ⟨C, c, X, hC, hc, hX, hcount⟩ := hcount
  let H : ℝ := 1024 * (1 + C)
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨H + 16 * C, by positivity, ?_⟩
  intro delta hdelta
  have hprobeLim : Tendsto (fun z : ℝ => 4 * z * exp (-z / 20)) atTop (𝓝 0) := by
    convert (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 20)
      (by norm_num)).const_mul 4 using 1 <;> simp [rpow_one]; <;> congr 2 <;> ring
  obtain ⟨S0, hS0⟩ := eventually_atTop.mp
    (hprobeLim.eventually_le_const (by positivity : 0 < c * exp (-(21 / 20 : ℝ))))
  let S : ℝ := max 8 (max (log X + 2) S0)
  have hfirstLim : Tendsto (fun x : ℝ => 3 * x * exp (-(23 / 80 : ℝ) * x))
      atTop (𝓝 0) := by
    simpa [rpow_one, mul_assoc] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (23 / 80) (by norm_num)).const_mul 3
  have hratio : Tendsto (fun x : ℝ => log x / x) atTop (𝓝 0) :=
    isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hevent : ∀ᶠ x : ℝ in atTop,
      16 ≤ x ∧ H ≤ x ∧ X ≤ x ∧
      log (2 * x / log 2) ≤ x / 4 ∧
      3 * x * exp (-(23 / 80 : ℝ) * x) ≤ c ∧ S ≤ log x ∧
      ∀ u : ℝ, 0 < u → u ≤ delta * x / (log x) ^ 2 + 1 →
        log x ≤ x / u ∧ x * exp (-(19 / 40 : ℝ) * x / u) ≤ 1 / x := by
    filter_upwards [eventually_ge_atTop (16 : ℝ), eventually_ge_atTop H,
      eventually_ge_atTop X, eventually_ge_atTop (8 * |log (2 / log 2)|),
      hratio.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 8),
      hfirstLim.eventually_le_const hc,
      tendsto_log_atTop.eventually_ge_atTop S,
      moving_window_log_scale hdelta (by norm_num : (0 : ℝ) < 1),
      moving_window_exp_small hdelta (by norm_num : (0 : ℝ) < 19 / 40) 1]
      with x hx16 hxH hxX hconst hrat hfirst hS hscale hexp
    have hx0 : 0 < x := by linarith
    have hl2 : 0 < log 2 := log_pos (by norm_num)
    have hid : log (2 * x / log 2) = log (2 / log 2) + log x := by
      rw [← log_mul (by positivity : (2 / log 2 : ℝ) ≠ 0) hx0.ne']
      congr 1; ring
    have hrat' := (div_le_iff₀ hx0).mp hrat
    have hlog : log (2 * x / log 2) ≤ x / 4 := by
      rw [hid]
      linarith [le_abs_self (log (2 / log 2))]
    refine ⟨hx16, hxH, hxX, hlog, hfirst, hS, ?_⟩
    intro u hu hule
    exact ⟨by simpa only [one_mul] using hscale.2.2 u hu hule,
      by simpa only [pow_one] using hexp.2 u hu hule⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.eventually hevent).and (eventually_gt_atTop (1 : ℝ)))
  refine ⟨max T 1, by positivity, ?_⟩
  intro m hm mu hmu hrecord hlarge j hj hindex
  let P : ℝ := largestPrime m
  let x : ℝ := log P
  let t : ℝ := P ^ (-priceExponent j)
  let rho : ℝ := cutoff j (beta 1 P)
  let rm : ℝ := rho * exp (-(H * t))
  let rp : ℝ := rho * exp (H * t)
  let K : ℕ := comparisonCount j P
  let e : ℝ := 48 * C * P ^ (-priceExponent 1)
  let q : ℝ := 8 * (j : ℝ) / (K : ℝ)
  let Z : ℝ := x / (4 * (j : ℝ))
  have hraw := hT P ((le_max_left T 1).trans hlarge)
  have hP1 : 1 < P := hraw.2
  have hP0 : 0 < P := by linarith
  rcases hraw.1 with ⟨hx16, hxH, hxX, hlog, hfirst, hS, hwindow⟩
  change 16 ≤ x at hx16
  change H ≤ x at hxH
  change X ≤ x at hxX
  have hx0 : 0 < x := by linarith
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have ht : 0 < t := rpow_pos_of_pos hP0 _
  have hHt0 : 0 < H * t := mul_pos hH ht
  have hw := hwindow (j : ℝ) hj0 hindex
  have hz8 : 8 ≤ x / (j : ℝ) := (le_max_left _ _).trans (hS.trans hw.1)
  have hzS0 : S0 ≤ x / (j : ℝ) :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans (hS.trans hw.1)
  have hzX : log X + 2 ≤ x / (j : ℝ) :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans (hS.trans hw.1)
  have hjx : (j : ℝ) ≤ x / 4 := by
    have hh := (le_div_iff₀ hj0).mp hz8
    linarith
  have hjx1 : (j : ℝ) ≤ x := by linarith
  have htform : t = exp (-(19 / 40 : ℝ) * x / j) := by
    dsimp [t, x]
    rw [rpow_def_of_pos hP0]
    congr 1; unfold priceExponent; ring
  have hxt : x * t ≤ 1 / x := by rw [htform]; exact hw.2
  have hjt : (j : ℝ) * t ≤ 1 / x :=
    (mul_le_mul_of_nonneg_right hjx1 ht.le).trans hxt
  have hHjt : H * ((j : ℝ) * t) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hjt hH.le
    have hdiv : H * (1 / x) ≤ 1 := by
      rw [mul_one_div]; exact (div_le_one hx0).mpr hxH
    exact hh.trans hdiv
  have hHt : H * t ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ j by linarith) hHt0.le
    nlinarith only [hHjt, hh]
  have hCt : C * t ≤ 1 / 1024 := by
    dsimp only [H] at hHt
    nlinarith only [hHt, ht.le]
  have ht1 : P ^ (-priceExponent 1) ≤ t := by
    apply rpow_le_rpow_of_exponent_le hP1.le
    have hh : priceExponent j ≤ priceExponent 1 := by
      unfold priceExponent
      norm_num
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 40 * j)).mpr
      nlinarith
    linarith
  have he : 0 ≤ e := by dsimp [e]; positivity
  have he1 : e ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left ht1 (show 0 ≤ 48 * C by positivity)
    dsimp only [e]
    nlinarith only [hh, hCt]
  have hshort : 4 * C * t ≤ 1 / 2 := by nlinarith only [hCt]
  have hP4 : 4 ≤ P := by
    have hh := log_le_self hP0.le
    change x ≤ P at hh
    linarith
  have hactive : beta 1 P < beta j 2 := literal_cutoff_active hj hP0 (by linarith) hjx
  have hs := cutoff_spec hj (beta_pos (by linarith : 2 ≤ P) (by norm_num : 1 ≤ 1))
  have hrho : 2 < rho := hs.2.2.2.mp hactive
  have hroot : beta j rho = beta 1 P := hs.2.2.1 hrho
  have hrho0 : 0 < rho := by linarith
  have hrm0 : 0 < rm := mul_pos hrho0 (exp_pos _)
  have hrp0 : 0 < rp := mul_pos hrho0 (exp_pos _)
  have hgeo := literal_displaced_probe_geometry hj hP0 (by linarith : 4 ≤ log P)
    hrho.le hroot hlog hH hHt
  change x / (j : ℝ) - 2 ≤ log rm ∧ x / (j : ℝ) - 1 ≤ log rp ∧
    log rp ≤ 5 * x / (4 * (j : ℝ)) + 1 ∧
    rm ^ bhpExponent / rm ≤ 4 * t ∧ rp ^ bhpExponent / rp ≤ 4 * t at hgeo
  have hmrp : rm ≤ rp := by
    dsimp only [rm, rp]
    exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith : -(H * t) ≤ H * t)) hrho0.le
  have hupp : log rp ≤ 2 * (x / (j : ℝ)) := by
    have hid : 5 * x / (4 * (j : ℝ)) = (5 / 4 : ℝ) * (x / j) := by ring
    rw [hid] at hgeo
    linarith only [hgeo.2.2.1, hz8]
  have hupm : log rm ≤ 2 * (x / (j : ℝ)) :=
    (log_le_log hrm0 hmrp).trans hupp
  have hcapz := hS0 (x / (j : ℝ)) hzS0
  have hcapM := probe_count_capacity hj hP1 hrm0 hc (by linarith : 4 ≤ log P / (j : ℝ))
    hgeo.1 hupm hcapz
  have hcapR := probe_count_capacity hj hP1 hrp0 hc (by linarith : 4 ≤ log P / (j : ℝ))
    (by linarith [hgeo.2.1] : log P / (j : ℝ) - 2 ≤ log rp) hupp hcapz
  have hX0 : 0 < X := by linarith
  have hXm : X ≤ rm := (log_le_log_iff hX0 hrm0).mp (by linarith [hgeo.1])
  have hXp : X ≤ rp := hXm.trans hmrp
  have hXP : X ≤ P := hxX.trans (log_le_self hP0.le)
  have hwm : C * rm ^ bhpExponent / rm ≤ 4 * C * t := by
    have hh := mul_le_mul_of_nonneg_left hgeo.2.2.2.1 hC.le
    convert hh using 1 <;> ring
  have hwp : C * rp ^ bhpExponent / rp ≤ 4 * C * t := by
    have hh := mul_le_mul_of_nonneg_left hgeo.2.2.2.2 hC.le
    convert hh using 1 <;> ring
  have hhalfM : C * rm ^ bhpExponent ≤ rm / 2 := by
    have hh := (div_le_iff₀ hrm0).mp (hwm.trans hshort)
    linarith
  have hhalfP : C * rp ^ bhpExponent ≤ rp / 2 := by
    have hh := (div_le_iff₀ hrp0).mp (hwp.trans hshort)
    linarith
  have hlog4 : log 4 ≤ 3 := by
    have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hrm4 : 4 ≤ rm := (log_le_log_iff (by norm_num : (0 : ℝ) < 4) hrm0).mp
    (by linarith [hgeo.1])
  have hrm : 2 ≤ rm - C * rm ^ bhpExponent := by linarith
  have hidwidth : P ^ bhpExponent = P * P ^ (-priceExponent 1) := by
    calc
      _ = P ^ ((1 : ℝ) + -priceExponent 1) := by norm_num [bhpExponent, priceExponent]
      _ = P ^ (1 : ℝ) * P ^ (-priceExponent 1) := rpow_add hP0 _ _
      _ = _ := by rw [rpow_one]
  have hwidth : C * P ^ bhpExponent ≤ P / 2 := by
    have hh := mul_le_mul_of_nonneg_left ht1 hC.le
    have hh' := mul_le_mul_of_nonneg_left (hh.trans hCt) hP0.le
    rw [hidwidth]
    nlinarith only [hh', hP0.le]
  have hrpP : rp ≤ P / 4 := by
    have hphi : log rp ≤ 5 * x / 8 + 1 := by
      have hd := div_le_div_of_nonneg_left (show 0 ≤ 5 * x by positivity)
        (by norm_num : (0 : ℝ) < 8) (show (8 : ℝ) ≤ 4 * j by linarith)
      linarith [hgeo.2.2.1]
    apply (log_le_log_iff hrp0 (by positivity : 0 < P / 4)).mp
    rw [log_div hP0.ne' (by norm_num : (4 : ℝ) ≠ 0)]
    change log rp ≤ x - log 4
    linarith
  have hprefix : rp + C * rp ^ bhpExponent < P - C * P ^ bhpExponent := by
    nlinarith only [hhalfP, hrpP, hwidth, hP0]
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hlog2 : log 2 ≤ 1 := by
    have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hZM : Z ≤ log (rm - C * rm ^ bhpExponent) := by
    have hhalf : rm / 2 ≤ rm - C * rm ^ bhpExponent := by linarith
    have hh := log_le_log (by positivity : 0 < rm / 2) hhalf
    rw [log_div hrm0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hh
    have hid : Z = (x / (j : ℝ)) / 4 := by dsimp [Z]; ring
    rw [hid]
    linarith only [hh, hgeo.1, hz8, hlog2]
  have hZP : Z ≤ log rp := by
    have hid : Z = (x / (j : ℝ)) / 4 := by dsimp [Z]; ring
    rw [hid]
    linarith only [hgeo.2.1, hz8]
  have hKlow : P ^ priceExponent j ≤ (K : ℝ) := Nat.le_ceil _
  have hKpos : (0 : ℝ) < K := (rpow_pos_of_pos hP0 _).trans_le hKlow
  have hK : 1 ≤ K := by
    have hh : 0 < K := by exact_mod_cast hKpos
    omega
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hbudget : 2 * log P ≤ q * ((K : ℝ) * Z) := by
    have hid : q * ((K : ℝ) * Z) = 2 * x := by
      dsimp [q, Z]
      field_simp
      <;> ring
    rw [hid]
  have hsmall : (j : ℝ) / 3 * (H * t) ≤ 1 := by nlinarith only [hHjt]
  exact counted_displaced_cutoff_log_localization hm hmu hrecord hj hK rfl hP4
    hC hX hH rfl rfl hactive rfl rfl hcount hXP hXm hXp
    (first_count_capacity hj hP1 hc hfirst) hcapM hcapR hwidth hrm hprefix
    he he1 hq (first_price_error_bound hP0 (by linarith) hC) hZ hZM hZP hbudget
    (exchange_error_margin hj hP1.le hC) hsmall hwm hwp hshort

end D5.S3.Arith.Robin.PriceRecord.ActualMovingBoundaryLocalization
