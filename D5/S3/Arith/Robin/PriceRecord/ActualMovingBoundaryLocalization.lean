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

end D5.S3.Arith.Robin.PriceRecord.ActualMovingBoundaryLocalization
