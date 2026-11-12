/- GID: D5/S3/Arith/Robin/PriceRecord/ActualFiveModeInventory
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualFiveModeInventory
   mirror-E: none(waiver:elementary-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Actual prime inventories, finite predecessors and uniform clock. -/
/- proof_shape: content
admission_basis: escape-witness
escape_witness: pointwise_boundary_estimates: interval logarithmic control and beta variation transfer the actual boundary and root errors to both actual-prime logarithmic and complete marginal-fee estimates.
utility: none. The actual-record construction is an unbounded conditional
mathematical argument. All prime counts, valuations and fees retain their
original hypotheses; the prescribed full bank and RH remain open. -/
import D5.S3.Arith.Robin.PriceRecord.ActualFiveModeStencil

/-! Actual-record arithmetic: ActualFiveModeInventory. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack

open Real Filter Finset
open scoped Topology BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference (referencePrice)
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (price_record_prime_structure)
open D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
  (beta gain beta_pos beta_nat log_beta_drop)
open D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
  (cutoff cutoff_spec cutoff_antitone)
open D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster (root_atTop)
open D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature
  (d normalized_gain_bounds)
open D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffFourthOrder
  (P actual_quartic_error)
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
  (layerPrime valuation_below_layer_prime valuation_above_layer_prime
   signed_exchange_certificate)
open D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
  (FullRecord BHPMaximumGap BHPShortIntervalCount bhpExponent priceExponent
   comparisonCount primesIn logMass bhp_boundary_price_localization)

/- Price conversion is an inequality about the actual price, not an identification
of referencePrice X with beta 1 X. It is uniform in real X >= 2. -/

theorem actual_high_inventory
    (hgap : BHPMaximumGap) (hcount : BHPShortIntervalCount)
    (j : ℕ) (hj : 2 ≤ j) :
    ∃ A W T : ℝ, 0 < A ∧ 0 < W ∧ 0 < T ∧
      ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
        T ≤ (largestPrime m : ℝ) →
        let Q : ℝ := layerPrime m j
        let R : ℝ := largestPrime m
        ∃ Lo Hi : Finset ℕ,
          Lo.card = comparisonCount j R ∧ Hi.card = comparisonCount j R ∧
          Disjoint Lo Hi ∧ R ≤ Q ^ j ∧ W * Q ^ bhpExponent ≤ Q / 2 ∧
          |beta j Q - beta 1 R| ≤ A * beta 1 R * R ^ (-priceExponent j) ∧
          (∀ p ∈ Lo, p.Prime ∧ 2 < p ∧ m.factorization p = j ∧
            Q - W * Q ^ bhpExponent ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q) ∧
          (∀ p ∈ Hi, p.Prime ∧ 2 < p ∧ m.factorization p = j - 1 ∧
            Q < (p : ℝ) ∧ (p : ℝ) ≤ Q + W * Q ^ bhpExponent) := by
  have hcounted := hcount
  obtain ⟨W, c, X, hW, hc, _, hshort⟩ := hcounted
  obtain ⟨A, Ta, hA, hTa, hloc⟩ := bhp_boundary_price_localization hgap hcount j hj
  obtain ⟨Tg, hTg, hgeom⟩ :=
    ActualBoundaryPriceLocalization.uniform_higher_geometry j hj W c (max X 5) hW hc
  refine ⟨A, W, max Ta Tg, hA, hW, lt_of_lt_of_le hTa (le_max_left _ _), ?_⟩
  intro m hm mu hmu hrecord hlarge
  dsimp only
  let Q : ℝ := layerPrime m j
  let R : ℝ := largestPrime m
  let w : ℝ := W * Q ^ bhpExponent
  obtain ⟨hXQ, hcap, hw, hbelow, habove, hRQ⟩ :=
    hgeom m hm mu hmu hrecord ((le_max_right Ta Tg).trans hlarge)
  have hQ5 : 5 ≤ Q := (le_max_right X 5).trans hXQ
  have hXQ' : X ≤ Q := (le_max_left X 5).trans hXQ
  obtain ⟨Lo, Hi, hLo, hHi, hLoI, hHiI⟩ :=
    ActualBoundaryPriceLocalization.counted_higher_pools hshort hXQ' hcap
  have hanti := (price_record_prime_structure hm hmu hrecord).1
  have hlo (p : ℕ) (hp : p ∈ Lo) :
      p.Prime ∧ 2 < p ∧ m.factorization p = j ∧
        Q - w ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q := by
    obtain ⟨hpprime, hpQlo, hpQhi⟩ := hLoI p hp
    have hpQnat : p ≤ layerPrime m j := by exact_mod_cast hpQhi
    have hpnext : layerPrime m (j + 1) < p := by
      exact_mod_cast hbelow.trans_le hpQlo
    have hjlo := valuation_below_layer_prime hpprime hanti hpQnat
    have hjhi := valuation_above_layer_prime (by omega : 0 < m)
      (by omega : 1 ≤ j + 1) hpprime hpnext
    have hp2r : (2 : ℝ) < p := by dsimp [w] at *; linarith
    exact ⟨hpprime, by exact_mod_cast hp2r, by omega, hpQlo, hpQhi⟩
  have hhi (p : ℕ) (hp : p ∈ Hi) :
      p.Prime ∧ 2 < p ∧ m.factorization p = j - 1 ∧
        Q < (p : ℝ) ∧ (p : ℝ) ≤ Q + w := by
    obtain ⟨hpprime, hpQlo, hpQhi⟩ := hHiI p hp
    have hpQnat : layerPrime m j < p := by exact_mod_cast hpQlo
    have hpprev : p ≤ layerPrime m (j - 1) := by exact_mod_cast hpQhi.trans habove
    have hjlo := valuation_below_layer_prime hpprime hanti hpprev
    have hjhi := valuation_above_layer_prime (by omega : 0 < m)
      (by omega : 1 ≤ j) hpprime hpQnat
    have hp2r : (2 : ℝ) < p := by linarith
    exact ⟨hpprime, by exact_mod_cast hp2r, by omega, hpQlo, hpQhi⟩
  have hdis : Disjoint Lo Hi := disjoint_left.mpr (by
    intro p hpL hpH
    have hL := (hlo p hpL).2.2.1
    have hH := (hhi p hpH).2.2.1
    omega)
  exact ⟨Lo, Hi, hLo, hHi, hdis, hRQ, hw,
    hloc m hm mu hmu hrecord ((le_max_left Ta Tg).trans hlarge), hlo, hhi⟩

theorem actual_first_inventory (hcount : BHPShortIntervalCount) :
    ∃ W T : ℝ, 0 < W ∧ 0 < T ∧
      ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
        T ≤ (largestPrime m : ℝ) →
        let R : ℝ := largestPrime m
        ∃ Lo Hi : Finset ℕ,
          Lo.card = comparisonCount 16 R ∧ Hi.card = comparisonCount 16 R ∧
          Disjoint Lo Hi ∧ W * R ^ bhpExponent ≤ R / 2 ∧
          (∀ p ∈ Lo, p.Prime ∧ 2 < p ∧ m.factorization p = 1 ∧
            R - W * R ^ bhpExponent ≤ (p : ℝ) ∧ (p : ℝ) ≤ R) ∧
          (∀ p ∈ Hi, p.Prime ∧ 2 < p ∧ m.factorization p = 0 ∧
            R < (p : ℝ) ∧ (p : ℝ) ≤ R + W * R ^ bhpExponent) := by
  obtain ⟨W, c, X, hW, hc, _, hshort⟩ := hcount
  obtain ⟨Tf, hTf, hfirst⟩ :=
    ActualBoundaryPriceLocalization.uniform_counted_first_pools 16 (by norm_num)
      W c X hW hc hshort
  obtain ⟨Tg, hTg, hgeom⟩ :=
    ActualBoundaryPriceLocalization.uniform_coarse_geometry 2 (by norm_num)
  refine ⟨W, max 8 (max Tf Tg), hW,
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro m hm mu hmu hrecord hlarge
  dsimp only
  let R : ℝ := largestPrime m
  have hR8 : 8 ≤ R := (le_max_left 8 (max Tf Tg)).trans hlarge
  have hTfR : Tf ≤ R :=
    (le_max_left Tf Tg).trans ((le_max_right 8 (max Tf Tg)).trans hlarge)
  have hTgR : Tg ≤ R :=
    (le_max_right Tf Tg).trans ((le_max_right 8 (max Tf Tg)).trans hlarge)
  obtain ⟨_, _, hw, Lo, Hi, hLo, hHi, hLoI, hHiI⟩ := hfirst (largestPrime m) hTfR
  obtain ⟨_, _, _, hQ2, _⟩ := hgeom m hm mu hmu hrecord hTgR
  obtain ⟨_, hsupport⟩ := price_record_prime_structure hm hmu hrecord
  have hlo (p : ℕ) (hp : p ∈ Lo) :
      p.Prime ∧ 2 < p ∧ m.factorization p = 1 ∧
        R - W * R ^ bhpExponent ≤ (p : ℝ) ∧ (p : ℝ) ≤ R := by
    obtain ⟨hpprime, hpRlo, hpRhi⟩ := hLoI p hp
    have hpmem : p ∈ m.primeFactors := by
      rw [hsupport]
      exact Nat.mem_primesLE.mpr ⟨by exact_mod_cast hpRhi, hpprime⟩
    have hpdiv : p ∣ m := Nat.dvd_of_mem_primeFactors hpmem
    have hval1 : 1 ≤ m.factorization p :=
      (hpprime.dvd_iff_one_le_factorization (by omega : m ≠ 0)).mp hpdiv
    have hpQ2 : layerPrime m 2 < p := by exact_mod_cast (by linarith :
      (layerPrime m 2 : ℝ) < p)
    have hval2 := valuation_above_layer_prime (by omega : 0 < m)
      (by norm_num : 1 ≤ 2) hpprime hpQ2
    have hp2 : (2 : ℝ) < p := by linarith
    exact ⟨hpprime, by exact_mod_cast hp2, by omega, hpRlo, hpRhi⟩
  have hhi (p : ℕ) (hp : p ∈ Hi) :
      p.Prime ∧ 2 < p ∧ m.factorization p = 0 ∧
        R < (p : ℝ) ∧ (p : ℝ) ≤ R + W * R ^ bhpExponent := by
    obtain ⟨hpprime, hpRlo, hpRhi⟩ := hHiI p hp
    have hpnot : p ∉ m.primeFactors := by
      rw [hsupport]
      intro hp'
      have hpR : (p : ℝ) ≤ R := by
        change (p : ℝ) ≤ (largestPrime m : ℝ)
        exact_mod_cast (Nat.mem_primesLE.mp hp').1
      exact hpRlo.not_ge hpR
    have hval : m.factorization p = 0 := by
      simpa only [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] using hpnot
    have hp2 : (2 : ℝ) < p := by linarith
    exact ⟨hpprime, by exact_mod_cast hp2, hval, hpRlo, hpRhi⟩
  have hdis : Disjoint Lo Hi := disjoint_left.mpr (by
    intro p hpL hpH
    have hL := (hlo p hpL).2.2.1
    have hH := (hhi p hpH).2.2.1
    omega)
  exact ⟨Lo, Hi, hLo, hHi, hdis, hw, hlo, hhi⟩

private theorem two_dvd_actual_record {m : ℕ} (hm : 2 ≤ m)
    {mu : ℝ} (hmu : 0 < mu) (hrecord : FullRecord m mu) : 2 ∣ m := by
  have hs := (price_record_prime_structure hm hmu hrecord).2
  have hex : m.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  obtain ⟨p, hp⟩ := hex
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hpP : p ≤ largestPrime m := (Nat.mem_primesLE.mp (hs ▸ hp)).1
  have hP : 2 ≤ largestPrime m := hpprime.two_le.trans hpP
  have h2mem : 2 ∈ m.primeFactors := by
    rw [hs]
    exact Nat.mem_primesLE.mpr ⟨hP, Nat.prime_two⟩
  exact Nat.dvd_of_mem_primeFactors h2mem

def topGain (lambda : ℝ) (m : ℕ) : ℝ :=
  lambda * log 2 - goldenLayerMarginal 2 (m.factorization 2) * log 2

def auxiliaryGain (lambda : ℝ) (m : ℕ) (D U : Finset ℕ) : ℝ :=
  (∑ p ∈ U, (goldenLayerMarginal p (m.factorization p + 1) - lambda) * log p) -
    ∑ p ∈ D, (goldenLayerMarginal p (m.factorization p) - lambda) * log p

private theorem prime_product_log (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    log ((∏ p ∈ S, p : ℕ) : ℝ) = logMass S := by
  rw [Nat.cast_prod]
  exact Real.log_prod (fun p hp => by exact_mod_cast (hS p hp).ne_zero)

/- Finite exact integer realization, using the existing signed certificate and
the unchanged objective_exchange_delta through a separate visibility patch.
Only mass positivity is an intermediate input. The global proof must derive
it by substituting selected actual pools into actual_root_greedy_stencil.
Every auxiliary prime is changed once and the actual highest 2-layer is deleted.
No hypothetical recordhood at lambda is used: recordhood stays at arbitrary mu.
-/
theorem actual_finite_predecessor {m : ℕ} (hm : 2 ≤ m)
    {mu lambda : ℝ} (hmu : 0 < mu) (hrecord : FullRecord m mu)
    (D U : Finset ℕ)
    (hD : ∀ p ∈ D, p.Prime ∧ 2 < p ∧ p ∣ m)
    (hU : ∀ p ∈ U, p.Prime ∧ 2 < p)
    (hDU : Disjoint D U)
    (hmass : 0 < log 2 + logMass D - logMass U) :
    ∃ n : ℕ, 0 < n ∧ n < m ∧
      log (m : ℝ) - log (n : ℝ) = log 2 + logMass D - logMass U ∧
      n.factorization 2 + 1 = m.factorization 2 ∧
      goldenResourceObjective lambda n - goldenResourceObjective lambda m =
        topGain lambda m + auxiliaryGain lambda m D U ∧
      topGain lambda m < (lambda - mu) * (log (m : ℝ) - log (n : ℝ)) -
        auxiliaryGain lambda m D U := by
  classical
  have hm0 : 0 < m := by omega
  have h2dvd := two_dvd_actual_record hm hmu hrecord
  have h2D : 2 ∉ D := by intro hp; have := (hD 2 hp).2.1; omega
  have h2U : 2 ∉ U := by intro hp; have := (hU 2 hp).2; omega
  let S := insert 2 D
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime := by
    rcases mem_insert.mp hp with rfl | hp
    · exact Nat.prime_two
    · exact (hD p hp).1
  have hSd (p : ℕ) (hp : p ∈ S) : p ∣ m := by
    rcases mem_insert.mp hp with rfl | hp
    · exact h2dvd
    · exact (hD p hp).2.2
  have hUp (p : ℕ) (hp : p ∈ U) : p.Prime := (hU p hp).1
  have hSU : Disjoint S U := disjoint_left.mpr (by
    intro p hpS hpU
    rcases mem_insert.mp hpS with rfl | hpD
    · exact h2U hpU
    · exact disjoint_left.mp hDU hpD hpU)
  have hmassS : logMass S = log 2 + logMass D := by
    dsimp [S, logMass]
    rw [sum_insert h2D]
    norm_num
  let d0 : ℕ := ∏ p ∈ S, p
  let u0 : ℕ := ∏ p ∈ U, p
  have hdpos : 0 < d0 := Finset.prod_pos (fun p hp => (hS p hp).pos)
  have hupos : 0 < u0 := Finset.prod_pos (fun p hp => (hUp p hp).pos)
  have hdR : (0 : ℝ) < d0 := by exact_mod_cast hdpos
  have huR : (0 : ℝ) < u0 := by exact_mod_cast hupos
  have hdlog : log (d0 : ℝ) = log 2 + logMass D := by
    exact (prime_product_log S hS).trans hmassS
  have hulog : log (u0 : ℝ) = logMass U := prime_product_log U hUp
  have hprodR : (u0 : ℝ) < d0 := (log_lt_log_iff huR hdR).mp (by
    rw [hdlog, hulog]
    linarith only [hmass])
  have hprod : u0 < d0 := by exact_mod_cast hprodR
  let r : ℕ := m / d0
  let n : ℕ := r * u0
  have hcert := signed_exchange_certificate mu hm0 hrecord S U hS hUp hSd hSU hprod
  have hnpos : 0 < n := hcert.1
  have hnm : n < m := hcert.2.1
  have hSmem : S ⊆ m.primeFactors := fun p hp =>
    Nat.mem_primeFactors.mpr ⟨hS p hp, hSd p hp, hm0.ne'⟩
  have hdvd : d0 ∣ m :=
    (prod_dvd_prod_of_subset S m.primeFactors id hSmem).trans (Nat.prod_primeFactors_dvd m)
  have hrpos : 0 < r := Nat.div_pos (Nat.le_of_dvd hm0 hdvd) hdpos
  have hrd : r * d0 = m := Nat.div_mul_cancel hdvd
  have hrR : (0 : ℝ) < r := by exact_mod_cast hrpos
  have hlogm : log (m : ℝ) = log (r : ℝ) + log (d0 : ℝ) := by
    rw [← hrd, Nat.cast_mul, log_mul hrR.ne' hdR.ne']
  have hlogn : log (n : ℝ) = log (r : ℝ) + log (u0 : ℝ) := by
    change log ((r * u0 : ℕ) : ℝ) = _
    rw [Nat.cast_mul, log_mul hrR.ne' huR.ne']
  have heta : log (m : ℝ) - log (n : ℝ) = log 2 + logMass D - logMass U := by
    rw [hlogm, hlogn, hdlog, hulog]
    ring
  have hdfac : d0.factorization 2 = 1 := by
    simpa [d0, S, D5.S3.Factorization.PrimePowers.FiniteCrtJoin.primePowerProduct] using
      (D5.S3.Arith.Robin.PrimeValuation5040Bridge.primeBlock_factorization
        hS (fun _ => 1) 2)
  have hufac : u0.factorization 2 = 0 := by
    simpa [u0, h2U, D5.S3.Factorization.PrimePowers.FiniteCrtJoin.primePowerProduct] using
      (D5.S3.Arith.Robin.PrimeValuation5040Bridge.primeBlock_factorization
        hUp (fun _ => 1) 2)
  have hmf : m.factorization 2 = r.factorization 2 + 1 := by
    rw [← hrd, Nat.factorization_mul hrpos.ne' hdpos.ne', Finsupp.add_apply, hdfac]
  have hnf : n.factorization 2 = r.factorization 2 := by
    change (r * u0).factorization 2 = _
    rw [Nat.factorization_mul hrpos.ne' hupos.ne', Finsupp.add_apply, hufac, add_zero]
  have hdelta := FixedLayerRigidity.objective_exchange_delta lambda hm0 S U hS hUp hSd hSU
  have hgain : goldenResourceObjective lambda n - goldenResourceObjective lambda m =
      topGain lambda m + auxiliaryGain lambda m D U := by
    change goldenResourceObjective lambda n - goldenResourceObjective lambda m = _ at hdelta
    rw [hdlog, hulog] at hdelta
    change goldenResourceObjective lambda n - goldenResourceObjective lambda m = _
    rw [hdelta]
    dsimp [S, topGain, auxiliaryGain]
    rw [sum_insert h2D]
    simp only [sub_mul, sum_sub_distrib, ← mul_sum]
    dsimp [logMass]
    ring
  have hrec : goldenResourceObjective mu n - goldenResourceObjective mu m < 0 :=
    sub_neg.mpr (hrecord n hnpos hnm)
  have hprice : goldenResourceObjective mu n - goldenResourceObjective mu m =
      (goldenResourceObjective lambda n - goldenResourceObjective lambda m) -
        (lambda - mu) * (log (m : ℝ) - log (n : ℝ)) := by
    unfold goldenResourceObjective
    ring
  refine ⟨n, hnpos, hnm, heta, by omega, hgain, ?_⟩
  rw [hprice, hgain] at hrec
  linarith only [hrec]

/- Exact arbitrary-record clock comparison is already supplied by the pinned
record_mass_limits theorem. This conversion does not identify mu with a clock
price and assumes no power bound for Chebyshev.theta. -/
theorem uniform_actual_clock : ∃ T : ℝ, 0 < T ∧
    ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
      T ≤ (largestPrime m : ℝ) →
      1 ≤ log (largestPrime m : ℝ) ∧ 0 < log (log (m : ℝ)) ∧
      log (largestPrime m : ℝ) / 2 ≤ log (log (m : ℝ)) ∧
      log (log (m : ℝ)) ≤ 2 * log (largestPrime m : ℝ) := by
  let S := {v : ℕ × ℝ // 2 ≤ v.1 ∧ 0 < v.2 ∧ FullRecord v.1 v.2}
  let m : S → ℕ := fun x => x.1.1
  let mu : S → ℝ := fun x => x.1.2
  let R : S → ℝ := fun x => largestPrime (m x)
  let L : S → ℝ := fun x => log (R x)
  let M : S → ℝ := fun x => log (log (m x : ℝ))
  let l : Filter S := comap R atTop
  have hR : Tendsto R l atTop := tendsto_comap
  have hL : Tendsto L l atTop := tendsto_log_atTop.comp hR
  have hm (x : S) : 2 ≤ m x := x.2.1
  have hmu (x : S) : 0 < mu x := x.2.2.1
  have hrec (x : S) : FullRecord (m x) (mu x) := x.2.2.2
  have hmass := FullArithmeticCorrectionSecondOrder.record_mass_limits
    m mu hm hmu hrec hR
  have hr : Tendsto (fun x => log (m x : ℝ) / R x) l (𝓝 1) := hmass.2.2.1
  have hlogr : Tendsto (fun x => log (log (m x : ℝ) / R x)) l (𝓝 0) := by
    simpa only [log_one, Function.comp_def] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp hr
  have hz : Tendsto (fun x => log (log (m x : ℝ) / R x) / L x) l (𝓝 0) :=
    hlogr.div_atTop hL
  have hratio : Tendsto (fun x => M x / L x) l (𝓝 1) := by
    have hh := (tendsto_const_nhds : Tendsto (fun _ : S => (1 : ℝ)) l (𝓝 1)).add hz
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [hR.eventually_gt_atTop 1] with x hx
    have hlogm : 0 < log (m x : ℝ) :=
      log_pos (by exact_mod_cast (show 1 < m x from lt_of_lt_of_le (by norm_num) (hm x)))
    dsimp [M, L]
    rw [log_div hlogm.ne' (by linarith : R x ≠ 0)]
    field_simp [(log_pos hx).ne']
    <;> ring
  have hall : ∀ᶠ x in l,
      1 ≤ L x ∧ 0 < M x ∧ L x / 2 ≤ M x ∧ M x ≤ 2 * L x := by
    filter_upwards [hL.eventually_ge_atTop 1,
      hratio.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
      hratio.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))]
      with x hLx hlo hhi
    have hL0 : 0 < L x := by linarith
    have hlo' := (lt_div_iff₀ hL0).mp hlo
    have hhi' := (div_lt_iff₀ hL0).mp hhi
    exact ⟨hLx, by linarith, by linarith, hhi'.le⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_comap.mp hall)
  refine ⟨max T 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro n hn nu hnu hrecord hlarge
  let x : S := ⟨(n, nu), hn, hnu, hrecord⟩
  exact hT (largestPrime n : ℝ) ((le_max_left T 2).trans hlarge) x rfl

/- A complete mass error of size K log(P) P^(-19/640), once derived by the
simultaneous selection below, is o(mesh4). This has a proved real threshold
before all records; it is not an assumed small-slack producer. -/
theorem eventual_mass_error_absorption (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ X : ℝ in atTop,
      0 < mesh4 X ∧ K * log X * X ^ (-(19 / 640 : ℝ)) ≤ mesh4 X / 2 := by
  have hmesh := actual_stencil_limits.2.2.2
  have ha : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hc : 0 < 6 * log (2 : ℝ) ^ 4 := by positivity
  have hsmall : Tendsto (fun X : ℝ => log X ^ 5 / X ^ (19 / 640 : ℝ))
      atTop (𝓝 0) := by
    simpa only [rpow_natCast] using
      (_root_.isLittleO_log_rpow_rpow_atTop (5 : ℕ) (by norm_num : (0 : ℝ) < 19 / 640)).tendsto_div_nhds_zero
  have hp : ∀ᶠ X : ℝ in atTop, 0 < mesh4 X := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      hmesh.eventually (eventually_gt_nhds hc)] with X hX hmeshX
    exact (mul_pos_iff_of_pos_left (pow_pos (log_pos hX) 4)).mp hmeshX
  have hratio : Tendsto
      (fun X : ℝ => (K * log X * X ^ (-(19 / 640 : ℝ))) / mesh4 X)
      atTop (𝓝 0) := by
    have hh := (hsmall.const_mul K).div hmesh hc.ne'
    simp only [mul_zero, zero_div] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ), hp] with X hX hmeshX
    dsimp only [Pi.div_apply]
    rw [rpow_neg (by linarith : 0 ≤ X)]
    field_simp [(log_pos hX).ne', hmeshX.ne',
      (rpow_pos_of_pos (by linarith : 0 < X) (19 / 640 : ℝ)).ne']
    <;> ring
  filter_upwards [hp, hratio.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with X hX hr
  exact ⟨hX, by linarith [(div_le_iff₀ hX).mp hr.le]⟩

/- Pointwise estimates retain the original prime and its original layer index.
The three analytic declarations below are reused by visibility-only exposure;
no beta derivative or boundary-localization proof is duplicated. -/
private theorem interval_log_distance {Q w x : ℝ} (hQ : 4 ≤ Q)
    (hw : 0 ≤ w) (hwQ : w ≤ Q / 2)
    (hxlo : Q - w ≤ x) (hxhi : x ≤ Q + w) :
    |log x - log Q| ≤ 2 * w / Q := by
  have hQ0 : 0 < Q := by linarith
  have ha : 0 < Q / 2 := by positivity
  have hx : Q / 2 ≤ x := by linarith
  have hd : ∀ t ∈ Set.Ici (Q / 2), HasDerivAt log (t⁻¹) t := by
    intro t ht
    exact hasDerivAt_log (ne_of_gt (ha.trans_le ht))
  have hb : ∀ t ∈ Set.Ici (Q / 2), ‖t⁻¹‖ ≤ 2 / Q := by
    intro t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (ha.le.trans ht))]
    have hh := one_div_le_one_div_of_le ha ht
    calc
      _ = 1 / t := by simp
      _ ≤ 1 / (Q / 2) := hh
      _ = 2 / Q := by field_simp [hQ0.ne'] <;> ring
  have hv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hd t ht).hasDerivWithinAt) hb
    (convex_Ici (Q / 2)) (by linarith : Q / 2 ≤ Q) hx
  have habs : |x - Q| ≤ w := abs_le.mpr ⟨by linarith, by linarith⟩
  have hh : |log x - log Q| ≤ (2 / Q) * |x - Q| := by
    simpa only [Real.norm_eq_abs] using hv
  calc
    _ ≤ (2 / Q) * |x - Q| := hh
    _ ≤ (2 / Q) * w := mul_le_mul_of_nonneg_left habs (by positivity)
    _ = _ := by ring

private theorem width_power_transfer {j : ℕ} (hj : 1 ≤ j)
    {R Q : ℝ} (hR : 1 ≤ R) (hQ : 0 < Q) (hRQ : R ≤ Q ^ j) :
    Q ^ (bhpExponent - 1) ≤ R ^ (-priceExponent j) := by
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hgamma : 0 < priceExponent j := by dsimp [priceExponent]; positivity
  have hh := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < R) hRQ
    (neg_nonpos.mpr hgamma.le)
  have he : (Q ^ j) ^ (-priceExponent j) = Q ^ (bhpExponent - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ.le]
    congr 1
    dsimp [priceExponent, bhpExponent]
    field_simp [hj0.ne'] <;> ring
  rwa [he] at hh

theorem pointwise_boundary_estimates {j : ℕ} (hj : 1 ≤ j)
    {R Q W A H root : ℝ} (hR : 4 ≤ R) (hQ : 4 ≤ Q) (hQR : Q ≤ R)
    (hRQ : R ≤ Q ^ j) (hW : 0 ≤ W) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hlog : log R / (4 * (j : ℝ)) ≤ log (Q / 2))
    (hwidth : W * Q ^ bhpExponent ≤ Q / 2)
    (hband : |beta j Q - beta 1 R| ≤ A * beta 1 R * R ^ (-priceExponent j))
    (hroot : |(j : ℝ) * log Q - root| ≤ H * R ^ (-priceExponent j)) :
    ∀ p : ℕ, p.Prime → Q - W * Q ^ bhpExponent ≤ (p : ℝ) →
      (p : ℝ) ≤ Q + W * Q ^ bhpExponent →
      |log (p : ℝ) - root / (j : ℝ)| ≤
        (2 * W + H) * R ^ (-priceExponent j) ∧
      |(goldenLayerMarginal p j - beta 1 R) * log (p : ℝ)| ≤
        (2 * (A + 2 * W *
          (((j : ℝ) + 2) * (2 : ℝ) ^ (j + 1) * (4 * (j : ℝ))))) *
          beta 1 R * log R * R ^ (-priceExponent j) := by
  intro p hp hlo hhi
  let t := R ^ (-priceExponent j)
  let B := ((j : ℝ) + 2) * (2 : ℝ) ^ (j + 1) * (4 * (j : ℝ))
  have hR0 : 0 < R := by linarith
  have hQ0 : 0 < Q := by linarith
  have hL : 0 < log R := log_pos (by linarith)
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have ht : 0 ≤ t := rpow_nonneg hR0.le _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hlambda : 0 < beta 1 R := beta_pos (by linarith) (by norm_num)
  have hw : 0 ≤ W * Q ^ bhpExponent := by positivity
  have hpQ : Q / 2 ≤ (p : ℝ) := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hplog : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hpR2 : (p : ℝ) ≤ R ^ 2 := by nlinarith [sq_nonneg (R - 1)]
  have hlogp : log (p : ℝ) ≤ 2 * log R := by
    have hh := log_le_log hp0 hpR2
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hpow := width_power_transfer hj (by linarith : 1 ≤ R) hQ0 hRQ
  have hwidthRatio : W * Q ^ bhpExponent / Q ≤ W * t := by
    have he : Q ^ bhpExponent / Q = Q ^ (bhpExponent - 1) := by
      rw [Real.rpow_sub hQ0, Real.rpow_one]
    calc
      _ = W * Q ^ (bhpExponent - 1) := by rw [← he]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hW
  have hlogdist : |log (p : ℝ) - log Q| ≤ 2 * W * t := by
    calc
      _ ≤ 2 * (W * Q ^ bhpExponent) / Q := interval_log_distance hQ hw hwidth hlo hhi
      _ = 2 * (W * Q ^ bhpExponent / Q) := by ring
      _ ≤ 2 * (W * t) := mul_le_mul_of_nonneg_left hwidthRatio (by norm_num)
      _ = _ := by ring
  have hroot' : |log Q - root / (j : ℝ)| ≤ H * t := by
    have he : (j : ℝ) * (log Q - root / (j : ℝ)) = (j : ℝ) * log Q - root := by
      field_simp [hj0.ne'] <;> ring
    have hh : (j : ℝ) * |log Q - root / (j : ℝ)| ≤ H * t := by
      calc
        _ = |(j : ℝ) * (log Q - root / (j : ℝ))| := by
          rw [abs_mul, abs_of_pos hj0]
        _ ≤ H * t := by rw [he]; exact hroot
    have hmul := mul_le_mul_of_nonneg_right hj1
      (abs_nonneg (log Q - root / (j : ℝ)))
    have hmul' : |log Q - root / (j : ℝ)| ≤
        (j : ℝ) * |log Q - root / (j : ℝ)| := by simpa only [one_mul] using hmul
    exact hmul'.trans hh
  refine ⟨(abs_sub_le (log (p : ℝ)) (log Q) (root / (j : ℝ))).trans
    (by nlinarith), ?_⟩
  have hLip := ActualBoundaryPriceLocalization.priceLip_half_bound j
    (by linarith : 1 < R) hQ (by positivity : 0 < 4 * (j : ℝ)) hlog
  have hbase := ActualBoundaryPriceLocalization.first_beta_lower (by linarith : 2 ≤ R)
  have hnorm : ActualBoundaryPriceLocalization.priceLip j (Q / 2) *
      (W * Q ^ bhpExponent) ≤ (2 * W * B) * beta 1 R * t := by
    have he : Q ^ bhpExponent = Q ^ (bhpExponent - 1) * Q := by
      calc
        _ = Q ^ ((bhpExponent - 1) + 1) := by congr 1 <;> ring
        _ = _ := by rw [Real.rpow_add hQ0, Real.rpow_one]
    calc
      _ ≤ (B / (Q ^ (j + 1) * log R)) * (W * Q ^ bhpExponent) :=
        mul_le_mul_of_nonneg_right hLip hw
      _ = (W * B) * (1 / (Q ^ j * log R)) * Q ^ (bhpExponent - 1) := by
        rw [he, pow_succ]
        field_simp [hQ0.ne', hL.ne'] <;> ring
      _ ≤ (W * B) * (1 / (R * log R)) * t := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left
            (one_div_le_one_div_of_le (by positivity)
              (mul_le_mul_of_nonneg_right hRQ hL.le)) (mul_nonneg hW hB)
        · exact hpow
        · positivity
        · positivity
      _ ≤ (W * B) * (2 * beta 1 R) * t :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbase (mul_nonneg hW hB)) ht
      _ = _ := by ring
  have hLip0 : 0 ≤ ActualBoundaryPriceLocalization.priceLip j (Q / 2) := by
    unfold ActualBoundaryPriceLocalization.priceLip
    have hlogQ : 0 < log (Q / 2) := log_pos (by linarith)
    positivity
  have hdist : |(p : ℝ) - Q| ≤ W * Q ^ bhpExponent :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hvar := (ActualBoundaryPriceLocalization.price_variation hj
    (by linarith : 2 ≤ Q / 2) (by linarith : Q / 2 ≤ Q) hpQ).trans
      (mul_le_mul_of_nonneg_left hdist hLip0)
  have hprice : |beta j (p : ℝ) - beta 1 R| ≤ (A + 2 * W * B) * beta 1 R * t :=
    (abs_sub_le (beta j (p : ℝ)) (beta j Q) (beta 1 R)).trans (by nlinarith)
  rw [← beta_nat hp hj, abs_mul, abs_of_nonneg hplog]
  calc
    _ ≤ ((A + 2 * W * B) * beta 1 R * t) * (2 * log R) :=
      mul_le_mul hprice hlogp hplog (by positivity)
    _ = _ := by dsimp [B]; ring


end D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack
