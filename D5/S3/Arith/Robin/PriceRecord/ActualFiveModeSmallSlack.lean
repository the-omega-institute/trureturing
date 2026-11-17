/- GID: D5/S3/Arith/Robin/PriceRecord/ActualFiveModeSmallSlack
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualFiveModeSmallSlack
   mirror-E: none(waiver:elementary-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Actual simultaneous five-mode selection and uniform small-slack endpoint. -/
/- proof_shape: content
admission_basis: escape-witness
escape_witness: finite_five_mode_selection: distinct actual primes realize all modes and both signs with exact counts and complete signed fees.
utility: none. The actual-record construction is an unbounded conditional
mathematical argument. All prime counts, valuations and fees retain their
original hypotheses; the prescribed full bank and RH remain open. -/
import D5.S3.Arith.Robin.PriceRecord.ActualFiveModeInventory

/-! Actual-record arithmetic: ActualFiveModeSmallSlack. -/

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

private def modeIndex (k : Fin 5) : ℕ := 2 ^ k.val
private def countIndex (k : Fin 5) : ℕ := if k = 0 then 16 else modeIndex k
private def rootLog (R : ℝ) (k : Fin 5) : ℝ :=
  if k = 0 then log R else log (cutoff (modeIndex k) (beta 1 R))

private theorem mode_index_bounds (k : Fin 5) :
    1 ≤ modeIndex k ∧ modeIndex k ≤ 16 ∧ 2 ≤ countIndex k ∧
      19 / 640 ≤ priceExponent (modeIndex k) := by
  fin_cases k <;> norm_num [modeIndex, countIndex, priceExponent]

/- The two scale fields are deliberately present even though original exponent
labels separate all the other pairs. In particular exponent 1 is shared. -/
private def ModeAtom (m : ℕ) (k : Fin 5) (up : Bool) (p : ℕ) : Prop :=
  p.Prime ∧ 2 < p ∧
    m.factorization p + (if up then 1 else 0) = modeIndex k ∧
    (k = 0 → (largestPrime m : ℝ) / 2 ≤ (p : ℝ)) ∧
    (k = 1 → (p : ℝ) ≤ 3 * (layerPrime m 2 : ℝ) / 2)

private def ModeEstimate (A : ℝ) (R : ℝ) (k : Fin 5) (p : ℕ) : Prop :=
  |log (p : ℝ) - rootLog R k| ≤ A * R ^ (-priceExponent (modeIndex k)) ∧
    |(goldenLayerMarginal p (modeIndex k) - beta 1 R) * log (p : ℝ)| ≤
      A * beta 1 R * log R * R ^ (-priceExponent (modeIndex k))

private theorem root_mass_coordinate (k : Fin 5) (hk : k ≠ 0) (R : ℝ) :
    rootMasses R k = log R + actualOffset (modeIndex k) R := by
  fin_cases k <;> simp_all [rootMasses, modeIndex]

private theorem root_log_mass (k : Fin 5) (R : ℝ) :
    rootLog R k = rootMasses R k / (modeIndex k : ℝ) := by
  by_cases hk : k = 0
  · subst k; simp [rootLog, rootMasses, modeIndex]
  · have hj0 : (modeIndex k : ℝ) ≠ 0 := by
      have hj := (mode_index_bounds k).1
      exact_mod_cast (show modeIndex k ≠ 0 by omega)
    rw [rootLog, if_neg hk, root_mass_coordinate k hk R]
    dsimp [actualOffset]
    field_simp [hj0] <;> ring

/- Fixed-mode constants and thresholds precede all original integers and prices.
Both pools are actual original-boundary pools; no ideal exponent is supplied. -/
private theorem uniform_mode_inventory
    (hgap : BHPMaximumGap) (hcount : BHPShortIntervalCount) (k : Fin 5) :
    ∃ A T : ℝ, 0 < A ∧ 0 < T ∧
      ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
        T ≤ (largestPrime m : ℝ) → ∃ Lo Hi : Finset ℕ,
          Lo.card = comparisonCount (countIndex k) (largestPrime m) ∧
          Hi.card = comparisonCount (countIndex k) (largestPrime m) ∧
          (∀ p ∈ Lo, ModeAtom m k false p ∧ ModeEstimate A (largestPrime m) k p) ∧
          (∀ p ∈ Hi, ModeAtom m k true p ∧ ModeEstimate A (largestPrime m) k p) := by
  classical
  by_cases hk : k = 0
  · subst k
    obtain ⟨W, Ti, hW, hTi, hi⟩ := actual_first_inventory hcount
    let A : ℝ := 1 + 2 * W + 2 * (2 * W * ((1 + 2) * 2 ^ (1 + 1) * (4 * 1)))
    refine ⟨A, max 4 Ti, by dsimp [A]; positivity,
      lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
    intro m hm mu hmu hrecord hlarge
    let R : ℝ := largestPrime m
    have hR4 : 4 ≤ R := (le_max_left 4 Ti).trans hlarge
    obtain ⟨Lo, Hi, hLo, hHi, _, hw, hlo, hhi⟩ :=
      hi m hm mu hmu hrecord ((le_max_right 4 Ti).trans hlarge)
    have hlog : log R / (4 * (1 : ℝ)) ≤ log (R / 2) := by
      have hh := log_le_log (by norm_num : (0 : ℝ) < 4) hR4
      have he : log (4 : ℝ) = 2 * log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      rw [he] at hh
      rw [log_div (by linarith : R ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      linarith [log_pos (by norm_num : (1 : ℝ) < 2)]
    have hpoint := pointwise_boundary_estimates (j := 1) (root := log R) (by norm_num)
      hR4 hR4 (le_refl R) (by simp) hW.le (le_refl (0 : ℝ)) (le_refl (0 : ℝ))
      (by simpa only [Nat.cast_one] using hlog) hw (by simp) (by simp)
    have pack (p : ℕ) (hp : p.Prime) (hp2 : 2 < p)
        (hv : m.factorization p + (if false then 1 else 0) = 1)
        (hl : R - W * R ^ bhpExponent ≤ (p : ℝ))
        (hu : (p : ℝ) ≤ R + W * R ^ bhpExponent) :
        ModeAtom m 0 false p ∧ ModeEstimate A R 0 p := by
      have hh := hpoint p hp hl hu
      have ht : 0 ≤ R ^ (-priceExponent 1) := by positivity
      have hlambda : 0 ≤ beta 1 R := (beta_pos (by linarith) (by norm_num)).le
      have hL : 0 ≤ log R := log_nonneg (by linarith)
      refine ⟨⟨hp, hp2, by simpa [modeIndex] using hv, ?_, by simp⟩, ?_⟩
      · intro _; dsimp [R] at *; linarith
      · dsimp [ModeEstimate, rootLog, rootMasses, modeIndex]
        norm_num at hh ⊢
        constructor
        · exact hh.1.trans (mul_le_mul_of_nonneg_right (by dsimp [A]; nlinarith) ht)
        · have hconst : 2 * (2 * W * 48) ≤ A := by dsimp [A]; nlinarith
          exact hh.2.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hconst hlambda) hL) ht)
    refine ⟨Lo, Hi, by simpa [countIndex] using hLo,
      by simpa [countIndex] using hHi, ?_, ?_⟩
    · intro p hp
      obtain ⟨hpP, hp2, hv, hl, hu⟩ := hlo p hp
      exact pack p hpP hp2 (by simpa using hv) hl (hu.trans (le_add_of_nonneg_right (by positivity)))
    · intro p hp
      obtain ⟨hpP, hp2, hv, hl, hu⟩ := hhi p hp
      have hh := hpoint p hpP (by linarith [show 0 ≤ W * R ^ bhpExponent by positivity]) hu
      have ht : 0 ≤ R ^ (-priceExponent 1) := by positivity
      have hlambda : 0 ≤ beta 1 R := (beta_pos (by linarith) (by norm_num)).le
      have hL : 0 ≤ log R := log_nonneg (by linarith)
      refine ⟨⟨hpP, hp2, by simpa [modeIndex, hv], by intro _; linarith, by simp⟩, ?_⟩
      dsimp [ModeEstimate, rootLog, rootMasses, modeIndex]
      norm_num at hh ⊢
      constructor
      · exact hh.1.trans (mul_le_mul_of_nonneg_right (by dsimp [A]; nlinarith) ht)
      · have hconst : 2 * (2 * W * 48) ≤ A := by dsimp [A]; nlinarith
        exact hh.2.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hconst hlambda) hL) ht)
  · let j := modeIndex k
    have hj : 2 ≤ j := by fin_cases k <;> simp_all [j, modeIndex]
    obtain ⟨Ai, W, Ti, hAi, hW, hTi, hi⟩ := actual_high_inventory hgap hcount j hj
    obtain ⟨H, Tr, hH, hTr, hr⟩ := uniform_boundary_root_log_transfer hgap hcount j hj
    obtain ⟨Tg, hTg, hg⟩ := ActualBoundaryPriceLocalization.uniform_coarse_geometry j hj
    let B : ℝ := ((j : ℝ) + 2) * (2 : ℝ) ^ (j + 1) * (4 * (j : ℝ))
    let A : ℝ := 1 + (2 * W + H) + 2 * (Ai + 2 * W * B)
    let T := max Ti (max Tr Tg)
    refine ⟨A, T, by dsimp [A, B]; positivity,
      lt_of_lt_of_le hTi (le_max_left _ _), ?_⟩
    intro m hm mu hmu hrecord hlarge
    let R : ℝ := largestPrime m
    let Q : ℝ := layerPrime m j
    have hTiR : Ti ≤ R := (le_max_left Ti (max Tr Tg)).trans hlarge
    have hTrR : Tr ≤ R := (le_max_left Tr Tg).trans ((le_max_right Ti _).trans hlarge)
    have hTgR : Tg ≤ R := (le_max_right Tr Tg).trans ((le_max_right Ti _).trans hlarge)
    obtain ⟨Lo, Hi, hLo, hHi, _, hRQ, hw, hband, hlo, hhi⟩ :=
      hi m hm mu hmu hrecord hTiR
    obtain ⟨hR4, hQ4, hQR, _, hlog⟩ := hg m hm mu hmu hrecord hTgR
    have hroot := hr m hm mu hmu hrecord hTrR
    rw [← root_mass_coordinate k hk R] at hroot
    have hpoint := pointwise_boundary_estimates (by omega : 1 ≤ j) hR4 hQ4
      (by linarith : Q ≤ R) hRQ hW.le hAi.le hH.le hlog hw hband hroot
    have pack (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (up : Bool)
        (hv : m.factorization p + (if up then 1 else 0) = j)
        (hl : Q - W * Q ^ bhpExponent ≤ (p : ℝ))
        (hu : (p : ℝ) ≤ Q + W * Q ^ bhpExponent) :
        ModeAtom m k up p ∧ ModeEstimate A R k p := by
      obtain ⟨hplog, hpfee⟩ := hpoint p hp hl hu
      have ht : 0 ≤ R ^ (-priceExponent j) := by positivity
      have hlambda : 0 ≤ beta 1 R := (beta_pos (by linarith) (by norm_num)).le
      have hL : 0 ≤ log R := log_nonneg (by linarith)
      have hB : 0 ≤ B := by dsimp [B]; positivity
      refine ⟨⟨hp, hp2, hv, by simp [hk], ?_⟩, ?_⟩
      · intro hk1
        have hj2 : j = 2 := by simp [j, modeIndex, hk1]
        have hQeq : Q = (layerPrime m 2 : ℝ) := by dsimp only [Q]; rw [hj2]
        rw [← hQeq]
        linarith
      · constructor
        · rw [root_log_mass k R]
          exact hplog.trans (mul_le_mul_of_nonneg_right
            (by dsimp only [A]; nlinarith [mul_nonneg hW.le hB]) ht)
        · exact hpfee.trans (by
            have hconst : 2 * (Ai + 2 * W * B) ≤ A := by
              dsimp [A]; linarith [mul_pos (by norm_num : (0 : ℝ) < 2) hW]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hconst hlambda) hL) ht)
    refine ⟨Lo, Hi, by simpa [countIndex, hk, j] using hLo,
      by simpa [countIndex, hk, j] using hHi, ?_, ?_⟩
    · intro p hp
      obtain ⟨hpP, hp2, hv, hl, hu⟩ := hlo p hp
      exact pack p hpP hp2 false (by simpa using hv) hl
        (hu.trans (by
          change Q ≤ Q + W * Q ^ bhpExponent
          exact le_add_of_nonneg_right (by positivity)))
    · intro p hp
      obtain ⟨hpP, hp2, hv, hl, hu⟩ := hhi p hp
      exact pack p hpP hp2 true (by change m.factorization p + 1 = j; omega)
        (by
          change Q - W * Q ^ bhpExponent ≤ (p : ℝ)
          have hln : Q < (p : ℝ) := hl
          linarith [show 0 ≤ W * Q ^ bhpExponent by positivity]) hu

private theorem uniform_five_mode_pools
    (hgap : BHPMaximumGap) (hcount : BHPShortIntervalCount) :
    ∃ A T : ℝ, 0 < A ∧ 0 < T ∧
      ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
        T ≤ (largestPrime m : ℝ) →
        (layerPrime m 2 : ℝ) ≤ (largestPrime m : ℝ) / 8 ∧
        ∃ Lo Hi : Fin 5 → Finset ℕ, ∀ k : Fin 5,
          (Lo k).card = comparisonCount (countIndex k) (largestPrime m) ∧
          (Hi k).card = comparisonCount (countIndex k) (largestPrime m) ∧
          (∀ p ∈ Lo k, ModeAtom m k false p ∧ ModeEstimate A (largestPrime m) k p) ∧
          (∀ p ∈ Hi k, ModeAtom m k true p ∧ ModeEstimate A (largestPrime m) k p) := by
  classical
  choose a t ha ht hpool using uniform_mode_inventory hgap hcount
  obtain ⟨Tg, hTg, hg⟩ := ActualBoundaryPriceLocalization.uniform_coarse_geometry 2 (by norm_num)
  let A := 1 + ∑ k : Fin 5, a k
  let T := 1 + Tg + ∑ k : Fin 5, t k
  have hsumA : 0 ≤ ∑ k : Fin 5, a k := sum_nonneg (fun k _ => (ha k).le)
  have hsumT : 0 ≤ ∑ k : Fin 5, t k := sum_nonneg (fun k _ => (ht k).le)
  have haA (k : Fin 5) : a k ≤ A := by
    have hh := single_le_sum (s := (univ : Finset (Fin 5)))
      (fun i _ => (ha i).le) (mem_univ k)
    dsimp [A]; linarith
  have htT (k : Fin 5) : t k ≤ T := by
    have hh := single_le_sum (s := (univ : Finset (Fin 5)))
      (fun i _ => (ht i).le) (mem_univ k)
    dsimp [T]; linarith
  refine ⟨A, T, by dsimp [A]; linarith, by dsimp [T]; linarith, ?_⟩
  intro m hm mu hmu hrecord hlarge
  have hTg : Tg ≤ (largestPrime m : ℝ) := by dsimp [T] at hlarge; linarith
  have hQ8 := (hg m hm mu hmu hrecord hTg).2.2.1
  have hR4 := (hg m hm mu hmu hrecord hTg).1
  have hR0 : (0 : ℝ) < largestPrime m := by linarith
  have hL : 0 ≤ log (largestPrime m : ℝ) := log_nonneg (by linarith)
  have hlam : 0 ≤ beta 1 (largestPrime m : ℝ) := (beta_pos (by linarith) (by norm_num)).le
  choose Lo Hi hLo hHi hlo hhi using
    (fun k : Fin 5 => hpool k m hm mu hmu hrecord ((htT k).trans hlarge))
  refine ⟨hQ8, Lo, Hi, ?_⟩
  intro k
  have liftEstimate (p : ℕ) (hp : ModeEstimate (a k) (largestPrime m) k p) :
      ModeEstimate A (largestPrime m) k p := by
    have he : 0 ≤ (largestPrime m : ℝ) ^ (-priceExponent (modeIndex k)) := by positivity
    exact ⟨hp.1.trans (mul_le_mul_of_nonneg_right (haA k) he),
      hp.2.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (haA k) hlam) hL) he)⟩
  exact ⟨hLo k, hHi k,
    fun p hp => ⟨(hlo k p hp).1, liftEstimate p (hlo k p hp).2⟩,
    fun p hp => ⟨(hhi k p hp).1, liftEstimate p (hhi k p hp).2⟩⟩

private theorem uniform_selection_capacity (B : ℝ) :
    ∀ᶠ R : ℝ in atTop, ∀ k : Fin 5, ∀ z : ℤ,
      |(z : ℝ)| ≤ B * log R →
        modeIndex k * z.natAbs ≤ comparisonCount (countIndex k) R := by
  have hone (k : Fin 5) : ∀ᶠ R : ℝ in atTop,
      (modeIndex k : ℝ) * B * log R ≤ R ^ priceExponent (countIndex k) := by
    have hgamma : 0 < priceExponent (countIndex k) := by
      have hj := (mode_index_bounds k).2.2.1
      have hj0 : (0 : ℝ) < countIndex k := by
        exact_mod_cast (show 0 < countIndex k by omega)
      dsimp [priceExponent]; positivity
    have hlim : Tendsto (fun R : ℝ => log R / R ^ priceExponent (countIndex k))
        atTop (𝓝 0) := by
      simpa only [rpow_one] using
        (_root_.isLittleO_log_rpow_rpow_atTop 1 hgamma).tendsto_div_nhds_zero
    have hh := hlim.const_mul ((modeIndex k : ℝ) * B)
    simp only [mul_zero] at hh
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      hh.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
      with R hR hbound
    have hp : 0 < R ^ priceExponent (countIndex k) := rpow_pos_of_pos (by linarith) _
    have he : (modeIndex k : ℝ) * B * (log R / R ^ priceExponent (countIndex k)) =
        ((modeIndex k : ℝ) * B * log R) / R ^ priceExponent (countIndex k) := by ring
    rw [he] at hbound
    exact ((div_lt_one hp).mp hbound).le
  filter_upwards [Filter.eventually_all.mpr hone] with R hR k z hz
  have habs : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hcard : ((modeIndex k * z.natAbs : ℕ) : ℝ) ≤
      (comparisonCount (countIndex k) R : ℝ) := by
    calc
      _ = (modeIndex k : ℝ) * |(z : ℝ)| := by rw [Nat.cast_mul, habs]
      _ ≤ (modeIndex k : ℝ) * B * log R := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg _)
      _ ≤ R ^ priceExponent (countIndex k) := hR k
      _ ≤ _ := Nat.le_ceil _
  exact_mod_cast hcard

private theorem mode_atoms_separate {m : ℕ} {R : ℝ} (hR : R = largestPrime m)
    (hRpos : 0 < R) (hQ8 : (layerPrime m 2 : ℝ) ≤ R / 8)
    {k l : Fin 5} (hkl : k ≠ l) {up vp : Bool} {p : ℕ}
    (hp : ModeAtom m k up p) (hq : ModeAtom m l vp p) : False := by
  obtain ⟨_, _, hvk, hk0, hk1⟩ := hp
  obtain ⟨_, _, hvl, hl0, hl1⟩ := hq
  have hscale : 3 * (layerPrime m 2 : ℝ) / 2 < (largestPrime m : ℝ) / 2 := by
    rw [← hR]; linarith
  generalize hval : m.factorization p = a at hvk hvl
  fin_cases k <;> fin_cases l <;> cases up <;> cases vp
  all_goals try exact (hkl rfl).elim
  all_goals norm_num [modeIndex] at hvk hvl
  all_goals first
    | omega
    | (norm_num at hk0 hk1 hl0 hl1 <;> linarith)

private theorem finite_sum_point_error (S : Finset ℕ) (f : ℕ → ℝ)
    (a E : ℝ) (h : ∀ p ∈ S, |f p - a| ≤ E) :
    |(∑ p ∈ S, f p) - (S.card : ℝ) * a| ≤ (S.card : ℝ) * E := by
  calc
    _ = |∑ p ∈ S, (f p - a)| := by
      congr 1
      simp only [sum_sub_distrib, sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ S, |f p - a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ S, E := sum_le_sum h
    _ = _ := by simp

private def positiveModes (v : Fin 5 → ℤ) : Finset (Fin 5) :=
  univ.filter (fun k => 0 ≤ v k)
private def negativeModes (v : Fin 5 → ℤ) : Finset (Fin 5) :=
  univ.filter (fun k => v k < 0)

/- G2–G4 are one finite construction. Each chosen S_k has exactly j_k*|v_k|
DISTINCT original primes. Both signed unions, every log error, and every
insertion/deletion fee are summed before taking the common exponent. -/
private theorem finite_five_mode_selection {m : ℕ} (hm : 2 ≤ m)
    {R A B : ℝ} (hRdef : R = largestPrime m) (hR : 4 ≤ R)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hQ8 : (layerPrime m 2 : ℝ) ≤ R / 8)
    (Lo Hi : Fin 5 → Finset ℕ)
    (hpools : ∀ k : Fin 5,
      (Lo k).card = comparisonCount (countIndex k) R ∧
      (Hi k).card = comparisonCount (countIndex k) R ∧
      (∀ p ∈ Lo k, ModeAtom m k false p ∧ ModeEstimate A R k p) ∧
      (∀ p ∈ Hi k, ModeAtom m k true p ∧ ModeEstimate A R k p))
    (v : Fin 5 → ℤ) (hv : ∀ k, |(v k : ℝ)| ≤ B * log R)
    (hcap : ∀ k, modeIndex k * (v k).natAbs ≤ comparisonCount (countIndex k) R) :
    ∃ D U : Finset ℕ, Disjoint D U ∧
      (∀ p ∈ D, p.Prime ∧ 2 < p ∧ p ∣ m) ∧
      (∀ p ∈ U, p.Prime ∧ 2 < p) ∧
      |(logMass U - logMass D) - ∑ k : Fin 5, (v k : ℝ) * rootMasses R k| ≤
        (80 * A * B) * log R * R ^ (-(19 / 640 : ℝ)) ∧
      |auxiliaryGain (beta 1 R) m D U| ≤
        (80 * A * B) * beta 1 R * log R ^ 2 * R ^ (-(19 / 640 : ℝ)) := by
  classical
  have choose_mode (k : Fin 5) : ∃ S : Finset ℕ,
      S.card = modeIndex k * (v k).natAbs ∧
      ∀ p ∈ S, ModeAtom m k (decide (0 ≤ v k)) p ∧ ModeEstimate A R k p := by
    by_cases hk : 0 ≤ v k
    · obtain ⟨S, hS, hc⟩ := exists_subset_card_eq ((hcap k).trans_eq (hpools k).2.1.symm)
      exact ⟨S, hc, fun p hp => by simpa [hk] using (hpools k).2.2.2 p (hS hp)⟩
    · obtain ⟨S, hS, hc⟩ := exists_subset_card_eq ((hcap k).trans_eq (hpools k).1.symm)
      exact ⟨S, hc, fun p hp => by simpa [hk] using (hpools k).2.2.1 p (hS hp)⟩
  choose S hSc hS using choose_mode
  have hpair : Pairwise (fun k l : Fin 5 => Disjoint (S k) (S l)) := by
    intro k l hkl
    exact disjoint_left.mpr (fun p hp hq =>
      mode_atoms_separate hRdef (by linarith) hQ8 hkl (hS k p hp).1 (hS l p hq).1)
  let D := (negativeModes v).biUnion S
  let U := (positiveModes v).biUnion S
  have hDmem {p : ℕ} : p ∈ D ↔ ∃ k, v k < 0 ∧ p ∈ S k := by
    simp [D, negativeModes]
  have hUmem {p : ℕ} : p ∈ U ↔ ∃ k, 0 ≤ v k ∧ p ∈ S k := by
    simp [U, positiveModes]
  have hDU : Disjoint D U := disjoint_left.mpr (by
    intro p hp hq
    obtain ⟨k, hk, hpk⟩ := hDmem.mp hp
    obtain ⟨l, hl, hpl⟩ := hUmem.mp hq
    by_cases hkl : k = l
    · subst l; omega
    · exact disjoint_left.mp (hpair hkl) hpk hpl)
  have hDlegal : ∀ p ∈ D, p.Prime ∧ 2 < p ∧ p ∣ m := by
    intro p hp
    obtain ⟨k, hk, hpk⟩ := hDmem.mp hp
    have ha := (hS k p hpk).1
    have hvp : m.factorization p = modeIndex k := by
      simpa [ModeAtom, show ¬0 ≤ v k by omega] using ha.2.2.1
    refine ⟨ha.1, ha.2.1, ?_⟩
    exact (ha.1.dvd_iff_one_le_factorization (by omega : m ≠ 0)).mpr
      (by rw [hvp]; exact (mode_index_bounds k).1)
  have hUlegal : ∀ p ∈ U, p.Prime ∧ 2 < p := by
    intro p hp
    obtain ⟨k, hk, hpk⟩ := hUmem.mp hp
    exact ⟨(hS k p hpk).1.1, (hS k p hpk).1.2.1⟩
  have hsumUnion (I : Finset (Fin 5)) (f : ℕ → ℝ) :
      (∑ p ∈ I.biUnion S, f p) = ∑ k ∈ I, ∑ p ∈ S k, f p := by
    exact sum_biUnion (fun k _ l _ hkl => hpair hkl)
  have habs (k : Fin 5) : (((v k).natAbs : ℕ) : ℝ) = |(v k : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hcard (k : Fin 5) : ((S k).card : ℝ) = (modeIndex k : ℝ) * |(v k : ℝ)| := by
    rw [hSc, Nat.cast_mul, habs]
  have hR0 : 0 < R := by linarith
  have hL : 0 ≤ log R := log_nonneg (by linarith)
  have hlam : 0 ≤ beta 1 R := (beta_pos (by linarith) (by norm_num)).le
  have ht : 0 ≤ R ^ (-(19 / 640 : ℝ)) := by positivity
  have htexp (k : Fin 5) :
      R ^ (-priceExponent (modeIndex k)) ≤ R ^ (-(19 / 640 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith)
      (neg_le_neg (mode_index_bounds k).2.2.2)
  have hcardBound (k : Fin 5) : ((S k).card : ℝ) ≤ 16 * B * log R := by
    rw [hcard]
    calc
      _ ≤ (modeIndex k : ℝ) * (B * log R) :=
        mul_le_mul_of_nonneg_left (hv k) (Nat.cast_nonneg _)
      _ ≤ 16 * B * log R := by
        have hj : (modeIndex k : ℝ) ≤ 16 := by exact_mod_cast (mode_index_bounds k).2.1
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right hj (mul_nonneg hB hL)
  let signedMass : Fin 5 → ℝ := fun k => if 0 ≤ v k then logMass (S k) else -logMass (S k)
  let signedFee : Fin 5 → ℝ := fun k =>
    if 0 ≤ v k then
      ∑ p ∈ S k, (goldenLayerMarginal p (m.factorization p + 1) - beta 1 R) * log (p : ℝ)
    else -(∑ p ∈ S k, (goldenLayerMarginal p (m.factorization p) - beta 1 R) * log (p : ℝ))
  have hmassId : logMass U - logMass D = ∑ k : Fin 5, signedMass k := by
    dsimp [logMass, D, U]
    rw [hsumUnion, hsumUnion]
    simp only [positiveModes, negativeModes, sum_filter, signedMass, logMass]
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    split_ifs <;> first | omega | ring
  have hfeeId : auxiliaryGain (beta 1 R) m D U = ∑ k : Fin 5, signedFee k := by
    dsimp [auxiliaryGain, D, U]
    rw [hsumUnion, hsumUnion]
    simp only [positiveModes, negativeModes, sum_filter, signedFee]
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    split_ifs <;> first | omega | ring
  have hmassOne (k : Fin 5) :
      |signedMass k - (v k : ℝ) * rootMasses R k| ≤
        (16 * A * B) * log R * R ^ (-(19 / 640 : ℝ)) := by
    have hpoint := finite_sum_point_error (S k) (fun p => log (p : ℝ))
      (rootLog R k) (A * R ^ (-priceExponent (modeIndex k)))
      (fun p hp => (hS k p hp).2.1)
    have hj0 : (modeIndex k : ℝ) ≠ 0 := by
      have := (mode_index_bounds k).1; exact_mod_cast (by omega : modeIndex k ≠ 0)
    have he : (S k).card * rootLog R k = |(v k : ℝ)| * rootMasses R k := by
      rw [hcard, root_log_mass k R]
      field_simp [hj0] <;> ring
    change |logMass (S k) - (S k).card * rootLog R k| ≤ _ at hpoint
    rw [he] at hpoint
    have hsign : |signedMass k - (v k : ℝ) * rootMasses R k| =
        |logMass (S k) - |(v k : ℝ)| * rootMasses R k| := by
      by_cases hk : 0 ≤ v k
      · have hkR : 0 ≤ (v k : ℝ) := by exact_mod_cast hk
        simp [signedMass, hk, abs_of_nonneg hkR]
      · have hkR : (v k : ℝ) < 0 := by exact_mod_cast (show v k < 0 by omega)
        dsimp only [signedMass]
        rw [if_neg hk, abs_of_neg hkR]
        convert abs_neg (logMass (S k) + (v k : ℝ) * rootMasses R k) using 1 <;> congr 1 <;> ring
    rw [hsign]
    exact hpoint.trans (by
      calc
        _ ≤ (16 * B * log R) * (A * R ^ (-(19 / 640 : ℝ))) :=
          mul_le_mul (hcardBound k) (mul_le_mul_of_nonneg_left (htexp k) hA)
            (by positivity) (by positivity)
        _ = _ := by ring)
  have hfeeOne (k : Fin 5) : |signedFee k| ≤
      (16 * A * B) * beta 1 R * log R ^ 2 * R ^ (-(19 / 640 : ℝ)) := by
    let f : ℕ → ℝ := fun p => (goldenLayerMarginal p (modeIndex k) - beta 1 R) * log (p : ℝ)
    have hpoint : |∑ p ∈ S k, f p| ≤ (S k).card *
        (A * beta 1 R * log R * R ^ (-priceExponent (modeIndex k))) := by
      simpa only [sub_zero, mul_zero] using
        finite_sum_point_error (S k) f 0
          (A * beta 1 R * log R * R ^ (-priceExponent (modeIndex k)))
          (fun p hp => by simpa [f] using (hS k p hp).2.2)
    have he : |signedFee k| = |∑ p ∈ S k, f p| := by
      by_cases hk : 0 ≤ v k
      · dsimp [signedFee]; rw [if_pos hk]
        congr 1
        apply sum_congr rfl
        intro p hp
        have hvp : m.factorization p + 1 = modeIndex k := by
          simpa [hk] using (hS k p hp).1.2.2.1
        rw [hvp]
      · dsimp [signedFee]; rw [if_neg hk, abs_neg]
        congr 1
        apply sum_congr rfl
        intro p hp
        have hvp : m.factorization p = modeIndex k := by
          simpa [hk] using (hS k p hp).1.2.2.1
        rw [hvp]
    rw [he]
    exact hpoint.trans (by
      calc
        _ ≤ (16 * B * log R) *
            (A * beta 1 R * log R * R ^ (-(19 / 640 : ℝ))) := by
          apply mul_le_mul (hcardBound k)
          · exact mul_le_mul_of_nonneg_left (htexp k) (by positivity)
          · positivity
          · positivity
        _ = _ := by ring)
  refine ⟨D, U, hDU, hDlegal, hUlegal, ?_, ?_⟩
  · rw [hmassId, ← sum_sub_distrib]
    calc
      _ ≤ ∑ k : Fin 5, |signedMass k - (v k : ℝ) * rootMasses R k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin 5, (16 * A * B) * log R * R ^ (-(19 / 640 : ℝ)) :=
        sum_le_sum (fun k _ => hmassOne k)
      _ = _ := by simp; ring
  · rw [hfeeId]
    calc
      _ ≤ ∑ k : Fin 5, |signedFee k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin 5, (16 * A * B) * beta 1 R * log R ^ 2 * R ^ (-(19 / 640 : ℝ)) :=
        sum_le_sum (fun k _ => hfeeOne k)
      _ = _ := by simp; ring

private theorem clock_rescaling {L M : ℝ} (hL : 0 < L) (hM : 0 < M)
    (hlo : L / 2 ≤ M) (hhi : M ≤ 2 * L) :
    1 / L ^ 4 ≤ 16 * M ^ (-(4 : ℝ)) ∧ L ^ 2 ≤ 4 * M ^ 2 := by
  have hfour : M ^ 4 ≤ 16 * L ^ 4 := by
    have hh := pow_le_pow_left₀ hM.le hhi 4
    norm_num [mul_pow] at hh
    exact hh
  have htwo : L ^ 2 ≤ (2 * M) ^ 2 :=
    pow_le_pow_left₀ hL.le (by linarith) 2
  have hneg : M ^ (-(4 : ℝ)) = 1 / M ^ 4 := by
    rw [Real.rpow_neg hM.le]
    norm_num
  refine ⟨?_, by nlinarith only [htwo]⟩
  rw [hneg, show (16 : ℝ) * (1 / M ^ 4) = 16 / M ^ 4 by ring]
  apply (div_le_div_iff₀ (pow_pos hL 4) (pow_pos hM 4)).mpr
  nlinarith only [hfour]

/-- Uniform actual test-predecessor slack under two independent BHP hypotheses.
The slack is for this predecessor; prescribed bank payment and RH remain open. -/
theorem bhp_actual_five_mode_small_slack :
    BHPMaximumGap → BHPShortIntervalCount →
      ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
        ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
          T ≤ (largestPrime m : ℝ) →
          let lambda := beta 1 (largestPrime m : ℝ)
          let Dtop := lambda * Real.log 2 -
            goldenLayerMarginal 2 (m.factorization 2) * Real.log 2
          ∃ n : ℕ, 0 < n ∧ n < m ∧
            let eta := Real.log (m : ℝ) - Real.log (n : ℝ)
            0 < eta ∧
            eta ≤ C * Real.log (Real.log (m : ℝ)) ^ (-(4 : ℝ)) ∧
            |(goldenResourceObjective lambda n - goldenResourceObjective lambda m) - Dtop| ≤
              C * lambda * Real.log (Real.log (m : ℝ)) ^ 2 *
                (largestPrime m : ℝ) ^ (-(19 / 640 : ℝ)) ∧
            Dtop ≤ (lambda - mu) * eta +
              C * lambda * Real.log (Real.log (m : ℝ)) ^ 2 *
                (largestPrime m : ℝ) ^ (-(19 / 640 : ℝ)) := by
  classical
  intro hgap hcount
  obtain ⟨A, Ti, hA, hTi, hi⟩ := uniform_five_mode_pools hgap hcount
  obtain ⟨B, Tv, hB, hTv, hv⟩ := actual_root_greedy_stencil
  obtain ⟨Tc, hTc, hc⟩ := uniform_actual_clock
  let K : ℝ := 80 * A * B
  have hK : 0 < K := by dsimp [K]; positivity
  have hgood : ∀ᶠ R : ℝ in atTop,
      4 ≤ R ∧
      (∀ k : Fin 5, ∀ z : ℤ, |(z : ℝ)| ≤ B * log R →
        modeIndex k * z.natAbs ≤ comparisonCount (countIndex k) R) ∧
      0 < mesh4 R ∧ K * log R * R ^ (-(19 / 640 : ℝ)) ≤ mesh4 R / 2 := by
    filter_upwards [eventually_ge_atTop (4 : ℝ), uniform_selection_capacity B,
      eventual_mass_error_absorption K hK.le] with R hR hcap habs
    exact ⟨hR, hcap, habs⟩
  obtain ⟨Ts, hTs⟩ := eventually_atTop.mp hgood
  let C : ℝ := 1 + 64 * B + 4 * K
  let T := max Ti (max Tv (max Tc Ts))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, T, hC, lt_of_lt_of_le hTi (le_max_left _ _), ?_⟩
  intro m hm mu hmu hrecord hlarge
  dsimp only
  let R : ℝ := largestPrime m
  let lambda := beta 1 R
  let M := log (log (m : ℝ))
  have hTiR : Ti ≤ R := (le_max_left Ti _).trans hlarge
  have hTvR : Tv ≤ R := (le_max_left Tv _).trans ((le_max_right Ti _).trans hlarge)
  have hTcR : Tc ≤ R := (le_max_left Tc Ts).trans
    ((le_max_right Tv _).trans ((le_max_right Ti _).trans hlarge))
  have hTsR : Ts ≤ R := (le_max_right Tc Ts).trans
    ((le_max_right Tv _).trans ((le_max_right Ti _).trans hlarge))
  obtain ⟨hR4, hcapacity, hmesh, habsorb⟩ := hTs R hTsR
  obtain ⟨hL1, hM, hclockLo, hclockHi⟩ := hc m hm mu hmu hrecord hTcR
  have hL : 0 < log R := by linarith
  have hlam : 0 < lambda := beta_pos (by linarith) (by norm_num)
  have ht : 0 ≤ R ^ (-(19 / 640 : ℝ)) := by positivity
  obtain ⟨hQ8, Lo, Hi, hpools⟩ := hi m hm mu hmu hrecord hTiR
  obtain ⟨v, _hsum, hvbound, _hmesh, hmeshUpper, hidealLo, hidealHi⟩ := hv R hTvR
  have hcap (k : Fin 5) : modeIndex k * (v k).natAbs ≤ comparisonCount (countIndex k) R :=
    hcapacity k (v k) (hvbound k)
  obtain ⟨D, U, hDU, hD, hU, hmassError, hfee⟩ :=
    finite_five_mode_selection hm (show R = largestPrime m from rfl) hR4 hA.le hB.le
      hQ8 Lo Hi hpools v hvbound hcap
  let eta0 := log 2 + logMass D - logMass U
  have heta0 : 0 < eta0 := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hmassError
    dsimp [eta0, K] at *
    linarith only [hidealLo, hhi, habsorb, hmesh]
  have heta4 : eta0 ≤ 4 * mesh4 R := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hmassError
    dsimp [eta0, K] at *
    linarith only [hidealHi, hlo, habsorb, hmesh]
  obtain ⟨n, hnpos, hnm, heta, _htop, hgain, hrecordGain⟩ :=
    actual_finite_predecessor hm hmu hrecord (lambda := lambda) D U hD hU hDU heta0
  have hetaPos : 0 < log (m : ℝ) - log (n : ℝ) := by rwa [heta]
  obtain ⟨hinv, hsq⟩ := clock_rescaling hL hM hclockLo hclockHi
  have h64 : 64 * B ≤ C := by dsimp [C]; linarith
  have h4K : 4 * K ≤ C := by dsimp [C]; linarith
  have hgainBound : |auxiliaryGain lambda m D U| ≤ C * lambda * M ^ 2 *
      R ^ (-(19 / 640 : ℝ)) := by
    calc
      _ ≤ K * lambda * log R ^ 2 * R ^ (-(19 / 640 : ℝ)) := hfee
      _ ≤ K * lambda * (4 * M ^ 2) * R ^ (-(19 / 640 : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq (mul_nonneg hK.le hlam.le)) ht
      _ = (4 * K) * lambda * M ^ 2 * R ^ (-(19 / 640 : ℝ)) := by ring
      _ ≤ C * lambda * M ^ 2 * R ^ (-(19 / 640 : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h4K hlam.le) (sq_nonneg M)) ht
  refine ⟨n, hnpos, hnm, hetaPos, ?_, ?_, ?_⟩
  · calc
      _ = eta0 := heta
      _ ≤ 4 * mesh4 R := heta4
      _ ≤ 4 * (B / log R ^ 4) := mul_le_mul_of_nonneg_left hmeshUpper (by norm_num)
      _ = (4 * B) * (1 / log R ^ 4) := by ring
      _ ≤ (4 * B) * (16 * M ^ (-(4 : ℝ))) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (64 * B) * M ^ (-(4 : ℝ)) := by ring
      _ ≤ C * M ^ (-(4 : ℝ)) :=
        mul_le_mul_of_nonneg_right h64 (by positivity)
  · change |(goldenResourceObjective lambda n - goldenResourceObjective lambda m) -
        topGain lambda m| ≤ _
    rw [hgain, add_sub_cancel_left]
    exact hgainBound
  · change topGain lambda m ≤ (lambda - mu) * (log (m : ℝ) - log (n : ℝ)) + _
    have hneg : -auxiliaryGain lambda m D U ≤ |auxiliaryGain lambda m D U| :=
      neg_le_abs _
    exact hrecordGain.le.trans (by linarith only [hneg, hgainBound])

end D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack
