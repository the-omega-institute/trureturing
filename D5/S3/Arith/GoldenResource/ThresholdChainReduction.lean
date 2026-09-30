/- GID: D5/S3/Arith/GoldenResource/ThresholdChainReduction
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/ThresholdChainReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The ordered layer chain attains the minimum Robin margin in an exponent box. -/

import D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
import D5.S3.Weil.GronwallLowerEnvelope
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

namespace D5.S3.Arith.GoldenResource.ThresholdChainReduction

open Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open D5.S3.Weil.GronwallLowerEnvelope

noncomputable section

/-- The independent added prime layers between the lower and upper exponents. -/
def exponentLayers (B U : ℕ) : Finset (ℕ × ℕ) :=
  U.primeFactors.biUnion fun p =>
    (Ioc (B.factorization p) (U.factorization p)).image fun k => (p, k)

/-- The finite exponent box expressed by its divisibility endpoints. -/
def exponentBox (B U : ℕ) : Finset ℕ := U.divisors.filter (B ∣ ·)

/-- Multiply the lower endpoint by the primes of the first `j` added layers. -/
def layerChain (B U : ℕ)
    (e : Fin (exponentLayers B U).card ≃ {pk // pk ∈ exponentLayers B U})
    (j : ℕ) : ℕ :=
  B * ∏ i ∈ univ.filter (fun i : Fin (exponentLayers B U).card => i.val < j),
    (e i).val.1

/-- Exact chain minimization, including both cardinalities and legality of the prefixes. -/
theorem threshold_chain_reduction {B U : ℕ} (hB : 3 ≤ B) (hU : U ≠ 0)
    (hBU : B ∣ U)
    (e : Fin (exponentLayers B U).card ≃ {pk // pk ∈ exponentLayers B U})
    (horder : Antitone (fun i => goldenLayerMarginal (e i).val.1 (e i).val.2)) :
    (exponentLayers B U).card =
      (∑ p ∈ U.primeFactors, (U.factorization p - B.factorization p)) ∧
    (exponentBox B U).card =
      (∏ p ∈ U.primeFactors, (U.factorization p - B.factorization p + 1)) ∧
    (∀ j ≤ (exponentLayers B U).card, layerChain B U e j ∈ exponentBox B U) ∧
    (∀ j ≤ (exponentLayers B U).card, ∀ i : Fin (exponentLayers B U).card,
      i.val < j → ∀ k, B.factorization (e i).val.1 < k → k ≤ (e i).val.2 →
        ∃ r : Fin (exponentLayers B U).card,
          r.val < j ∧ (e r).val = ((e i).val.1, k)) ∧
    (∃ j ≤ (exponentLayers B U).card,
      IsLeast (robinLogMargin '' (↑(exponentBox B U) : Set ℕ))
        (robinLogMargin (layerChain B U e j)) ∧
      IsLeast ((fun j => robinLogMargin (layerChain B U e j)) ''
        Set.Iic (exponentLayers B U).card)
        (robinLogMargin (layerChain B U e j))) ∧
    sInf (robinLogMargin '' (↑(exponentBox B U) : Set ℕ)) =
      sInf ((fun j => robinLogMargin (layerChain B U e j)) ''
        Set.Iic (exponentLayers B U).card) := by
  classical
  have hB0 : B ≠ 0 := by omega
  have hmemBox (m : ℕ) : m ∈ exponentBox B U ↔ B ∣ m ∧ m ∣ U := by
    simp [exponentBox, Nat.mem_divisors, hU, and_comm]
  have memLayers (pk : ℕ × ℕ) : pk ∈ exponentLayers B U ↔
      pk.1 ∈ U.primeFactors ∧ B.factorization pk.1 < pk.2 ∧
        pk.2 ≤ U.factorization pk.1 := by
    rcases pk with ⟨p, k⟩
    simp [exponentLayers]
  have reconstruct : ∀ {n : ℕ}, B ∣ n → n ∣ U →
      n = B * ∏ pk ∈ (exponentLayers B U).filter
        (fun pk => pk.2 ≤ n.factorization pk.1), pk.1 := by
    intro n hBn hnU
    classical
    have hn : n ≠ 0 := ne_zero_of_dvd_ne_zero hU hnU
    have hq : n / B ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hBn)
      (Nat.pos_of_ne_zero hB0)).ne'
    have hle := (Nat.factorization_le_iff_dvd hn hU).mpr hnU
    have hprimeSubset : (n / B).primeFactors ⊆ U.primeFactors :=
      Nat.primeFactors_mono ((Nat.div_dvd_of_dvd hBn).trans hnU) hU
    have hfiltered : (exponentLayers B U).filter (fun pk => pk.2 ≤ n.factorization pk.1) =
        U.primeFactors.biUnion (fun p =>
          (Ioc (B.factorization p) (n.factorization p)).image fun k => (p, k)) := by
      ext pk
      simp only [mem_filter, exponentLayers, mem_biUnion, mem_image, mem_Ioc]
      constructor
      · rintro ⟨⟨p, hp, k, hk, hpk⟩, hkn⟩
        cases hpk
        exact ⟨p, hp, k, ⟨hk.1, hkn⟩, rfl⟩
      · rintro ⟨p, hp, k, hk, hpk⟩
        cases hpk
        exact ⟨⟨p, hp, k, ⟨hk.1, hk.2.trans (hle p)⟩, rfl⟩, hk.2⟩
    have hdisj : (↑U.primeFactors : Set ℕ).PairwiseDisjoint (fun p =>
        (Ioc (B.factorization p) (n.factorization p)).image fun k => (p, k)) := by
      intro p hp q hq hpq
      apply disjoint_left.mpr
      intro pk hpk hqk
      obtain ⟨k, _, hk⟩ := mem_image.mp hpk
      obtain ⟨r, _, hr⟩ := mem_image.mp hqk
      exact hpq (congrArg Prod.fst (hk.trans hr.symm))
    rw [hfiltered, prod_biUnion hdisj]
    simp only [prod_image (fun _ _ _ _ h => Prod.mk.inj h |>.2), prod_const, Nat.card_Ioc]
    have heq : (∏ p ∈ U.primeFactors, p ^ (n.factorization p - B.factorization p)) = n / B := by
      rw [Nat.prod_primeFactors_pow_factorization hq]
      have hfactor := Nat.factorization_div hBn
      simp only [DFunLike.ext_iff, Finsupp.coe_tsub, Pi.sub_apply] at hfactor
      calc
        (∏ p ∈ U.primeFactors, p ^ (n.factorization p - B.factorization p)) =
            ∏ p ∈ U.primeFactors, p ^ (n / B).factorization p := by
          apply prod_congr rfl
          intro p hp
          rw [hfactor p]
        _ = ∏ p ∈ (n / B).primeFactors, p ^ (n / B).factorization p := by
          apply (prod_subset hprimeSubset ?_).symm
          intro p hp hpn
          have hz : (n / B).factorization p = 0 := by
            simpa [← Nat.support_factorization, Finsupp.mem_support_iff] using hpn
          simp [hz]
    rw [heq, Nat.mul_div_cancel' hBn]
  have layerCard : (exponentLayers B U).card =
      ∑ p ∈ U.primeFactors, (U.factorization p - B.factorization p) := by
    classical
    unfold exponentLayers
    rw [card_biUnion]
    · apply sum_congr rfl
      intro p hp
      rw [card_image_of_injective _ (fun _ _ h => Prod.mk.inj h |>.2), Nat.card_Ioc]
    · intro p hp q hq hpq
      apply disjoint_left.mpr
      intro pk hpk hqk
      obtain ⟨k, _, hk⟩ := mem_image.mp hpk
      obtain ⟨r, _, hr⟩ := mem_image.mp hqk
      exact hpq (congrArg Prod.fst (hk.trans hr.symm))
  have boxCard : (exponentBox B U).card =
      ∏ p ∈ U.primeFactors, (U.factorization p - B.factorization p + 1) := by
    classical
    have hq : U / B ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hU) hBU)
      (Nat.pos_of_ne_zero hB0)).ne'
    have hbox : exponentBox B U = (U / B).divisors.image (B * ·) := by
      ext n
      simp only [exponentBox, mem_filter, Nat.mem_divisors, mem_image]
      constructor
      · rintro ⟨⟨hnU, _⟩, hBn⟩
        refine ⟨n / B, ⟨?_, hq⟩, Nat.mul_div_cancel' hBn⟩
        apply (Nat.dvd_div_iff_mul_dvd hBU).mpr
        simpa [Nat.mul_div_cancel' hBn] using hnU
      · rintro ⟨k, ⟨hk, _⟩, rfl⟩
        refine ⟨⟨?_, hU⟩, dvd_mul_right B k⟩
        have := mul_dvd_mul_left B hk
        simpa [Nat.mul_div_cancel' hBU] using this
    rw [hbox, card_image_of_injective _ (fun x y h => mul_left_cancel₀ hB0 h),
      Nat.card_divisors hq]
    have hsub : (U / B).primeFactors ⊆ U.primeFactors :=
      Nat.primeFactors_mono (Nat.div_dvd_of_dvd hBU) hU
    calc
      (∏ p ∈ (U / B).primeFactors, ((U / B).factorization p + 1)) =
          ∏ p ∈ U.primeFactors, ((U / B).factorization p + 1) := by
        apply prod_subset hsub
        intro p hp hpq
        have hz : (U / B).factorization p = 0 := by
          simpa [← Nat.support_factorization, Finsupp.mem_support_iff] using hpq
        simp [hz]
      _ = ∏ p ∈ U.primeFactors, (U.factorization p - B.factorization p + 1) := by
        simp only [Nat.factorization_div hBU, Finsupp.coe_tsub, Pi.sub_apply]
  have threshold : ∃ n ∈ exponentBox B U, ∃ lambda : ℝ, 0 < lambda ∧
      (∀ m ∈ exponentBox B U, robinLogMargin n ≤ robinLogMargin m) ∧
      ∀ pk ∈ exponentLayers B U,
        (pk.2 ≤ n.factorization pk.1 ↔ lambda < goldenLayerMarginal pk.1 pk.2) := by
    classical
    have hB0 : B ≠ 0 := by omega
    have hmemBox (m : ℕ) : m ∈ exponentBox B U ↔ B ∣ m ∧ m ∣ U := by
      simp only [exponentBox, mem_filter, Nat.mem_divisors, and_comm]
      simp [hU]
    have hboxNe : (exponentBox B U).Nonempty := ⟨B, (hmemBox B).mpr ⟨dvd_rfl, hBU⟩⟩
    obtain ⟨n, hn, hmin⟩ := (exponentBox B U).exists_min_image robinLogMargin hboxNe
    obtain ⟨hBn, hnU⟩ := (hmemBox n).mp hn
    have hn0 : n ≠ 0 := ne_zero_of_dvd_ne_zero hU hnU
    have hn3 : 3 ≤ n := hB.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hBn)
    have logGt (m : ℕ) (hm : 3 ≤ m) : 1 < Real.log m := by
      apply (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < m)).mpr
      exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hm)
    let lambda : ℝ := 1 / (Real.log n * Real.log (Real.log n))
    have hlambda : 0 < lambda := div_pos zero_lt_one
      (mul_pos (lt_trans zero_lt_one (logGt n hn3)) (Real.log_pos (logGt n hn3)))
    have tangent : ∀ {x y : ℝ}, 1 < x → 1 < y → x ≠ y →
        Real.log (Real.log y) < Real.log (Real.log x) +
          (1 / (x * Real.log x)) * (y - x) := by
      intro x y hx hy hne
      have himage : Real.log '' Set.Ioi (1 : ℝ) ⊆ Set.Ioi 0 := by
        rintro _ ⟨z, hz, rfl⟩
        exact Real.log_pos hz
      have hinner : StrictConcaveOn ℝ (Set.Ioi (1 : ℝ)) Real.log :=
        StrictConcaveOn.subset strictConcaveOn_log_Ioi
          (by intro z hz; change 1 < z at hz; change 0 < z; linarith)
          (convex_Ioi (1 : ℝ))
      have houter : StrictConcaveOn ℝ (Real.log '' Set.Ioi (1 : ℝ)) Real.log := by
        simpa only [Real.image_log_Ioi zero_lt_one, Real.log_one] using
          strictConcaveOn_log_Ioi
      have hmono : StrictMonoOn Real.log (Real.log '' Set.Ioi (1 : ℝ)) :=
        Real.strictMonoOn_log.mono himage
      have hsc : StrictConcaveOn ℝ (Set.Ioi (1 : ℝ)) (fun z => Real.log (Real.log z)) :=
        houter.comp hinner hmono (Real.strictMonoOn_log.mono
          (by intro z hz; change 1 < z at hz; change 0 < z; linarith)).injOn
      have hd : HasDerivAt (fun z => Real.log (Real.log z))
          (1 / (x * Real.log x)) x := by
        convert (Real.hasDerivAt_log (ne_of_gt (lt_trans zero_lt_one hx))).log
          (Real.log_pos hx).ne' using 1
        field_simp
      rcases lt_or_gt_of_ne hne with hxy | hyx
      · have ht := hsc.slope_lt_of_hasDerivAt hx hy hxy hd
        rw [slope_def_field] at ht
        have := (div_lt_iff₀ (sub_pos.mpr hxy)).mp ht
        linarith
      · have ht := hsc.lt_slope_of_hasDerivAt hy hx hyx hd
        rw [slope_def_field] at ht
        have := (lt_div_iff₀ (sub_pos.mpr hyx)).mp ht
        nlinarith
    have margin (m : ℕ) (hm : 1 ≤ m) : robinLogMargin m =
        Real.eulerMascheroniConstant + Real.log (Real.log (Real.log m)) -
          goldenResourceObjective 0 m := by
      simp only [robinLogMargin, golden_resource_sigma_identity 0 hm, zero_mul, sub_zero]
    have upper (p : ℕ) (hp : p.Prime) (hup : n.factorization p < U.factorization p) :
        goldenLayerMarginal p (n.factorization p + 1) < lambda := by
      have hnp0 : n * p ≠ 0 := mul_ne_zero hn0 hp.ne_zero
      have hnpU : n * p ∣ U := by
        apply (Nat.factorization_le_iff_dvd hnp0 hU).mp
        intro q
        by_cases hqp : q = p
        · subst q
          simpa [Nat.factorization_mul hn0 hp.ne_zero, hp.factorization] using hup
        · simpa [Nat.factorization_mul hn0 hp.ne_zero, hp.factorization, Ne.symm hqp] using
            (Nat.factorization_le_iff_dvd hn0 hU).mpr hnU q
      have hnp : n * p ∈ exponentBox B U := (hmemBox _).mpr
        ⟨hBn.trans (dvd_mul_right n p), hnpU⟩
      have hnp3 : 3 ≤ n * p := hn3.trans (Nat.le_mul_of_pos_right n hp.pos)
      have hpLog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
      have hlog : Real.log (n * p : ℕ) = Real.log n + Real.log p := by
        rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hn0) (by exact_mod_cast hp.ne_zero)]
      have hne : Real.log n ≠ Real.log (n * p : ℕ) := by rw [hlog]; linarith
      have ht := tangent (logGt n hn3) (logGt (n * p) hnp3) hne
      have hm := hmin (n * p) hnp
      rw [margin n (by omega), margin (n * p) (by omega)] at hm
      have hg := golden_resource_objective_single_layer_delta 0 (by omega : 1 ≤ n) hp
      simp only [sub_zero] at hg
      rw [hlog] at ht hm
      have hprod : goldenLayerMarginal p (n.factorization p + 1) * Real.log p <
          lambda * Real.log p := by dsimp [lambda] at *; nlinarith
      exact (mul_lt_mul_iff_of_pos_right hpLog).mp hprod
    have lower (p : ℕ) (hp : p.Prime) (hlo : B.factorization p < n.factorization p) :
        lambda < goldenLayerMarginal p (n.factorization p) := by
      have hpdvd : p ∣ n := Nat.dvd_of_factorization_pos (by omega)
      have hm0 : n / p ≠ 0 := (Nat.div_pos
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpdvd) hp.pos).ne'
      have hBmp : B * p ∣ n := by
        apply (Nat.factorization_le_iff_dvd (mul_ne_zero hB0 hp.ne_zero) hn0).mp
        intro q
        by_cases hqp : q = p
        · subst q
          simpa [Nat.factorization_mul hB0 hp.ne_zero, hp.factorization] using hlo
        · simpa [Nat.factorization_mul hB0 hp.ne_zero, hp.factorization, Ne.symm hqp] using
            (Nat.factorization_le_iff_dvd hB0 hn0).mpr hBn q
      have hBm : B ∣ n / p := (Nat.dvd_div_iff_mul_dvd hpdvd).mpr (by simpa [mul_comm] using hBmp)
      have hmU : n / p ∣ U := (Nat.div_dvd_of_dvd hpdvd).trans hnU
      have hm : n / p ∈ exponentBox B U := (hmemBox _).mpr ⟨hBm, hmU⟩
      have hm3 : 3 ≤ n / p := hB.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hBm)
      have hpLog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
      have hlog : Real.log n = Real.log (n / p : ℕ) + Real.log p := by
        conv_lhs => rw [← Nat.div_mul_cancel hpdvd]
        rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hm0) (by exact_mod_cast hp.ne_zero)]
      have hne : Real.log n ≠ Real.log (n / p : ℕ) := by rw [hlog]; linarith
      have ht := tangent (logGt n hn3) (logGt (n / p) hm3) hne
      have hminimum := hmin (n / p) hm
      rw [margin n (by omega), margin (n / p) (by omega)] at hminimum
      have hg := golden_resource_objective_single_layer_delta 0
        (by omega : 1 ≤ n / p) hp
      rw [Nat.div_mul_cancel hpdvd] at hg
      have hfactor : (n / p).factorization p + 1 = n.factorization p := by
        simp only [Nat.factorization_div hpdvd, Finsupp.coe_tsub, Pi.sub_apply,
          hp.factorization, Finsupp.single_eq_same]
        omega
      rw [hfactor] at hg
      simp only [sub_zero] at hg
      have hdiff : Real.log (n / p : ℕ) - Real.log n = -Real.log p := by linarith
      rw [hdiff] at ht
      have hprod : lambda * Real.log p < goldenLayerMarginal p (n.factorization p) *
          Real.log p := by dsimp [lambda] at *; nlinarith
      exact (mul_lt_mul_iff_of_pos_right hpLog).mp hprod
    refine ⟨n, hn, lambda, hlambda, hmin, ?_⟩
    intro pk hpk
    obtain ⟨p, hpU, heq⟩ := mem_biUnion.mp hpk
    obtain ⟨k, hk, rfl⟩ := mem_image.mp heq
    obtain ⟨hklo, hkup⟩ := mem_Ioc.mp hk
    have hp := Nat.prime_of_mem_primeFactors hpU
    change k ≤ n.factorization p ↔ lambda < goldenLayerMarginal p k
    constructor
    · intro hkn
      have ht := lower p hp (hklo.trans_le hkn)
      rcases eq_or_lt_of_le hkn with heq | hlt
      · simpa only [← heq] using ht
      · exact ht.trans (golden_layer_strict_decrease hp (by omega) hlt)
    · intro ht
      by_contra hkn
      have hnk : n.factorization p < k := Nat.lt_of_not_ge hkn
      have hu := upper p hp (hnk.trans_le hkup)
      have hkle : goldenLayerMarginal p k ≤ goldenLayerMarginal p (n.factorization p + 1) := by
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt hnk) with heq | hlt
        · rw [← heq]
        · exact (golden_layer_strict_decrease hp (by omega) hlt).le
      exact (not_lt_of_ge (hkle.trans hu.le)) ht
  -- The minimizing threshold cuts a whole initial segment of the exact order.
  let selectedPrefix (j : ℕ) : Finset (ℕ × ℕ) :=
    (univ.filter fun i : Fin (exponentLayers B U).card => i.val < j).image
      (fun i => (e i).val)
  have prefixSub (j : ℕ) : selectedPrefix j ⊆ exponentLayers B U := by
    intro pk hpk
    obtain ⟨i, _, rfl⟩ := mem_image.mp hpk
    exact (e i).property
  have productChain (j : ℕ) : layerChain B U e j = B * ∏ pk ∈ selectedPrefix j, pk.1 := by
    unfold layerChain selectedPrefix
    rw [prod_image]
    intro i hi r hr her
    exact e.injective (Subtype.ext her)
  have legal (j : ℕ) : layerChain B U e j ∈ exponentBox B U := by
    have hfull := reconstruct (n := U) hBU dvd_rfl
    have hfilter : (exponentLayers B U).filter (fun pk => pk.2 ≤ U.factorization pk.1) =
        exponentLayers B U := by
      apply filter_eq_self.mpr
      intro pk hpk
      exact ((memLayers pk).mp hpk).2.2
    rw [hfilter] at hfull
    rw [hmemBox, productChain]
    refine ⟨dvd_mul_right _ _, ?_⟩
    rw [hfull]
    exact mul_dvd_mul_left B (prod_dvd_prod_of_subset _ _ Prod.fst (prefixSub j))
  have closed (j : ℕ) (i : Fin (exponentLayers B U).card) (hi : i.val < j)
      (k : ℕ) (hk : B.factorization (e i).val.1 < k) (hki : k ≤ (e i).val.2) :
      ∃ r : Fin (exponentLayers B U).card,
        r.val < j ∧ (e r).val = ((e i).val.1, k) := by
    have hlayer := (memLayers _).mp (e i).property
    let pk : {pk // pk ∈ exponentLayers B U} :=
      ⟨((e i).val.1, k), (memLayers _).mpr ⟨hlayer.1, hk, hki.trans hlayer.2.2⟩⟩
    let r := e.symm pk
    have her : (e r).val = ((e i).val.1, k) := congrArg Subtype.val (e.apply_symm_apply pk)
    refine ⟨r, ?_, her⟩
    rcases eq_or_lt_of_le hki with heq | hlt
    · have hri : r = i := e.injective (Subtype.ext (by simpa [heq] using her))
      simpa [hri] using hi
    · have hmargin := golden_layer_strict_decrease
        (Nat.prime_of_mem_primeFactors hlayer.1) (by omega : 1 ≤ k) hlt
      have hri : r ≤ i := by
        by_contra hri
        have hiLe : i ≤ r := le_of_lt (lt_of_not_ge hri)
        have hbad := horder hiLe
        dsimp only at hbad
        rw [her] at hbad
        exact (not_lt_of_ge hbad) hmargin
      exact lt_of_le_of_lt hri hi
  obtain ⟨n, hn, lambda, hlambda, hmin, hthreshold⟩ := threshold
  let T : Finset (Fin (exponentLayers B U).card) :=
    univ.filter fun i => lambda < goldenLayerMarginal (e i).val.1 (e i).val.2
  let j := T.card
  have hj : j ≤ (exponentLayers B U).card := by
    simpa [j] using card_le_card (show T ⊆ univ from subset_univ T)
  have initial (i : Fin (exponentLayers B U).card) : i ∈ T ↔ i.val < j := by
    constructor
    · intro hi
      have hsub : Iic i ⊆ T := by
        intro r hr
        have hri := mem_Iic.mp hr
        apply mem_filter.mpr
        exact ⟨mem_univ _, ((mem_filter.mp hi).2).trans_le (horder hri)⟩
      have := card_le_card hsub
      rw [Fin.card_Iic] at this
      exact this
    · intro hij
      by_contra hi
      have hle : goldenLayerMarginal (e i).val.1 (e i).val.2 ≤ lambda := by
        simpa [T] using hi
      have hsub : T ⊆ Iio i := by
        intro r hr
        apply mem_Iio.mpr
        by_contra hri
        have hbad := (horder (le_of_not_gt hri)).trans hle
        exact (not_lt_of_ge hbad) (mem_filter.mp hr).2
      have hc := card_le_card hsub
      rw [Fin.card_Iio] at hc
      exact (not_lt_of_ge hc) hij
  have hprefix : selectedPrefix j = (exponentLayers B U).filter
      (fun pk => pk.2 ≤ n.factorization pk.1) := by
    ext pk
    constructor
    · intro hpk
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hpk
      refine mem_filter.mpr ⟨(e i).property, ?_⟩
      apply (hthreshold _ (e i).property).mpr
      exact (mem_filter.mp ((initial i).mpr (mem_filter.mp hi).2)).2
    · intro hpk
      let v : {pk // pk ∈ exponentLayers B U} := ⟨pk, (mem_filter.mp hpk).1⟩
      refine mem_image.mpr ⟨e.symm v, ?_, congrArg Subtype.val (e.apply_symm_apply v)⟩
      apply mem_filter.mpr
      refine ⟨mem_univ _, (initial _).mp ?_⟩
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      simpa only [e.apply_symm_apply] using
        (hthreshold _ (mem_filter.mp hpk).1).mp (mem_filter.mp hpk).2
  have hchain : layerChain B U e j = n := by
    rw [productChain, hprefix]
    exact (reconstruct ((hmemBox n).mp hn).1 ((hmemBox n).mp hn).2).symm
  have leastBox : IsLeast (robinLogMargin '' (↑(exponentBox B U) : Set ℕ))
      (robinLogMargin (layerChain B U e j)) := by
    rw [hchain]
    refine ⟨⟨n, hn, rfl⟩, ?_⟩
    rintro _ ⟨m, hm, rfl⟩
    exact hmin m hm
  have leastChain : IsLeast ((fun j => robinLogMargin (layerChain B U e j)) ''
      Set.Iic (exponentLayers B U).card) (robinLogMargin (layerChain B U e j)) := by
    refine ⟨⟨j, hj, rfl⟩, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    apply leastBox.2
    exact ⟨_, legal r, rfl⟩
  exact ⟨layerCard, boxCard, fun j _ => legal j, fun j _ => closed j,
    ⟨j, hj, leastBox, leastChain⟩, leastBox.csInf_eq.trans leastChain.csInf_eq.symm⟩

#print axioms threshold_chain_reduction

end
end D5.S3.Arith.GoldenResource.ThresholdChainReduction
