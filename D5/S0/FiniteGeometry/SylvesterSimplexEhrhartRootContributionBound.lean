/- GID: D5/S0/FiniteGeometry/SylvesterSimplexEhrhartRootContributionBound
   generality: G
   mirror-B: D5/B/S0/FiniteGeometry/SylvesterSimplexEhrhartRootContributionBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Support cutoff and normalized cardinality-four source-root contribution. -/

import D5.S0.FiniteGeometry.SylvesterSimplexEhrhartPrincipalPart

noncomputable section

namespace D5.S0.FiniteGeometry.SylvesterSimplexEhrhartRootContributionBound

open scoped BigOperators

open D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity

open private rootLocalCoordinate_pow_partitionWeight rootDenominatorFactor
  rootVanishingQuotient sourceLocalRegularDenominator sourceLocalRegularInverse
  sourceLocalRegularInverse_constantCoeff sourceVanishingFactors
  sourceExponentialLocalJet sourceLocalRootContributionPolynomial
  sourceLocalRootContributionPolynomial_target_coeff sourcePoleOrder
  sourcePoleOrder_add_support_card sourceRootSupport from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartCoefficient

open private baseWeight baseWeight_last base_axisScale_dvd_mass sylvester_pos
  sylvester_sub_one_eq_prod two_le_sylvester from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity

open private partitionWeight partitionWeight_pos partitionWeight_dvd_period from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartSamples

/-- Nontrivial source roots have the literal paper support. Contributions
whose paper support has more than four indices vanish by the degree of the
actual finite local-root polynomial, without invoking the guarded jet formula. -/
theorem sourceNontrivialRootContribution_support_cutoff
    (n : ℕ) (hn : 7 ≤ n) (ζ : ℂ)
    (hζ : ζ ∈ Polynomial.nthRootsFinset
      (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (n + 1) - 1)
      (1 : ℂ))
    (hζne : ζ ≠ 1) (c : ℤ) :
    let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (n + 1) - 1
    let R := Finset.univ.filter fun i : Fin n =>
      ζ ^ (M / D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i.1 + 1)) ≠ 1
    sourceRootSupport (n + 1) ζ =
        insert none (insert (some (Fin.last n)) (R.image fun i => some i.castSucc)) ∧
      (sourceRootSupport (n + 1) ζ).card = R.card + 2 ∧
      sourcePoleOrder (n + 1) ζ = n - R.card ∧
      ‖ζ ^ (-c)‖ = 1 ∧
      (4 < R.card →
        (sourceLocalRootContributionPolynomial (n + 1) ζ c).coeff (n + 1 - 6) = 0) := by
  classical
  dsimp only
  let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (n + 1) - 1
  let R := Finset.univ.filter fun i : Fin n =>
    ζ ^ (M / D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i.1 + 1)) ≠ 1
  have hweight (i : Fin n) :
      partitionWeight (n + 1) (some i.castSucc) =
        M / D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i.1 + 1) := by
    simp [partitionWeight, baseWeight,
      D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.axisScale, M,
      show i.1 ≠ n by omega]
  have hsupport : sourceRootSupport (n + 1) ζ =
      insert none (insert (some (Fin.last n)) (R.image fun i => some i.castSucc)) := by
    ext j
    cases j with
    | none =>
        simp only [sourceRootSupport, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [partitionWeight] using hζne
    | some j =>
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp only [sourceRootSupport, Finset.mem_filter, Finset.mem_univ, true_and]
          simpa [partitionWeight, baseWeight_last] using hζne
        · simp [sourceRootSupport, R, hweight]
  have hinjective : Function.Injective
      (fun i : Fin n => (some i.castSucc : Option (Fin (n + 1)))) := by
    intro i j hij
    simp only [Option.some.injEq, Fin.castSucc_inj] at hij
    exact hij
  have hcard : (sourceRootSupport (n + 1) ζ).card = R.card + 2 := by
    rw [hsupport]
    simp [Finset.card_image_of_injective R hinjective]
  have hpole : sourcePoleOrder (n + 1) ζ = n - R.card := by
    have hpartition := sourcePoleOrder_add_support_card (n + 1) ζ
    rw [hcard] at hpartition
    omega
  have hM : 0 < M := Nat.sub_pos_of_lt
    (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester (n + 1) (by omega)))
  have hpow : ζ ^ M = 1 :=
    (Polynomial.mem_nthRootsFinset hM (1 : ℂ)).mp hζ
  have hphase : ‖ζ ^ (-c)‖ = 1 := by
    rw [norm_zpow, Complex.norm_eq_one_of_pow_eq_one hpow hM.ne', one_zpow]
  refine ⟨hsupport, hcard, hpole, hphase, ?_⟩
  intro hlarge
  change 4 < R.card at hlarge
  rw [sourceLocalRootContributionPolynomial, Polynomial.coeff_C_mul]
  have hsum :
      (∑ m ∈ Finset.range (sourcePoleOrder (n + 1) ζ),
        Polynomial.C
            ((m.factorial : ℂ)⁻¹ *
              PowerSeries.coeff (sourcePoleOrder (n + 1) ζ - m - 1)
                (sourceExponentialLocalJet (n + 1) ζ c)) *
          Polynomial.X ^ m).coeff (n + 1 - 6) = 0 := by
    change Polynomial.lcoeff ℂ (n + 1 - 6)
        (∑ m ∈ Finset.range (sourcePoleOrder (n + 1) ζ),
          Polynomial.C
              ((m.factorial : ℂ)⁻¹ *
                PowerSeries.coeff (sourcePoleOrder (n + 1) ζ - m - 1)
                  (sourceExponentialLocalJet (n + 1) ζ c)) *
            Polynomial.X ^ m) = 0
    rw [map_sum]
    simp only [Polynomial.lcoeff_apply]
    apply Finset.sum_eq_zero
    intro m hm
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]
    intro heq
    have hmlt := Finset.mem_range.mp hm
    rw [hpole] at hmlt
    omega
  rw [hsum, mul_zero]

theorem sourceNontrivialRootContribution_card_four_exact
    (n : ℕ) (hn : 7 ≤ n) (ζ : ℂ)
    (hζ : ζ ∈ Polynomial.nthRootsFinset
      (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (n + 1) - 1)
      (1 : ℂ))
    (hζne : ζ ≠ 1) (c : ℤ)
    (hRcard : (Finset.univ.filter fun i : Fin n =>
      ζ ^ ((D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester
          (n + 1) - 1) /
        D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester
          (i.1 + 1)) ≠ 1).card = 4) :
    let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (n + 1) - 1
    let R := Finset.univ.filter fun i : Fin n =>
      ζ ^ (M / D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i.1 + 1)) ≠ 1
    let S := ∏ i ∈ R,
      D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i.1 + 1)
    let chord : Fin n → ℂ := fun i => 1 - ζ ^ (M /
      D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i.1 + 1))
    sourceRootSupport (n + 1) ζ =
      insert none (insert (some (Fin.last n)) (R.image fun i => some i.castSucc)) ∧
      (sourceRootSupport (n + 1) ζ).card = R.card + 2 ∧
      (sourceLocalRootContributionPolynomial (n + 1) ζ c).coeff (n + 1 - 6) =
        ζ ^ (-c) * ((n + 1 - 6).factorial : ℂ)⁻¹ * (S : ℂ)⁻¹ *
          ((1 - ζ) ^ 2 * ∏ i ∈ R, chord i)⁻¹ ∧
      0 < ((n + 1 - 6).factorial : ℝ) * (S : ℝ) * ‖1 - ζ‖ ^ 2 *
        ∏ i ∈ R, ‖chord i‖ ∧
      ‖(sourceLocalRootContributionPolynomial (n + 1) ζ c).coeff (n + 1 - 6)‖ ≤
        1 / (((n + 1 - 6).factorial : ℝ) * (S : ℝ) * ‖1 - ζ‖ ^ 2 *
          ∏ i ∈ R, ‖chord i‖) := by
  classical
  dsimp only
  let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (n + 1) - 1
  let R := Finset.univ.filter fun i : Fin n =>
    ζ ^ (M / D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i.1 + 1)) ≠ 1
  let S := ∏ i ∈ R,
    D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i.1 + 1)
  let chord : Fin n → ℂ := fun i => 1 - ζ ^ (M /
    D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i.1 + 1))
  rcases (show
      sourceRootSupport (n + 1) ζ =
          insert none (insert (some (Fin.last n)) (R.image fun i => some i.castSucc)) ∧
        (sourceRootSupport (n + 1) ζ).card = R.card + 2 ∧
        sourcePoleOrder (n + 1) ζ = n - R.card ∧
        ‖ζ ^ (-c)‖ = 1 ∧ _ by
      simpa [M, R] using
        sourceNontrivialRootContribution_support_cutoff n hn ζ hζ hζne c) with
    ⟨hsupport, hcard, _, hphase, _⟩
  have hweight (i : Fin n) :
      partitionWeight (n + 1) (some i.castSucc) =
        M / D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i.1 + 1) := by
    simp [partitionWeight, baseWeight,
      D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.axisScale, M,
      show i.1 ≠ n by omega]
  have hinjective : Function.Injective
      (fun i : Fin n => (some i.castSucc : Option (Fin (n + 1)))) := by
    intro i j hij
    simp only [Option.some.injEq, Fin.castSucc_inj] at hij
    exact hij
  have hsupportCard : (sourceRootSupport (n + 1) ζ).card = 6 := by
    rw [hcard, hRcard]
  have hExact :
      (sourceLocalRootContributionPolynomial (n + 1) ζ c).coeff (n + 1 - 6) =
        ζ ^ (-c) * ((n + 1 - 6).factorial : ℂ)⁻¹ * (S : ℂ)⁻¹ *
          ((1 - ζ) ^ 2 * ∏ i ∈ R, chord i)⁻¹ := by
    rw [sourceLocalRootContributionPolynomial_target_coeff (n + 1) (by omega) ζ c
      (by omega), hsupportCard]
    simp only [Nat.reduceSubDiff, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [sourceExponentialLocalJet, map_mul,
      sourceLocalRegularInverse_constantCoeff (n + 1) (by omega)]
    simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_rescale, pow_zero, one_mul, PowerSeries.coeff_exp]
    have hvanishing : sourceVanishingFactors (n + 1) ζ =
      Rᶜ.image (fun i => (some i.castSucc : Option (Fin (n + 1)))) := by
      ext j
      cases j with
      | none =>
          simp only [sourceVanishingFactors, Finset.mem_filter, Finset.mem_univ, true_and]
          simpa [partitionWeight] using hζne
      | some j =>
          refine Fin.lastCases ?_ (fun i => ?_) j
          · simp only [sourceVanishingFactors, Finset.mem_filter, Finset.mem_univ, true_and]
            simpa [partitionWeight, baseWeight_last] using hζne
          · simp [sourceVanishingFactors, R, hweight]
    have hscale (i : Fin n) :
      M / partitionWeight (n + 1) (some i.castSucc) =
        D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i.1 + 1) := by
      apply Nat.div_eq_of_eq_mul_left (partitionWeight_pos (n + 1) (by omega)
        (some i.castSucc))
      rw [partitionWeight, baseWeight]
      simpa [D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.axisScale, M,
        show i.1 ≠ n by omega, Nat.mul_comm] using
        (Nat.div_mul_cancel (base_axisScale_dvd_mass (n + 1) (by omega) i.castSucc)).symm
    have hall :
      (∏ i : Fin n,
          D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i.1 + 1)) = M := by
      calc
        (∏ i : Fin n,
            D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i.1 + 1)) =
            ∏ i ∈ Finset.range n,
              D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i + 1) :=
          Fin.prod_univ_eq_prod_range
            (fun i ↦
              D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i + 1)) n
        _ = M := by
          change (∏ i ∈ Finset.range n,
            D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i + 1)) =
              D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (n + 1) - 1
          rw [sylvester_sub_one_eq_prod (n + 1) (by omega), Finset.prod_range_succ']
          simp [D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester]
    have hsplit :
      S * ∏ i ∈ Rᶜ,
          D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i.1 + 1) = M := by
      simpa [S, hall] using Finset.prod_mul_prod_compl R
        (fun i : Fin n =>
          D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i.1 + 1))
    have hvprod :
      (∏ j ∈ Rᶜ.image (fun i => (some i.castSucc : Option (Fin (n + 1)))),
          (((M / partitionWeight (n + 1) j : ℕ) : ℂ)⁻¹)) =
        ∏ i ∈ Rᶜ,
          (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester
            (i.1 + 1) : ℂ)⁻¹ := by
      rw [Finset.prod_image hinjective.injOn]
      apply Finset.prod_congr rfl
      intro i hi
      rw [hscale]
    have hrootprod :
      (∏ j ∈ insert none
          (insert (some (Fin.last n)) (R.image fun i => some i.castSucc)),
          (1 - ζ ^ partitionWeight (n + 1) j)) =
        (1 - ζ) ^ 2 * ∏ i ∈ R, chord i := by
      have hnone : (none : Option (Fin (n + 1))) ∉
          insert (some (Fin.last n)) (R.image fun i => some i.castSucc) := by
        simp
      have hlast : (some (Fin.last n) : Option (Fin (n + 1))) ∉
          R.image (fun i => some i.castSucc) := by
        simp [Fin.castSucc_ne_last]
      have hbase (i : Fin n) :
          baseWeight (n + 1) i.castSucc =
            M / D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester
              (i.1 + 1) := by
        simpa [partitionWeight] using hweight i
      rw [Finset.prod_insert hnone, Finset.prod_insert hlast,
        Finset.prod_image hinjective.injOn]
      simp [partitionWeight, baseWeight_last, hbase, chord, pow_two]
      ring
    rw [hvanishing, hsupport]
    rw [hvprod, hrootprod]
    norm_num
    have hM : 0 < M := Nat.sub_pos_of_lt
      (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester (n + 1) (by omega)))
    have hS : 0 < S := Finset.prod_pos fun i _ =>
      sylvester_pos (i.1 + 1)
    have hsplitC :
      (S : ℂ) * (∏ i ∈ Rᶜ,
          (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i.1 + 1) : ℂ)) =
        (M : ℂ) := by
      exact_mod_cast hsplit
    have hMC :
      (M : ℂ) =
        (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester
          (n + 1) : ℂ) - 1 := by
      dsimp [M]
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [← hMC]
    have hcastS :
      (∏ i ∈ R,
          (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester
            (i.1 + 1) : ℂ)) = (S : ℂ) := by
      exact_mod_cast (rfl : (∏ i ∈ R,
        D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester
          (i.1 + 1)) = S)
    have hchordR :
      (∏ i ∈ R, (1 - ζ ^ (M /
          D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester
            (i.1 + 1)))) = ∏ i ∈ R, chord i := by
      rfl
    change
      (ζ ^ c)⁻¹ * (M : ℂ)⁻¹ * ((n - 5).factorial : ℂ)⁻¹ *
          ((∏ i ∈ R, chord i)⁻¹ * ((1 - ζ) ^ 2)⁻¹ *
            ∏ i ∈ Rᶜ,
              (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester
                (i.1 + 1) : ℂ)) =
        (ζ ^ c)⁻¹ * ((n - 5).factorial : ℂ)⁻¹ * (S : ℂ)⁻¹ *
          ((∏ i ∈ R, chord i)⁻¹ * ((1 - ζ) ^ 2)⁻¹)
    have hcancel :
      (M : ℂ)⁻¹ * (∏ i ∈ Rᶜ,
          (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester
            (i.1 + 1) : ℂ)) = (S : ℂ)⁻¹ := by
      field_simp [Nat.ne_of_gt hM, Nat.ne_of_gt hS]
      simpa [mul_comm] using hsplitC
    rw [← hcancel]
    ring
  have hM : 0 < M := Nat.sub_pos_of_lt
    (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester (n + 1) (by omega)))
  have hS : 0 < S := Finset.prod_pos fun i _ => sylvester_pos (i.1 + 1)
  have hchord_ne (i : Fin n) (hi : i ∈ R) : chord i ≠ 0 := by
    apply sub_ne_zero.mpr
    exact (Finset.mem_filter.mp hi).2.symm
  have hchordProd : 0 < ∏ i ∈ R, ‖chord i‖ :=
    Finset.prod_pos fun i hi => norm_pos_iff.mpr (hchord_ne i hi)
  have honeChord : 0 < ‖1 - ζ‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hζne.symm)
  have hdenom : 0 < ((n + 1 - 6).factorial : ℝ) * (S : ℝ) * ‖1 - ζ‖ ^ 2 *
      ∏ i ∈ R, ‖chord i‖ := by
    positivity
  refine ⟨hsupport, hcard, hExact, hdenom, ?_⟩
  change ‖(sourceLocalRootContributionPolynomial (n + 1) ζ c).coeff (n + 1 - 6)‖ ≤
    1 / (((n + 1 - 6).factorial : ℝ) * (S : ℝ) * ‖1 - ζ‖ ^ 2 *
      ∏ i ∈ R, ‖chord i‖)
  rw [hExact]
  simp only [norm_mul, hphase, one_mul, norm_inv, Complex.norm_natCast,
    norm_pow, norm_prod]
  simp only [one_div]
  ring_nf
  exact le_rfl

end D5.S0.FiniteGeometry.SylvesterSimplexEhrhartRootContributionBound
