/- GID: D5/S0/FiniteGeometry/SylvesterSimplexEhrhartPrincipalPart
   generality: G
   mirror-B: D5/B/S0/FiniteGeometry/SylvesterSimplexEhrhartPrincipalPart
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual local-coordinate cofactor bridge for the source Sylvester simplex. -/

import D5.S0.FiniteGeometry.SylvesterSimplexEhrhartCoefficient

noncomputable section

namespace D5.S0.FiniteGeometry.SylvesterSimplexEhrhartPrincipalPart

open scoped BigOperators

open private rootLocalCoordinate rootDenominatorFactor sourceDenominator sourcePoleOrder
  sourceLocalRegularDenominator sourceLocalRegularInverse sourceLocalDenominator_factorization
  sourceDenominator_root_factorization sourceRootExpansion
  sourceExponentialLocalJet sourceLocalRootContributionPolynomial
  sourceLocalRootContributionPolynomial_eval sourceLocalRootContributionPolynomial_target_coeff
  sourcePoleOneNormalizedJet sourceLocalRootContributionPolynomial_one_target_coeff
  sourceRootSupport sourceRootExpansion_principalPart_coefficients from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartCoefficient

open private two_le_sylvester from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity

open private baseSamplePolynomial interiorSamplePolynomial sourceEhrhartPolynomial from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartSamples

/-- Evaluating the actual root factorization in the nonzero-centered exponential
coordinate and cancelling its forced `X`-power identifies the regular cofactor. -/
private lemma sourceRootCofactor_localCoordinate (d : ℕ) (hd : 1 ≤ d) :
    let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1
    let roots := Polynomial.nthRootsFinset M (1 : ℂ)
    ∀ ζ ∈ roots,
      let e := PowerSeries.rescale (-(M : ℂ)⁻¹) (PowerSeries.exp ℂ)
      let h := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) (e - 1)
      sourceLocalRegularDenominator d ζ =
        (-1 : PowerSeries ℂ) ^ (d + 1) *
          (PowerSeries.C ζ * h) ^ sourcePoleOrder d ζ *
            ∏ η ∈ roots.erase ζ,
              (rootLocalCoordinate ζ M - PowerSeries.C η) ^ sourcePoleOrder d η := by
  classical
  dsimp only
  let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1
  let roots := Polynomial.nthRootsFinset M (1 : ℂ)
  have hM : 0 < M := Nat.sub_pos_of_lt
    (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester d hd))
  have hglobal :
      sourceDenominator d =
        (-1 : Polynomial ℂ) ^ (d + 1) *
          ∏ ζ ∈ roots,
            (Polynomial.X - Polynomial.C ζ) ^ sourcePoleOrder d ζ :=
    sourceDenominator_root_factorization d hd
  intro ζ hζ
  let e := PowerSeries.rescale (-(M : ℂ)⁻¹) (PowerSeries.exp ℂ)
  let h := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) (e - 1)
  have heConstant : PowerSeries.constantCoeff e = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [e, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  have heSub : e - 1 = h * PowerSeries.X := by
    have hconstant : PowerSeries.constantCoeff (e - 1) = 0 := by
      simp [heConstant]
    calc
      e - 1 = (PowerSeries.mk fun n => PowerSeries.coeff (n + 1) (e - 1)) *
          PowerSeries.X + PowerSeries.C (PowerSeries.constantCoeff (e - 1)) :=
        PowerSeries.eq_shift_mul_X_add_const (e - 1)
      _ = h * PowerSeries.X := by rw [hconstant]; simp [h]
  have hcoordinate :
      rootLocalCoordinate ζ M - PowerSeries.C ζ =
        PowerSeries.C ζ * h * PowerSeries.X := by
    change PowerSeries.C ζ * e - PowerSeries.C ζ = _
    calc
      PowerSeries.C ζ * e - PowerSeries.C ζ =
          PowerSeries.C ζ * (e - 1) := by ring
      _ = _ := by rw [heSub]; ring
  have heval :
      (∏ j : Option (Fin d), rootDenominatorFactor d ζ j) =
        (-1 : PowerSeries ℂ) ^ (d + 1) *
          ∏ η ∈ roots,
            (rootLocalCoordinate ζ M - PowerSeries.C η) ^ sourcePoleOrder d η := by
    calc
      _ = Polynomial.eval₂ PowerSeries.C (rootLocalCoordinate ζ M)
            (sourceDenominator d) := by
              simp [sourceDenominator, rootDenominatorFactor,
                Polynomial.eval₂_finsetProd, M]
      _ = _ := by
        rw [hglobal]
        simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_neg,
          Polynomial.eval₂_one, Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub,
          Polynomial.eval₂_X, Polynomial.eval₂_C]
  rw [sourceLocalDenominator_factorization d hd] at heval
  rw [← Finset.prod_erase_mul roots _ hζ, hcoordinate, mul_pow] at heval
  apply mul_right_cancel₀ (pow_ne_zero _ (PowerSeries.X_ne_zero :
    (PowerSeries.X : PowerSeries ℂ) ≠ 0))
  calc
    sourceLocalRegularDenominator d ζ * PowerSeries.X ^ sourcePoleOrder d ζ =
        _ := heval
    _ = ((-1 : PowerSeries ℂ) ^ (d + 1) *
          (PowerSeries.C ζ * h) ^ sourcePoleOrder d ζ *
            ∏ η ∈ roots.erase ζ,
              (rootLocalCoordinate ζ M - PowerSeries.C η) ^ sourcePoleOrder d η) *
          PowerSeries.X ^ sourcePoleOrder d ζ := by ring

/-- The coefficients in the actual global principal-part expansion determine
the inverse regular cofactor through its finite jet at every actual root. -/
private lemma sourceRootExpansion_localCofactor_finiteJet (d : ℕ) (hd : 1 ≤ d)
    (a : (ζ : ℂ) → Fin (sourcePoleOrder d ζ) → ℂ)
    (ha :
      let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1
      sourceRootExpansion d =
        ∑ ζ ∈ Polynomial.nthRootsFinset M (1 : ℂ), ∑ j,
          PowerSeries.C (a ζ j) *
            (algebraMap (Polynomial ℂ) (PowerSeries ℂ)
              (Polynomial.X - Polynomial.C ζ))⁻¹ ^ (j.1 + 1)) :
    let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1
    let roots := Polynomial.nthRootsFinset M (1 : ℂ)
    ∀ ζ ∈ roots,
      let e := PowerSeries.rescale (-(M : ℂ)⁻¹) (PowerSeries.exp ℂ)
      let h := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) (e - 1)
      PowerSeries.trunc (sourcePoleOrder d ζ) (sourceLocalRegularInverse d ζ) =
        PowerSeries.trunc (sourcePoleOrder d ζ)
          (∑ j : Fin (sourcePoleOrder d ζ),
            PowerSeries.C (a ζ j) * PowerSeries.X ^ (sourcePoleOrder d ζ - j.1 - 1) *
              (PowerSeries.C ζ * h)⁻¹ ^ (j.1 + 1)) := by
  classical
  dsimp only at ha ⊢
  let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1
  let roots := Polynomial.nthRootsFinset M (1 : ℂ)
  let D : Polynomial ℂ := ∏ ζ ∈ roots,
    (Polynomial.X - Polynomial.C ζ) ^ sourcePoleOrder d ζ
  have hM : 0 < M := Nat.sub_pos_of_lt
    (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester d hd))
  have hrootNonzero (ζ : ℂ) (hζ : ζ ∈ roots) : ζ ≠ 0 := by
    have hζpow : ζ ^ M = 1 := (Polynomial.mem_nthRootsFinset hM (1 : ℂ)).mp hζ
    intro hzero
    have : (0 : ℂ) = 1 := by simpa [hzero, zero_pow hM.ne'] using hζpow
    exact zero_ne_one this
  have hinverse (ζ : ℂ) (hζ : ζ ∈ roots) :
      (algebraMap (Polynomial ℂ) (PowerSeries ℂ)
          (Polynomial.X - Polynomial.C ζ))⁻¹ *
        algebraMap (Polynomial ℂ) (PowerSeries ℂ)
          (Polynomial.X - Polynomial.C ζ) = 1 := by
    rw [PowerSeries.inv_mul_cancel]
    simpa [PowerSeries.algebraMap_apply'] using neg_ne_zero.mpr (hrootNonzero ζ hζ)
  have hsourceD :
      sourceRootExpansion d * algebraMap (Polynomial ℂ) (PowerSeries ℂ) D =
        PowerSeries.C ((-1 : ℂ) ^ (d + 1)) := by
    rw [sourceRootExpansion]
    change
      (-1 : PowerSeries ℂ) ^ (d + 1) *
          (∏ ζ ∈ roots,
            (algebraMap (Polynomial ℂ) (PowerSeries ℂ)
              (Polynomial.X - Polynomial.C ζ))⁻¹ ^ sourcePoleOrder d ζ) *
        algebraMap (Polynomial ℂ) (PowerSeries ℂ) D = _
    simp only [D, map_prod, map_pow]
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    have hcancel (ζ : ℂ) (hζ : ζ ∈ roots) :
        (algebraMap (Polynomial ℂ) (PowerSeries ℂ)
            (Polynomial.X - Polynomial.C ζ))⁻¹ ^ sourcePoleOrder d ζ *
          algebraMap (Polynomial ℂ) (PowerSeries ℂ)
            (Polynomial.X - Polynomial.C ζ) ^ sourcePoleOrder d ζ = 1 := by
      rw [← mul_pow, hinverse ζ hζ, one_pow]
    rw [Finset.prod_congr rfl hcancel, Finset.prod_const_one, mul_one]
    simp
  have hfinitePolynomial :
      (∑ ζ ∈ roots, ∑ j : Fin (sourcePoleOrder d ζ),
        Polynomial.C (a ζ j) *
          (Polynomial.X - Polynomial.C ζ) ^ (sourcePoleOrder d ζ - j.1 - 1) *
            ∏ η ∈ roots.erase ζ,
              (Polynomial.X - Polynomial.C η) ^ sourcePoleOrder d η) =
        Polynomial.C ((-1 : ℂ) ^ (d + 1)) := by
    apply Polynomial.coe_injective ℂ
    calc
      ((↑((∑ ζ ∈ roots, ∑ j : Fin (sourcePoleOrder d ζ),
          Polynomial.C (a ζ j) *
            (Polynomial.X - Polynomial.C ζ) ^ (sourcePoleOrder d ζ - j.1 - 1) *
              ∏ η ∈ roots.erase ζ,
                (Polynomial.X - Polynomial.C η) ^ sourcePoleOrder d η) : Polynomial ℂ) :
          PowerSeries ℂ)) =
          ∑ ζ ∈ roots, ∑ j : Fin (sourcePoleOrder d ζ),
            PowerSeries.C (a ζ j) *
              (algebraMap (Polynomial ℂ) (PowerSeries ℂ)
                (Polynomial.X - Polynomial.C ζ))⁻¹ ^ (j.1 + 1) *
                algebraMap (Polynomial ℂ) (PowerSeries ℂ) D := by
        change Polynomial.coeToPowerSeries.ringHom
          (∑ ζ ∈ roots, ∑ j : Fin (sourcePoleOrder d ζ),
            Polynomial.C (a ζ j) *
              (Polynomial.X - Polynomial.C ζ) ^ (sourcePoleOrder d ζ - j.1 - 1) *
                ∏ η ∈ roots.erase ζ,
                  (Polynomial.X - Polynomial.C η) ^ sourcePoleOrder d η) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro ζ hζ
        rw [map_sum]
        apply Fintype.sum_congr
        intro j
        have hD : D =
            (Polynomial.X - Polynomial.C ζ) ^ sourcePoleOrder d ζ *
              ∏ η ∈ roots.erase ζ,
                (Polynomial.X - Polynomial.C η) ^ sourcePoleOrder d η := by
          dsimp [D]
          rw [← Finset.prod_erase_mul roots
            (fun η => (Polynomial.X - Polynomial.C η) ^ sourcePoleOrder d η) hζ]
          ring
        have hDseries := congrArg (Polynomial.coeToPowerSeries.ringHom (R := ℂ)) hD
        simp only [map_mul, map_pow, map_prod,
          Polynomial.coeToPowerSeries.ringHom_apply] at hDseries
        simp only [map_mul, map_pow, map_prod,
          Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
          PowerSeries.algebraMap_apply', Algebra.algebraMap_self, PowerSeries.map_id, id_eq]
        rw [hDseries]
        have hp : sourcePoleOrder d ζ =
            (j.1 + 1) + (sourcePoleOrder d ζ - j.1 - 1) := by omega
        have hpow :
            (↑((Polynomial.X : Polynomial ℂ) - Polynomial.C ζ) : PowerSeries ℂ) ^
                sourcePoleOrder d ζ =
              (↑((Polynomial.X : Polynomial ℂ) - Polynomial.C ζ) : PowerSeries ℂ) ^
                  (j.1 + 1) *
                (↑((Polynomial.X : Polynomial ℂ) - Polynomial.C ζ) : PowerSeries ℂ) ^
                    (sourcePoleOrder d ζ - j.1 - 1) := by
          calc
            _ = (↑((Polynomial.X : Polynomial ℂ) - Polynomial.C ζ) : PowerSeries ℂ) ^
                  ((j.1 + 1) + (sourcePoleOrder d ζ - j.1 - 1)) :=
              congrArg
                (fun n =>
                  (↑((Polynomial.X : Polynomial ℂ) - Polynomial.C ζ) : PowerSeries ℂ) ^ n) hp
            _ = _ := pow_add _ _ _
        rw [hpow]
        calc
          PowerSeries.C (a ζ j) *
                (↑((Polynomial.X : Polynomial ℂ) - Polynomial.C ζ) : PowerSeries ℂ) ^
                  (sourcePoleOrder d ζ - j.1 - 1) *
              ∏ η ∈ roots.erase ζ,
                (↑((Polynomial.X : Polynomial ℂ) - Polynomial.C η) : PowerSeries ℂ) ^
                  sourcePoleOrder d η =
            PowerSeries.C (a ζ j) *
                (((↑((Polynomial.X : Polynomial ℂ) - Polynomial.C ζ) : PowerSeries ℂ))⁻¹ ^
                    (j.1 + 1) *
                  (↑((Polynomial.X : Polynomial ℂ) - Polynomial.C ζ) : PowerSeries ℂ) ^
                    (j.1 + 1)) *
                (↑((Polynomial.X : Polynomial ℂ) - Polynomial.C ζ) : PowerSeries ℂ) ^
                  (sourcePoleOrder d ζ - j.1 - 1) *
              ∏ η ∈ roots.erase ζ,
                (↑((Polynomial.X : Polynomial ℂ) - Polynomial.C η) : PowerSeries ℂ) ^
                  sourcePoleOrder d η := by
                    rw [← mul_pow]
                    have hinverse' :
                        ((↑((Polynomial.X : Polynomial ℂ) - Polynomial.C ζ) :
                          PowerSeries ℂ))⁻¹ *
                          (↑((Polynomial.X : Polynomial ℂ) - Polynomial.C ζ) :
                            PowerSeries ℂ) = 1 := by
                      simpa [PowerSeries.algebraMap_apply', Algebra.algebraMap_self,
                        PowerSeries.map_id] using hinverse ζ hζ
                    rw [hinverse', one_pow, mul_one]
          _ = _ := by ring
      _ =
          (∑ ζ ∈ roots, ∑ j : Fin (sourcePoleOrder d ζ),
            PowerSeries.C (a ζ j) *
              (algebraMap (Polynomial ℂ) (PowerSeries ℂ)
                (Polynomial.X - Polynomial.C ζ))⁻¹ ^ (j.1 + 1)) *
            algebraMap (Polynomial ℂ) (PowerSeries ℂ) D := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro ζ hζ
              rw [Finset.sum_mul]
      _ = sourceRootExpansion d *
            algebraMap (Polynomial ℂ) (PowerSeries ℂ) D := by rw [← ha]
      _ = PowerSeries.C ((-1 : ℂ) ^ (d + 1)) := hsourceD
      _ = (↑(Polynomial.C ((-1 : ℂ) ^ (d + 1))) : PowerSeries ℂ) := by simp
  intro ζ hζ
  let e := PowerSeries.rescale (-(M : ℂ)⁻¹) (PowerSeries.exp ℂ)
  let h := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) (e - 1)
  change PowerSeries.trunc (sourcePoleOrder d ζ) (sourceLocalRegularInverse d ζ) =
    PowerSeries.trunc (sourcePoleOrder d ζ)
      (∑ j : Fin (sourcePoleOrder d ζ),
        PowerSeries.C (a ζ j) * PowerSeries.X ^ (sourcePoleOrder d ζ - j.1 - 1) *
          (PowerSeries.C ζ * h)⁻¹ ^ (j.1 + 1))
  by_cases hp : sourcePoleOrder d ζ = 0
  · simp [hp]
  have hpPos : 0 < sourcePoleOrder d ζ := Nat.pos_of_ne_zero hp
  have heConstant : PowerSeries.constantCoeff e = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [e, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  have heSub : e - 1 = h * PowerSeries.X := by
    have hconstant : PowerSeries.constantCoeff (e - 1) = 0 := by simp [heConstant]
    calc
      e - 1 = (PowerSeries.mk fun n => PowerSeries.coeff (n + 1) (e - 1)) *
          PowerSeries.X + PowerSeries.C (PowerSeries.constantCoeff (e - 1)) :=
        PowerSeries.eq_shift_mul_X_add_const (e - 1)
      _ = h * PowerSeries.X := by rw [hconstant]; simp [h]
  have hcoordinate :
      rootLocalCoordinate ζ M - PowerSeries.C ζ =
        (PowerSeries.C ζ * h) * PowerSeries.X := by
    change PowerSeries.C ζ * e - PowerSeries.C ζ = _
    rw [show PowerSeries.C ζ * e - PowerSeries.C ζ =
      PowerSeries.C ζ * (e - 1) by ring, heSub]
    ring
  have hcofactor := sourceRootCofactor_localCoordinate d hd ζ hζ
  change sourceLocalRegularDenominator d ζ =
      (-1 : PowerSeries ℂ) ^ (d + 1) *
        (PowerSeries.C ζ * h) ^ sourcePoleOrder d ζ *
          ∏ η ∈ roots.erase ζ,
            (rootLocalCoordinate ζ M - PowerSeries.C η) ^ sourcePoleOrder d η at hcofactor
  have hhConstant : PowerSeries.constantCoeff h = -(M : ℂ)⁻¹ := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [h, e, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  have huConstant :
      PowerSeries.constantCoeff (PowerSeries.C ζ * h) = ζ * (-(M : ℂ)⁻¹) := by
    simp [hhConstant]
  have huNonzero :
      PowerSeries.constantCoeff (PowerSeries.C ζ * h) ≠ 0 := by
    rw [huConstant]
    exact mul_ne_zero (hrootNonzero ζ hζ)
      (neg_ne_zero.mpr (inv_ne_zero (Nat.cast_ne_zero.mpr hM.ne')))
  have hotherConstant (η : ℂ) (hη : η ∈ roots.erase ζ) :
      PowerSeries.constantCoeff (rootLocalCoordinate ζ M - PowerSeries.C η) = ζ - η := by
    rw [rootLocalCoordinate, map_sub, map_mul]
    have heConstant' :
        PowerSeries.constantCoeff
          (PowerSeries.rescale (-(M : ℂ)⁻¹) (PowerSeries.exp ℂ)) = 1 := by
      simpa [e] using heConstant
    rw [heConstant']
    simp
  have hotherNonzero (η : ℂ) (hη : η ∈ roots.erase ζ) :
      PowerSeries.constantCoeff (rootLocalCoordinate ζ M - PowerSeries.C η) ≠ 0 := by
    rw [hotherConstant η hη]
    exact sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hη))
  have hregularNonzero :
      PowerSeries.constantCoeff (sourceLocalRegularDenominator d ζ) ≠ 0 := by
    have huNonzero' :
        PowerSeries.constantCoeff (PowerSeries.C ζ) * PowerSeries.constantCoeff h ≠ 0 := by
      simpa only [map_mul] using huNonzero
    rw [hcofactor]
    simp only [map_mul, map_pow, map_prod]
    apply mul_ne_zero
    · apply mul_ne_zero
      · simp
      · exact pow_ne_zero _ huNonzero'
    · exact Finset.prod_ne_zero_iff.mpr fun η hη => pow_ne_zero _ (hotherNonzero η hη)
  have heval := congrArg
    (Polynomial.eval₂ PowerSeries.C (rootLocalCoordinate ζ M)) hfinitePolynomial
  simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at heval
  have htrunc := congrArg (PowerSeries.trunc (sourcePoleOrder d ζ))
    (congrArg (sourceLocalRegularInverse d ζ * ·) heval)
  rw [sourceLocalRegularInverse] at htrunc
  -- The selected-root terms cancel against the actual regular cofactor; every
  -- other-root term still contains the full `X^p` and disappears on truncation.
  have hevalRest (x : ℂ) :
      Polynomial.eval₂ PowerSeries.C (rootLocalCoordinate ζ M)
          (∏ η ∈ roots.erase x,
            (Polynomial.X - Polynomial.C η) ^ sourcePoleOrder d η) =
        ∏ η ∈ roots.erase x,
          (rootLocalCoordinate ζ M - PowerSeries.C η) ^ sourcePoleOrder d η := by
    simp only [Polynomial.eval₂_finsetProd, Polynomial.eval₂_pow,
      Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
  have hsignSquare :
      (-1 : PowerSeries ℂ) ^ (d + 1) * (-1 : PowerSeries ℂ) ^ (d + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  have huCancelPow (n : ℕ) :
      (PowerSeries.C ζ * h) ^ n * (PowerSeries.C ζ * h)⁻¹ ^ n = 1 := by
    rw [← mul_pow, PowerSeries.mul_inv_cancel _ huNonzero, one_pow]
  have hselectedTerm (j : Fin (sourcePoleOrder d ζ)) :
      (sourceLocalRegularDenominator d ζ)⁻¹ *
          (PowerSeries.C (a ζ j) *
            (rootLocalCoordinate ζ M - PowerSeries.C ζ) ^
                (sourcePoleOrder d ζ - j.1 - 1) *
              Polynomial.eval₂ PowerSeries.C (rootLocalCoordinate ζ M)
                (∏ η ∈ roots.erase ζ,
                  (Polynomial.X - Polynomial.C η) ^ sourcePoleOrder d η)) =
        PowerSeries.C ((-1 : ℂ) ^ (d + 1)) *
          (PowerSeries.C (a ζ j) *
            PowerSeries.X ^ (sourcePoleOrder d ζ - j.1 - 1) *
              (PowerSeries.C ζ * h)⁻¹ ^ (j.1 + 1)) := by
    apply (PowerSeries.isUnit_iff_constantCoeff.mpr
      (isUnit_iff_ne_zero.mpr hregularNonzero)).mul_left_cancel
    rw [← mul_assoc, PowerSeries.mul_inv_cancel _ hregularNonzero, one_mul]
    have hpSplit : sourcePoleOrder d ζ =
        (j.1 + 1) + (sourcePoleOrder d ζ - j.1 - 1) := by omega
    have huPowSplit :
        (PowerSeries.C ζ * h) ^ sourcePoleOrder d ζ =
          (PowerSeries.C ζ * h) ^ (j.1 + 1) *
            (PowerSeries.C ζ * h) ^ (sourcePoleOrder d ζ - j.1 - 1) := by
      calc
        _ = (PowerSeries.C ζ * h) ^
            ((j.1 + 1) + (sourcePoleOrder d ζ - j.1 - 1)) :=
          congrArg (fun n => (PowerSeries.C ζ * h) ^ n) hpSplit
        _ = _ := pow_add _ _ _
    rw [hevalRest, hcoordinate, hcofactor, huPowSplit, mul_pow]
    change
      PowerSeries.C (a ζ j) *
            ((PowerSeries.C ζ * h) ^ (sourcePoleOrder d ζ - j.1 - 1) *
              PowerSeries.X ^ (sourcePoleOrder d ζ - j.1 - 1)) *
          ∏ η ∈ roots.erase ζ,
            (rootLocalCoordinate ζ M - PowerSeries.C η) ^ sourcePoleOrder d η = _
    rw [show PowerSeries.C ((-1 : ℂ) ^ (d + 1)) =
        (-1 : PowerSeries ℂ) ^ (d + 1) by simp]
    calc
      _ = ((-1 : PowerSeries ℂ) ^ (d + 1) * (-1 : PowerSeries ℂ) ^ (d + 1)) *
          ((PowerSeries.C ζ * h) ^ (j.1 + 1) *
            (PowerSeries.C ζ * h)⁻¹ ^ (j.1 + 1)) *
          (PowerSeries.C (a ζ j) *
            (PowerSeries.C ζ * h) ^ (sourcePoleOrder d ζ - j.1 - 1) *
              PowerSeries.X ^ (sourcePoleOrder d ζ - j.1 - 1) *
                ∏ η ∈ roots.erase ζ,
                  (rootLocalCoordinate ζ M - PowerSeries.C η) ^ sourcePoleOrder d η) := by
            rw [hsignSquare, huCancelPow, one_mul]
            ring
      _ = _ := by ring
  have hselected :
      (sourceLocalRegularDenominator d ζ)⁻¹ *
          ∑ j : Fin (sourcePoleOrder d ζ),
            PowerSeries.C (a ζ j) *
              (rootLocalCoordinate ζ M - PowerSeries.C ζ) ^
                  (sourcePoleOrder d ζ - j.1 - 1) *
                Polynomial.eval₂ PowerSeries.C (rootLocalCoordinate ζ M)
                  (∏ η ∈ roots.erase ζ,
                    (Polynomial.X - Polynomial.C η) ^ sourcePoleOrder d η) =
        PowerSeries.C ((-1 : ℂ) ^ (d + 1)) *
          ∑ j : Fin (sourcePoleOrder d ζ),
            PowerSeries.C (a ζ j) *
              PowerSeries.X ^ (sourcePoleOrder d ζ - j.1 - 1) *
                (PowerSeries.C ζ * h)⁻¹ ^ (j.1 + 1) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => hselectedTerm j
  have hotherTerm (x : ℂ) (hx : x ∈ roots.erase ζ)
      (j : Fin (sourcePoleOrder d x)) :
      PowerSeries.trunc (sourcePoleOrder d ζ)
          ((sourceLocalRegularDenominator d ζ)⁻¹ *
            (PowerSeries.C (a x j) *
              (rootLocalCoordinate ζ M - PowerSeries.C x) ^
                  (sourcePoleOrder d x - j.1 - 1) *
                Polynomial.eval₂ PowerSeries.C (rootLocalCoordinate ζ M)
                  (∏ η ∈ roots.erase x,
                    (Polynomial.X - Polynomial.C η) ^ sourcePoleOrder d η))) = 0 := by
    have hxne : x ≠ ζ := Finset.ne_of_mem_erase hx
    have hζerase : ζ ∈ roots.erase x :=
      Finset.mem_erase.mpr ⟨Ne.symm hxne, hζ⟩
    have hrestFactor :
        Polynomial.eval₂ PowerSeries.C (rootLocalCoordinate ζ M)
            (∏ η ∈ roots.erase x,
              (Polynomial.X - Polynomial.C η) ^ sourcePoleOrder d η) =
          PowerSeries.X ^ sourcePoleOrder d ζ *
            ((PowerSeries.C ζ * h) ^ sourcePoleOrder d ζ *
              ∏ η ∈ (roots.erase x).erase ζ,
                (rootLocalCoordinate ζ M - PowerSeries.C η) ^ sourcePoleOrder d η) := by
      rw [hevalRest x, ← Finset.prod_erase_mul (roots.erase x)
        (fun η => (rootLocalCoordinate ζ M - PowerSeries.C η) ^ sourcePoleOrder d η)
        hζerase, hcoordinate, mul_pow]
      ring
    rw [hrestFactor]
    let q : PowerSeries ℂ :=
      (sourceLocalRegularDenominator d ζ)⁻¹ *
        (PowerSeries.C (a x j) *
          (rootLocalCoordinate ζ M - PowerSeries.C x) ^
              (sourcePoleOrder d x - j.1 - 1) *
            ((PowerSeries.C ζ * h) ^ sourcePoleOrder d ζ *
              ∏ η ∈ (roots.erase x).erase ζ,
                (rootLocalCoordinate ζ M - PowerSeries.C η) ^ sourcePoleOrder d η))
    have hfactor :
        (sourceLocalRegularDenominator d ζ)⁻¹ *
            (PowerSeries.C (a x j) *
              (rootLocalCoordinate ζ M - PowerSeries.C x) ^
                  (sourcePoleOrder d x - j.1 - 1) *
                (PowerSeries.X ^ sourcePoleOrder d ζ *
                  ((PowerSeries.C ζ * h) ^ sourcePoleOrder d ζ *
                    ∏ η ∈ (roots.erase x).erase ζ,
                      (rootLocalCoordinate ζ M - PowerSeries.C η) ^
                        sourcePoleOrder d η))) =
          PowerSeries.X ^ sourcePoleOrder d ζ * q := by
      dsimp [q]
      ring
    rw [hfactor]
    exact PowerSeries.trunc_X_pow_self_mul _ _
  have hother :
      PowerSeries.trunc (sourcePoleOrder d ζ)
          ((sourceLocalRegularDenominator d ζ)⁻¹ *
            ∑ x ∈ roots.erase ζ,
              ∑ j : Fin (sourcePoleOrder d x),
                PowerSeries.C (a x j) *
                  (rootLocalCoordinate ζ M - PowerSeries.C x) ^
                      (sourcePoleOrder d x - j.1 - 1) *
                    Polynomial.eval₂ PowerSeries.C (rootLocalCoordinate ζ M)
                      (∏ η ∈ roots.erase x,
                        (Polynomial.X - Polynomial.C η) ^ sourcePoleOrder d η)) = 0 := by
    rw [Finset.mul_sum, map_sum]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mul_sum, map_sum]
    exact Finset.sum_eq_zero fun j _ => hotherTerm x hx j
  rw [← Finset.sum_erase_add roots
    (fun x => ∑ j : Fin (sourcePoleOrder d x),
      PowerSeries.C (a x j) *
        (rootLocalCoordinate ζ M - PowerSeries.C x) ^
            (sourcePoleOrder d x - j.1 - 1) *
          Polynomial.eval₂ PowerSeries.C (rootLocalCoordinate ζ M)
            (∏ η ∈ roots.erase x,
              (Polynomial.X - Polynomial.C η) ^ sourcePoleOrder d η)) hζ,
    mul_add, map_add, hother, zero_add, hselected] at htrunc
  rw [PowerSeries.trunc_C_mul, PowerSeries.trunc_mul_C] at htrunc
  rw [sourceLocalRegularInverse]
  have hsignPolynomial :
      Polynomial.C ((-1 : ℂ) ^ (d + 1)) ≠ 0 := by simp
  apply mul_left_cancel₀ hsignPolynomial
  calc
    Polynomial.C ((-1 : ℂ) ^ (d + 1)) *
          PowerSeries.trunc (sourcePoleOrder d ζ)
            (sourceLocalRegularDenominator d ζ)⁻¹ =
        PowerSeries.trunc (sourcePoleOrder d ζ)
            (sourceLocalRegularDenominator d ζ)⁻¹ *
          Polynomial.C ((-1 : ℂ) ^ (d + 1)) := by ring
    _ = Polynomial.C ((-1 : ℂ) ^ (d + 1)) *
          PowerSeries.trunc (sourcePoleOrder d ζ)
            (∑ j : Fin (sourcePoleOrder d ζ),
              PowerSeries.C (a ζ j) *
                PowerSeries.X ^ (sourcePoleOrder d ζ - j.1 - 1) *
                  (PowerSeries.C ζ * h)⁻¹ ^ (j.1 + 1)) := htrunc.symm

/-- The diagonal coefficient of the divided exponential difference is the
ordinary rising-binomial coefficient.  This is the nonzero-exponential
coefficient step that is not supplied by the one-factor Bernoulli generating
function. -/
private lemma exponential_dividedDifference_diagonal_coeff
    (b : ℂ) (hb : b ≠ 0) (n j : ℕ) :
    let e := PowerSeries.rescale b (PowerSeries.exp ℂ)
    let h := PowerSeries.mk fun k => PowerSeries.coeff (k + 1) (e - 1)
    PowerSeries.coeff j
        (PowerSeries.rescale (-((n : ℂ) * b)) (PowerSeries.exp ℂ) * h⁻¹ ^ (j + 1)) =
      (-1 : ℂ) ^ j * b⁻¹ * (Nat.choose (n + j) j : ℂ) := by
  dsimp only
  let e := PowerSeries.rescale b (PowerSeries.exp ℂ)
  let h := PowerSeries.mk fun k => PowerSeries.coeff (k + 1) (e - 1)
  let E := PowerSeries.rescale (-((n : ℂ) * b)) (PowerSeries.exp ℂ)
  have heConstant : PowerSeries.constantCoeff e = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [e, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  have heSub : e - 1 = h * PowerSeries.X := by
    have hconstant : PowerSeries.constantCoeff (e - 1) = 0 := by simp [heConstant]
    calc
      e - 1 = (PowerSeries.mk fun k => PowerSeries.coeff (k + 1) (e - 1)) *
          PowerSeries.X + PowerSeries.C (PowerSeries.constantCoeff (e - 1)) :=
        PowerSeries.eq_shift_mul_X_add_const (e - 1)
      _ = h * PowerSeries.X := by rw [hconstant]; simp [h]
  have hhConstant : PowerSeries.constantCoeff h = b := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [h, e, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  have hhinv : h * h⁻¹ = 1 := PowerSeries.mul_inv_cancel h (by simpa [hhConstant] using hb)
  have heDerivative : PowerSeries.derivative ℂ e = PowerSeries.C b * e := by
    ext k
    dsimp [e]
    simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_rescale, PowerSeries.coeff_exp, map_div, map_one,
      map_natCast, one_div]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    repeat' rw [map_inv₀]
    push_cast
    field_simp
    ring
  have hEDerivative :
      PowerSeries.derivative ℂ E = PowerSeries.C (-((n : ℂ) * b)) * E := by
    ext k
    dsimp [E]
    simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_rescale, PowerSeries.coeff_exp, map_div, map_one,
      map_natCast, one_div]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    repeat' rw [map_inv₀]
    push_cast
    field_simp
    ring
  have hhDerivative :
      PowerSeries.X * PowerSeries.derivative ℂ h =
        PowerSeries.C b + PowerSeries.C b * PowerSeries.X * h - h := by
    have hd := congrArg (PowerSeries.derivative ℂ) heSub
    simp only [map_sub, PowerSeries.derivative_one, sub_zero, Derivation.leibniz,
      PowerSeries.derivative_X, smul_eq_mul, heDerivative, mul_one] at hd
    have heEq : e = 1 + h * PowerSeries.X := by
      linear_combination heSub
    rw [heEq] at hd
    rw [show PowerSeries.C b * (1 + h * PowerSeries.X) =
        PowerSeries.C b + PowerSeries.C b * PowerSeries.X * h by ring] at hd
    rw [eq_sub_iff_add_eq]
    simpa [add_comm] using hd.symm
  have hrecurrence (r : ℕ) :
      PowerSeries.X * PowerSeries.derivative ℂ (E * h⁻¹ ^ r) -
          PowerSeries.C (r : ℂ) * (E * h⁻¹ ^ r) =
        PowerSeries.C (-((n : ℂ) * b) - (r : ℂ) * b) *
            PowerSeries.X * (E * h⁻¹ ^ r) -
          PowerSeries.C ((r : ℂ) * b) * (E * h⁻¹ ^ (r + 1)) := by
    cases r with
    | zero =>
        simp [hEDerivative]
        ring
    | succ r =>
        have haux :
            E * h⁻¹ ^ (r + 2) * (PowerSeries.X * PowerSeries.derivative ℂ h) =
              PowerSeries.C b * (E * h⁻¹ ^ (r + 2)) +
                PowerSeries.C b * PowerSeries.X * (E * h⁻¹ ^ (r + 1)) -
                  E * h⁻¹ ^ (r + 1) := by
          rw [hhDerivative]
          simp only [pow_succ]
          have hinv_h : h⁻¹ * h = 1 := by simpa [mul_comm] using hhinv
          linear_combination
            (PowerSeries.C b * PowerSeries.X * E * h⁻¹ ^ (r + 1) -
              E * h⁻¹ ^ (r + 1)) * hinv_h
        simp only [Derivation.leibniz, hEDerivative, PowerSeries.derivative_pow,
          PowerSeries.derivative_inv', smul_eq_mul, Nat.add_sub_cancel, map_add,
          map_sub, map_neg, map_mul, map_one, map_natCast]
        rw [show (↑(r + 1) : PowerSeries ℂ) = PowerSeries.C (r + 1 : ℂ) by simp]
        simp only [pow_succ]
        linear_combination -(PowerSeries.C (r + 1 : ℂ)) * haux
  induction j with
  | zero =>
      rw [pow_one, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
        PowerSeries.constantCoeff_inv, hhConstant]
      have hEConstant : PowerSeries.constantCoeff E = 1 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
        simp [E, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
      rw [hEConstant]
      simp
  | succ j ih =>
      have hr := congrArg (PowerSeries.coeff (j + 1)) (hrecurrence (j + 1))
      simp only [map_sub, PowerSeries.coeff_C_mul] at hr
      have hleft :
          PowerSeries.coeff (j + 1)
              (PowerSeries.X * PowerSeries.derivative ℂ (E * h⁻¹ ^ (j + 1))) =
            PowerSeries.coeff (j + 1) (E * h⁻¹ ^ (j + 1)) * (j + 1) := by
        calc
          _ = PowerSeries.coeff (j + 1)
              (PowerSeries.derivative ℂ (E * h⁻¹ ^ (j + 1)) * PowerSeries.X) := by
                rw [mul_comm]
          _ = PowerSeries.coeff j (PowerSeries.derivative ℂ (E * h⁻¹ ^ (j + 1))) := by
                simpa using PowerSeries.coeff_mul_X_pow
                  (PowerSeries.derivative ℂ (E * h⁻¹ ^ (j + 1))) 1 j
          _ = _ := PowerSeries.coeff_derivative _ _
      have hright :
          PowerSeries.coeff (j + 1)
              ((PowerSeries.C (-((n : ℂ) * b)) - PowerSeries.C ((j + 1 : ℂ) * b)) *
                PowerSeries.X * (E * h⁻¹ ^ (j + 1))) =
            (-((n : ℂ) * b) - (j + 1 : ℂ) * b) *
              PowerSeries.coeff j (E * h⁻¹ ^ (j + 1)) := by
        calc
          _ = PowerSeries.coeff (j + 1)
              ((PowerSeries.C (-((n : ℂ) * b)) - PowerSeries.C ((j + 1 : ℂ) * b)) *
                (E * h⁻¹ ^ (j + 1)) * PowerSeries.X) := by
                  rw [show
                    (PowerSeries.C (-((n : ℂ) * b)) -
                        PowerSeries.C ((j + 1 : ℂ) * b)) * PowerSeries.X *
                          (E * h⁻¹ ^ (j + 1)) =
                      (PowerSeries.C (-((n : ℂ) * b)) -
                        PowerSeries.C ((j + 1 : ℂ) * b)) *
                          (E * h⁻¹ ^ (j + 1)) * PowerSeries.X by ring]
          _ = PowerSeries.coeff j
              ((PowerSeries.C (-((n : ℂ) * b)) - PowerSeries.C ((j + 1 : ℂ) * b)) *
                (E * h⁻¹ ^ (j + 1))) := by
                  simpa using PowerSeries.coeff_mul_X_pow
                    ((PowerSeries.C (-((n : ℂ) * b)) -
                      PowerSeries.C ((j + 1 : ℂ) * b)) *
                        (E * h⁻¹ ^ (j + 1))) 1 j
          _ = _ := by
            rw [← map_sub, PowerSeries.coeff_C_mul]
      simp only [Nat.cast_add, Nat.cast_one] at hr hleft hright
      rw [hleft, hright] at hr
      have ih' :
          PowerSeries.coeff j (E * h⁻¹ ^ (j + 1)) =
            (-1 : ℂ) ^ j * b⁻¹ * (Nat.choose (n + j) j : ℂ) := by
        simpa [E, h, e] using ih
      have hchoose :
          ((n + j + 1 : ℕ) : ℂ) * (Nat.choose (n + j) j : ℂ) =
            ((j + 1 : ℕ) : ℂ) * (Nat.choose (n + j + 1) (j + 1) : ℂ) := by
        exact_mod_cast (Nat.add_one_mul_choose_eq (n + j) j).trans (mul_comm _ _)
      rw [ih'] at hr
      change PowerSeries.coeff (j + 1) (E * h⁻¹ ^ (j + 2)) = _
      have hjC : ((j + 1 : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero j
      have hfactor :
          (-((n : ℂ) * b) - (j + 1 : ℂ) * b) *
                ((-1 : ℂ) ^ j * b⁻¹ * (Nat.choose (n + j) j : ℂ)) =
            -((n + j + 1 : ℕ) : ℂ) * (-1 : ℂ) ^ j *
              (Nat.choose (n + j) j : ℂ) := by
        field_simp [hb]
        push_cast
        ring
      rw [hfactor] at hr
      have hr' :
          ((j + 1 : ℕ) : ℂ) * b *
                PowerSeries.coeff (j + 1) (E * h⁻¹ ^ (j + 2)) =
            -((n + j + 1 : ℕ) : ℂ) * (-1 : ℂ) ^ j *
              (Nat.choose (n + j) j : ℂ) := by
        push_cast at hr ⊢
        linear_combination hr
      have hscaled :
          ((j + 1 : ℕ) : ℂ) * b *
                PowerSeries.coeff (j + 1) (E * h⁻¹ ^ (j + 2)) =
            ((j + 1 : ℕ) : ℂ) *
              ((-1 : ℂ) ^ (j + 1) *
                (Nat.choose (n + j + 1) (j + 1) : ℂ)) := by
        calc
          _ = -((n + j + 1 : ℕ) : ℂ) * (-1 : ℂ) ^ j *
                (Nat.choose (n + j) j : ℂ) := hr'
          _ = _ := by
            rw [pow_succ]
            linear_combination (-((-1 : ℂ) ^ j)) * hchoose
      have hcancelled :
          b * PowerSeries.coeff (j + 1) (E * h⁻¹ ^ (j + 2)) =
            (-1 : ℂ) ^ (j + 1) *
              (Nat.choose (n + j + 1) (j + 1) : ℂ) := by
        apply mul_left_cancel₀ hjC
        simpa [mul_assoc] using hscaled
      calc
        PowerSeries.coeff (j + 1) (E * h⁻¹ ^ (j + 2)) =
            b⁻¹ * (b * PowerSeries.coeff (j + 1) (E * h⁻¹ ^ (j + 2))) := by
              field_simp [hb]
        _ = b⁻¹ * ((-1 : ℂ) ^ (j + 1) *
              (Nat.choose (n + j + 1) (j + 1) : ℂ)) := by rw [hcancelled]
        _ = (-1 : ℂ) ^ (j + 1) * b⁻¹ *
              (Nat.choose (n + j + 1) (j + 1) : ℂ) := by ring

/-- The finite cofactor jet evaluates the literal local residue polynomials at
the two source sample shifts.  The same statement retains the target
coefficient normalization, including the pole-one factor `M^2`. -/
private lemma sourceLocalRootContributionPolynomial_sample_bridge
    (d : ℕ) (hd : 6 ≤ d) :
    let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1
    let roots := Polynomial.nthRootsFinset M (1 : ℂ)
    ∃ (a : (ζ : ℂ) → Fin (sourcePoleOrder d ζ) → ℂ),
      sourceRootExpansion d =
          ∑ ζ ∈ roots, ∑ j,
            PowerSeries.C (a ζ j) *
              (algebraMap (Polynomial ℂ) (PowerSeries ℂ)
                (Polynomial.X - Polynomial.C ζ))⁻¹ ^ (j.1 + 1) ∧
      (baseSamplePolynomial d).map (Rat.castHom ℂ) =
          ∑ ζ ∈ roots, sourceLocalRootContributionPolynomial d ζ 0 ∧
      (interiorSamplePolynomial d).map (Rat.castHom ℂ) =
          ∑ ζ ∈ roots, sourceLocalRootContributionPolynomial d ζ (-1) ∧
      (∀ k : ℕ,
        (sourceEhrhartPolynomial (d - 1) k).map (Rat.castHom ℂ) =
          (∑ ζ ∈ roots, sourceLocalRootContributionPolynomial d ζ 0) +
            Polynomial.C (k : ℂ) *
              ∑ ζ ∈ roots, sourceLocalRootContributionPolynomial d ζ (-1)) ∧
      (∀ k : ℕ,
        ((sourceEhrhartPolynomial (d - 1) k).map (Rat.castHom ℂ)).coeff (d - 6) =
          (∑ ζ ∈ roots, (sourceLocalRootContributionPolynomial d ζ 0).coeff (d - 6)) +
            (k : ℂ) * ∑ ζ ∈ roots,
              (sourceLocalRootContributionPolynomial d ζ (-1)).coeff (d - 6)) ∧
      (∀ (ζ : ℂ) (c : ℤ), (sourceRootSupport d ζ).card ≤ 6 →
        (sourceLocalRootContributionPolynomial d ζ c).coeff (d - 6) =
          ζ ^ (-c) * (M : ℂ)⁻¹ * ((d - 6).factorial : ℂ)⁻¹ *
            PowerSeries.coeff (6 - (sourceRootSupport d ζ).card)
              (sourceExponentialLocalJet d ζ c)) ∧
      ∀ c : ℤ,
        (sourceLocalRootContributionPolynomial d 1 c).coeff (d - 6) =
          (M : ℂ) ^ 2 * ((d - 6).factorial : ℂ)⁻¹ *
            PowerSeries.coeff 6 (sourcePoleOneNormalizedJet d c) := by
  classical
  dsimp only
  let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1
  let roots := Polynomial.nthRootsFinset M (1 : ℂ)
  have hd1 : 1 ≤ d := by omega
  have hM : 0 < M := Nat.sub_pos_of_lt
    (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester d hd1))
  have hMC :
      (M : ℂ) =
        (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d : ℂ) - 1 := by
    dsimp [M]
    rw [Nat.cast_sub (by omega)]
    norm_num
  obtain ⟨a, ha, hcoeff, hbase, hinterior⟩ :=
    sourceRootExpansion_principalPart_coefficients d hd1
  have hjet := sourceRootExpansion_localCofactor_finiteJet d hd1 a ha
  have hlocal (ζ : ℂ) (hζ : ζ ∈ roots) (t n : ℕ) (c : ℤ)
      (hparameter :
        (t : ℂ) + (c : ℂ) * (M : ℂ)⁻¹ = (n : ℂ) * (M : ℂ)⁻¹) :
      (sourceLocalRootContributionPolynomial d ζ c).eval (t : ℂ) =
        ∑ j : Fin (sourcePoleOrder d ζ),
          a ζ j * (-1 : ℂ) ^ (j.1 + 1) * ζ ^ (-c) *
            (ζ ^ (j.1 + 1))⁻¹ * (Nat.choose (n + j.1) j.1 : ℂ) := by
    have hζpow : ζ ^ M = 1 :=
      (Polynomial.mem_nthRootsFinset hM (1 : ℂ)).mp hζ
    have hζne : ζ ≠ 0 := by
      intro hzero
      have : (0 : ℂ) = 1 := by simpa [hzero, zero_pow hM.ne'] using hζpow
      exact zero_ne_one this
    by_cases hp : sourcePoleOrder d ζ = 0
    · letI : IsEmpty (Fin (sourcePoleOrder d ζ)) :=
        ⟨fun j => by have := j.isLt; omega⟩
      simp [sourceLocalRootContributionPolynomial, hp, Finset.univ_eq_empty]
    · exact (by
        have hpole : 0 < sourcePoleOrder d ζ := Nat.pos_of_ne_zero hp
        have hbelow : sourcePoleOrder d ζ - 1 < sourcePoleOrder d ζ := by omega
        let e := PowerSeries.rescale (-(M : ℂ)⁻¹) (PowerSeries.exp ℂ)
        let h := PowerSeries.mk fun k => PowerSeries.coeff (k + 1) (e - 1)
        let F := PowerSeries.rescale ((n : ℂ) * (M : ℂ)⁻¹) (PowerSeries.exp ℂ)
        let Q := ∑ j : Fin (sourcePoleOrder d ζ),
          PowerSeries.C (a ζ j) *
            PowerSeries.X ^ (sourcePoleOrder d ζ - j.1 - 1) *
              (PowerSeries.C ζ * h)⁻¹ ^ (j.1 + 1)
        have hjetζ :
            PowerSeries.trunc (sourcePoleOrder d ζ) (sourceLocalRegularInverse d ζ) =
              PowerSeries.trunc (sourcePoleOrder d ζ) Q := by
          simpa [M, roots, e, h, Q] using hjet ζ hζ
        have hcombined :
            PowerSeries.rescale (t : ℂ) (PowerSeries.exp ℂ) *
                PowerSeries.rescale ((c : ℂ) * (M : ℂ)⁻¹) (PowerSeries.exp ℂ) = F := by
          rw [PowerSeries.exp_mul_exp_eq_exp_add, hparameter]
        have htransport :
            PowerSeries.coeff (sourcePoleOrder d ζ - 1)
                (F * sourceLocalRegularInverse d ζ) =
              PowerSeries.coeff (sourcePoleOrder d ζ - 1) (F * Q) := by
          calc
            _ = PowerSeries.coeff (sourcePoleOrder d ζ - 1)
                ((PowerSeries.trunc (sourcePoleOrder d ζ) F : PowerSeries ℂ) *
                  (PowerSeries.trunc (sourcePoleOrder d ζ)
                    (sourceLocalRegularInverse d ζ) : PowerSeries ℂ)) :=
              PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc F
                (sourceLocalRegularInverse d ζ) hbelow
            _ = PowerSeries.coeff (sourcePoleOrder d ζ - 1)
                ((PowerSeries.trunc (sourcePoleOrder d ζ) F : PowerSeries ℂ) *
                  (PowerSeries.trunc (sourcePoleOrder d ζ) Q : PowerSeries ℂ)) := by
                    rw [hjetζ]
            _ = _ := (PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc F Q hbelow).symm
        rw [sourceLocalRootContributionPolynomial_eval d t ζ c hpole]
        rw [sourceExponentialLocalJet]
        rw [← hMC]
        rw [← mul_assoc, hcombined]
        rw [htransport]
        dsimp [Q]
        rw [Finset.mul_sum, map_sum]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hshift : j.1 + (sourcePoleOrder d ζ - j.1 - 1) =
            sourcePoleOrder d ζ - 1 := by omega
        have hinversePower :
            (PowerSeries.C ζ * h)⁻¹ ^ (j.1 + 1) =
              PowerSeries.C ((ζ ^ (j.1 + 1))⁻¹) * h⁻¹ ^ (j.1 + 1) := by
          rw [PowerSeries.mul_inv_rev, PowerSeries.C_inv, mul_pow, ← map_pow, inv_pow]
          ring
        rw [hinversePower]
        have hterm :
            PowerSeries.coeff (sourcePoleOrder d ζ - 1)
                (F * (PowerSeries.C (a ζ j) *
                  PowerSeries.X ^ (sourcePoleOrder d ζ - j.1 - 1) *
                    (PowerSeries.C ((ζ ^ (j.1 + 1))⁻¹) * h⁻¹ ^ (j.1 + 1)))) =
              a ζ j * (ζ ^ (j.1 + 1))⁻¹ *
                PowerSeries.coeff j.1 (F * h⁻¹ ^ (j.1 + 1)) := by
          calc
            _ = PowerSeries.coeff (sourcePoleOrder d ζ - 1)
                ((PowerSeries.C (a ζ j * (ζ ^ (j.1 + 1))⁻¹) *
                    (F * h⁻¹ ^ (j.1 + 1))) *
                      PowerSeries.X ^ (sourcePoleOrder d ζ - j.1 - 1)) := by
                        congr 1
                        rw [map_mul]
                        ring
            _ = PowerSeries.coeff j.1
                (PowerSeries.C (a ζ j * (ζ ^ (j.1 + 1))⁻¹) *
                  (F * h⁻¹ ^ (j.1 + 1))) := by
                    rw [← hshift]
                    exact PowerSeries.coeff_mul_X_pow _ _ _
            _ = _ := by rw [PowerSeries.coeff_C_mul]
        rw [hterm]
        have hb : (-(M : ℂ)⁻¹) ≠ 0 := by
          simp [Nat.ne_of_gt hM]
        have hdiag := exponential_dividedDifference_diagonal_coeff
          (-(M : ℂ)⁻¹) hb n j.1
        have hF :
            F = PowerSeries.rescale (-((n : ℂ) * (-(M : ℂ)⁻¹)))
              (PowerSeries.exp ℂ) := by
          dsimp [F]
          congr 2
          ring
        have hdiag' :
            PowerSeries.coeff j.1 (F * h⁻¹ ^ (j.1 + 1)) =
              (-1 : ℂ) ^ j.1 * (-(M : ℂ)⁻¹)⁻¹ *
                (Nat.choose (n + j.1) j.1 : ℂ) := by
          rw [hF]
          simpa [e, h] using hdiag
        rw [hdiag']
        field_simp [Nat.ne_of_gt hM]
        rw [pow_succ]
        ring)
  have hbasePoly :
      (baseSamplePolynomial d).map (Rat.castHom ℂ) =
        ∑ ζ ∈ roots, sourceLocalRootContributionPolynomial d ζ 0 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective
      ((Rat.castHom ℂ).injective.comp Nat.cast_injective)).mono
    rintro _ ⟨t, rfl⟩
    change ((baseSamplePolynomial d).map (Rat.castHom ℂ)).eval
      (Rat.castHom ℂ (t : ℚ)) = _
    rw [Polynomial.eval_map_apply, hbase t, Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro ζ hζ
    symm
    simp only [Function.comp_apply]
    rw [show Rat.castHom ℂ (t : ℚ) = (t : ℂ) by norm_num]
    rw [hlocal ζ hζ t (t * M) 0 (by norm_num; field_simp [Nat.ne_of_gt hM])]
    apply Finset.sum_congr rfl
    intro j hj
    have hζpow := (Polynomial.mem_nthRootsFinset hM (1 : ℂ)).mp hζ
    have hphase : (ζ ^ (t * M + (j.1 + 1)))⁻¹ =
        ζ ^ (-(0 : ℤ)) * (ζ ^ (j.1 + 1))⁻¹ := by
      rw [Nat.mul_comm t M, pow_add, pow_mul, hζpow, one_pow, one_mul]
      simp
    rw [hphase]
    simp only [M, Nat.add_comm]
    ring
  have hinteriorPoly :
      (interiorSamplePolynomial d).map (Rat.castHom ℂ) =
        ∑ ζ ∈ roots, sourceLocalRootContributionPolynomial d ζ (-1) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective
      ((Rat.castHom ℂ).injective.comp (Nat.cast_injective.comp Nat.succ_injective))).mono
    rintro _ ⟨t, rfl⟩
    change ((interiorSamplePolynomial d).map (Rat.castHom ℂ)).eval
      (Rat.castHom ℂ ((t + 1 : ℕ) : ℚ)) = _
    rw [Polynomial.eval_map_apply, hinterior (t + 1) (by omega), Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro ζ hζ
    symm
    simp only [Function.comp_apply]
    rw [show Rat.castHom ℂ (((t + 1 : ℕ) : ℚ)) = ((t + 1 : ℕ) : ℂ) by norm_num]
    have hζpow := (Polynomial.mem_nthRootsFinset hM (1 : ℂ)).mp hζ
    have hζne : ζ ≠ 0 := fun hzero => (zero_ne_one : (0 : ℂ) ≠ 1) (by
      simpa [hzero, zero_pow hM.ne'] using hζpow)
    have hprod : 1 ≤ (t + 1) * M := Nat.mul_pos (by omega) hM
    rw [hlocal ζ hζ (t + 1) ((t + 1) * M - 1) (-1) (by
      rw [show ((-1 : ℤ) : ℂ) = (-1 : ℂ) by norm_num]
      rw [Nat.cast_sub hprod, Nat.cast_mul]
      field_simp [Nat.ne_of_gt hM]
      ring)]
    apply Finset.sum_congr rfl
    intro j hj
    have hphase : (ζ ^ ((t + 1) * M - 1 + (j.1 + 1)))⁻¹ =
        ζ ^ (-(-1 : ℤ)) * (ζ ^ (j.1 + 1))⁻¹ := by
      rw [show (t + 1) * M - 1 + (j.1 + 1) = (t + 1) * M + j.1 by omega]
      rw [Nat.mul_comm (t + 1) M, pow_add, pow_mul, hζpow, one_pow, one_mul]
      simp only [neg_neg, Int.reduceNeg, zpow_one, pow_succ, mul_inv_rev]
      field_simp [hζne]
    rw [hphase]
    simp only [M, Nat.add_comm]
    ring
  have hglobalPoly (k : ℕ) :
      (sourceEhrhartPolynomial (d - 1) k).map (Rat.castHom ℂ) =
        (∑ ζ ∈ roots, sourceLocalRootContributionPolynomial d ζ 0) +
          Polynomial.C (k : ℂ) *
            ∑ ζ ∈ roots, sourceLocalRootContributionPolynomial d ζ (-1) := by
    simp [sourceEhrhartPolynomial, Nat.sub_add_cancel (by omega), hbasePoly, hinteriorPoly]
  have hglobalCoeff (k : ℕ) :
      ((sourceEhrhartPolynomial (d - 1) k).map (Rat.castHom ℂ)).coeff (d - 6) =
        (∑ ζ ∈ roots, (sourceLocalRootContributionPolynomial d ζ 0).coeff (d - 6)) +
          (k : ℂ) * ∑ ζ ∈ roots,
            (sourceLocalRootContributionPolynomial d ζ (-1)).coeff (d - 6) := by
    rw [hglobalPoly, Polynomial.coeff_add, Polynomial.coeff_C_mul]
    simp only [Polynomial.finsetSum_coeff]
  refine ⟨a, by simpa [roots] using ha, hbasePoly, hinteriorPoly,
    hglobalPoly, hglobalCoeff, ?_, ?_⟩
  · intro ζ c hsupport
    rw [hMC]
    exact sourceLocalRootContributionPolynomial_target_coeff d hd ζ c hsupport
  · intro c
    rw [hMC]
    exact sourceLocalRootContributionPolynomial_one_target_coeff d hd c

end D5.S0.FiniteGeometry.SylvesterSimplexEhrhartPrincipalPart
