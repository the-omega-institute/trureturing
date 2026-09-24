/- GID: D5/S0/FiniteGeometry/SylvesterSimplexEhrhartPoleOneBound
   generality: G
   mirror-B: D5/B/S0/FiniteGeometry/SylvesterSimplexEhrhartPoleOneBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S0/FiniteGeometry/SylvesterSimplexEhrhartPoleOneBound.sylvesterSimplex_actual_negative_coeff_of_eight_le; premises=D5/S0/FiniteGeometry/SylvesterSimplexEhrhartGlobalRootBound.fixed_prefix_bounds; result=D5/S0/FiniteGeometry/SylvesterSimplexEhrhartPoleOneBound.sourcePoleOneRootContribution_re_lt
   digest: Negative pole-one sixth jet and actual all-k Ehrhart consumer for d at least eight. -/

import D5.S0.FiniteGeometry.SylvesterSimplexEhrhartGlobalRootBound

set_option linter.style.longLine false

noncomputable section

namespace D5.S0.FiniteGeometry.SylvesterSimplexEhrhartPoleOneBound

open scoped BigOperators

open D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity

open private baseWeight base_axisScale_dvd_mass sylvester_pos
  sylvester_sub_one_eq_prod two_le_sylvester from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity

open private partitionWeight partitionWeight_pos partitionWeight_dvd_period
  sourceEhrhartPolynomial sourceEhrhartPolynomial_eval from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartSamples

open private rootLocalCoordinate_pow_partitionWeight rootDenominatorFactor rootVanishingQuotient
  sourceExponentialLocalJet sourceLocalRegularDenominator sourceLocalRegularInverse
  sourcePoleOneNormalizedJet
  sourceLocalRootContributionPolynomial sourceLocalRootContributionPolynomial_one_target_coeff
  sourceRootSupport sourceVanishingFactors sourceScaleProduct from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartCoefficient

open private rf vf vq vf_coeff sylvester_quotient_sum_for_root_bound from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartRootContributionLowSupportBound

open private sourceLocalRootContributionPolynomial_sample_bridge from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartPrincipalPart

open private fixed_prefix_bounds sylvester_mono_of_le from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartGlobalRootBound

open D5.S0.FiniteGeometry.SylvesterSimplexEhrhartGlobalRootBound

/-- The actual pole at one has a uniformly negative sixth normalized jet. -/
theorem sourcePoleOneRootContribution_re_lt
    (d : Nat) (hd : 8 <= d) (c : Int) (hc : c = 0 \/ c = -1) :
    ((sourceLocalRootContributionPolynomial d 1 c).coeff (d - 6)).re <
      -((sylvester d - 1 : Real)^2 / (600000 * (d - 6).factorial)) := by
  classical
  let M := sylvester d - 1
  have hd1 : 1 <= d := by omega
  have hM : 0 < M := Nat.sub_pos_of_lt
    (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester d hd1))
  have hfactor (j : Option (Fin d)) :
      rootVanishingQuotient d 1 j =
        vq ((((M / partitionWeight d j : Nat) : Complex))⁻¹) := by
    apply PowerSeries.ext
    intro k
    simp only [rootVanishingQuotient, vq, PowerSeries.coeff_mk]
    simp only [rootDenominatorFactor]
    rw [rootLocalCoordinate_pow_partitionWeight d hd1]
    simp [rf, M]
  let b : Option (Fin d) -> Complex := fun j =>
    ((((M / partitionWeight d j : Nat) : Complex))⁻¹)
  have hb (j : Option (Fin d)) : b j ≠ 0 := by
    dsimp [b]
    exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.div_pos
      (Nat.le_of_dvd hM (partitionWeight_dvd_period d hd1 j))
      (partitionWeight_pos d hd1 j))))
  have hvf456 (a : Complex) (ha : a ≠ 0) :
      PowerSeries.coeff 4 (vf a) = -(a ^ 4 / 720) /\
      PowerSeries.coeff 5 (vf a) = 0 /\
      PowerSeries.coeff 6 (vf a) = a ^ 6 / 30240 := by
    as_aux_lemma =>
    have hq0 : PowerSeries.constantCoeff (vq a) = a := by
      rw [<- PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp [vq, rf,
        PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
    have hmul : vf a * vq a = PowerSeries.C a := by
      dsimp [vf]
      rw [mul_assoc, PowerSeries.inv_mul_cancel]
      · simp
      · simpa [hq0] using ha
    rcases vf_coeff a ha with ⟨h0, h1, h2, h3⟩
    have hrec (n : Nat) := congrArg (PowerSeries.coeff n) hmul
    have h4 := hrec 4
    have h5 := hrec 5
    have h6 := hrec 6
    rw [PowerSeries.coeff_mul] at h4 h5 h6
    norm_num [Finset.antidiagonal, vq,
      rf,
      PowerSeries.coeff_rescale, PowerSeries.coeff_exp, h0, h1, h2, h3] at h4 h5 h6
    have hh4 : PowerSeries.coeff 4 (vf a) = -(a ^ 4 / 720) := by
      apply mul_right_cancel₀ ha
      linear_combination h4
    have hh5 : PowerSeries.coeff 5 (vf a) = 0 := by
      apply mul_right_cancel₀ ha
      rw [hh4] at h5
      linear_combination h5
    refine ⟨hh4, hh5, ?_⟩
    apply mul_right_cancel₀ ha
    rw [hh4, hh5] at h6
    linear_combination h6
  let centered : Complex -> PowerSeries Complex := fun a =>
    PowerSeries.rescale (-a / 2) (PowerSeries.exp Complex) * vf a
  have hcentered (a : Complex) (ha : a ≠ 0) :
      PowerSeries.coeff 0 (centered a) = 1 /\
      PowerSeries.coeff 1 (centered a) = 0 /\
      PowerSeries.coeff 2 (centered a) = -(a ^ 2 / 24) /\
      PowerSeries.coeff 3 (centered a) = 0 /\
      PowerSeries.coeff 4 (centered a) = 7 * a ^ 4 / 5760 /\
      PowerSeries.coeff 5 (centered a) = 0 /\
      PowerSeries.coeff 6 (centered a) = -(31 * a ^ 6 / 967680) := by
    as_aux_lemma =>
    rcases vf_coeff a ha with ⟨h0, h1, h2, h3⟩
    rcases hvf456 a ha with ⟨h4, h5, h6⟩
    simp only [centered]
    repeat' first | constructor
    all_goals
      rw [PowerSeries.coeff_mul]
      norm_num [Finset.antidiagonal, PowerSeries.coeff_rescale,
        PowerSeries.coeff_exp, h0, h1, h2, h3, h4, h5, h6]
      try ring
  have hvanishing : sourceVanishingFactors d 1 = Finset.univ := by
    ext j
    simp [sourceVanishingFactors]
  have hsupport : sourceRootSupport d 1 = ∅ := by
    ext j
    simp [sourceRootSupport]
  have hbprod : ∏ j : Option (Fin d), b j = ((M : Complex) ^ 3)⁻¹ := by
    have hscale :
        (∏ j : Option (Fin d),
          ((M / partitionWeight d j : Nat) : Complex)) = (M : Complex) ^ 3 := by
      exact_mod_cast sourceScaleProduct d hd1
    simp only [b]
    rw [Finset.prod_inv_distrib, hscale]
  have hprodInv {s : Finset (Option (Fin d))} (f : Option (Fin d) → PowerSeries Complex) :
      (∏ j ∈ s, f j)⁻¹ = ∏ j ∈ s, (f j)⁻¹ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
        rw [Finset.prod_insert hj, PowerSeries.mul_inv_rev, ih,
          Finset.prod_insert hj, mul_comm]
  have hvfprod :
      (∏ j : Option (Fin d), vf (b j)) =
        PowerSeries.C (((M : Complex) ^ 3)⁻¹) *
          (∏ j : Option (Fin d), vq (b j))⁻¹ := by
    simp_rw [vf]
    rw [Finset.prod_mul_distrib]
    rw [← map_prod]
    rw [hbprod]
    rw [← hprodInv]
  have hMcast : ((sylvester d - 1 : Nat) : Complex) = (M : Complex) := by
    rfl
  have hMdiff : (sylvester d : Complex) - 1 = (M : Complex) := by
    dsimp [M]
    rw [Nat.cast_sub (by omega : 1 ≤ sylvester d)]
    norm_num
  have hsourceProduct :
      sourcePoleOneNormalizedJet d c =
        PowerSeries.rescale ((c : Complex) * (M : Complex)⁻¹)
            (PowerSeries.exp Complex) *
          ∏ j : Option (Fin d), vf (b j) := by
    have hregular : sourceLocalRegularInverse d 1 =
        (∏ j : Option (Fin d), vq (b j))⁻¹ := by
      rw [sourceLocalRegularInverse, sourceLocalRegularDenominator,
        hvanishing, hsupport]
      simp only [Finset.prod_empty, mul_one]
      simp_rw [hfactor]
      simp only [b]
    have hjet : sourceExponentialLocalJet d 1 c =
        PowerSeries.rescale ((c : Complex) * (M : Complex)⁻¹)
            (PowerSeries.exp Complex) *
          (∏ j : Option (Fin d), vq (b j))⁻¹ := by
      rw [sourceExponentialLocalJet, hMdiff, hregular]
    rw [sourcePoleOneNormalizedJet, hMcast, hjet, hvfprod]
    rw [hMdiff]
    ring
  have hprod_moments (s : Finset (Option (Fin d))) :
      let S2 := ∑ j ∈ s, b j ^ 2
      let S4 := ∑ j ∈ s, b j ^ 4
      let S6 := ∑ j ∈ s, b j ^ 6
      let H := ∏ j ∈ s, centered (b j)
      PowerSeries.coeff 0 H = 1 /\
      PowerSeries.coeff 1 H = 0 /\
      PowerSeries.coeff 2 H = -S2 / 24 /\
      PowerSeries.coeff 3 H = 0 /\
      PowerSeries.coeff 4 H = (5 * S2 ^ 2 + 2 * S4) / 5760 /\
      PowerSeries.coeff 5 H = 0 /\
      PowerSeries.coeff 6 H =
        -(35 * S2 ^ 3 + 42 * S2 * S4 + 16 * S6) / 2903040 := by
    as_aux_lemma =>
    induction s using Finset.induction_on with
    | empty => norm_num
    | @insert a s ha ih =>
        dsimp only
        simp only [Finset.sum_insert ha, Finset.prod_insert ha]
        dsimp only at ih
        rcases ih with ⟨p0, p1, p2, p3, p4, p5, p6⟩
        rcases hcentered (b a) (hb a) with ⟨q0, q1, q2, q3, q4, q5, q6⟩
        repeat' first | constructor
        all_goals
          rw [PowerSeries.coeff_mul]
          norm_num [Finset.antidiagonal, p0, p1, p2, p3, p4, p5, p6,
            q0, q1, q2, q3, q4, q5, q6]
          try ring
  let S1 : Complex := ∑ j : Option (Fin d), b j
  let S2 : Complex := ∑ j : Option (Fin d), b j ^ 2
  let S4 : Complex := ∑ j : Option (Fin d), b j ^ 4
  let S6 : Complex := ∑ j : Option (Fin d), b j ^ 6
  let H : PowerSeries Complex := ∏ j : Option (Fin d), centered (b j)
  rcases hprod_moments Finset.univ with ⟨hH0, hH1, hH2, hH3, hH4, hH5, hH6⟩
  change PowerSeries.coeff 0 H = 1 at hH0
  change PowerSeries.coeff 1 H = 0 at hH1
  change PowerSeries.coeff 2 H = -S2 / 24 at hH2
  change PowerSeries.coeff 3 H = 0 at hH3
  change PowerSeries.coeff 4 H = (5 * S2 ^ 2 + 2 * S4) / 5760 at hH4
  change PowerSeries.coeff 5 H = 0 at hH5
  change PowerSeries.coeff 6 H =
    -(35 * S2 ^ 3 + 42 * S2 * S4 + 16 * S6) / 2903040 at hH6
  have huncenter (a : Complex) :
      PowerSeries.rescale (a / 2) (PowerSeries.exp Complex) * centered a = vf a := by
    dsimp [centered]
    rw [← mul_assoc, PowerSeries.exp_mul_exp_eq_exp_add]
    have hexp0 : PowerSeries.rescale 0 (PowerSeries.exp Complex) = 1 := by
      rw [PowerSeries.rescale_zero_apply, PowerSeries.constantCoeff_exp, map_one]
    rw [show a / 2 + -a / 2 = 0 by ring, hexp0, one_mul]
  have hprodUncentered :
      (∏ j : Option (Fin d), vf (b j)) =
        (∏ j : Option (Fin d),
          PowerSeries.rescale (b j / 2) (PowerSeries.exp Complex)) * H := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    exact (huncenter (b j)).symm
  have hprodExp :
      (∏ j : Option (Fin d),
        PowerSeries.rescale (b j / 2) (PowerSeries.exp Complex)) =
          PowerSeries.rescale (S1 / 2) (PowerSeries.exp Complex) := by
    change _ = PowerSeries.rescale
      ((∑ j ∈ (Finset.univ : Finset (Option (Fin d))), b j) / 2)
        (PowerSeries.exp Complex)
    induction (Finset.univ : Finset (Option (Fin d))) using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, ih,
          PowerSeries.exp_mul_exp_eq_exp_add]
        congr 1
        ring_nf
  let X : Complex := 2 * (c : Complex) * (M : Complex)⁻¹ + S1
  have hsourceCentered : sourcePoleOneNormalizedJet d c =
      PowerSeries.rescale (X / 2) (PowerSeries.exp Complex) * H := by
    rw [hsourceProduct, hprodUncentered, hprodExp, ← mul_assoc,
      PowerSeries.exp_mul_exp_eq_exp_add]
    congr 1
    dsimp [X]
    ring_nf
  have hcoeffP :
      PowerSeries.coeff 6 (sourcePoleOneNormalizedJet d c) =
        (63 * X ^ 6 - 315 * X ^ 4 * S2 + 315 * X ^ 2 * S2 ^ 2 -
          35 * S2 ^ 3 + 126 * X ^ 2 * S4 - 42 * S2 * S4 - 16 * S6) /
            2903040 := by
    rw [hsourceCentered, PowerSeries.coeff_mul]
    norm_num [Finset.antidiagonal, PowerSeries.coeff_rescale,
      PowerSeries.coeff_exp, hH0, hH1, hH2, hH3, hH4, hH5, hH6]
    ring
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  let u : Real := (M : Real)⁻¹
  have hsome (i : Fin (n + 1)) :
      M / partitionWeight (n + 1) (some i) = axisScale (n + 1) 0 i := by
    apply Nat.div_eq_of_eq_mul_left (partitionWeight_pos (n + 1) (by omega) (some i))
    rw [partitionWeight, baseWeight]
    simpa [M, Nat.mul_comm] using
      (Nat.div_mul_cancel (base_axisScale_dvd_mass (n + 1) (by omega) i)).symm
  have hbprefix (i : Fin n) :
      b (some i.castSucc) = (((sylvester (i.1 + 1) : Real)⁻¹ : Real) : Complex) := by
    dsimp [b]
    rw [hsome]
    have haxis : axisScale (n + 1) 0 i.castSucc = sylvester (i.1 + 1) := by
      rw [axisScale, if_neg (by simp only [Fin.val_castSucc]; omega)]
      simp
    rw [haxis]
    exact (Complex.ofReal_inv (sylvester (i.1 + 1) : Real)).symm
  have hblast : b (some (Fin.last n)) = (u : Complex) := by
    dsimp [b, u]
    rw [hsome]
    simp [axisScale, M]
  have hbnone : b none = (u : Complex) := by
    dsimp [b, u]
    simp [partitionWeight]
  let R1 : Real := ∑ i : Fin n, (sylvester (i.1 + 1) : Real)⁻¹
  let Y : Real := (∑ i : Fin n, (sylvester (i.1 + 1) : Real)⁻¹ ^ 2) + 2 * u ^ 2
  let Z : Real := (∑ i : Fin n, (sylvester (i.1 + 1) : Real)⁻¹ ^ 4) + 2 * u ^ 4
  let V : Real := (∑ i : Fin n, (sylvester (i.1 + 1) : Real)⁻¹ ^ 6) + 2 * u ^ 6
  have hS1 : S1 = ((R1 + 2 * u : Real) : Complex) := by
    dsimp [S1]
    rw [Fintype.sum_option, Fin.sum_univ_castSucc]
    simp_rw [hbprefix]
    rw [hblast, hbnone]
    dsimp [R1]
    push_cast
    ring
  have hS2 : S2 = (Y : Complex) := by
    dsimp [S2, Y]
    rw [Fintype.sum_option, Fin.sum_univ_castSucc]
    simp_rw [hbprefix]
    rw [hblast, hbnone]
    push_cast
    ring
  have hS4 : S4 = (Z : Complex) := by
    dsimp [S4, Z]
    rw [Fintype.sum_option, Fin.sum_univ_castSucc]
    simp_rw [hbprefix]
    rw [hblast, hbnone]
    push_cast
    ring
  have hS6 : S6 = (V : Complex) := by
    dsimp [S6, V]
    rw [Fintype.sum_option, Fin.sum_univ_castSucc]
    simp_rw [hbprefix]
    rw [hblast, hbnone]
    push_cast
    ring
  have hshift (m : Nat) :
      (∏ j ∈ Finset.range m, sylvester (j + 1)) = sylvester (m + 1) - 1 := by
    induction m with
    | zero => simp [sylvester]
    | succ m ih =>
        rw [Finset.prod_range_succ, ih]
        simp [sylvester, Nat.mul_comm]
  have hR1 : R1 = 1 - u := by
    as_aux_lemma =>
    have hq := sylvester_quotient_sum_for_root_bound n (by omega)
    rw [hshift] at hq
    have hterm (i : Nat) (hi : i ∈ Finset.range n) :
        ((M / sylvester (i + 1) : Nat) : Real) / (M : Real) =
          (sylvester (i + 1) : Real)⁻¹ := by
      have hdvd : sylvester (i + 1) ∣ M := by
        change sylvester (i + 1) ∣ sylvester (n + 1) - 1
        rw [← hshift n]
        exact Finset.dvd_prod_of_mem _ hi
      have hmul := Nat.div_mul_cancel hdvd
      have hmulR :
          ((M / sylvester (i + 1) : Nat) : Real) * sylvester (i + 1) = M := by
        exact_mod_cast hmul
      field_simp [Nat.ne_of_gt hM, Nat.ne_of_gt (sylvester_pos (i + 1))]
      nlinarith
    dsimp [R1]
    change (∑ i : Fin n, (sylvester (i.1 + 1) : Real)⁻¹) = _
    rw [Fin.sum_univ_eq_sum_range
      (fun i => (sylvester (i + 1) : Real)⁻¹)]
    calc
      (∑ i ∈ Finset.range n, (sylvester (i + 1) : Real)⁻¹) =
          ∑ i ∈ Finset.range n,
            ((M / sylvester (i + 1) : Nat) : Real) / (M : Real) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hterm i hi).symm
      _ = (∑ i ∈ Finset.range n,
            ((M / sylvester (i + 1) : Nat) : Real)) / (M : Real) := by
        simp_rw [div_eq_mul_inv]
        rw [Finset.sum_mul]
      _ = ((M - 1 : Nat) : Real) / (M : Real) := by
        rw [← Nat.cast_sum, hq]
      _ = 1 - u := by
        dsimp [u]
        rw [Nat.cast_sub (by omega : 1 ≤ M)]
        norm_num
        field_simp [Nat.ne_of_gt hM]
  let XR : Real := 1 + (2 * (c : Real) + 1) * u
  have hX : X = (XR : Complex) := by
    dsimp [X, XR]
    rw [hS1, hR1]
    dsimp [u]
    have hMinv : (M : Complex)⁻¹ = (((M : Real)⁻¹ : Real) : Complex) :=
      (Complex.ofReal_inv (M : Real)).symm
    rw [hMinv]
    push_cast
    ring
  let P : Real := 63 * XR ^ 6 - 315 * XR ^ 4 * Y + 315 * XR ^ 2 * Y ^ 2 -
    35 * Y ^ 3 + 126 * XR ^ 2 * Z - 42 * Y * Z - 16 * V
  have hcoeffReal :
      PowerSeries.coeff 6 (sourcePoleOneNormalizedJet (n + 1) c) =
        ((P / 2903040 : Real) : Complex) := by
    rw [hcoeffP, hX, hS2, hS4, hS6]
    dsimp [P]
    push_cast
    ring
  clear hfactor b hb hvf456 centered hcentered hvanishing hsupport hbprod hprodInv
    hvfprod hsourceProduct hprod_moments S1 S2 S4 S6 H hH0 hH1 hH2 hH3 hH4 hH5 hH6
    huncenter hprodUncentered hprodExp hX X hsourceCentered hcoeffP hsome hbprefix hblast
    hbnone hS1 hS2 hS4 hS6 hshift
  have hcastProduct (m f : Nat) (p : Real) :
      (((m : Complex) ^ 2 * ((f : Complex))⁻¹ *
        ((p / 2903040 : Real) : Complex))).re =
        (m : Real) ^ 2 * ((f : Real))⁻¹ * (p / 2903040) := by
    as_aux_lemma =>
    have hm : (m : Complex) = ((m : Real) : Complex) := rfl
    have hf : (f : Complex) = ((f : Real) : Complex) := rfl
    rw [hm, hf, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  have htargetReal :
      ((sourceLocalRootContributionPolynomial (n + 1) 1 c).coeff
          (n + 1 - 6)).re =
        (M : Real) ^ 2 * (((n + 1 - 6).factorial : Real))⁻¹ *
          (P / 2903040) := by
    as_aux_lemma =>
    have hbridge := sourceLocalRootContributionPolynomial_one_target_coeff
      (n + 1) (by omega) c
    have hcomplex := hbridge.trans (congrArg (fun z : Complex =>
      ((sylvester (n + 1) : Complex) - 1) ^ 2 *
        (((n + 1 - 6).factorial : Complex))⁻¹ * z) hcoeffReal)
    rw [hMdiff] at hcomplex
    exact (congrArg Complex.re hcomplex).trans
      (hcastProduct M (n + 1 - 6).factorial P)
  clear hcoeffReal hcastProduct hMcast hMdiff
  have hp := fixed_prefix_bounds (n + 1) (by omega)
  have hMlarge : (9000000000000 : Real) < (M : Real) := by
    as_aux_lemma =>
    exact_mod_cast hp.2.2.2
  have hu0 : 0 < u := by
    as_aux_lemma =>
    dsimp [u]
    positivity
  have hu : u < (1 / 1000000000000 : Real) := by
    as_aux_lemma =>
    dsimp [u]
    have hMtarget : (1000000000000 : Real) < (M : Real) := by
      linarith only [hMlarge]
    simpa [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : Real) < 1000000000000)
      hMtarget
  let aR : Nat → Real := fun i => (sylvester (i + 1) : Real)⁻¹
  let B : Real := (sylvester 6 : Real)⁻¹
  have hsyl1 : sylvester 1 = 2 := by norm_num [sylvester]
  have hsyl2 : sylvester 2 = 3 := by norm_num [sylvester]
  have hsyl3 : sylvester 3 = 7 := by norm_num [sylvester]
  have htailRec : (∑ i ∈ Finset.Ico 5 n, aR i) ≤ R1 := by
    as_aux_lemma =>
    dsimp [R1]
    change (∑ i ∈ Finset.Ico 5 n, aR i) ≤
      ∑ i : Fin n, aR i.1
    rw [Fin.sum_univ_eq_sum_range]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [Finset.mem_Ico] at hi
      exact Finset.mem_range.mpr hi.2
    · intro i hi _
      dsimp [aR]
      positivity
  have htail (r : Nat) (hr : 1 ≤ r) :
      (∑ i ∈ Finset.Ico 5 n, aR i ^ r) ≤ B ^ (r - 1) * R1 := by
    as_aux_lemma =>
    calc
      (∑ i ∈ Finset.Ico 5 n, aR i ^ r) ≤
          ∑ i ∈ Finset.Ico 5 n, B ^ (r - 1) * aR i := by
        apply Finset.sum_le_sum
        intro i hi
        have hi5 : 5 ≤ i := (Finset.mem_Ico.mp hi).1
        have hsmono := sylvester_mono_of_le 6 (i + 1) (by omega) (by omega)
        have hspos : (0 : Real) < sylvester 6 := by
          exact_mod_cast sylvester_pos 6
        have hai0 : 0 ≤ aR i := by dsimp [aR]; positivity
        have haiB : aR i ≤ B := by
          dsimp [aR, B]
          simpa [one_div] using one_div_le_one_div_of_le hspos (by exact_mod_cast hsmono)
        have hpow : aR i ^ (r - 1) ≤ B ^ (r - 1) :=
          pow_le_pow_left₀ (by positivity) haiB _
        calc
          aR i ^ r = aR i ^ ((r - 1) + 1) := by
            congr 1
            omega
          _ = aR i ^ (r - 1) * aR i := by rw [pow_add, pow_one]
          _ ≤ B ^ (r - 1) * aR i := mul_le_mul_of_nonneg_right hpow hai0
      _ = B ^ (r - 1) * (∑ i ∈ Finset.Ico 5 n, aR i) := by
        rw [Finset.mul_sum]
      _ ≤ B ^ (r - 1) * R1 :=
        mul_le_mul_of_nonneg_left htailRec (by positivity)
  have hR1pos : 0 < R1 := by
    as_aux_lemma =>
    rw [hR1]
    nlinarith
  have hR1lt : R1 < 1 := by
    as_aux_lemma =>
    rw [hR1]
    linarith
  have hsumPower (r : Nat) (hr : 1 ≤ r) :
      (∑ i : Fin n, (sylvester (i.1 + 1) : Real)⁻¹ ^ r) ≤
        (∑ i ∈ Finset.range 5, aR i ^ r) + B ^ (r - 1) := by
    as_aux_lemma =>
    change (∑ i : Fin n, aR i.1 ^ r) ≤ _
    rw [Fin.sum_univ_eq_sum_range (fun i => aR i ^ r)]
    have hsplit := Finset.sum_range_add_sum_Ico (fun i => aR i ^ r)
      (by omega : 5 ≤ n)
    rw [← hsplit]
    have ht := htail r hr
    have hB0 : 0 ≤ B ^ (r - 1) := by positivity
    have ht' : (∑ i ∈ Finset.Ico 5 n, aR i ^ r) ≤ B ^ (r - 1) :=
      ht.trans (by simpa using mul_le_mul_of_nonneg_left hR1lt.le hB0)
    exact add_le_add_right ht' _
  clear hp hMlarge htailRec htail hR1pos hR1lt hR1 R1
  have hYlower : (7641 / 20000 : Real) < Y := by
    as_aux_lemma =>
    dsimp [Y]
    change (7641 / 20000 : Real) <
      (∑ i : Fin n, aR i.1 ^ 2) + 2 * u ^ 2
    rw [Fin.sum_univ_eq_sum_range (fun i => aR i ^ 2)]
    have hsubset : Finset.range 4 ⊆ Finset.range n := by
      intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    have hlower := Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun i _ _ => by positivity : ∀ i ∈ Finset.range n, i ∉ Finset.range 4 →
        0 ≤ (sylvester (i + 1) : Real)⁻¹ ^ 2)
    have hpref : (7641 / 20000 : Real) <
        ∑ i ∈ Finset.range 4, (sylvester (i + 1) : Real)⁻¹ ^ 2 := by
      norm_num [sylvester, Finset.sum_range_succ]
    exact hpref.trans_le (hlower.trans (le_add_of_nonneg_right (by positivity)))
  have hu2tiny : u ^ 2 < (1 / 1000000000000000000000000 : Real) := by
    as_aux_lemma =>
    calc
      u ^ 2 < (1 / 1000000000000 : Real) ^ 2 :=
        pow_lt_pow_left₀ hu hu0.le (by norm_num)
      _ = (1 / 1000000000000000000000000 : Real) := by norm_num
  have hYupper : Y < (382061 / 1000000 : Real) := by
    as_aux_lemma =>
    have hs := hsumPower 2 (by omega)
    dsimp [Y]
    have hprefix : (∑ i ∈ Finset.range 5, aR i ^ 2) + B +
        2 * u ^ 2 < (382061 / 1000000 : Real) := by
      dsimp [aR, B]
      norm_num [sylvester, Finset.sum_range_succ] at ⊢
      linarith only [hu2tiny]
    exact lt_of_le_of_lt (by simpa [aR, B] using add_le_add_right hs (2 * u ^ 2)) hprefix
  have hXRbounds : (9999 / 10000 : Real) < XR /\
      XR < (10001 / 10000 : Real) := by
    rcases hc with rfl | rfl
    · have hXR : XR = 1 + u := by
        simp [XR]
      rw [hXR]
      constructor <;> linarith only [hu0, hu]
    · have hXR : XR = 1 - u := by
        norm_num [XR]
        simp only [sub_eq_add_neg]
      rw [hXR]
      constructor <;> linarith only [hu0, hu]
  rcases hXRbounds with ⟨hXRlower, hXRupper⟩
  have hZlower : (3763 / 50000 : Real) < Z := by
    as_aux_lemma =>
    dsimp [Z]
    change (3763 / 50000 : Real) <
      (∑ i : Fin n, aR i.1 ^ 4) + 2 * u ^ 4
    rw [Fin.sum_univ_eq_sum_range (fun i => aR i ^ 4)]
    have hsubset : Finset.range 3 ⊆ Finset.range n := by
      intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    have hlower := Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun i _ _ => by positivity : ∀ i ∈ Finset.range n, i ∉ Finset.range 3 →
        0 ≤ (sylvester (i + 1) : Real)⁻¹ ^ 4)
    have hpref : (3763 / 50000 : Real) <
        ∑ i ∈ Finset.range 3, (sylvester (i + 1) : Real)⁻¹ ^ 4 := by
      norm_num [Finset.sum_range_succ, hsyl1, hsyl2, hsyl3]
    exact hpref.trans_le (hlower.trans (le_add_of_nonneg_right (by positivity)))
  have hu1 : u < 1 := by
    as_aux_lemma =>
    linarith only [hu]
  have hu2le : u ^ 2 ≤ u := by
    as_aux_lemma =>
    nlinarith only [mul_nonneg hu0.le (sub_nonneg.mpr hu1.le)]
  have hu2one : u ^ 2 ≤ 1 := by
    as_aux_lemma =>
    exact hu2le.trans hu1.le
  have hu4le : u ^ 4 ≤ u := by
    as_aux_lemma =>
    have h := mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu2one)
    nlinarith only [h, hu2le]
  have hZupper : Z < (75263 / 1000000 : Real) := by
    as_aux_lemma =>
    have hs := hsumPower 4 (by omega)
    dsimp [Z]
    have hprefix : (∑ i ∈ Finset.range 5, aR i ^ 4) + B ^ 3 +
        2 * u < (75263 / 1000000 : Real) := by
      dsimp [aR, B]
      norm_num [sylvester, Finset.sum_range_succ] at ⊢
      linarith only [hu]
    have hsum :
        (∑ i : Fin n, (sylvester (i.1 + 1) : Real)⁻¹ ^ 4) + 2 * u ^ 4 ≤
          ((∑ i ∈ Finset.range 5, aR i ^ 4) + B ^ 3) + 2 * u := by
      exact add_le_add hs (mul_le_mul_of_nonneg_left hu4le (by norm_num))
    exact hsum.trans_lt hprefix
  have hVlower : (3401 / 200000 : Real) < V := by
    as_aux_lemma =>
    dsimp [V]
    change (3401 / 200000 : Real) <
      (∑ i : Fin n, aR i.1 ^ 6) + 2 * u ^ 6
    rw [Fin.sum_univ_eq_sum_range (fun i => aR i ^ 6)]
    have hsubset : Finset.range 3 ⊆ Finset.range n := by
      intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    have hlower := Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun i _ _ => by positivity : ∀ i ∈ Finset.range n, i ∉ Finset.range 3 →
        0 ≤ (sylvester (i + 1) : Real)⁻¹ ^ 6)
    have hpref : (3401 / 200000 : Real) <
        ∑ i ∈ Finset.range 3, (sylvester (i + 1) : Real)⁻¹ ^ 6 := by
      norm_num [Finset.sum_range_succ, hsyl1, hsyl2, hsyl3]
    exact hpref.trans_le (hlower.trans (le_add_of_nonneg_right (by positivity)))
  have hXR0 : 0 ≤ XR := by
    as_aux_lemma =>
    exact le_trans (by norm_num) hXRlower.le
  have hY0 : 0 ≤ Y := by
    as_aux_lemma =>
    exact le_trans (by norm_num) hYlower.le
  have hZ0 : 0 ≤ Z := by
    as_aux_lemma =>
    exact le_trans (by norm_num) hZlower.le
  have hX6 : XR ^ 6 ≤ (10001 / 10000 : Real) ^ 6 := by
    as_aux_lemma =>
    exact pow_le_pow_left₀ hXR0 hXRupper.le _
  have hX4Y : (9999 / 10000 : Real) ^ 4 * (7641 / 20000 : Real) ≤ XR ^ 4 * Y := by
    as_aux_lemma =>
    calc
      _ ≤ XR ^ 4 * (7641 / 20000 : Real) :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by norm_num) hXRlower.le _) (by norm_num)
      _ ≤ XR ^ 4 * Y := mul_le_mul_of_nonneg_left hYlower.le (by positivity)
  have hX2Y2 : XR ^ 2 * Y ^ 2 ≤
      (10001 / 10000 : Real) ^ 2 * (382061 / 1000000 : Real) ^ 2 := by
    as_aux_lemma =>
    exact mul_le_mul
      (pow_le_pow_left₀ hXR0 hXRupper.le _)
      (pow_le_pow_left₀ hY0 hYupper.le _) (by positivity) (by positivity)
  have hY3 : (7641 / 20000 : Real) ^ 3 ≤ Y ^ 3 := by
    as_aux_lemma =>
    exact pow_le_pow_left₀ (by norm_num) hYlower.le _
  have hX2Z : XR ^ 2 * Z ≤
      (10001 / 10000 : Real) ^ 2 * (75263 / 1000000 : Real) := by
    as_aux_lemma =>
    exact mul_le_mul (pow_le_pow_left₀ hXR0 hXRupper.le _) hZupper.le
      hZ0 (by positivity)
  have hYZ : (7641 / 20000 : Real) * (3763 / 50000 : Real) ≤ Y * Z := by
    as_aux_lemma =>
    exact mul_le_mul hYlower.le hZlower.le (by norm_num) hY0
  have hP : P ≤
      (-5216316273642692209644937 / 1000000000000000000000000 : Real) := by
    as_aux_lemma =>
    calc
      P ≤ 63 * (10001 / 10000 : Real) ^ 6 -
          315 * ((9999 / 10000 : Real) ^ 4 * (7641 / 20000 : Real)) +
          315 * ((10001 / 10000 : Real) ^ 2 * (382061 / 1000000 : Real) ^ 2) -
          35 * (7641 / 20000 : Real) ^ 3 +
          126 * ((10001 / 10000 : Real) ^ 2 * (75263 / 1000000 : Real)) -
          42 * ((7641 / 20000 : Real) * (3763 / 50000 : Real)) -
          16 * (3401 / 200000 : Real) := by
            dsimp [P]
            linarith only [hX6, hX4Y, hX2Y2, hY3, hX2Z, hYZ, hVlower]
      _ = (-5216316273642692209644937 /
          1000000000000000000000000 : Real) := by norm_num
  have hPfive : P < -5 := by
    as_aux_lemma =>
    exact hP.trans_lt (by norm_num)
  have hjet : P / 2903040 < -(1 / 600000 : Real) := by
    as_aux_lemma =>
    rw [div_lt_iff₀ (by norm_num : (0 : Real) < 2903040)]
    exact hPfive.trans (by norm_num)
  have hscale : 0 < (M : Real) ^ 2 * (((n + 1 - 6).factorial : Real))⁻¹ := by
    as_aux_lemma =>
    positivity
  rw [htargetReal]
  calc
    (M : Real) ^ 2 * ((n + 1 - 6).factorial : Real)⁻¹ * (P / 2903040) <
        (M : Real) ^ 2 * ((n + 1 - 6).factorial : Real)⁻¹ *
          (-(1 / 600000 : Real)) := mul_lt_mul_of_pos_left hjet hscale
    _ = -((sylvester (n + 1) - 1 : Real) ^ 2 /
        (600000 * (n + 1 - 6).factorial)) := by
          dsimp [M]
          rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (sylvester_pos (n + 1))))]
          push_cast
          ring

/-- Every actual Sylvester-simplex Ehrhart count in dimension at least eight has
a representing polynomial whose sixth-from-top coefficient is negative. -/
theorem sylvesterSimplex_actual_negative_coeff_of_eight_le
    (d k : Nat) (hd : 8 <= d) :
    ∃ E : Polynomial Rat,
      (∀ t : Nat, E.eval (t : Rat) = (ehrhartCount d k t : Rat)) /\
        E.coeff (d - 6) < 0 := by
  classical
  let M := sylvester d - 1
  let roots := Polynomial.nthRootsFinset M (1 : Complex)
  have hM : 0 < M := Nat.sub_pos_of_lt
    (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester d (by omega)))
  have hsyl : 1 <= sylvester d := by omega
  have hone : (1 : Complex) ∈ roots := by
    exact Polynomial.one_mem_nthRootsFinset hM
  obtain ⟨a, ha, hbase, hinterior, hpoly, hcoeff, hlocal, hpoleCoeff⟩ :=
    sourceLocalRootContributionPolynomial_sample_bridge d (by omega)
  clear hpoleCoeff hlocal hpoly hinterior hbase ha a
  have hsumNeg (c : Int) (hc : c = 0 \/ c = -1) :
      ((∑ z ∈ roots,
        (sourceLocalRootContributionPolynomial d z c).coeff (d - 6))).re < 0 := by
    as_aux_lemma =>
    let q : Real := (M : Real) ^ 2 / ((d - 6).factorial : Real)
    have hq : 0 < q := by
      dsimp [q]
      positivity
    have hpole :
        ((sourceLocalRootContributionPolynomial d 1 c).coeff (d - 6)).re <
          -(q / 600000) := by
      calc
        _ < -((sylvester d - 1 : Real) ^ 2 /
            (600000 * (d - 6).factorial)) :=
          sourcePoleOneRootContribution_re_lt d hd c hc
        _ = -(q / 600000) := by
          dsimp [q, M]
          rw [Nat.cast_sub hsyl]
          push_cast
          ring
    have hnorm :
        (∑ z ∈ roots.erase 1,
          ‖(sourceLocalRootContributionPolynomial d z c).coeff (d - 6)‖) <
            q / 1900000 := by
      calc
        _ < (sylvester d - 1 : Real) ^ 2 /
            (1900000 * (d - 6).factorial) :=
          sourceNontrivialRootContribution_norm_sum_lt d hd c hc
        _ = q / 1900000 := by
          dsimp [q, M]
          rw [Nat.cast_sub hsyl]
          push_cast
          ring
    have herased :
        ((∑ z ∈ roots.erase 1,
          (sourceLocalRootContributionPolynomial d z c).coeff (d - 6))).re <=
            ∑ z ∈ roots.erase 1,
              ‖(sourceLocalRootContributionPolynomial d z c).coeff (d - 6)‖ :=
      (Complex.re_le_norm _).trans (norm_sum_le _ _)
    rw [← Finset.sum_erase_add roots
      (fun z => (sourceLocalRootContributionPolynomial d z c).coeff (d - 6)) hone]
    change
      ((∑ z ∈ roots.erase 1,
          (sourceLocalRootContributionPolynomial d z c).coeff (d - 6))).re +
        ((sourceLocalRootContributionPolynomial d 1 c).coeff (d - 6)).re < 0
    calc
      _ <= (∑ z ∈ roots.erase 1,
          ‖(sourceLocalRootContributionPolynomial d z c).coeff (d - 6)‖) +
            ((sourceLocalRootContributionPolynomial d 1 c).coeff (d - 6)).re :=
        add_le_add_left herased _
      _ < q / 1900000 + (-(q / 600000)) := add_lt_add hnorm hpole
      _ < 0 := by linarith only [hq]
  have hsum0 := hsumNeg 0 (Or.inl rfl)
  have hsumNegOne := hsumNeg (-1) (Or.inr rfl)
  have hcoeffMapped := congrArg Complex.re (hcoeff k)
  have hcoeffReal :
      (((sourceEhrhartPolynomial (d - 1) k).coeff (d - 6) : Rat) : Real) =
        ((∑ z ∈ roots,
            (sourceLocalRootContributionPolynomial d z 0).coeff (d - 6))).re +
          (k : Real) *
            ((∑ z ∈ roots,
              (sourceLocalRootContributionPolynomial d z (-1)).coeff (d - 6))).re := by
    simpa [roots, M, Polynomial.coeff_map] using hcoeffMapped
  have hk0 : (0 : Real) <= k := by positivity
  have hweighted :
      (k : Real) *
          ((∑ z ∈ roots,
            (sourceLocalRootContributionPolynomial d z (-1)).coeff (d - 6))).re <= 0 :=
    mul_nonpos_of_nonneg_of_nonpos hk0 hsumNegOne.le
  have hcoeffRealNeg :
      (((sourceEhrhartPolynomial (d - 1) k).coeff (d - 6) : Rat) : Real) < 0 := by
    rw [hcoeffReal]
    linarith only [hsum0, hweighted]
  have hcoeffRatNeg :
      (sourceEhrhartPolynomial (d - 1) k).coeff (d - 6) < 0 := by
    exact_mod_cast hcoeffRealNeg
  refine ⟨sourceEhrhartPolynomial (d - 1) k, ?_, hcoeffRatNeg⟩
  intro t
  simpa [Nat.sub_add_cancel (by omega : 1 <= d)] using
    sourceEhrhartPolynomial_eval (d - 1) k t

end D5.S0.FiniteGeometry.SylvesterSimplexEhrhartPoleOneBound
