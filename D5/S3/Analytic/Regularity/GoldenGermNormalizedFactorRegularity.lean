/- GID: D5/S3/Analytic/Regularity/GoldenGermNormalizedFactorRegularity
   generality: I
   mirror-B: D5/B/S3/Analytic/Regularity/GoldenGermNormalizedFactorRegularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The normalized golden germ is holomorphic above 1/phi^3 and continuous at 1/phi^2. -/

/- Library-search audit trail (2026-08-28):
   * Searches over D5 and Blueprint for normalized golden-germ regularity found
     pointwise summability in `GoldenGermZetaFactorization`, raw-product
     holomorphy on `Re s > 1 / phi^2` in `GermProductAnalytic`, and the boundary
     reduction in `GoldenGermZetaBoundary`, but no public continuity theorem for
     the normalized product on the wider half-plane.
   * The factorization proof has private cancellation and shifted-tail helpers;
     `germLocalFactor_eq_one_add` is public only on `Re s > 1 / phi^2`.
     Consequently neither result exposes the uniform wider-half-plane estimate
     needed here.
   * Pinned Mathlib supplies `hasProdLocallyUniformlyOn_one_add`,
     `Complex.differentiableOn_tsum_of_summable_norm`,
     `TendstoLocallyUniformlyOn.differentiableOn`, and
     `Nat.Primes.summable_rpow`; no theorem specialized to this cancellation
     family was found.

   STOPPING JUSTIFICATION: this node proves all four regularity rungs, including
   holomorphy on `Re s > 1 / phi^3`, but does not state the downstream
   singularity conclusion for the continued germ. The next input is a distinct
   theorem combining boundary continuity here with the identities, transported
   zeta residue, and nonvanishing recorded by `GoldenGermZetaBoundary`. It also
   makes no regularity or convergence claim at or left of `Re s = 1 / phi^3`. -/

import D5.S3.Analytic.EulerGerm.GermProductBound

namespace D5.S3.Analytic.Regularity.GoldenGermNormalizedFactorRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor

noncomputable section

private theorem phi_cubed :
    Real.goldenRatio ^ 3 = 2 + Real.sqrt 5 := by
  have h5 : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  rw [Real.goldenRatio]
  nlinarith [h5, Real.sqrt_nonneg 5]

private theorem shifted_growth (k : ℕ) :
    Real.goldenRatio ^ 3 + 2 * (k : ℝ) ≤ o5Beta (k + 2) := by
  have h5 : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hlow : (2.23 : ℝ) < Real.sqrt 5 := by
    have : ((2.23 : ℝ)) ^ 2 < 5 := by norm_num
    nlinarith [h5, Real.sqrt_nonneg 5]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [Nat.cast_zero, mul_zero, add_zero]
    exact le_of_eq o5_beta_power_law.2.1.symm
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hg := o5_beta_growth (k + 2)
    have hcast : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by
      push_cast
      ring
    rw [hcast] at hg
    have hinv : 1 / Real.goldenRatio = (Real.sqrt 5 - 1) / 2 := by
      rw [Real.goldenRatio]
      have hpos : (0 : ℝ) < 1 + Real.sqrt 5 := by
        nlinarith [Real.sqrt_nonneg 5]
      field_simp
      nlinarith [h5, Real.sqrt_nonneg 5]
    rw [hinv] at hg
    rw [phi_cubed]
    nlinarith [hg, hlow, hk1]

private theorem shifted_prime_part (sigma : ℝ)
    (h : 1 / Real.goldenRatio ^ 3 < sigma) :
    Summable (fun p : Nat.Primes =>
      (p : ℝ) ^ (-sigma * Real.goldenRatio ^ 3)) := by
  have hphi : (0 : ℝ) < Real.goldenRatio ^ 3 := by
    positivity
  rw [Nat.Primes.summable_rpow]
  rw [div_lt_iff₀ hphi] at h
  nlinarith [h]

private theorem shifted_geometric_part (sigma : ℝ) (hs : 0 < sigma) :
    Summable (fun k : ℕ => ((2 : ℝ) ^ (-2 * sigma)) ^ k) := by
  refine summable_geometric_of_lt_one (by positivity) ?_
  have : ((2 : ℝ) ^ (-2 * sigma)) < (2 : ℝ) ^ (0 : ℝ) := by
    refine Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ?_
    nlinarith [hs]
  simpa using this

private theorem shifted_pow_identity (sigma : ℝ) (k : ℕ) :
    ((2 : ℝ) ^ (-2 * sigma)) ^ k =
      (2 : ℝ) ^ (-2 * sigma * (k : ℝ)) := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (-2 * sigma)) k,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

private theorem shifted_real_summable (sigma : ℝ)
    (h : 1 / Real.goldenRatio ^ 3 < sigma) :
    Summable (fun q : Nat.Primes × ℕ =>
      (q.1 : ℝ) ^ (-sigma * o5Beta (q.2 + 2))) := by
  have hs : 0 < sigma := lt_trans (by positivity) h
  have hmaj := (shifted_prime_part sigma h).mul_of_nonneg
    (shifted_geometric_part sigma hs)
    (fun p => Real.rpow_nonneg (by positivity) _)
    (fun k => pow_nonneg (Real.rpow_nonneg (by norm_num) _) k)
  refine hmaj.of_nonneg_of_le
    (fun q => Real.rpow_nonneg (by positivity) _) ?_
  rintro ⟨p, k⟩
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast p.prop.one_lt.le
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast p.prop.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hstep : -sigma * o5Beta (k + 2) ≤
      -sigma * Real.goldenRatio ^ 3 + -2 * sigma * (k : ℝ) := by
    nlinarith [shifted_growth k, hs]
  calc
    (p : ℝ) ^ (-sigma * o5Beta (k + 2)) ≤
        (p : ℝ) ^
          (-sigma * Real.goldenRatio ^ 3 + -2 * sigma * (k : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hp1 hstep
    _ = (p : ℝ) ^ (-sigma * Real.goldenRatio ^ 3) *
          (p : ℝ) ^ (-2 * sigma * (k : ℝ)) :=
      Real.rpow_add hppos _ _
    _ ≤ (p : ℝ) ^ (-sigma * Real.goldenRatio ^ 3) *
          ((2 : ℝ) ^ (-2 * sigma)) ^ k := by
      refine mul_le_mul_of_nonneg_left ?_
        (Real.rpow_nonneg (by positivity) _)
      rw [shifted_pow_identity sigma k]
      refine Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 ?_
      nlinarith [hs, Nat.cast_nonneg (α := ℝ) k]

private theorem shifted_norm_summable (s : ℂ)
    (hs : 1 / Real.goldenRatio ^ 3 < s.re) :
    Summable (fun q : Nat.Primes × ℕ =>
      ‖(q.1 : ℂ) ^ (-s * (o5Beta (q.2 + 2) : ℂ))‖) := by
  refine (shifted_real_summable s.re hs).congr fun q => ?_
  rw [Complex.norm_natCast_cpow_of_pos q.1.prop.pos]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

private theorem local_factor_eq_first_order_and_tail (s : ℂ)
    (hs : 1 / Real.goldenRatio ^ 3 < s.re) (p : Nat.Primes) :
    germLocalFactor s p =
      1 + (p : ℂ) ^
          (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ)) +
        ∑' k : ℕ, (p : ℂ) ^ (-s * (o5Beta (k + 2) : ℂ)) := by
  let f : ℕ → ℂ := fun v =>
    (p : ℂ) ^ (-s * (o5Beta v : ℂ))
  have htail : Summable (fun k : ℕ => f (k + 2)) := by
    simpa [f, Nat.add_comm] using
      ((shifted_norm_summable s hs).prod_factor p).of_norm
  have hall : Summable f := (summable_nat_add_iff 2).1 htail
  rw [germLocalFactor, show (fun v : ℕ =>
      (p : ℂ) ^ (-s * (o5Beta v : ℂ))) = f from rfl,
    ← hall.sum_add_tsum_nat_add 2]
  simp [f, Finset.sum_range_succ,
    D5.S3.Analytic.EulerGerm.GoldenLocalFactor.o5_beta_zero,
    o5_beta_power_law.1, Real.goldenRatio_sq, add_assoc]

private theorem first_mode_square_summable (sigma : ℝ)
    (hsigma : 1 / Real.goldenRatio ^ 3 < sigma) :
    Summable (fun p : Nat.Primes =>
      ‖((p : ℂ) ^
        (-(sigma : ℂ) * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) ^ 2‖) := by
  have hsigma_pos : 0 < sigma := lt_trans (by positivity) hsigma
  have hphi2 : 0 < Real.goldenRatio ^ 2 := by positivity
  have hphi3_lt : Real.goldenRatio ^ 3 < 2 * Real.goldenRatio ^ 2 := by
    calc
      Real.goldenRatio ^ 3 =
          Real.goldenRatio ^ 2 * Real.goldenRatio := by ring
      _ < Real.goldenRatio ^ 2 * 2 :=
        mul_lt_mul_of_pos_left Real.goldenRatio_lt_two hphi2
      _ = 2 * Real.goldenRatio ^ 2 := by ring
  have hcritical : 1 < sigma * Real.goldenRatio ^ 3 :=
    (div_lt_iff₀ (by positivity : 0 < Real.goldenRatio ^ 3)).mp
      (by simpa [div_eq_mul_inv] using hsigma)
  have hexponent : -sigma * Real.goldenRatio ^ 2 * 2 < -1 := by
    have := mul_lt_mul_of_pos_left hphi3_lt hsigma_pos
    nlinarith
  refine (Nat.Primes.summable_rpow.mpr hexponent).congr fun p => ?_
  rw [norm_pow, Complex.norm_natCast_cpow_of_pos p.prop.pos]
  rw [show (-(sigma : ℂ) *
      ((Real.goldenRatio ^ 2 : ℝ) : ℂ)).re =
        -sigma * Real.goldenRatio ^ 2 by norm_num]
  exact Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ (p : ℝ))
    (-sigma * Real.goldenRatio ^ 2) 2

private theorem first_mode_norm_le_one (s : ℂ)
    (hs : 1 / Real.goldenRatio ^ 3 < s.re) (p : Nat.Primes) :
    ‖(p : ℂ) ^
        (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))‖ ≤ 1 := by
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  rw [show (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ)).re =
      -s.re * Real.goldenRatio ^ 2 by norm_num]
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast p.prop.one_le)
    (by nlinarith [sq_pos_of_pos Real.goldenRatio_pos])

private theorem uniform_majorant (sigma : ℝ)
    (hsigma : 1 / Real.goldenRatio ^ 3 < sigma) :
    ∃ u : Nat.Primes → ℝ, Summable u ∧
      ∀ p : Nat.Primes, ∀ s : ℂ, sigma < s.re →
        ‖(1 - (p : ℂ) ^
              (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) *
            germLocalFactor s p - 1‖ ≤ u p := by
  let tailBound : Nat.Primes → ℝ := fun p =>
    ∑' k : ℕ,
      ‖(p : ℂ) ^
        (-(sigma : ℂ) * (o5Beta (k + 2) : ℂ))‖
  let squareBound : Nat.Primes → ℝ := fun p =>
    ‖((p : ℂ) ^
      (-(sigma : ℂ) * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) ^ 2‖
  let u : Nat.Primes → ℝ := fun p =>
    2 * tailBound p + squareBound p
  have hsigmaNorm := shifted_norm_summable (sigma : ℂ) (by simpa using hsigma)
  have htailBound : Summable tailBound := by
    simpa [tailBound] using hsigmaNorm.prod
  have hsquareBound : Summable squareBound := by
    simpa [squareBound] using first_mode_square_summable sigma hsigma
  have hu : Summable u := by
    exact (htailBound.mul_left 2).add hsquareBound
  refine ⟨u, hu, ?_⟩
  intro p s hssigma
  have hs : 1 / Real.goldenRatio ^ 3 < s.re := hsigma.trans hssigma
  let a : ℂ := (p : ℂ) ^
    (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))
  let tail : ℂ := ∑' k : ℕ,
    (p : ℂ) ^ (-s * (o5Beta (k + 2) : ℂ))
  have hsNorm := shifted_norm_summable s hs
  have htail : ‖tail‖ ≤ tailBound p := by
    refine (norm_tsum_le_tsum_norm (hsNorm.prod_factor p)).trans ?_
    exact (hsNorm.prod_factor p).tsum_le_tsum
      (fun k =>
        D5.S3.Analytic.EulerGerm.GermProductBound.germ_mode_norm_le
          sigma s hssigma.le p (k + 2))
      (hsigmaNorm.prod_factor p)
  have haSigma : ‖a‖ ≤
      ‖(p : ℂ) ^
        (-(sigma : ℂ) * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))‖ := by
    simpa [a, o5_beta_power_law.1] using
      (D5.S3.Analytic.EulerGerm.GermProductBound.germ_mode_norm_le
        sigma s hssigma.le p 1)
  have haOne : ‖a‖ ≤ 1 := by
    simpa [a] using first_mode_norm_le_one s hs p
  have haSquare : ‖a ^ 2‖ ≤ squareBound p := by
    dsimp [squareBound]
    simp only [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg a) haSigma 2
  have haTail : ‖a * tail‖ ≤ tailBound p := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg tail) haOne).trans htail
  have hrewrite :
      (1 - (p : ℂ) ^
            (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) *
          germLocalFactor s p - 1 = tail - a ^ 2 - a * tail := by
    rw [local_factor_eq_first_order_and_tail s hs p]
    dsimp [a, tail]
    ring
  rw [hrewrite]
  calc
    ‖tail - a ^ 2 - a * tail‖ ≤
        ‖tail‖ + ‖a ^ 2‖ + ‖a * tail‖ := by
      calc
        ‖tail - a ^ 2 - a * tail‖ ≤
            ‖tail - a ^ 2‖ + ‖a * tail‖ := norm_sub_le _ _
        _ ≤ ‖tail‖ + ‖a ^ 2‖ + ‖a * tail‖ := by
          gcongr
          exact norm_sub_le _ _
    _ ≤ tailBound p + squareBound p + tailBound p :=
      add_le_add (add_le_add htail haSquare) haTail
    _ = u p := by
      dsimp [u]
      ring

private theorem germLocalFactor_differentiableOn (p : Nat.Primes)
    (sigma : ℝ) (hsigma : 1 / Real.goldenRatio ^ 3 < sigma) :
    DifferentiableOn ℂ (fun s : ℂ => germLocalFactor s p)
      {s : ℂ | sigma < s.re} := by
  let U : Set ℂ := {s : ℂ | sigma < s.re}
  let v : ℕ → ℝ := fun k =>
    ‖(p : ℂ) ^ (-(sigma : ℂ) * (o5Beta k : ℂ))‖
  have htail : Summable (fun k : ℕ => v (k + 2)) := by
    simpa [v] using
      (shifted_norm_summable (sigma : ℂ) (by simpa using hsigma)).prod_factor p
  have hv : Summable v := (summable_nat_add_iff 2).1 htail
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hterms : ∀ k : ℕ, DifferentiableOn ℂ
      (fun s : ℂ => (p : ℂ) ^ (-s * (o5Beta k : ℂ))) U := by
    intro k
    have hbase : (p : ℂ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
    exact ((differentiable_id.neg.mul_const (o5Beta k : ℂ)).const_cpow
      (.inl hbase)).differentiableOn
  have hsum := Complex.differentiableOn_tsum_of_summable_norm hv hterms hU
    (fun k s hs =>
      D5.S3.Analytic.EulerGerm.GermProductBound.germ_mode_norm_le
        sigma s hs.le p k)
  simpa [germLocalFactor, U, v] using hsum

private theorem normalized_product_differentiableOn (sigma : ℝ)
    (hsigma : 1 / Real.goldenRatio ^ 3 < sigma) :
    DifferentiableOn ℂ
      (fun s : ℂ => ∏' p : Nat.Primes,
        (1 - (p : ℂ) ^
            (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) *
          germLocalFactor s p)
      {s : ℂ | sigma < s.re} := by
  let U : Set ℂ := {s : ℂ | sigma < s.re}
  let f : Nat.Primes → ℂ → ℂ := fun p s =>
    (1 - (p : ℂ) ^
        (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) *
      germLocalFactor s p - 1
  obtain ⟨u, hu, hbound⟩ := uniform_majorant sigma hsigma
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hfactor : ∀ p : Nat.Primes, DifferentiableOn ℂ (f p) U := by
    intro p
    have hbase : (p : ℂ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
    have hfirst : Differentiable ℂ (fun s : ℂ =>
        (p : ℂ) ^
          (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) :=
      (differentiable_id.neg.mul_const
        ((Real.goldenRatio ^ 2 : ℝ) : ℂ)).const_cpow (.inl hbase)
    have hone : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) U :=
      differentiableOn_const (c := (1 : ℂ))
    exact (((hone.sub hfirst.differentiableOn).mul
      (germLocalFactor_differentiableOn p sigma hsigma)).sub hone)
  have hcts : ∀ p : Nat.Primes, ContinuousOn (f p) U := fun p =>
    (hfactor p).continuousOn
  have hprod := hu.hasProdLocallyUniformlyOn_one_add hU
    (Filter.Eventually.of_forall fun p s hs => hbound p s hs) hcts
  have hfinite : ∀ J : Finset Nat.Primes,
      DifferentiableOn ℂ (fun s : ℂ => ∏ p ∈ J, (1 + f p s)) U := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
        simp only [Finset.prod_empty]
        exact differentiableOn_const (c := (1 : ℂ))
    | @insert p J hp ih =>
        simp only [Finset.prod_insert hp]
        have hone : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) U :=
          differentiableOn_const (c := (1 : ℂ))
        exact ((hone.add (hfactor p)).mul ih)
  have hlimit := hprod.differentiableOn
    (Filter.Eventually.of_forall hfinite) hU
  simpa [f, U] using hlimit

/-- The cancellation of the first excited golden mode gives a uniform
summable majorant and makes the normalized Euler product holomorphic on
`Re s > 1 / phi^3`. In particular it is continuous at `1 / phi^2`. -/
theorem golden_germ_normalized_factor_regularity :
    let G : ℂ → ℂ := fun s =>
      ∏' p : Nat.Primes,
        (1 - (p : ℂ) ^
            (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) *
          germLocalFactor s p
    (∀ sigma : ℝ, 1 / Real.goldenRatio ^ 3 < sigma →
      ∃ u : Nat.Primes → ℝ, Summable u ∧
        ∀ p : Nat.Primes, ∀ s : ℂ, sigma < s.re →
          ‖(1 - (p : ℂ) ^
                (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) *
              germLocalFactor s p - 1‖ ≤ u p) ∧
    ContinuousOn G {s : ℂ | 1 / Real.goldenRatio ^ 3 < s.re} ∧
    ContinuousAt G ((1 / Real.goldenRatio ^ 2 : ℝ) : ℂ) ∧
    AnalyticOnNhd ℂ G {s : ℂ | 1 / Real.goldenRatio ^ 3 < s.re} := by
  dsimp only
  let K : Set ℂ := {s : ℂ | 1 / Real.goldenRatio ^ 3 < s.re}
  have hK : IsOpen K := isOpen_lt continuous_const Complex.continuous_re
  have hanalytic : AnalyticOnNhd ℂ
      (fun s : ℂ => ∏' p : Nat.Primes,
        (1 - (p : ℂ) ^
            (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) *
          germLocalFactor s p) K := by
    intro s hs
    change 1 / Real.goldenRatio ^ 3 < s.re at hs
    let sigma : ℝ := (1 / Real.goldenRatio ^ 3 + s.re) / 2
    have hsigma : 1 / Real.goldenRatio ^ 3 < sigma := by
      dsimp [sigma]
      linarith
    have hssigma : sigma < s.re := by
      dsimp [sigma]
      linarith
    have hU : IsOpen {z : ℂ | sigma < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    exact (normalized_product_differentiableOn sigma hsigma).analyticAt
      (hU.mem_nhds hssigma)
  have hcontinuous : ContinuousOn
      (fun s : ℂ => ∏' p : Nat.Primes,
        (1 - (p : ℂ) ^
            (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) *
          germLocalFactor s p) K :=
    hanalytic.continuousOn
  have hthreshold :
      1 / Real.goldenRatio ^ 3 < 1 / Real.goldenRatio ^ 2 := by
    apply one_div_lt_one_div_of_lt (pow_pos Real.goldenRatio_pos 2)
    nlinarith [Real.one_lt_goldenRatio,
      sq_pos_of_pos Real.goldenRatio_pos]
  have hboundary : ContinuousAt
      (fun s : ℂ => ∏' p : Nat.Primes,
        (1 - (p : ℂ) ^
            (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) *
          germLocalFactor s p)
      ((1 / Real.goldenRatio ^ 2 : ℝ) : ℂ) := by
    apply hcontinuous.continuousAt
    apply hK.mem_nhds
    change 1 / Real.goldenRatio ^ 3 < 1 / Real.goldenRatio ^ 2
    exact hthreshold
  exact ⟨uniform_majorant, hcontinuous, hboundary, hanalytic⟩

#print axioms golden_germ_normalized_factor_regularity

end

end D5.S3.Analytic.Regularity.GoldenGermNormalizedFactorRegularity
