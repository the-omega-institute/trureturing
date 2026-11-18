/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original four-point Laurent diagonal descends to a negative-square analytic germ. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeNormal

/-! The original energy diagonal in the negative square of the sewing coordinate. -/

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators Topology TensorProduct NNReal
open Filter Metric

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChargeGerm

open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open LatticeTwistedGroundRealization LatticeInvolution LatticeHalfFockGradedTrace
open HalfFock.LatticeHalfFockParityField OperatorAlgebra
open LatticeHalfFockChargedTensorCoefficients LatticeTwistedGroundRealization.SignQuotient
open OriginalFourMChargeCoset OriginalFourMEnergyCoefficient OriginalFourMChargeNormal
open OriginalGaussianSewnAnalytic
open private sewn_term_diff projectOccupations cosetSeries_sewnTaylor
  from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeNormal
open private groundForm from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset

private theorem analytic_neg_square_even_part {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∃ G : ℂ → ℂ,
      HasFPowerSeriesAt G (FormalMultilinearSeries.ofScalars ℂ
        (fun n => (-1 : ℂ) ^ n * coefficient (2 * n) f)) 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), G (-(z ^ 2)) = (f z + f (-z))/2 := by
  let c (n : ℕ) := coefficient n f
  let p := FormalMultilinearSeries.ofScalars ℂ c
  let d (n : ℕ) := (-1 : ℂ) ^ n * c (2 * n)
  let q := FormalMultilinearSeries.ofScalars ℂ d
  obtain ⟨r, hp⟩ : HasFPowerSeriesAt f p 0 := hf.hasFPowerSeriesAt
  obtain ⟨R, hR0, hRr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hs : Summable (fun n => ‖c n‖ * (R : ℝ) ^ n) := by
    simpa only [p, FormalMultilinearSeries.ofScalars_norm] using
      p.summable_norm_mul_pow (hRr.trans_le hp.r_le)
  have heven : Function.Injective (fun n : ℕ => 2 * n) := by
    intro a b hab
    dsimp at hab
    omega
  have hqsum : Summable (fun n => ‖q n‖ * ((R ^ 2 : ℝ≥0) : ℝ) ^ n) := by
    have h := hs.comp_injective heven
    apply h.congr
    intro n
    simp [q, d, norm_pow, pow_mul]
  have hRpos : (0 : ℝ≥0) < R := by exact_mod_cast hR0
  have hR2 : (0 : ENNReal) < ((R ^ 2 : ℝ≥0) : ENNReal) := by exact_mod_cast pow_pos hRpos 2
  have hpos : 0 < q.radius := hR2.trans_le (q.le_radius_of_summable hqsum)
  refine ⟨q.sum, (q.hasFPowerSeriesOnBall hpos).hasFPowerSeriesAt, ?_⟩
  filter_upwards [Metric.eball_mem_nhds (0 : ℂ) hp.r_pos] with z hz
  have hnz : -z ∈ Metric.eball (0 : ℂ) r := by
    simpa only [mem_eball_zero_iff, enorm_neg] using hz
  have hplus : HasSum (fun n => z ^ n * c n) (f z) := by
    simpa [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using hp.hasSum hz
  have hminus : HasSum (fun n => (-z) ^ n * c n) (f (-z)) := by
    simpa [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using hp.hasSum hnz
  let u (n : ℕ) := (z ^ n * c n + (-z) ^ n * c n)/2
  have hu : HasSum u ((f z + f (-z))/2) := (hplus.add hminus).div_const 2
  have he (n : ℕ) : (-z)^(2 * n) = z ^ (2 * n) := by
    rw [pow_mul, neg_sq, ← pow_mul]
  have huE (n : ℕ) : u (2 * n) = (-(z ^ 2)) ^ n * d n := by
    dsimp [u, d]
    rw [he]
    calc
      _ = z ^ (2 * n) * c (2 * n) := by ring
      _ = (-(z ^ 2)) ^ n * ((-1) ^ n * c (2 * n)) := by
        rw [← mul_assoc, ← mul_pow, neg_mul_neg, mul_one, ← pow_mul]
  have huO (n : ℕ) : u (2 * n + 1) = 0 := by
    dsimp [u]
    rw [pow_succ (-z), pow_succ z, he]
    ring
  have hodd : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro a b hab
    dsimp at hab
    omega
  have hUE := hu.summable.comp_injective heven
  have hUO := hu.summable.comp_injective hodd
  have hspl := tsum_even_add_odd hUE hUO
  simp only [huE, huO, tsum_zero, add_zero, hu.tsum_eq] at hspl
  change FormalMultilinearSeries.ofScalarsSum d (-(z ^ 2)) = _
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simpa only [smul_eq_mul, mul_comm] using hspl


private def chargeSectorSewn (D : LatticeData) (a : ModTwoCharge D)
    (betaL gammaL betaR gammaR : Exponent D) (z : ℂ) : ℂ :=
  ∑' q : Charge D, if reduceCharge D q = a then
    sewnChargeTerm D betaL gammaL betaR gammaR q z else 0

@[fun_prop] private theorem chargeSectorSewn_analyticAt (D : LatticeData)
    (hunit : IsUnit D.G.det) (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (a : ModTwoCharge D) (betaL gammaL betaR gammaR : Exponent D) :
    AnalyticAt ℂ (chargeSectorSewn D a betaL gammaL betaR gammaR) 0 := by
  classical
  obtain ⟨r, hr, hr1, ⟨b, hb, hbound⟩, _⟩ :=
    sewn_charge_normal_at_zero D hunit hD betaL gammaL betaR gammaR
  apply DifferentiableOn.analyticAt
    (s := ball (0 : ℂ) r) _ (isOpen_ball.mem_nhds (mem_ball_self hr))
  unfold chargeSectorSewn
  refine Complex.differentiableOn_tsum_of_summable_norm hb ?_ isOpen_ball ?_
  · intro q
    by_cases hq : reduceCharge D q = a
    · simpa only [hq, ite_true] using
        (sewn_term_diff D hunit betaL gammaL betaR gammaR q).mono
          (ball_subset_ball hr1.le)
    · simp [hq]
  · intro q z hz
    have h := hbound q z (ball_subset_closedBall hz)
    by_cases hq : reduceCharge D q = a
    · simpa only [hq, ite_true] using h
    · simpa only [hq, ite_false, norm_zero] using (norm_nonneg _).trans h

private theorem coefficient_fun_sum {ι : Type*} (s : Finset ι)
    (F : ι → ℂ → ℂ) (n : ℕ) (hF : ∀ i ∈ s, AnalyticAt ℂ (F i) 0) :
    coefficient n (fun z => ∑ i ∈ s, F i z) = ∑ i ∈ s, coefficient n (F i) := by
  unfold coefficient
  rw [iteratedDeriv_fun_sum (fun i hi => (hF i hi).contDiffAt), Finset.sum_div]

private theorem coefficient_const_mul (n : ℕ) (c : ℂ) (f : ℂ → ℂ) :
    coefficient n (fun z => c * f z) = c * coefficient n f := by
  simp [coefficient, iteratedDeriv_const_mul_field, mul_div_assoc]

private theorem coefficient_mul_const (n : ℕ) (c : ℂ) (f : ℂ → ℂ) :
    coefficient n (fun z => f z * c) = coefficient n f * c := by
  simpa only [mul_comm] using coefficient_const_mul n c f

private theorem projection_on_diagonal (D : LatticeData) (H K E : ℕ) (t₀ : ℤ)
    (P Q R S : Oscillator D) (F : Exponent D → Exponent D → Exponent D → Exponent D → ℂ) :
    projectOccupations D H K E ((E : ℤ) + t₀) P Q R S F =
      projectOccupations D H K 0 t₀ P Q R S F := by
  have hzero : chargeNorm D 0 = 0 := by simp [chargeNorm, bilinear]
  have hs (e : ℤ) (β γ : Exponent D) :
      selector D 0 (e - 2 * (E : ℤ)) E β γ = selector D 0 e 0 β γ := by
    have he :
        e - 2 * (E : ℤ) = -2 * (E : ℤ) - doubledWeight D β + doubledWeight D γ ↔
        e = -doubledWeight D β + doubledWeight D γ := by omega
    simp only [selector, hzero, add_zero, Nat.cast_zero, mul_zero, zero_sub, he]
  have hL (i j : ℕ) (β γ : Exponent D) :
      selector D 0 (leftExponent H K E i j) E β γ =
        selector D 0 (leftExponent H K 0 i j) 0 β γ := by
    rw [show leftExponent H K E i j = leftExponent H K 0 i j - 2 * (E : ℤ) by
      simp only [leftExponent, Nat.cast_zero]
      ring]
    exact hs _ _ _
  have hR (β γ : Exponent D) :
      selector D 0 (-2 * ((E : ℤ) + t₀) - 2) E β γ = selector D 0 (-2 * t₀ - 2) 0 β γ := by
    rw [show -2 * ((E : ℤ) + t₀) - 2 = (-2 * t₀ - 2) - 2 * (E : ℤ) by ring]
    exact hs _ _ _
  simp only [projectOccupations, hL, hR]

/-- The native sewn charge sum with the finite lowering and Laurent projection
on the right-mode diagonal `t = E + t₀`. -/
def diagonalSewn (D : LatticeData) (H K : ℕ) (t₀ : ℤ)
    (P Q R S : Oscillator D) (a : ModTwoCharge D) (z : ℂ) : ℂ :=
  projectOccupations D H K 0 t₀ P Q R S
    (fun betaL gammaL betaR gammaR => chargeSectorSewn D a betaL gammaL betaR gammaR z)

/-- The rescaled original coset coefficients on the energy diagonal form a
holomorphic germ. Pullback by the negative square gives the even part of the
actual sewn sum with the original finite lowering and Laurent projection. -/
theorem cosetSeries_negative_square_germ (D : LatticeData) (hunit : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (H K : ℕ) (t₀ : ℤ) (P Q R S : Oscillator D) (a : ModTwoCharge D) :
    let f := diagonalSewn D H K t₀ P Q R S a
    ∃ G : ℂ → ℂ, HasFPowerSeriesAt G (FormalMultilinearSeries.ofScalars ℂ
      (fun E => PowerSeries.coeff E
        (PowerSeries.rescale (-1) (cosetSeries D hD H K ((E : ℤ) + t₀) P Q R S a)))) 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), G (-(z ^ 2)) = (f z + f (-z)) / 2 := by
  dsimp only
  let f := diagonalSewn D H K t₀ P Q R S a
  have hSector (betaL gammaL betaR gammaR : Exponent D) :
      AnalyticAt ℂ (chargeSectorSewn D a betaL gammaL betaR gammaR) 0 :=
    chargeSectorSewn_analyticAt D hunit hD a betaL gammaL betaR gammaR
  have hf : AnalyticAt ℂ f 0 := by
    change AnalyticAt ℂ (fun z => projectOccupations D H K 0 t₀ P Q R S
      (fun betaL gammaL betaR gammaR => chargeSectorSewn D a betaL gammaL betaR gammaR z)) 0
    unfold projectOccupations
    fun_prop
  have hc (n : ℕ) :
      coefficient n f = projectOccupations D H K 0 t₀ P Q R S
        (fun betaL gammaL betaR gammaR =>
          coefficient n (chargeSectorSewn D a betaL gammaL betaR gammaR)) := by
    change coefficient n (fun z => projectOccupations D H K 0 t₀ P Q R S
      (fun betaL gammaL betaR gammaR => chargeSectorSewn D a betaL gammaL betaR gammaR z)) = _
    simp (discharger := fun_prop) only [projectOccupations, coefficient_fun_sum,
      coefficient_const_mul]
  have hcoef (E : ℕ) :
      (-1 : ℂ) ^ E * coefficient (2 * E) f = PowerSeries.coeff E
        (PowerSeries.rescale (-1) (cosetSeries D hD H K ((E : ℤ) + t₀) P Q R S a)) := by
    rw [hc, PowerSeries.coeff_rescale, cosetSeries_sewnTaylor D hunit hD]
    change _ = (-1 : ℂ) ^ E * projectOccupations D H K E ((E : ℤ) + t₀) P Q R S
      (fun betaL gammaL betaR gammaR =>
        coefficient (2 * E) (chargeSectorSewn D a betaL gammaL betaR gammaR))
    rw [projection_on_diagonal]
  obtain ⟨G, hG, hpb⟩ := analytic_neg_square_even_part hf
  exact ⟨G, by simpa only [hcoef] using hG, hpb⟩

/-- The actual rank-24 scalar on the Laurent diagonal is the Taylor series of
the germ obtained by weighting the descended coset germs by the two ordered
ground forms. -/
theorem fourM_scalar_negative_square_germ (D : LatticeData) (hunit : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K : ℕ) (t₀ : ℤ) (u v : paritySpace D hunit (-1))
    (P Q R S : Oscillator D) (x y z d : ActualGround D hunit)
    (huP : u.val = P ⊗ₜ[ℂ] x) (hvQ : v.val = Q ⊗ₜ[ℂ] y)
    (huH : actualTensorL0 D hunit u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hunit v.val = (K : ℂ) • v.val) :
    let f := diagonalSewn D H K t₀ P Q R S
    ∃ G : ℂ → ℂ, HasFPowerSeriesAt G (FormalMultilinearSeries.ofScalars ℂ
      (fun E : ℕ => fourMScalar D hunit hD ((H : ℤ) + (K : ℤ) - E - 1) ((E : ℤ) + t₀)
        u v (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d))) 0 ∧
      ∀ᶠ w in 𝓝 (0 : ℂ), G (-(w ^ 2)) = ∑ a : ModTwoCharge D,
        ((f a w + f a (-w)) / 2) *
          groundForm D hunit y (chargeOperator D (groundRepresentation D hunit) a x) *
          groundForm D hunit d (chargeOperator D (groundRepresentation D hunit) a z) := by
  classical
  dsimp only
  choose g hg hpull using fun a => cosetSeries_negative_square_germ D hunit hD H K t₀ P Q R S a
  let l (a : ModTwoCharge D) :=
    groundForm D hunit y (chargeOperator D (groundRepresentation D hunit) a x)
  let r (a : ModTwoCharge D) :=
    groundForm D hunit d (chargeOperator D (groundRepresentation D hunit) a z)
  let G (w : ℂ) := ∑ a : ModTwoCharge D, g a w * l a * r a
  have ha (a : ModTwoCharge D) : AnalyticAt ℂ (g a) 0 := (hg a).analyticAt
  have hG : AnalyticAt ℂ G 0 := by
    dsimp only [G]
    fun_prop
  have hgcoef (a : ModTwoCharge D) (E : ℕ) :
      coefficient E (g a) = PowerSeries.coeff E
        (PowerSeries.rescale (-1) (cosetSeries D hD H K ((E : ℤ) + t₀) P Q R S a)) := by
    have heq := (ha a).hasFPowerSeriesAt.eq_formalMultilinearSeries (hg a)
    simpa only [FormalMultilinearSeries.coeff_ofScalars, coefficient] using
      congrArg (fun p => FormalMultilinearSeries.coeff p E) heq
  have hGcoef (E : ℕ) : coefficient E G =
      fourMScalar D hunit hD ((H : ℤ) + (K : ℤ) - E - 1) ((E : ℤ) + t₀)
        u v (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d) := by
    rw [fourM_energy_coefficient D hunit hD h24 H K E _ u v P Q R S x y z d huP hvQ huH hvK]
    dsimp only [G]
    simp (discharger := fun_prop) only [coefficient_fun_sum, coefficient_mul_const, hgcoef, l, r]
  refine ⟨G, ?_, ?_⟩
  · have hs : HasFPowerSeriesAt G (FormalMultilinearSeries.ofScalars ℂ
        (fun E => coefficient E G)) 0 := hG.hasFPowerSeriesAt
    simpa only [hGcoef] using hs
  · filter_upwards [eventually_all.mpr hpull] with w hw
    dsimp only [G, l, r]
    simp only [hw]

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChargeGerm
