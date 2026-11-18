/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeNormal
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeNormal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normal convergence for the original fixed four-point occupation over charges. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient
import D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadial
import D5.S3.VertexAlgebra.Sewing.CanonicalFullChargeLoop
import D5.S3.Analytic.OriginalHalfBinomialNome

/-! Compact normal convergence for the literal fixed-occupation four-point terms. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Topology
open Set Filter Metric

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeNormal

open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open LatticeHalfFockChargedTensorCoefficients OriginalGaussianExternalRadial
open OriginalChargedRowSource OriginalGaussianExternalBlocks OriginalGaussianSourceMeans
open OriginalGaussianSourceRestriction OriginalGaussianSewnAnalytic OriginalGaussianDeterminant
open FactorialFockQuadraticEstimate
open OriginalGaussianDifferentiation OriginalGaussianResolvent OriginalGaussianAllIndexResolvent
open D5.S3.Analytic.OriginalHalfBinomialNome
open private chargeSize chargeSize_one_le bilinear_charge_bound charge_gaussian_moment
  from D5.S3.VertexAlgebra.Sewing.CanonicalFullChargeLoop
open private affine_norm_le_positive
  from D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm
open private gaussianCoefficient_smul
  from D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum
open private affine_coefficient_differentiableOn finite_data_differentiableOn
  from D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic
open private chargeScalar_pair
  from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient

private lemma affine_bound {I : Type*} [Fintype I]
    (d : I →₀ ℕ) (C : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (A : Matrix I I ℂ) (m : I → ℂ) (s : ℝ), 1 ≤ s →
      (∀ i j, ‖A i j‖ ≤ C * s) → (∀ i, ‖m i‖ ≤ C * s) →
      ‖affineCoefficient A m d‖ ≤ B * s ^ d.degree := by
  classical
  let M := affineKernel (fun _ _ : I => (C : ℂ)) (fun _ => (C : ℂ))
  refine ⟨∑ k ∈ Finset.range (d.degree + 1),
      ‖gaussianCoefficient M (d.sumElim (Finsupp.single () k))‖, by positivity, ?_⟩
  intro A m s hs hA hm
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  have hM : affineKernel (fun _ _ : I => ((C * s : ℝ) : ℂ))
      (fun _ => ((C * s : ℝ) : ℂ)) = (s : ℂ) • M := by
    ext i j
    cases i <;> cases j <;>
      simp [affineKernel, ElementaryGaussianContraction.leftKernel, M, mul_comm]
  refine (affine_norm_le_positive A m (fun _ _ => C * s) (fun _ => C * s) hA hm d).trans ?_
  rw [hM, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  have hk' : k ≤ d.degree := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hd : (d.sumElim (Finsupp.single () k)).degree = d.degree + k := by
    simp only [Finsupp.degree_eq_sum, Fintype.sum_sum_type, Finsupp.sumElim_inl,
      Finsupp.sumElim_inr, Fintype.sum_unique, Finsupp.single_eq_same]
  rw [gaussianCoefficient_smul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hs0, hd, mul_comm]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hs (by omega)) (norm_nonneg _)

private lemma compact_bound {K : Set ℂ} (hK : IsCompact K)
    {f : ℂ → ℂ} (hf : ContinuousOn f K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K, ‖f z‖ ≤ B := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image hf.norm
  exact ⟨max B 0, le_max_right _ _,
    fun z hz => (hB (mem_image_of_mem _ hz)).trans (le_max_left _ _)⟩

/-- On a compact chart, one summable majorant controls all actual fixed-occupation
terms once the chart supplies the covariance, scalar prefactor and signed mean
factors. The nome is raised to the original lattice charge energy. -/
theorem compact_charge_normal (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (betaL gammaL betaR gammaR : Exponent D)
    (K : Set ℂ) (hK : IsCompact K) (p Q : ℂ → ℂ)
    (hp : DifferentiableOn ℂ p K) (hQ : DifferentiableOn ℂ Q K)
    (hQlt : ∀ z ∈ K, ‖Q z‖ < 1)
    (A : ℂ → Matrix
      (CompactExternal D (fourSupport D betaL gammaL betaR gammaR) ⊕
       CompactExternal D (fourSupport D betaL gammaL betaR gammaR))
      (CompactExternal D (fourSupport D betaL gammaL betaR gammaR) ⊕
       CompactExternal D (fourSupport D betaL gammaL betaR gammaR)) ℂ)
    (u : ℂ → CompactExternal D (fourSupport D betaL gammaL betaR gammaR) ⊕
       CompactExternal D (fourSupport D betaL gammaL betaR gammaR) → ℂ)
    (hA : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) K)
    (hu : ∀ i, DifferentiableOn ℂ (fun z => u z i) K) :
    let F := fourSupport D betaL gammaL betaR gammaR
    let d := externalOccupation D F betaL gammaL betaR gammaR
    let label := Sum.elim (compactExternal D F) (compactExternal D F)
    let term := fun (q : Charge D) (z : ℂ) =>
      p z * Q z ^ (chargeEnergy D q).toNat *
        affineCoefficient (A z) (fun i =>
          (bilinear D (unitCharge D (label i).2.1) q : ℂ) * u z i) d
    (∃ b : Charge D → ℝ, Summable b ∧ ∀ q z, z ∈ K → ‖term q z‖ ≤ b q) ∧
      DifferentiableOn ℂ (fun z => ∑' q, term q z) (interior K) := by
  classical
  dsimp only
  let F := fourSupport D betaL gammaL betaR gammaR
  let I := CompactExternal D F ⊕ CompactExternal D F
  let label : I → External D := Sum.elim (compactExternal D F) (compactExternal D F)
  let d := externalOccupation D F betaL gammaL betaR gammaR
  let m (q : Charge D) (z : ℂ) (i : I) :=
    (bilinear D (unitCharge D (label i).2.1) q : ℂ) * u z i
  let term (q : Charge D) (z : ℂ) :=
    p z * Q z ^ (chargeEnergy D q).toNat * affineCoefficient (A z) (m q z) d
  change (∃ b : Charge D → ℝ, Summable b ∧ ∀ q z, z ∈ K → ‖term q z‖ ≤ b q) ∧ _
  obtain ⟨ρ, hρ, hρ1, hρQ⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ z ∈ K, ‖Q z‖ ≤ ρ := by
    rcases K.eq_empty_or_nonempty with h | h
    · exact ⟨0, le_rfl, zero_lt_one, by simp [h]⟩
    · obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn h hQ.continuousOn.norm
      exact ⟨‖Q z‖, norm_nonneg _, hQlt z hz, fun w hw => hmax hw⟩
  obtain ⟨P, hP, hp'⟩ := compact_bound hK hp.continuousOn
  choose a ha ha' using fun i j : I => compact_bound hK (hA i j).continuousOn
  choose v hv hv' using fun i : I => compact_bound hK (hu i).continuousOn
  let row (i : I) := ∑ j : Fin D.rank, ‖(D.G (label i).2.1 j : ℂ)‖
  let C := (∑ i : I, ∑ j : I, a i j) + ∑ i : I, row i * v i
  have hrow (i : I) : 0 ≤ row i := by positivity
  have hCa (i j : I) : a i j ≤ C := by
    have hj := Finset.single_le_sum (f := a i) (fun j _ => ha i j) (Finset.mem_univ j)
    have hi := Finset.single_le_sum (f := fun i => ∑ j, a i j)
      (fun i _ => Finset.sum_nonneg fun j _ => ha i j) (Finset.mem_univ i)
    exact (hj.trans hi).trans (le_add_of_nonneg_right
      (Finset.sum_nonneg fun i _ => mul_nonneg (hrow i) (hv i)))
  have hCv (i : I) : row i * v i ≤ C :=
    (Finset.single_le_sum (fun i _ => mul_nonneg (hrow i) (hv i))
      (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ha i j))
  have hC : 0 ≤ C := add_nonneg
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ha i j)
    (Finset.sum_nonneg fun i _ => mul_nonneg (hrow i) (hv i))
  obtain ⟨B, hB, hb⟩ := affine_bound d C
  have hmajor (q : Charge D) (z : ℂ) (hz : z ∈ K) :
      ‖term q z‖ ≤ P * B * (ρ ^ (chargeEnergy D q).toNat * chargeSize D q ^ d.degree) := by
    have hs := chargeSize_one_le D q
    have hs0 := zero_le_one.trans hs
    have hm : ∀ i : I, ‖m q z i‖ ≤ C * chargeSize D q := by
      intro i
      simp only [m, norm_mul]
      calc
        _ ≤ (row i * chargeSize D q) * v i :=
          mul_le_mul (bilinear_charge_bound D q _) (hv' i z hz) (norm_nonneg _)
            (mul_nonneg (hrow i) hs0)
        _ = (row i * v i) * chargeSize D q := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hCv i) hs0
    have hcoef := hb (A z) (m q z) (chargeSize D q) hs
      (fun i j => (ha' i j z hz).trans ((hCa i j).trans (le_mul_of_one_le_right hC hs))) hm
    simp only [term, norm_mul, norm_pow]
    calc
      _ ≤ (P * ρ ^ (chargeEnergy D q).toNat) * (B * chargeSize D q ^ d.degree) :=
        mul_le_mul (mul_le_mul (hp' z hz) (pow_le_pow_left₀ (norm_nonneg _) (hρQ z hz) _)
          (pow_nonneg (norm_nonneg _) _) hP) hcoef (norm_nonneg _)
          (mul_nonneg hP (pow_nonneg hρ _))
      _ = _ := by ring
  have hs := (charge_gaussian_moment D hD ρ hρ hρ1 d.degree).mul_left (P * B)
  refine ⟨⟨_, hs, hmajor⟩, ?_⟩
  change DifferentiableOn ℂ (fun z => ∑' q, term q z) (interior K)
  apply Complex.differentiableOn_tsum_of_summable_norm hs _ isOpen_interior
    (fun q z hz => hmajor q z (interior_subset hz))
  intro q
  apply DifferentiableOn.mono _ interior_subset
  exact (hp.mul (hQ.pow _)).mul (affine_coefficient_differentiableOn hA
    (fun i => (hu i).const_mul _) d)


private def pairing : H →L[ℂ] H →L[ℂ] ℂ :=
  (innerSL ℂ).comp (starL ℂ : H ≃L⋆[ℂ] H).toContinuousLinearMap

private lemma sourceConstant_diff :
    DifferentiableOn ℂ sourceConstant (ball 0 1) := by
  intro z hz
  have hz' := mem_ball_zero_iff.mp hz
  have h := pairing.hasFDerivAt_of_bilinear
    (hasDerivAt_sourceFamily 0 hz').hasFDerivAt (hasDerivAt_columnSeries hz').hasFDerivAt
  apply DifferentiableAt.differentiableWithinAt
  apply h.differentiableAt.congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact (source_pairings_explicit (mem_ball_zero_iff.mp hw) false 0).2.2.2.symm

private lemma sourceExternal_diff (out : Bool) (p : ℕ) :
    DifferentiableOn ℂ (sourceExternal out p) (ball 0 1) := by
  intro z hz
  have hz' := mem_ball_zero_iff.mp hz
  have h := pairing.hasFDerivAt_of_bilinear
    (hasDerivAt_externalVector out p hz').hasFDerivAt (hasDerivAt_columnSeries hz').hasFDerivAt
  apply DifferentiableAt.differentiableWithinAt
  apply h.differentiableAt.congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact (source_pairings_explicit (mem_ball_zero_iff.mp hw) out p).2.2.1.symm

private lemma explicitKernel_diff {X : Type*} [Finite X]
    (D : LatticeData) (hunit : IsUnit D.G.det) (e : X → External D) (i j : X ⊕ X) :
    DifferentiableOn ℂ (fun z => explicitEffectiveKernel D e z i j) (ball 0 1) := by
  classical
  let := Fintype.ofFinite X
  have hlim : TendstoLocallyUniformlyOn (fun N z => originalEffectiveKernel D N e z i j)
      (fun z => explicitEffectiveKernel D e z i j) atTop (ball 0 1) := by
    apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
    intro z hz
    obtain ⟨r, hzr, hr⟩ := exists_between (mem_ball_zero_iff.mp hz)
    refine ⟨{w : ℂ | ‖w‖ ≤ r}, ?_, original_effectiveKernel_blocks_tendsto_explicit
      D hunit e ((norm_nonneg z).trans hzr.le) hr i j⟩
    exact mem_nhdsWithin_of_mem_nhds (Filter.mem_of_superset
      ((isOpen_lt continuous_norm continuous_const).mem_nhds hzr)
        (fun w (hw : ‖w‖ < r) => show ‖w‖ ≤ r from hw.le))
  exact hlim.differentiableOn (Eventually.of_forall fun N =>
    (finite_data_differentiableOn D hunit 0 e N).1 i j) isOpen_ball

private lemma nome_square_diff : DifferentiableOn ℂ (fun z : ℂ => Q0 (z ^ 2)) (ball 0 1) := by
  apply actual_nome_disk.1.comp (differentiableOn_id.pow 2)
  intro z hz
  change z ^ 2 ∈ ball (0 : ℂ) 1
  exact mem_ball_zero_iff.mpr (by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg z) (mem_ball_zero_iff.mp hz) (by decide))

private lemma nome_square_source {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    Q0 (z ^ 2) = z ^ 2 * Complex.exp (2 * sourceConstant z) / 16 := by
  have hrhs := ((differentiableOn_id.pow 2).mul
    (sourceConstant_diff.const_mul 2).cexp).div_const (16 : ℂ)
  apply (nome_square_diff.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_frequently_eq
    (hrhs.analyticOnNhd isOpen_ball) isPreconnected_ball (by simp : (0 : ℂ) ∈ ball 0 1) _ hz
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℂ) + 1)) atTop (𝓝 (0 : ℂ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hp : Tendsto (fun n : ℕ => 1 / ((n : ℂ) + 1)) atTop (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall fun n => ?_⟩
    have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simpa using div_ne_zero one_ne_zero hn
  apply hp.frequently
  apply Eventually.frequently
  filter_upwards [eventually_ge_atTop 1] with n hn
  let t : ℝ := 1 / ((n : ℝ) + 1)
  have hpos : 0 < t := by dsimp [t]; positivity
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht1 : t < 1 := (div_lt_one (by positivity : 0 < (n : ℝ) + 1)).mpr (by linarith)
  have hcast : (t : ℂ) = 1 / ((n : ℂ) + 1) := by simp [t]
  have he := actual_nome_source.2 (t ^ 2) (sq_pos_of_pos hpos)
    (by nlinarith [mul_pos hpos (sub_pos.mpr ht1)])
  rw [Real.sqrt_sq hpos.le, Complex.ofReal_pow, hcast] at he
  exact he

/-- The literal shifted and weighted four-point charge term in the variable z. -/
def sewnChargeTerm (D : LatticeData) (betaL gammaL betaR gammaR : Exponent D)
    (q : Charge D) (z : ℂ) : ℂ :=
  let F := fourSupport D betaL gammaL betaR gammaR
  (chargeScalar D q * chargeScalar D (-q)) * z ^ (2 * (chargeEnergy D q).toNat) *
    sewn D q (compactExternal D F) (externalOccupation D F betaL gammaL betaR gammaR) z

/-- The original charge pair, energy shift, and sewn Gaussian have a single
summable majorant on a closed disk about zero. Their sum is holomorphic on the
interior, in the sewing coordinate used for the ordinary coefficients. -/
theorem sewn_charge_normal_at_zero (D : LatticeData) (hunit : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (betaL gammaL betaR gammaR : Exponent D) :
    let term := sewnChargeTerm D betaL gammaL betaR gammaR
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (∃ b : Charge D → ℝ, Summable b ∧ ∀ q z, z ∈ closedBall 0 r → ‖term q z‖ ≤ b q) ∧
      DifferentiableOn ℂ (fun z => ∑' q, term q z) (ball 0 r) := by
  classical
  dsimp only
  let F := fourSupport D betaL gammaL betaR gammaR
  let e := compactExternal D F
  let d := externalOccupation D F betaL gammaL betaR gammaR
  let Q := fun z : ℂ => Q0 (z ^ 2)
  let p := fun z : ℂ => Complex.exp (-(D.rank : ℂ) / 2 * gaussianLogDet z)
  let u (z : ℂ) : CompactExternal D F ⊕ CompactExternal D F → ℂ :=
    Sum.elim (fun x => -1 + sourceExternal (e x).1 (e x).2.2 z)
      (fun x => 1 - sourceExternal (e x).1 (e x).2.2 z)
  have hzero : Q 0 = 0 := by
    simpa [Q] using (actual_nome_disk.2.2.2.1 0).2 rfl
  have hnear : {z : ℂ | ‖Q z‖ < 1} ∈ 𝓝 0 := by
    have hQ0 : ContinuousAt Q 0 :=
      nome_square_diff.continuousOn.continuousAt (isOpen_ball.mem_nhds
      (by simp : (0 : ℂ) ∈ ball 0 1))
    have hball : ball (0 : ℂ) 1 ∈ 𝓝 (Q 0) := by simp [hzero, ball_mem_nhds]
    simpa only [preimage, mem_ball_zero_iff] using hQ0.preimage_mem_nhds hball
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hnear
    (ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)))
  let R := min (r / 2) (1 / 2 : ℝ)
  have hR : 0 < R := lt_min (by positivity) (by norm_num)
  have hR1 : R < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hK : closedBall (0 : ℂ) R ⊆ ball 0 1 :=
    fun z hz => mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt hR1)
  have hQlt (z : ℂ) (hz : z ∈ closedBall 0 R) : ‖Q z‖ < 1 :=
    (hsub (mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt
      ((min_le_left _ _).trans_lt (by linarith))))).1
  have hp : DifferentiableOn ℂ p (closedBall 0 R) :=
    (gaussianLogDet_differentiableOn.const_mul _).cexp.mono
      (fun z hz => mem_ball_zero_iff.mp (hK hz))
  have hu (i) : DifferentiableOn ℂ (fun z => u z i) (closedBall 0 R) := by
    cases i with
    | inl x => exact ((sourceExternal_diff (e x).1 (e x).2.2).const_add _).mono hK
    | inr x => exact ((sourceExternal_diff (e x).1 (e x).2.2).const_sub _).mono hK
  obtain ⟨⟨b, hb, hbound⟩, hsum⟩ := compact_charge_normal D hD betaL gammaL betaR gammaR
    (closedBall 0 R) (isCompact_closedBall _ _) p Q hp (nome_square_diff.mono hK) hQlt
    (explicitEffectiveKernel D e) u (fun i j => (explicitKernel_diff D hunit e i j).mono hK) hu
  let mChart (q : Charge D) (z : ℂ) (i : CompactExternal D F ⊕ CompactExternal D F) :=
    (bilinear D (unitCharge D ((Sum.elim e e) i).2.1) q : ℂ) * u z i
  let chart (q : Charge D) (z : ℂ) :=
    p z * Q z ^ (chargeEnergy D q).toNat *
      affineCoefficient (explicitEffectiveKernel D e z) (mChart q z) d
  change (∀ q z, z ∈ closedBall 0 R → ‖chart q z‖ ≤ b q) at hbound
  change DifferentiableOn ℂ (fun z => ∑' q, chart q z) (interior (closedBall 0 R)) at hsum
  have heq (q : Charge D) (z : ℂ) (hz : z ∈ closedBall 0 R) :
      chart q z = sewnChargeTerm D betaL gammaL betaR gammaR q z := by
    have hmean : mChart q z = explicitMean D q e z := by
      funext i
      cases i <;> rfl
    let m := (chargeEnergy D q).toNat
    have hm : (m : ℤ) = chargeEnergy D q := Int.toNat_of_nonneg (chargeEnergy_nonneg D hD q)
    have hn : (chargeNorm D q : ℂ) = 2 * (m : ℂ) := by
      have h : (chargeNorm D q : ℤ) = 2 * (m : ℤ) := by
        rw [hm, two_chargeEnergy]
        rfl
      exact_mod_cast h
    have hs : (16 : ℂ) ^ (-chargeEnergy D q) = ((16 : ℂ) ^ m)⁻¹ := by
      rw [← hm, zpow_neg, zpow_natCast]
    rw [show chart q z = p z * Q z ^ m *
      affineCoefficient (explicitEffectiveKernel D e z) (mChart q z) d from rfl, hmean]
    change p z * Q z ^ m *
      affineCoefficient (explicitEffectiveKernel D e z) (explicitMean D q e z) d =
      (chargeScalar D q * chargeScalar D (-q)) * z ^ (2 * m) * sewn D q e d z
    rw [chargeScalar_pair, hs, sewn, hn, show Q z = _ from nome_square_source (hK hz),
      div_pow, mul_pow, ← pow_mul, ← Complex.exp_nat_mul]
    rw [show (m : ℂ) * (2 * sourceConstant z) = 2 * (m : ℂ) * sourceConstant z by ring]
    unfold p
    ring
  refine ⟨R, hR, hR1, ⟨b, hb, ?_⟩, ?_⟩
  · intro q z hz
    rw [← heq q z hz]
    exact hbound q z hz
  · rw [interior_closedBall _ hR.ne'] at hsum
    refine hsum.congr fun z hz => ?_
    apply tsum_congr
    intro q
    exact (heq q z (ball_subset_closedBall hz)).symm

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeNormal
