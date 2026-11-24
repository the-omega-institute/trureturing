/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedBMonodromy
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nontrivial native Leech HHBB B-product monodromy around the zero insertion. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductUpperDisk
import D5.S3.VertexAlgebra.Lattice.LeechLowSpectrum

/-! The actual inner coefficient at doubled exponent `-5` acts through
the weight-one Leech currents. The native half-mode on the same ground
vector is injective on those currents, so a graded detector normalizes the
joint coefficient to one. This supplies a nonzero germ for the root lift. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section

open scoped BigOperators TensorProduct VertexOperator Topology
open Filter Metric Complex

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBMonodromy

open ActualLeechHyperbolic (leechData leech_spec leechCoordinates)
open LatticeGeneratingFieldLocality LatticePositiveEnergy
open LatticeAllStateField (vacuum)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open LatticeHalfFock (current tensorCurrent tensorEnd)
open LatticeHalfFockGradedTrace (actualGrade actualAmbientBasis actual_basis_apply OddMonomial)
open ActualChargedAdjoint (actualForm)
open NativeMixedBProductUpperDisk (b_joint_product_analytic)
open NativeMixedUpperProductCusp (bJointTerm bProductCoeff b_joint_product_neg_root)
open Orbifold.NativeMixedPairField (mu mu_coeff_of_grade mu_lower_truncation leech_mu_normalization)
open Orbifold.NativeMixedPairState (mixedPairState_grade mixedPairWeight)
open Orbifold.NativeOddTwistedIntertwiner (TwistedOdd OddCarrier leechUnit leechGroundVector
  oddCurrent J Jplus J_grade)
open Orbifold.NativeOddUpperRightSkew (R rightField rightField_coeff)

open private no_roots from D5.S3.VertexAlgebra.Lattice.LeechLowSpectrum
open private groundIndex groundBasis_energy J_current from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private R_lowest exists_grade_detector from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private bEnergyTerm bEnergy_hasSum_iff from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion
open private energyPole bEnergyTerm_factor bProductCoeff_summable_on_disk from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedProductSlot23Analytic
open private energySum energySum_analyticAt from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateSlot12Analytic
open private maxOddWeight_le_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedWickCuspGerm

local notation "ℒ" => leechData
local notation "H" => leechGroundVector

private theorem grade_one_span :
    grade ℒ 1 ≤ Submodule.span ℂ (Set.range fun i => (oddCurrent ℒ i).val) := by
  rw [grade_eq_span]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨⟨a, d⟩, hd, rfl⟩
  change chargeEnergy ℒ a + (oscillatorEnergy d : ℤ) = 1 at hd
  have ha : a = 0 := by
    by_contra h
    have hgap := Lattice.RootlessLowGrades.chargeEnergy_gap ℒ leech_spec.2.2.1
      (no_roots leechCoordinates leech_spec.2.2.2) a h
    omega
  subst a
  have hd' : oscillatorEnergy d = 1 := by
    have hz : chargeEnergy ℒ 0 = 0 :=
      (chargeEnergy_eq_zero_iff ℒ leech_spec.2.2.1 0).2 rfl
    omega
  obtain ⟨i, rfl⟩ := (Lattice.RootlessLowGrades.oscillator_one_iff ℒ d).mp hd'
  apply Submodule.subset_span
  refine ⟨i, ?_⟩
  change LatticeFiniteNegativeGeneration.neutralMode ℒ i (-1) (vacuum ℒ) = _
  rw [← LatticeSugawaraCurrents.neutralField_ncoeff,
    LatticeActualConformalState.current_state_creation, carrierBasis_apply]
  rfl

private theorem first_oscillator_basis (i : Fin leechData.rank) :
    (Jplus (-1) (oddCurrent ℒ i) H).val =
      actualAmbientBasis ℒ leechUnit (Finsupp.single (i, 0) 1, groundIndex) := by
  change (J ℒ leechUnit false (-1) (oddCurrent ℒ i) H).val = _
  rw [J_current, actual_basis_apply]
  change tensorCurrent ℒ _ i (-1)
      (actualAmbientBasis ℒ leechUnit (0, groundIndex)) = _
  rw [actual_basis_apply]
  simp [tensorCurrent, tensorEnd, current, MvPolynomial.X]

private theorem first_oscillator_ne_zero (a : OddCarrier ℒ)
    (ha : a.val ∈ grade ℒ 1) (ha₀ : a ≠ 0) :
    Jplus (-1) a H ≠ 0 := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (grade_one_span ha)
  have ha' : (∑ i, c i • oddCurrent ℒ i) = a := by
    apply Subtype.ext
    change (LatticeInvolution.minusSpace ℒ).subtype (∑ i, c i • oddCurrent ℒ i) = a.val
    simpa only [map_sum, map_smul, Submodule.subtype_apply] using hc
  let idx (i : Fin leechData.rank) : OddMonomial ℒ × _ :=
    (Finsupp.single (i, 0) 1, groundIndex)
  have hinj : Function.Injective idx := by
    intro i j hij
    exact congrArg Prod.fst ((Finsupp.single_left_inj (by decide)).mp
      (congrArg Prod.fst hij))
  have hlin := (actualAmbientBasis ℒ leechUnit).linearIndependent.comp idx hinj
  intro hz
  rw [← ha', map_sum, LinearMap.sum_apply] at hz
  simp only [map_smul, LinearMap.smul_apply] at hz
  have hsum : ∑ i, c i • actualAmbientBasis ℒ leechUnit (idx i) = 0 := by
    have hout := congrArg Subtype.val hz
    change (∑ i, c i • Jplus (-1) (oddCurrent ℒ i) H).val =
      (0 : TwistedOdd).val at hout
    change (Submodule.subtype _) (∑ i, c i • Jplus (-1) (oddCurrent ℒ i) H) = 0 at hout
    simpa only [map_sum, map_smul, Submodule.subtype_apply, first_oscillator_basis, idx] using hout
  have hcz := (linearIndependent_iff'.mp hlin) Finset.univ c hsum
  apply ha₀
  rw [← ha']
  exact Finset.sum_eq_zero fun i hi => by rw [hcz i hi, zero_smul]

private theorem odd_grade_pair : Odd ((0 : ℤ) + 1) ∧ Odd ((1 : ℤ) - 0) := by
  constructor <;> exact ⟨0, by decide⟩

set_option maxHeartbeats 800000 in
/-- With both even insertions equal to the actual Leech ground vector, there
are first-grade odd states whose joint mode at `(-5,-1)` has coefficient one. -/
theorem exists_hhbb_b_coefficient_one (i : Fin leechData.rank) :
    ∃ U V : TwistedOdd, U.val ∈ actualGrade ℒ leechUnit 1 ∧
      V.val ∈ actualGrade ℒ leechUnit 1 ∧ bProductCoeff false false 0 0 1 1 H U H V 1 = 1 := by
  obtain ⟨c, _, U, _, hU, _, _, _, _, hp, _⟩ := leech_mu_normalization i
  let a := (mu false H).coeff (-5) U
  have ha₀ : a ≠ 0 := by
    intro hz
    change sourcePairing ℒ a.val
      (c • oddCurrent ℒ i).val = 1 at hp
    simp only [hz, Submodule.coe_zero, map_zero, LinearMap.zero_apply] at hp
    exact zero_ne_one hp
  have hmode := mu_coeff_of_grade false 0 1 1 H U groundBasis_energy hU
  have ha : a.val ∈ grade ℒ 1 := by
    change a = _ at hmode
    rw [hmode]
    simpa only [show mixedPairWeight 0 1 1 = 1 by decide] using
      mixedPairState_grade false 0 1 1 H U
  have hR := R_lowest ℒ leechUnit false (-1) 1 0 H a ha groundBasis_energy
    (by norm_num) (by norm_num)
  have hphase : I ^ (-2 * (-1) - 3 : ℤ) ≠ 0 := zpow_ne_zero _ I_ne_zero
  have hR₀ : R ℒ leechUnit false (-1) H a ≠ 0 := by
    rw [hR]
    exact smul_ne_zero hphase (first_oscillator_ne_zero a ha ha₀)
  have hRg : (R ℒ leechUnit false (-1) H a).val ∈ actualGrade ℒ leechUnit 1 := by
    rw [hR, Submodule.coe_smul]
    exact (actualGrade ℒ leechUnit 1).smul_mem _
      (J_grade ℒ leechUnit false (-1) 1 0 1 a H ha groundBasis_energy (by norm_num))
  obtain ⟨V, hV, hpair⟩ := exists_grade_detector ℒ leechUnit true 1 _ hRg hR₀
    (by norm_num [Orbifold.NativeOddTwistedIntertwiner.paritySign])
  refine ⟨U, V, hU, hV, ?_⟩
  change actualForm ℒ leechUnit V.val ((rightField ℒ leechUnit false H).coeff (-1) a).val = 1
  have hc := rightField_coeff ℒ leechUnit false (-1) H a
  change (rightField ℒ leechUnit false H).coeff (-1) a = _ at hc
  rw [hc]
  exact hpair

private abbrev hhbbCoeff (U V : TwistedOdd) := bProductCoeff false false 0 0 1 1 H U H V

/-- The convergent joint-mode value on the two-sheeted root disk. -/
def hhbbB (U V : TwistedOdd) (z : ℂ) : ℂ :=
  ∑' i, bJointTerm false false H U H V 1 z i

/-- The regular holomorphic coefficient series after extracting `z⁻⁵`. -/
def hhbbRegular (U V : TwistedOdd) (y : ℂ) : ℂ :=
  ∑' E : ℕ, hhbbCoeff U V (E + 1) * y ^ E

private theorem hhbbCoeff_zero (U V : TwistedOdd)
    (hU : U.val ∈ actualGrade ℒ leechUnit 1) : hhbbCoeff U V 0 = 0 := by
  change actualForm ℒ leechUnit V.val
    ((rightField ℒ leechUnit false H).coeff 1 ((mu false H).coeff (-7) U)).val = 0
  have hHmax : ActualEnergyRestrictedDual.maxOddWeight ℒ leechUnit leechGroundVector.val ≤ 0 :=
    maxOddWeight_le_grade groundBasis_energy
  have hUmax := maxOddWeight_le_grade hU
  rw [mu_lower_truncation false H U (-7) (by omega), map_zero, Submodule.coe_zero,
    map_zero]

/-- The actual double series is the energy-one pole times a holomorphic
series on the base disk, whose value at zero is the joint coefficient. -/
theorem hhbb_hasSum_regular (U V : TwistedOdd)
    (hU : U.val ∈ actualGrade ℒ leechUnit 1)
    (hV : V.val ∈ actualGrade ℒ leechUnit 1) :
    AnalyticOnNhd ℂ (hhbbRegular U V) (Metric.ball 0 1) ∧
    hhbbRegular U V 0 = hhbbCoeff U V 1 ∧
    ∀ z : ℂ, z ≠ 0 → ‖z‖ < 1 →
      HasSum (bJointTerm false false H U H V 1 z)
        (z ^ (-5 : ℤ) * hhbbRegular U V (z ^ (2 : ℕ))) := by
  have hdisk (y : ℂ) (hy : ‖y‖ < 1) :
      Summable (fun E : ℕ => hhbbCoeff U V E * y ^ E) :=
    bProductCoeff_summable_on_disk false false 0 0 1 1 H U H V
      groundBasis_energy hU groundBasis_energy hV odd_grade_pair.1 odd_grade_pair.2 hy
  have hshift (y : ℂ) (hy : ‖y‖ < 1) :
      Summable (fun E : ℕ => hhbbCoeff U V (E + 1) * y ^ E) := by
    by_cases hy₀ : y = 0
    · subst y
      apply summable_of_ne_finset_zero (s := {0})
      intro E hE
      simp only [Finset.mem_singleton] at hE
      simp [zero_pow hE]
    · have h := (summable_nat_add_iff 1).2 (hdisk y hy)
      refine (h.mul_right y⁻¹).congr fun E => ?_
      rw [pow_succ, mul_assoc, mul_assoc, mul_inv_cancel₀ hy₀, mul_one]
  have hzero : hhbbRegular U V 0 = hhbbCoeff U V 1 := by
    unfold hhbbRegular
    rw [tsum_eq_single 0]
    · simp
    · intro E hE
      simp [zero_pow hE]
  refine ⟨fun y hy => energySum_analyticAt _ hshift (mem_ball_zero_iff.mp hy), hzero,
    fun z hz hr => ?_⟩
  have hy : ‖z ^ (2 : ℕ)‖ < 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg z]
  have hs := (hdisk _ hy).hasSum.mul_left (z ^ (-7 : ℤ))
  apply (bEnergy_hasSum_iff false false 0 0 1 1 H U H V groundBasis_energy hU
    groundBasis_energy hV odd_grade_pair.1 1 z _).mp
  have he : HasSum (bEnergyTerm false false 0 0 1 1 H U H V 1 z)
      (z ^ (-7 : ℤ) * energySum (hhbbCoeff U V) (z ^ (2 : ℕ))) := by
    refine hs.congr_fun fun E => ?_
    simpa only [show (- (energyPole 0 1)) = (-7 : ℤ) by decide,
      div_one, one_zpow, mul_one] using
      (bEnergyTerm_factor false false 0 0 1 1 H U H V one_ne_zero hz E)
  have hseries : energySum (hhbbCoeff U V) (z ^ (2 : ℕ)) =
      hhbbRegular U V (z ^ (2 : ℕ)) * z ^ (2 : ℕ) := by
    rw [energySum, hhbbRegular, (hdisk _ hy).tsum_eq_zero_add, hhbbCoeff_zero U V hU, zero_mul, zero_add,
      ← (hshift _ hy).tsum_mul_right]
    congr 1
    ext E
    rw [pow_succ, mul_assoc]
  convert he using 1
  rw [hseries, mul_left_comm, ← zpow_natCast z 2, ← zpow_add₀ hz]
  rw [show (-7 : ℤ) + ((2 : ℕ) : ℤ) = -5 by decide, mul_comm, zpow_natCast]

/-- The punctured unit disk in the inner root coordinate. -/
def rootDisk : Set ℂ := Metric.ball 0 1 ∩ {z : ℂ | z ≠ 0}

private theorem isOpen_rootDisk : IsOpen rootDisk :=
  Metric.isOpen_ball.inter isOpen_ne

/-- Convergence and holomorphy of the actual native mode sum on both sheets. -/
theorem hhbb_analytic_root (U V : TwistedOdd) :
    AnalyticOnNhd ℂ (hhbbB U V) rootDisk ∧
    ∀ z ∈ rootDisk, HasSum (bJointTerm false false H U H V 1 z) (hhbbB U V z) :=
  b_joint_product_analytic false false H U H V isOpen_rootDisk analyticOnNhd_const
    analyticOnNhd_id (fun z hz => ⟨one_ne_zero, hz.2, by
      simpa only [norm_one] using mem_ball_zero_iff.mp hz.1⟩)

private def sheetDomain (z₀ : ℂ) : Set ℂ :=
  Metric.ball 0 1 ∩ (fun y : ℂ => y / z₀ ^ (2 : ℕ)) ⁻¹' Complex.slitPlane

/-- The local square root taking the value `z₀` over `z₀²`. -/
def sheetRoot (z₀ y : ℂ) : ℂ := z₀ * Complex.sqrt (y / z₀ ^ (2 : ℕ))

private theorem isOpen_sheetDomain (z₀ : ℂ) : IsOpen (sheetDomain z₀) :=
  Metric.isOpen_ball.inter
    (Complex.isOpen_slitPlane.preimage (continuous_id.div_const _))

private theorem sheetRoot_sq (z₀ y : ℂ) (hz : z₀ ≠ 0) :
    sheetRoot z₀ y ^ (2 : ℕ) = y := by
  rw [sheetRoot, mul_pow, Complex.sqrt, Complex.cpow_ofNat_inv_pow]
  exact mul_div_cancel₀ _ (pow_ne_zero 2 hz)

private theorem sheetRoot_analytic (z₀ y : ℂ) (hy : y ∈ sheetDomain z₀) :
    AnalyticAt ℂ (sheetRoot z₀) y :=
  analyticAt_const.mul <| AnalyticAt.comp (g := Complex.sqrt)
    (f := fun v : ℂ => v / z₀ ^ (2 : ℕ))
    (Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane _ hy.2)
    analyticAt_id.div_const

private theorem sheetDomain_center {z₀ : ℂ} (hz : z₀ ∈ rootDisk) :
    z₀ ^ (2 : ℕ) ∈ sheetDomain z₀ := by
  refine ⟨mem_ball_zero_iff.mpr ?_, ?_⟩
  · have h := mem_ball_zero_iff.mp hz.1
    rw [norm_pow]
    nlinarith [norm_nonneg z₀]
  · change z₀ ^ (2 : ℕ) / z₀ ^ (2 : ℕ) ∈ Complex.slitPlane
    rw [div_self (pow_ne_zero 2 hz.2)]
    exact Complex.one_mem_slitPlane

private theorem sheetRoot_center {z₀ : ℂ} (hz : z₀ ≠ 0) :
    sheetRoot z₀ (z₀ ^ (2 : ℕ)) = z₀ := by
  rw [sheetRoot, div_self (pow_ne_zero 2 hz), Complex.sqrt_one, mul_one]

private theorem sheetRoot_lifts_locally {z₀ : ℂ} (hz : z₀ ∈ rootDisk) :
    ∀ᶠ z in 𝓝 z₀, sheetRoot z₀ (z ^ (2 : ℕ)) = z := by
  have hp : ContinuousAt (fun z : ℂ => z ^ (2 : ℕ)) z₀ := continuousAt_id.pow 2
  have hc : ContinuousAt (fun z : ℂ => sheetRoot z₀ (z ^ (2 : ℕ))) z₀ :=
    ContinuousAt.comp' (f := fun z : ℂ => z ^ (2 : ℕ))
      (sheetRoot_analytic z₀ _ (sheetDomain_center hz)).continuousAt hp
  have hn : sheetRoot z₀ (z₀ ^ (2 : ℕ)) ≠ -z₀ := by
    rw [sheetRoot_center hz.2]
    exact fun h => hz.2 (by linear_combination h / 2)
  have hneg : ContinuousAt (fun z : ℂ => -z) z₀ := continuousAt_id.neg
  filter_upwards [(hc.ne_iff_eventually_ne hneg).mp hn] with z hne
  exact ((sq_eq_sq_iff_eq_or_eq_neg).mp (sheetRoot_sq z₀ _ hz.2)).resolve_right hne

/-- Local analytic branches over the base disk reproduce the joint sum on a
neighborhood of every point of the root disk. -/
theorem hhbb_local_branch (U V : TwistedOdd) {z₀ : ℂ} (hz : z₀ ∈ rootDisk) :
    let σ := sheetRoot z₀
    ∃ W : Set ℂ, IsOpen W ∧ z₀ ^ (2 : ℕ) ∈ W ∧
      AnalyticOnNhd ℂ σ W ∧ (∀ y ∈ W, σ y ^ (2 : ℕ) = y ∧ σ y ∈ rootDisk) ∧
      AnalyticOnNhd ℂ (fun y => hhbbB U V (σ y)) W ∧
      (∀ y ∈ W, HasSum (bJointTerm false false H U H V 1 (σ y)) (hhbbB U V (σ y))) ∧
      ∀ᶠ z in 𝓝 z₀, σ (z ^ (2 : ℕ)) = z := by
  have hsheet (y : ℂ) (hy : y ∈ sheetDomain z₀) :
      sheetRoot z₀ y ^ (2 : ℕ) = y ∧ sheetRoot z₀ y ∈ rootDisk := by
    have hsq := sheetRoot_sq z₀ y hz.2
    have hy₀ : y ≠ 0 := by
      intro h
      have hslit := Complex.slitPlane_ne_zero hy.2
      exact hslit (by simp [h])
    have hσ₀ : sheetRoot z₀ y ≠ 0 := by
      intro h
      exact hy₀ (by simpa [h] using hsq.symm)
    have hσnorm : ‖sheetRoot z₀ y‖ ^ (2 : ℕ) = ‖y‖ := by rw [← norm_pow, hsq]
    have hy₁ := mem_ball_zero_iff.mp hy.1
    have hσ₁ : ‖sheetRoot z₀ y‖ < 1 := by
      by_contra! h
      nlinarith
    exact ⟨hsq, mem_ball_zero_iff.mpr hσ₁, hσ₀⟩
  have hchart := b_joint_product_analytic false false H U H V (isOpen_sheetDomain z₀)
    analyticOnNhd_const (sheetRoot_analytic z₀) (fun y hy => by
      have h := (hsheet y hy).2
      exact ⟨one_ne_zero, h.2, by simpa only [norm_one] using mem_ball_zero_iff.mp h.1⟩)
  exact ⟨sheetDomain z₀, isOpen_sheetDomain z₀, sheetDomain_center hz,
    sheetRoot_analytic z₀, hsheet, hchart.1, hchart.2, sheetRoot_lifts_locally hz⟩

/-- The lifted half circle. Its square makes one positive turn around zero. -/
def rootCircle (r t : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp (((Real.pi * t : ℝ) : ℂ) * I)

/-- The lifted half circle is a continuous path. -/
theorem rootCircle_continuous (r : ℝ) : Continuous (rootCircle r) := by
  unfold rootCircle
  fun_prop

@[simp] private theorem rootCircle_zero (r : ℝ) : rootCircle r 0 = r := by
  simp [rootCircle]

@[simp] private theorem rootCircle_one (r : ℝ) : rootCircle r 1 = -(r : ℂ) := by
  simp [rootCircle, Complex.exp_pi_mul_I]

private theorem rootCircle_norm (r t : ℝ) (hr : 0 ≤ r) : ‖rootCircle r t‖ = r := by
  rw [rootCircle, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_of_nonneg hr]

private theorem rootCircle_mem (r t : ℝ) (hr : 0 < r) (hr₁ : r < 1) :
    rootCircle r t ∈ rootDisk := by
  refine ⟨mem_ball_zero_iff.mpr ((rootCircle_norm r t hr.le).trans_lt hr₁), ?_⟩
  exact norm_pos_iff.mp ((rootCircle_norm r t hr.le).symm ▸ hr)

/-- The base projection is the counterclockwise circle of radius `r²`. -/
theorem rootCircle_sq (r t : ℝ) :
    rootCircle r t ^ (2 : ℕ) =
      (r : ℂ) ^ (2 : ℕ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * I) := by
  rw [rootCircle, mul_pow, pow_two (Complex.exp _), ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The joint sums along the lifted circle converge, and the endpoint value
has the opposite sign by odd inner-mode support. -/
theorem hhbb_circle_hasSum (U V : TwistedOdd) {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) :
    (∀ t : ℝ, HasSum (bJointTerm false false H U H V 1 (rootCircle r t))
      (hhbbB U V (rootCircle r t))) ∧
    hhbbB U V (rootCircle r 1) = -hhbbB U V (rootCircle r 0) := by
  refine ⟨fun t => (hhbb_analytic_root U V).2 _ (rootCircle_mem r t hr hr₁), ?_⟩
  rw [rootCircle_one, rootCircle_zero]
  exact b_joint_product_neg_root false false H U H V 1 r

/-- Starting at a positive real root, the local branch is the principal
upper-disk native branch. -/
theorem hhbb_circle_initial_germ (U V : TwistedOdd) {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) :
    ∀ᶠ y in 𝓝 ((r : ℂ) ^ (2 : ℕ)),
      hhbbB U V (sheetRoot r y) = hhbbB U V (Complex.sqrt y) := by
  have hz : (r : ℂ) ∈ rootDisk := by simpa only [rootCircle_zero] using rootCircle_mem r 0 hr hr₁
  have hslit : (r : ℂ) ^ (2 : ℕ) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using sq_pos_of_pos hr
  have hp : Complex.sqrt ((r : ℂ) ^ (2 : ℕ)) = r := by
    have hre : (Complex.sqrt ((r : ℂ) ^ (2 : ℕ))).re = r := by
      rw [← Complex.ofReal_pow, Complex.re_sqrt_ofReal, pow_two, Real.sqrt_mul_self hr.le]
    have hsq : (Complex.sqrt ((r : ℂ) ^ 2)) ^ (2 : ℕ) = (r : ℂ) ^ (2 : ℕ) :=
      Complex.cpow_ofNat_inv_pow _ 2
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact h
    · have hh := congrArg Complex.re h
      simp only [hre, Complex.neg_re, Complex.ofReal_re] at hh
      linarith
  have hc := (sheetRoot_analytic (r : ℂ) _ (sheetDomain_center hz)).continuousAt
  have hcs := (Complex.differentiableAt_sqrt hslit).continuousAt
  have hne : sheetRoot r ((r : ℂ) ^ (2 : ℕ)) ≠ -Complex.sqrt ((r : ℂ) ^ (2 : ℕ)) := by
    rw [sheetRoot_center hz.2, hp]
    exact fun h => hz.2 (by linear_combination h / 2)
  filter_upwards [(hc.ne_iff_eventually_ne hcs.neg).mp hne] with y hy
  apply congrArg (hhbbB U V)
  refine (sq_eq_sq_iff_eq_or_eq_neg.mp ?_).resolve_right hy
  rw [sheetRoot_sq _ _ hz.2, Complex.sqrt, Complex.cpow_ofNat_inv_pow]

/-- Near each parameter of the lifted circle, a local holomorphic native
sum on the base disk agrees with the continued value along the path. -/
theorem hhbb_circle_local_branch (U V : TwistedOdd) {r : ℝ} (hr : 0 < r) (hr₁ : r < 1)
    (t : ℝ) :
    let z₀ := rootCircle r t
    let σ := sheetRoot z₀
    ∃ W : Set ℂ, IsOpen W ∧ z₀ ^ (2 : ℕ) ∈ W ∧
      AnalyticOnNhd ℂ (fun y => hhbbB U V (σ y)) W ∧
      (∀ y ∈ W, HasSum (bJointTerm false false H U H V 1 (σ y)) (hhbbB U V (σ y))) ∧
      ∀ᶠ u in 𝓝 t, (rootCircle r u) ^ (2 : ℕ) ∈ W ∧
        σ ((rootCircle r u) ^ (2 : ℕ)) = rootCircle r u := by
  obtain ⟨W, hW, ht, _, _, ha, hs, hlocal⟩ :=
    hhbb_local_branch U V (rootCircle_mem r t hr hr₁)
  refine ⟨W, hW, ht, ha, hs, ?_⟩
  have hc : ContinuousAt (fun z : ℂ => z ^ (2 : ℕ)) (rootCircle r t) :=
    continuousAt_id.pow 2
  have hroot := (rootCircle_continuous r).continuousAt (x := t)
  exact hroot.tendsto.eventually ((hc.tendsto.eventually (hW.mem_nhds ht)).and hlocal)

/-- A normalized HHBB witness to nontrivial monodromy on every sufficiently
small positive circle. The regular coefficient at zero is exactly one. -/
theorem exists_hhbb_nontrivial_b_monodromy :
    ∃ (U V : TwistedOdd) (ε : ℝ),
      U.val ∈ actualGrade ℒ leechUnit 1 ∧ V.val ∈ actualGrade ℒ leechUnit 1 ∧
      bProductCoeff false false 0 0 1 1 H U H V 1 = 1 ∧ 0 < ε ∧ ε ≤ 1 ∧
      ∀ r : ℝ, 0 < r → r < ε →
        (∀ t : ℝ, HasSum (bJointTerm false false H U H V 1 (rootCircle r t))
          (hhbbB U V (rootCircle r t))) ∧
        hhbbB U V (rootCircle r 0) ≠ 0 ∧
        hhbbB U V (rootCircle r 1) = -hhbbB U V (rootCircle r 0) ∧
        hhbbB U V (rootCircle r 1) ≠ hhbbB U V (rootCircle r 0) := by
  let i : Fin leechData.rank := ⟨0, by rw [leech_spec.1]; decide⟩
  obtain ⟨U, V, hU, hV, hcoeff⟩ := exists_hhbb_b_coefficient_one i
  obtain ⟨ha, hzero, hsum⟩ := hhbb_hasSum_regular U V hU hV
  have hb : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := mem_ball_self zero_lt_one
  have hp : ContinuousAt (fun z : ℂ => z ^ (2 : ℕ)) 0 := continuousAt_id.pow 2
  have hc₀ : ContinuousAt (hhbbRegular U V) ((0 : ℂ) ^ (2 : ℕ)) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using (ha 0 hb).continuousAt
  have hc : ContinuousAt (fun z : ℂ => hhbbRegular U V (z ^ (2 : ℕ))) 0 :=
    ContinuousAt.comp' (f := fun z : ℂ => z ^ (2 : ℕ)) hc₀ hp
  have hn : hhbbRegular U V ((0 : ℂ) ^ (2 : ℕ)) ≠ 0 := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), hzero, hcoeff] using
      (one_ne_zero : (1 : ℂ) ≠ 0)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (hc.eventually_ne hn)
  refine ⟨U, V, min δ 1, hU, hV, hcoeff, lt_min hδ zero_lt_one, min_le_right _ _, ?_⟩
  intro r hr hrε
  have hr₁ := hrε.trans_le (min_le_right δ 1)
  have hz : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hrad : ‖(r : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_of_nonneg hr.le] using hr₁
  have hrδ : (r : ℂ) ∈ Metric.ball (0 : ℂ) δ := mem_ball_zero_iff.mpr (by
    simpa only [Complex.norm_real, Real.norm_of_nonneg hr.le] using
      hrε.trans_le (min_le_left δ 1))
  have hstart : hhbbB U V (rootCircle r 0) ≠ 0 := by
    rw [rootCircle_zero, hhbbB, (hsum _ hz hrad).tsum_eq]
    exact mul_ne_zero (zpow_ne_zero _ hz) (hsub hrδ)
  obtain ⟨hloop, hsign⟩ := hhbb_circle_hasSum U V hr hr₁
  refine ⟨hloop, hstart, hsign, ?_⟩
  rw [hsign]
  exact fun h => hstart (by linear_combination -h / 2)

#print axioms exists_hhbb_b_coefficient_one
#print axioms hhbb_hasSum_regular
#print axioms hhbb_circle_initial_germ
#print axioms hhbb_circle_local_branch
#print axioms exists_hhbb_nontrivial_b_monodromy

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBMonodromy
