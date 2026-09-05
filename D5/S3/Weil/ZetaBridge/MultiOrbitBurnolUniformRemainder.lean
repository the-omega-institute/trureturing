/- GID: D5/S3/Weil/ZetaBridge/MultiOrbitBurnolUniformRemainder
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/MultiOrbitBurnolUniformRemainder
   mirror-E: none(waiver:finite-family-full-zero-sum-certificate)
   anchors: []
   digest: Construct a coefficient-uniform geometrically decaying full Weil remainder and realize an entire finite negative family without assuming a remainder bound. -/

import D5.S3.Weil.ZetaBridge.FiniteOrbitBurnolPacket
import D5.S3.Weil.ZetaBridge.FiniteMixedWeilMajorant

/-!
# Uniform multi-orbit Burnol remainder

For a fixed finite separated family of nonreal off-line zero orbits, the
previous nodes construct a common peak b and simultaneous killers k_i. Let
f_{N,a} = sum_i a_i (b^{*(N+1)} * k_i).
Its selected-orbit contribution is exactly -4 sum_i m_i |a_i|^2.
All remaining zeros satisfy a single bound

  |R_N(a)| <= (1/4)^(N+1) C ||a||_2^2,

where C is the absolutely summed finite mixed-convolution majorant. It depends
on the chosen finite basis but not on a or N. This controls all cross terms,
not only the basis diagonals. The geometric factor supplies a finite N for
which every nonzero coefficient vector gives a negative full Weil square.

No assertion that an off-line zero exists, no uniformity over changing frames,
no computable bound on interpolation conditioning, and no RH conclusion are
made. All statements are conditional only on a valid finite orbit frame.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.MultiOrbitBurnolUniformRemainder

open Filter
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Fourier.ConvolutionPowerAmplification
open D5.S3.Weil.HolonomyBridge.OffLineOrbitParityDecomposition
open D5.S3.Weil.ZetaBridge.ConvolutionSquareOrbitBounds
open D5.S3.Weil.ZetaBridge.WeilEvaluationObservableSubspace
open D5.S3.Weil.ZetaBridge.FiniteEvenWeilOddInterpolation
open D5.S3.Weil.ZetaBridge.FiniteOrbitBurnolPacket
open D5.S3.Weil.ZetaBridge.FiniteMixedWeilMajorant
open D5.S3.Weil.ZetaBridge.QuantitativeMultiOrbitWeilNegativeCertificate
open D5.S3.Weil.ZetaBridge.SymmetricConvergentOfZetaSummable
open D5.S3.Weil.ZetaBridge.OffLineNonrealZeroNegativeWeilSquare
open scoped BigOperators ComplexConjugate Topology

variable {Z : ZeroData} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : FiniteEvenWeilOrbitFrame Z ι)

/-- A basis packet uses the same peak and depth for every orbit channel. -/
def burnolBasis (P : OrbitBurnolPacket F) (N : ℕ) (i : ι) : WeilTestFunction :=
  convolve (convolutionSuccPower P.peak N) (P.killer i)

/-- Explicit finite linear synthesis, so the realized family is a linear
coefficient family before any sign estimate is applied. -/
def burnolSynthesis (P : OrbitBurnolPacket F) (N : ℕ) (a : ι → ℂ) :
    WeilTestFunction :=
  finiteWeilLinearCombination a (burnolBasis F P N)

/-- The common peak factors out of the entire synthesized transform. -/
theorem burnolSynthesis_fourierLaplace
    (P : OrbitBurnolPacket F) (N : ℕ) (a : ι → ℂ) (z : ℂ) :
    fourierLaplace (burnolSynthesis F P N a) z =
      fourierLaplace P.peak z ^ (N + 1) *
        fourierLaplace (finiteWeilLinearCombination a P.killer) z := by
  rw [burnolSynthesis, fourierLaplace_finiteWeilLinearCombination,
    fourierLaplace_finiteWeilLinearCombination, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [burnolBasis, fourierLaplace_convolve_complex,
    fourierLaplace_convolutionSuccPower]
  ring

/-- Both target signs, and hence vanishing target even channels, are preserved
at every common power depth. -/
theorem burnolSynthesis_target_values
    (P : OrbitBurnolPacket F) (N : ℕ) (a : ι → ℂ) (j : ι) :
    fourierLaplace (burnolSynthesis F P N a) (Z.gamma (F.index j)) = a j ∧
      fourierLaplace (burnolSynthesis F P N a)
        (conj (Z.gamma (F.index j))) = -a j := by
  have hp : fourierLaplace (finiteWeilLinearCombination a P.killer)
      (Z.gamma (F.index j)) = a j := by
    rw [fourierLaplace_finiteWeilLinearCombination]
    have hkill (i : ι) : fourierLaplace (P.killer i)
        (Z.gamma (F.index j)) = frameDelta i j := (P.killer_values i j).1
    simp_rw [hkill]
    simp [frameDelta]
  have hm : fourierLaplace (finiteWeilLinearCombination a P.killer)
      (conj (Z.gamma (F.index j))) = -a j := by
    rw [fourierLaplace_finiteWeilLinearCombination]
    have hkill (i : ι) : fourierLaplace (P.killer i)
        (conj (Z.gamma (F.index j))) = -frameDelta i j := (P.killer_values i j).2
    simp_rw [hkill]
    simp [frameDelta]
  constructor
  · rw [burnolSynthesis_fourierLaplace, (P.peak_values j).1, hp]
    simp
  · rw [burnolSynthesis_fourierLaplace, (P.peak_values j).2, hm]
    simp

/-- Reduced odd evaluation remains a right inverse at every power depth. -/
theorem burnolSynthesis_readout
    (P : OrbitBurnolPacket F) (N : ℕ) (a : ι → ℂ) (j : ι) :
    frameOddReadout F (burnolSynthesis F P N a) j = a j := by
  rw [frameOddReadout, oddSpectralChannel,
    (burnolSynthesis_target_values F P N a j).1,
    (burnolSynthesis_target_values F P N a j).2]
  ring

theorem burnolSynthesis_injective (P : OrbitBurnolPacket F) (N : ℕ) :
    Function.Injective (burnolSynthesis F P N) := by
  intro a b hab
  funext i
  have h := congrArg (fun g => frameOddReadout F g i) hab
  simpa only [burnolSynthesis_readout] using h

/-- Exact common-power factorization, including analytic multiplicity. -/
theorem burnolSynthesis_zeroSummand
    (P : OrbitBurnolPacket F) (N : ℕ) (a : ι → ℂ) (j : ℕ) :
    zeroSummand Z (convolutionSquare (burnolSynthesis F P N a)) j =
      (fourierLaplace P.peak (Z.gamma j) *
        conj (fourierLaplace P.peak (conj (Z.gamma j)))) ^ (N + 1) *
          zeroSummand Z (convolutionSquare
            (finiteWeilLinearCombination a P.killer)) j := by
  rw [zeroSummand, fourierLaplace_convolutionSquare_complex,
    burnolSynthesis_fourierLaplace, burnolSynthesis_fourierLaplace,
    zeroSummand, fourierLaplace_convolutionSquare_complex]
  simp only [map_mul, map_pow, mul_pow]
  ring

/-- A pointwise bound on the complement of all target orbits. Exception
killers handle the finite ball; geometric decay handles its complement. -/
theorem burnolSynthesis_complement_norm_le
    (P : OrbitBurnolPacket F) (N : ℕ) (a : ι → ℂ)
    (j : ℕ) (hjO : j ∉ frameTargetIndices F) :
    ‖zeroSummand Z (convolutionSquare (burnolSynthesis F P N a)) j‖ ≤
      (1 / 4 : ℝ) ^ (N + 1) * finiteComplexEnergy a *
        finiteMixedMajorant Z P.killer j := by
  rw [burnolSynthesis_zeroSummand]
  by_cases hjE : j ∈ P.exceptional
  · have hkzero : fourierLaplace (finiteWeilLinearCombination a P.killer)
        (Z.gamma j) = 0 := by
      rw [fourierLaplace_finiteWeilLinearCombination]
      apply Finset.sum_eq_zero
      intro i _
      rw [P.kills_exception i j hjE hjO, mul_zero]
    have hs : zeroSummand Z (convolutionSquare
        (finiteWeilLinearCombination a P.killer)) j = 0 := by
      rw [zeroSummand, fourierLaplace_convolutionSquare_complex, hkzero]
      simp
    rw [hs, mul_zero, norm_zero]
    exact mul_nonneg
      (mul_nonneg (by positivity) (finiteComplexEnergy_nonneg a))
      (finiteMixedMajorant_nonneg Z P.killer j)
  · have hb := P.peak_tail j hjE
    have hbase :
        ‖fourierLaplace P.peak (Z.gamma j) *
          conj (fourierLaplace P.peak (conj (Z.gamma j)))‖ ≤ (1 / 4 : ℝ) := by
      rw [norm_mul, Complex.norm_conj]
      calc
        _ ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) :=
          mul_le_mul hb.1 hb.2 (norm_nonneg _) (by norm_num)
        _ = _ := by norm_num
    rw [norm_mul, norm_pow]
    calc
      _ ≤ (1 / 4 : ℝ) ^ (N + 1) *
          (finiteComplexEnergy a * finiteMixedMajorant Z P.killer j) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hbase (N + 1))
          (zeroSummand_finite_synthesis_norm_le Z a P.killer j)
          (norm_nonneg _) (by positivity)
      _ = _ := by ring

/-- The absolute full complement is uniformly bounded for every coefficient
vector by the same geometrically decaying finite constant. -/
theorem burnolSynthesis_tail_bound
    (P : OrbitBurnolPacket F) (N : ℕ) (a : ι → ℂ) :
    ‖∑' j : {j : ℕ // j ∉ frameTargetIndices F},
        zeroSummand Z (convolutionSquare (burnolSynthesis F P N a)) j.1‖ ≤
      ((1 / 4 : ℝ) ^ (N + 1) * finiteMixedMajorantTotal Z P.killer) *
        finiteComplexEnergy a := by
  let c : ℝ := (1 / 4 : ℝ) ^ (N + 1) * finiteComplexEnergy a
  let tail : {j : ℕ // j ∉ frameTargetIndices F} → ℂ := fun j =>
    zeroSummand Z (convolutionSquare (burnolSynthesis F P N a)) j.1
  have hc : 0 ≤ c := mul_nonneg (by positivity) (finiteComplexEnergy_nonneg a)
  have htail := (zeroSummand_summable_of_zeroData Z
    (convolutionSquare (burnolSynthesis F P N a))).subtype
      (fun j => j ∉ frameTargetIndices F)
  have hmajorAll := finiteMixedMajorant_summable Z P.killer
  have hmajorSub := hmajorAll.subtype (fun j => j ∉ frameTargetIndices F)
  have hpoint : ∀ j : {j : ℕ // j ∉ frameTargetIndices F},
      ‖tail j‖ ≤ c * finiteMixedMajorant Z P.killer j.1 := by
    intro j
    exact burnolSynthesis_complement_norm_le F P N a j.1 j.2
  calc
    ‖∑' j, tail j‖ ≤ ∑' j, ‖tail j‖ := norm_tsum_le_tsum_norm htail.norm
    _ ≤ ∑' j : {j : ℕ // j ∉ frameTargetIndices F},
        c * finiteMixedMajorant Z P.killer j.1 :=
      htail.norm.tsum_le_tsum hpoint (hmajorSub.mul_left c)
    _ = c * ∑' j : {j : ℕ // j ∉ frameTargetIndices F},
        finiteMixedMajorant Z P.killer j.1 := by rw [tsum_mul_left]
    _ ≤ c * finiteMixedMajorantTotal Z P.killer := by
      apply mul_le_mul_of_nonneg_left _ hc
      exact hmajorAll.tsum_subtype_le (finiteMixedMajorant Z P.killer)
        (fun j => j ∉ frameTargetIndices F)
        (finiteMixedMajorant_nonneg Z P.killer)
    _ = _ := by dsimp [c]; ring

/-- Each selected orbit retains exactly its prescribed negative contribution. -/
theorem burnolSynthesis_orbit_value
    (P : OrbitBurnolPacket F) (N : ℕ) (a : ι → ℂ) (i : ι) :
    (∑ j ∈ zeroOrbit Z (F.index i),
      zeroSummand Z (convolutionSquare (burnolSynthesis F P N a)) j).re =
        -4 * (Z.multiplicity (F.index i) : ℝ) * Complex.normSq (a i) := by
  have h := (off_line_orbit_parity_decomposition Z
    (burnolSynthesis F P N a) (F.index i)
    (F.conjugateMove i) (F.offLine i)).1
  dsimp only at h
  rw [(burnolSynthesis_target_values F P N a i).1,
    (burnolSynthesis_target_values F P N a i).2] at h
  have he : evenSpectralChannel (a i) (-a i) = 0 := by
    unfold evenSpectralChannel
    ring
  have ho : oddSpectralChannel (a i) (-a i) = a i := by
    unfold oddSpectralChannel
    ring
  change (∑ j ∈ zeroOrbit Z (F.index i),
      zeroSummand Z (convolutionSquare (burnolSynthesis F P N a)) j).re =
    orbitEvenEnergy (Z.multiplicity (F.index i)) (a i) (-a i) -
      orbitOddEnergy (Z.multiplicity (F.index i)) (a i) (-a i) at h
  rw [h, orbitEvenEnergy, orbitOddEnergy, he, ho]
  simp only [Complex.normSq_zero, mul_zero, zero_sub]
  ring

/-- Disjointness proved from the frame certificate identifies the target
block sum with the sum over the actual union, with no overcounting. -/
theorem burnolSynthesis_target_union_value
    (P : OrbitBurnolPacket F) (N : ℕ) (a : ι → ℂ) :
    (∑ j ∈ frameTargetIndices F,
      zeroSummand Z (convolutionSquare (burnolSynthesis F P N a)) j).re =
        frameOddTargetQuadratic F a := by
  have hsum :
      (∑ j ∈ frameTargetIndices F,
        zeroSummand Z (convolutionSquare (burnolSynthesis F P N a)) j) =
      ∑ i, ∑ j ∈ zeroOrbit Z (F.index i),
        zeroSummand Z (convolutionSquare (burnolSynthesis F P N a)) j := by
    rw [frameTargetIndices, Finset.sum_biUnion]
    intro i _ j _ hij
    exact frame_orbits_pairwise_disjoint F i j hij
  rw [hsum]
  change Complex.reAddGroupHom
      (∑ i, ∑ j ∈ zeroOrbit Z (F.index i),
        zeroSummand Z (convolutionSquare (burnolSynthesis F P N a)) j) = _
  rw [map_sum]
  change (∑ i, (∑ j ∈ zeroOrbit Z (F.index i),
    zeroSummand Z (convolutionSquare (burnolSynthesis F P N a)) j).re) = _
  simp_rw [burnolSynthesis_orbit_value]
  unfold frameOddTargetQuadratic
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual full Weil quadratic of a common-depth packet. -/
def burnolFullQuadratic (P : OrbitBurnolPacket F) (N : ℕ) (a : ι → ℂ) : ℝ :=
  (zeroSum Z (convolutionSquare (burnolSynthesis F P N a))
    (symmetricConvergent_of_zeroData Z
      (convolutionSquare (burnolSynthesis F P N a)))).re

/-- The remainder is the difference between the actual full form and its
proved exact selected-orbit contribution. -/
def burnolRemainder (P : OrbitBurnolPacket F) (N : ℕ) (a : ι → ℂ) : ℝ :=
  burnolFullQuadratic F P N a - frameOddTargetQuadratic F a

/-- The remainder is exactly the real part of the absolutely convergent
complementary zero sum. -/
theorem burnolRemainder_eq_tail (P : OrbitBurnolPacket F) (N : ℕ) (a : ι → ℂ) :
    burnolRemainder F P N a =
      (∑' j : {j : ℕ // j ∉ frameTargetIndices F},
        zeroSummand Z (convolutionSquare (burnolSynthesis F P N a)) j.1).re := by
  have hall := zeroSummand_summable_of_zeroData Z
    (convolutionSquare (burnolSynthesis F P N a))
  rw [burnolRemainder, burnolFullQuadratic, zeroSum_eq_tsum_of_zeroData,
    ← hall.sum_add_tsum_subtype_compl (frameTargetIndices F), Complex.add_re,
    burnolSynthesis_target_union_value]
  ring

/-- The derived, coefficient-uniform, geometrically decaying remainder bound. -/
theorem multiOrbitBurnol_uniform_remainder
    (P : OrbitBurnolPacket F) (N : ℕ) (a : ι → ℂ) :
    |burnolRemainder F P N a| ≤
      ((1 / 4 : ℝ) ^ (N + 1) * finiteMixedMajorantTotal Z P.killer) *
        finiteComplexEnergy a := by
  rw [burnolRemainder_eq_tail]
  exact (Complex.abs_re_le_norm _).trans (burnolSynthesis_tail_bound F P N a)

/-- The same error coefficient tends to zero independently of all coefficient
vectors in the fixed finite frame. -/
theorem multiOrbitBurnol_error_tendsto_zero (P : OrbitBurnolPacket F) :
    Tendsto (fun N : ℕ =>
      (1 / 4 : ℝ) ^ (N + 1) * finiteMixedMajorantTotal Z P.killer)
      atTop (nhds 0) := by
  have hpow : Tendsto (fun N : ℕ => (1 / 4 : ℝ) ^ N) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  simpa [pow_succ, mul_assoc] using
    hpow.mul_const ((1 / 4 : ℝ) * finiteMixedMajorantTotal Z P.killer)

/-- One finite common depth makes the whole coefficient family strictly
negative. The multiplicity floor one is derived from actual analytic orders. -/
theorem exists_common_depth_strictly_negative (P : OrbitBurnolPacket F) :
    ∃ N : ℕ, ∀ a : ι → ℂ, a ≠ 0 → burnolFullQuadratic F P N a < 0 := by
  obtain ⟨N, hN⟩ := exists_quarter_power_mul_lt
    (finiteMixedMajorantTotal Z P.killer) 4
    (finiteMixedMajorantTotal_nonneg Z P.killer) (by norm_num)
  refine ⟨N, ?_⟩
  apply strictNegative_of_uniformQuadraticRemainder
    (weight := fun i => 4 * (Z.multiplicity (F.index i) : ℝ))
    (margin := 4)
    (epsilon := (1 / 4 : ℝ) ^ (N + 1) * finiteMixedMajorantTotal Z P.killer)
    (full := burnolFullQuadratic F P N)
    (remainder := burnolRemainder F P N)
  · norm_num
  · intro i
    have hm : (1 : ℝ) ≤ (Z.multiplicity (F.index i) : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr (Z.multiplicity_pos (F.index i)))
    nlinarith
  · exact hN
  · intro a
    rw [burnolRemainder, ← frameOddTargetQuadratic_eq_weighted]
    ring
  · exact multiOrbitBurnol_uniform_remainder F P N

/-- Final full-zeta statement. A valid finite separated family of nonreal
 off-line orbits yields an injective finite linear synthesis whose every
nonzero coefficient vector has a strictly negative actual full Weil zero sum.
There is no supplied uniform remainder assumption. -/
theorem finite_multiOrbit_full_weil_negative_family
    (F : FiniteEvenWeilOrbitFrame Z ι) :
    ∃ basis : ι → WeilTestFunction,
      Function.Injective (fun a : ι → ℂ => finiteWeilLinearCombination a basis) ∧
      ∀ a : ι → ℂ, a ≠ 0 →
        (zeroSum Z (convolutionSquare (finiteWeilLinearCombination a basis))
          (symmetricConvergent_of_zeroData Z
            (convolutionSquare (finiteWeilLinearCombination a basis)))).re < 0 := by
  let P := chosenOrbitBurnolPacket F
  obtain ⟨N, hN⟩ := exists_common_depth_strictly_negative F P
  exact ⟨burnolBasis F P N, burnolSynthesis_injective F P N, hN⟩

#print axioms burnolSynthesis_target_union_value
#print axioms multiOrbitBurnol_uniform_remainder
#print axioms multiOrbitBurnol_error_tendsto_zero
#print axioms exists_common_depth_strictly_negative
#print axioms finite_multiOrbit_full_weil_negative_family

end D5.S3.Weil.ZetaBridge.MultiOrbitBurnolUniformRemainder
