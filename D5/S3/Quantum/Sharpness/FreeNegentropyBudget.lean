/- GID: D5/S3/Quantum/Sharpness/FreeNegentropyBudget
   generality: G
   mirror-B: D5/B/S3/Quantum/Sharpness/FreeNegentropyBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bound density-state sharpness by negentropy, including forgetting and endpoint laws. -/

/- Library and duplicate search audit (2026-09-04):
   * Repository searches for spectral sharpness, total variation from uniform, negentropy,
     doubly stochastic mixing, density-state eigenvalues, rank, and qubit fourth-order behavior
     found the canonical imports below but no theorem carrying all clauses together.
   * `SpectralSharpnessNegentropyBudget` proves the two central inequalities only at the finite
     spectrum level. It explicitly omits the density-state entropy bridge, forgetting law, qubit
     expansion, and rank endpoint, so it is imported rather than wrapped or rebound.
   * Pinned Mathlib searches found ordered Hermitian eigenvalues, trace/eigenvalue identities,
     convexity of `x * log x`, local logarithm remainder estimates, and l'Hopital's rule. No
     packaged finite Pinsker/negentropy theorem or whole density-state budget theorem was found.
   * No local `leansearch` or `loogle` executable and no importable third-party quantum-information
     package occurs in the pinned environment. The exact Mathlib and D5 hits are applied below.
   * Body-shape searches found the canonical `densityMatrix`, `positiveBiasLaw`,
     `spectralSharpness`, `totalVariation`, `shannonEntropy`, and `spectralPairingCapacity`
     definitions. This module reuses them and introduces only the missing density-state spectrum.
-/

import D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import D5.S3.Quantum.Sharpness.SpectralPairingCapacity
import D5.S3.Quantum.Sharpness.SpectralSharpnessDuality
import D5.S3.Quantum.Sharpness.SpectralSharpnessSaturation
import D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliSecondOrder
import D5.S3.TotalVariation.SpectralSharpnessNegentropyBudget
import D5.S3.Weil.ZetaLinear.PosIndex
import Mathlib.Analysis.Calculus.LHopital

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Sharpness.FreeNegentropyBudget

open Filter Finset Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Topology

open D5.S3.Entropy.MaxEntropy
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
open D5.S3.Quantum.Sharpness.SpectralPairingCapacity
open D5.S3.Quantum.Sharpness.SpectralSharpness
open D5.S3.Quantum.Sharpness.SpectralSharpnessDuality
open D5.S3.Quantum.Sharpness.SpectralSharpnessSaturation
open D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliSecondOrder
open D5.S3.TotalVariation.Pinsker
open D5.S3.TotalVariation.SpectralSharpnessNegentropyBudget

noncomputable section

variable {matrixIndex : Type*} [Fintype matrixIndex] [DecidableEq matrixIndex]

local instance (priority := 2000) :
    NormedAddCommGroup (Matrix matrixIndex matrixIndex Complex) :=
  Matrix.instL2OpNormedAddCommGroup

local instance (priority := 2000) :
    NormedSpace Complex (Matrix matrixIndex matrixIndex Complex) :=
  Matrix.instL2OpNormedSpace

local instance (priority := 2000) :
    NormedRing (Matrix matrixIndex matrixIndex Complex) :=
  Matrix.instL2OpNormedRing

local instance (priority := 2000) :
    NormedAlgebra Complex (Matrix matrixIndex matrixIndex Complex) :=
  Matrix.instL2OpNormedAlgebra

/-- The decreasing real eigenvalue spectrum constructed from a canonical density state. -/
noncomputable def stateSpectrum
    {n : Type*} [Fintype n] [DecidableEq n] (rho : DensityState n) :
    Fin (Fintype.card n) -> Real :=
  let hPos : (densityMatrix rho).PosSemidef := by
    rw [<- Matrix.nonneg_iff_posSemidef]
    exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1
  hPos.isHermitian.eigenvalues₀

private theorem state_spectrum_probability
    {n : Type*} [Fintype n] [DecidableEq n] (rho : DensityState n) :
    (forall i, 0 <= stateSpectrum rho i) /\ ∑ i, stateSpectrum rho i = 1 := by
  let hPos : (densityMatrix rho).PosSemidef := by
    rw [<- Matrix.nonneg_iff_posSemidef]
    exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1
  let hHerm := hPos.isHermitian
  constructor
  · intro i
    have hNonneg := hPos.eigenvalues_nonneg (RHLinalg.eigEquiv (n := n) i)
    rw [RHLinalg.eigenvalues_eigEquiv hHerm] at hNonneg
    simpa [stateSpectrum, hPos, hHerm] using hNonneg
  · have hTrace : ∑ i, hHerm.eigenvalues i = 1 := by
      have hComplex := hHerm.trace_eq_sum_eigenvalues
      have hRhoTrace : Matrix.trace (densityMatrix rho) = 1 := by
        change Matrix.trace (CStarMatrix.ofMatrix.symm rho.1) = 1
        exact rho.2.2
      rw [hRhoTrace] at hComplex
      simpa using congrArg Complex.re hComplex.symm
    have hReindex :=
      RHLinalg.sum_eigenvalues_reindex hHerm (fun x : Real => x)
    rw [hReindex] at hTrace
    simpa [stateSpectrum, hPos, hHerm] using hTrace

private theorem state_spectrum_antitone
    {n : Type*} [Fintype n] [DecidableEq n] (rho : DensityState n) :
    Antitone (stateSpectrum rho) := by
  let hPos : (densityMatrix rho).PosSemidef := by
    rw [<- Matrix.nonneg_iff_posSemidef]
    exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1
  simpa [stateSpectrum, hPos] using hPos.isHermitian.eigenvalues₀_antitone

private theorem state_spectrum_support_card_eq_rank
    {n : Type*} [Fintype n] [DecidableEq n] (rho : DensityState n) :
    (univ.filter (fun i => stateSpectrum rho i ≠ 0)).card =
      (densityMatrix rho).rank := by
  let hPos : (densityMatrix rho).PosSemidef := by
    rw [<- Matrix.nonneg_iff_posSemidef]
    exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1
  let hHerm := hPos.isHermitian
  change (univ.filter (fun i => hHerm.eigenvalues₀ i ≠ 0)).card =
    (densityMatrix rho).rank
  have hReindex := RHLinalg.card_eigenvalues_reindex hHerm (fun x : Real => 0 < x)
  have hPositiveNonzero :
      (univ.filter (fun i => 0 < hHerm.eigenvalues₀ i)).card =
        (univ.filter (fun i => hHerm.eigenvalues₀ i ≠ 0)).card := by
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hNonneg := hPos.eigenvalues_nonneg (RHLinalg.eigEquiv (n := n) i)
    rw [RHLinalg.eigenvalues_eigEquiv hHerm] at hNonneg
    constructor
    · exact ne_of_gt
    · intro hi
      exact lt_of_le_of_ne hNonneg hi.symm
  calc
    (univ.filter (fun i => hHerm.eigenvalues₀ i ≠ 0)).card =
        (univ.filter (fun i => 0 < hHerm.eigenvalues₀ i)).card := hPositiveNonzero.symm
    _ =
        RHLinalg.posIndex hHerm := by
      simpa [RHLinalg.posIndex] using hReindex.symm
    _ = (densityMatrix rho).rank := RHLinalg.posIndex_eq_rank_of_posSemidef hPos

/-- Von Neumann entropy is the Shannon entropy of the density state's ordered spectrum. -/
theorem von_neumann_entropy_eq_shannon_state_spectrum
    {n : Type*} [Fintype n] [DecidableEq n] (rho : DensityState n) :
    vonNeumannEntropy rho = shannonEntropy (stateSpectrum rho) := by
  let A : Matrix n n Complex := densityMatrix rho
  let hPos : A.PosSemidef := by
    dsimp only [A]
    rw [<- Matrix.nonneg_iff_posSemidef]
    exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1
  let hHerm := hPos.isHermitian
  have hTraceCfc (f : Real -> Real) :
      (Matrix.trace (A * cfc f A)).re =
        ∑ i, hHerm.eigenvalues i * f (hHerm.eigenvalues i) := by
    let V : Matrix n n Complex := hHerm.eigenvectorUnitary
    let D : Matrix n n Complex :=
      Matrix.diagonal (fun i => (hHerm.eigenvalues i : Complex))
    let F : Matrix n n Complex :=
      Matrix.diagonal (fun i => (f (hHerm.eigenvalues i) : Complex))
    have hStar : star V * V = 1 :=
      Unitary.star_mul_self_of_mem hHerm.eigenvectorUnitary.2
    have hAeq : A = V * D * star V := by
      simpa [V, D, Unitary.conjStarAlgAut_apply, Function.comp_def] using
        hHerm.spectral_theorem
    have hFeq : cfc f A = V * F * star V := by
      rw [hHerm.cfc_eq]
      rfl
    have hTraceEq :
        (Matrix.trace (A * cfc f A)).re =
          (Matrix.trace ((V * D * star V) * (V * F * star V))).re :=
      congrArg (fun X : Matrix n n Complex => (Matrix.trace X).re)
        (congrArg₂ (· * ·) hAeq hFeq)
    rw [hTraceEq]
    calc
      (Matrix.trace ((V * D * star V) * (V * F * star V))).re =
          (Matrix.trace (V * (D * F) * star V)).re := by
        congr 2
        calc
          (V * D * star V) * (V * F * star V) =
              V * D * (star V * V) * F * star V := by noncomm_ring
          _ = V * (D * F) * star V := by
            rw [hStar]
            simp only [Matrix.mul_one]
            noncomm_ring
      _ = (Matrix.trace (D * F)).re := by
        rw [Matrix.trace_mul_cycle, hStar, one_mul]
      _ = ∑ i, hHerm.eigenvalues i * f (hHerm.eigenvalues i) := by
        simp [D, F, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  have hLog : CFC.log rho.1 =
      CStarMatrix.ofMatrix (CFC.log (densityMatrix rho)) := rfl
  unfold vonNeumannEntropy
  rw [hLog]
  change -(Matrix.trace (densityMatrix rho * CFC.log (densityMatrix rho))).re =
    shannonEntropy (stateSpectrum rho)
  change -(Matrix.trace (A * CFC.log A)).re = shannonEntropy (stateSpectrum rho)
  rw [CFC.log, hTraceCfc]
  have hReindex :=
    RHLinalg.sum_eigenvalues_reindex hHerm (fun x : Real => x * Real.log x)
  rw [hReindex]
  simp only [shannonEntropy, Real.negMulLog]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [stateSpectrum, A]

private theorem spectral_sharpness_monotone_of_doubly_stochastic
    {n : Nat} {r r' : Fin n -> Real} {S : Matrix (Fin n) (Fin n) Real}
    (hrMono : Antitone r) (hr'Mono : Antitone r')
    (hS : S ∈ doublyStochastic Real (Fin n)) (hr : r = S *ᵥ r') :
    spectralSharpness r <= spectralSharpness r' := by
  let a : Fin n -> Real := fun i =>
    if r (Fin.rev i) <= r i then 1 else -1
  have haBound : forall i, |a i| <= 1 := by
    intro i
    by_cases hi : r (Fin.rev i) <= r i <;> simp [a, hi]
  have hgap : Antitone (fun i => r i - r (Fin.rev i)) := by
    intro i j hij
    have hforward := hrMono hij
    have hreverse := hrMono (Fin.rev_le_rev.mpr hij)
    linarith
  have haMono : Antitone a := by
    intro i j hij
    by_cases hi : r (Fin.rev i) <= r i
    · by_cases hj : r (Fin.rev j) <= r j <;> simp [a, hi, hj]
    · have hj : ¬r (Fin.rev j) <= r j := by
        intro hj
        have hjGap : 0 <= r j - r (Fin.rev j) := sub_nonneg.mpr hj
        exact hi (sub_nonneg.mp (hjGap.trans (hgap hij)))
      simp [a, hi, hj]
  have hAttains : spectralPairingCapacity r a = spectralSharpness r := by
    rw [spectralPairingCapacity, spectralSharpness]
    have hRewrite :
        (∑ i, r i * (a i - a (Fin.rev i))) =
          ∑ i, (r i - r (Fin.rev i)) * a i := by
      calc
        (∑ i, r i * (a i - a (Fin.rev i))) =
            (∑ i, r i * a i) - ∑ i, r i * a (Fin.rev i) := by
          simp only [mul_sub, Finset.sum_sub_distrib]
        _ = (∑ i, r i * a i) - ∑ i, r (Fin.rev i) * a i := by
          congr 1
          simpa using
            (Equiv.sum_comp Fin.revPerm (fun i => r (Fin.rev i) * a i))
        _ = ∑ i, (r i - r (Fin.rev i)) * a i := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
    rw [hRewrite]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : r (Fin.rev i) <= r i
    · simp only [a, if_pos hi, abs_of_nonneg (sub_nonneg.mpr hi)]
      ring
    · simp only [a, if_neg hi, abs_of_neg (sub_neg.mpr (lt_of_not_ge hi))]
      ring
  have hMixedCapacity :
      spectralPairingCapacity r a <= spectralPairingCapacity r' a :=
    spectral_pairing_capacity_monotone_of_doubly_stochastic hr'Mono haMono hS hr
  have hTargetCapacity : spectralPairingCapacity r' a <= spectralSharpness r' :=
    (spectral_sharpness_isGreatest_bounded_pairing r').2
      ⟨a, haBound, rfl⟩
  linarith

private theorem qubit_entropy_eq_bin_entropy (x : Real) :
    shannonEntropy (positiveBiasLaw (x / 2)) =
      Real.binEntropy (1 / 2 + x / 2) := by
  rw [shannonEntropy, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  norm_num [positiveBiasLaw, Fintype.sum_bool]
  congr 1
  ring

private theorem qubit_deficit_closed_form {x : Real} (hx : |x| < 1) :
    2 * (Real.log 2 - shannonEntropy (positiveBiasLaw (x / 2))) =
      (1 + x) * Real.log (1 + x) + (1 - x) * Real.log (1 - x) := by
  have hplus : 0 < 1 + x := by linarith [neg_lt_of_abs_lt hx]
  have hminus : 0 < 1 - x := by linarith [lt_of_abs_lt hx]
  rw [qubit_entropy_eq_bin_entropy]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have hp : 1 / 2 + x / 2 = (1 + x) / 2 := by ring
  have hm : 1 - (1 + x) / 2 = (1 - x) / 2 := by ring
  rw [hp, hm, Real.negMulLog, Real.negMulLog,
    Real.log_div hplus.ne' (by norm_num : (2 : Real) ≠ 0),
    Real.log_div hminus.ne' (by norm_num : (2 : Real) ≠ 0)]
  ring

private theorem qubit_twice_total_variation_eq_abs (x : Real) :
    2 * totalVariation (positiveBiasLaw (x / 2)) (positiveBiasLaw 0) = |x| := by
  rw [totalVariation]
  norm_num [positiveBiasLaw, Fintype.sum_bool]
  rw [abs_div]
  norm_num
  ring

private theorem qubit_fourth_order :
    (fun x : Real =>
      2 * (Real.log 2 - shannonEntropy (positiveBiasLaw (x / 2))) -
        x ^ 2 - x ^ 4 / 6) =O[nhds 0] (fun x : Real => x ^ 6) := by
  apply Asymptotics.IsBigO.of_bound 8
  filter_upwards [Metric.ball_mem_nhds (0 : Real) (by norm_num : (0 : Real) < 1 / 2)]
    with x hxBall
  have hx : |x| < 1 / 2 := by
    simpa [Metric.mem_ball, Real.dist_eq] using hxBall
  have hxOne : |x| < 1 := hx.trans (by norm_num)
  have hplusPos : 0 < 1 + x := by linarith [neg_lt_of_abs_lt hx]
  have hminusPos : 0 < 1 - x := by linarith [lt_of_abs_lt hx]
  have hclosed :
      2 * (Real.log 2 - shannonEntropy (positiveBiasLaw (x / 2))) =
        (1 + x) * Real.log (1 + x) + (1 - x) * Real.log (1 - x) :=
    qubit_deficit_closed_form hxOne
  have hminus := Real.abs_log_sub_add_sum_range_le hxOne 5
  have hplus := Real.abs_log_sub_add_sum_range_le
    (by simpa using hxOne : |-x| < 1) 5
  norm_num [Finset.sum_range_succ] at hminus hplus
  have hplus' :
      |-x + x ^ 2 / 2 - x ^ 3 / 3 + x ^ 4 / 4 - x ^ 5 / 5 +
        Real.log (1 + x)| <= |x| ^ 6 / (1 - |x|) := by
    convert hplus using 1
    all_goals ring_nf
  have hden : 1 / 2 <= 1 - |x| := by linarith
  have hdenPos : 0 < 1 - |x| := by linarith
  have hplusBound :
      |-x + x ^ 2 / 2 - x ^ 3 / 3 + x ^ 4 / 4 - x ^ 5 / 5 +
        Real.log (1 + x)| <= 2 * |x| ^ 6 := by
    calc
      _ <= |x| ^ 6 / (1 - |x|) := hplus'
      _ <= 2 * |x| ^ 6 := by
        apply (div_le_iff₀ hdenPos).2
        nlinarith [pow_nonneg (abs_nonneg x) 6]
  have hminusBound :
      |x + x ^ 2 / 2 + x ^ 3 / 3 + x ^ 4 / 4 + x ^ 5 / 5 +
        Real.log (1 - x)| <= 2 * |x| ^ 6 := by
    calc
      _ <= |x| ^ 6 / (1 - |x|) := hminus
      _ <= 2 * |x| ^ 6 := by
        apply (div_le_iff₀ hdenPos).2
        nlinarith [pow_nonneg (abs_nonneg x) 6]
  have hplusFactor : |1 + x| <= 3 / 2 := by
    rw [abs_of_pos hplusPos]
    linarith [le_abs_self x]
  have hminusFactor : |1 - x| <= 3 / 2 := by
    rw [abs_of_pos hminusPos]
    linarith [neg_le_of_abs_le hx.le]
  have hidentity :
      2 * (Real.log 2 - shannonEntropy (positiveBiasLaw (x / 2))) -
          x ^ 2 - x ^ 4 / 6 =
        (1 + x) *
            (-x + x ^ 2 / 2 - x ^ 3 / 3 + x ^ 4 / 4 - x ^ 5 / 5 +
              Real.log (1 + x)) +
          (1 - x) *
            (x + x ^ 2 / 2 + x ^ 3 / 3 + x ^ 4 / 4 + x ^ 5 / 5 +
              Real.log (1 - x)) +
          (2 / 5) * x ^ 6 := by
    rw [hclosed]
    ring_nf
  rw [hidentity, Real.norm_eq_abs, Real.norm_eq_abs]
  calc
    |(1 + x) *
          (-x + x ^ 2 / 2 - x ^ 3 / 3 + x ^ 4 / 4 - x ^ 5 / 5 +
            Real.log (1 + x)) +
        (1 - x) *
          (x + x ^ 2 / 2 + x ^ 3 / 3 + x ^ 4 / 4 + x ^ 5 / 5 +
            Real.log (1 - x)) +
        (2 / 5) * x ^ 6| <=
        |1 + x| *
            |-x + x ^ 2 / 2 - x ^ 3 / 3 + x ^ 4 / 4 - x ^ 5 / 5 +
              Real.log (1 + x)| +
          |1 - x| *
            |x + x ^ 2 / 2 + x ^ 3 / 3 + x ^ 4 / 4 + x ^ 5 / 5 +
              Real.log (1 - x)| +
          |2 / 5| * |x ^ 6| := by
      calc
        _ <= |(1 + x) *
              (-x + x ^ 2 / 2 - x ^ 3 / 3 + x ^ 4 / 4 - x ^ 5 / 5 +
                Real.log (1 + x))| +
            |(1 - x) *
              (x + x ^ 2 / 2 + x ^ 3 / 3 + x ^ 4 / 4 + x ^ 5 / 5 +
                Real.log (1 - x))| + |(2 / 5) * x ^ 6| := by
          linarith [abs_add_le ((1 + x) *
            (-x + x ^ 2 / 2 - x ^ 3 / 3 + x ^ 4 / 4 - x ^ 5 / 5 +
              Real.log (1 + x)) + (1 - x) *
            (x + x ^ 2 / 2 + x ^ 3 / 3 + x ^ 4 / 4 + x ^ 5 / 5 +
              Real.log (1 - x))) ((2 / 5) * x ^ 6),
            abs_add_le ((1 + x) *
              (-x + x ^ 2 / 2 - x ^ 3 / 3 + x ^ 4 / 4 - x ^ 5 / 5 +
                Real.log (1 + x))) ((1 - x) *
              (x + x ^ 2 / 2 + x ^ 3 / 3 + x ^ 4 / 4 + x ^ 5 / 5 +
                Real.log (1 - x)))]
        _ = _ := by simp only [abs_mul]
    _ <= (3 / 2) * (2 * |x| ^ 6) +
          (3 / 2) * (2 * |x| ^ 6) + (2 / 5) * |x ^ 6| := by
      gcongr
      norm_num
    _ <= 8 * |x ^ 6| := by
      rw [abs_pow]
      nlinarith [pow_nonneg (abs_nonneg x) 6]

private theorem qubit_first_order :
    Tendsto
      (fun x : Real =>
        (2 * totalVariation (positiveBiasLaw (x / 2)) (positiveBiasLaw 0)) /
          Real.sqrt
            (2 * (Real.log 2 - shannonEntropy (positiveBiasLaw (x / 2)))))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  have hRemainderLittle :
      (fun x : Real =>
        2 * (Real.log 2 - shannonEntropy (positiveBiasLaw (x / 2))) -
          x ^ 2 - x ^ 4 / 6) =o[nhds 0] (fun x : Real => x ^ 2) :=
    qubit_fourth_order.trans_isLittleO
      (Asymptotics.isLittleO_pow_pow (by omega : 2 < 6))
  have hRemainderLimit :
      Tendsto
        (fun x : Real =>
          (2 * (Real.log 2 - shannonEntropy (positiveBiasLaw (x / 2))) -
            x ^ 2 - x ^ 4 / 6) / x ^ 2)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    hRemainderLittle.tendsto_div_nhds_zero.mono_left nhdsWithin_le_nhds
  have hPowerLimit :
      Tendsto (fun x : Real => x ^ 2 / 6)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hId : Tendsto (fun x : Real => x) (nhds 0) (nhds 0) := tendsto_id
    simpa [nhdsWithin] using
      ((hId.pow 2).div_const 6).mono_left
        (inf_le_left : nhds 0 ⊓ Filter.principal (Ioi (0 : Real)) <= nhds 0)
  have hCombined :
      Tendsto
        (fun x : Real =>
          (2 * (Real.log 2 - shannonEntropy (positiveBiasLaw (x / 2))) -
              x ^ 2 - x ^ 4 / 6) / x ^ 2 + 1 + x ^ 2 / 6)
        (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    convert (hRemainderLimit.add tendsto_const_nhds).add hPowerLimit using 1
    all_goals norm_num
  have hScaled :
      Tendsto
        (fun x : Real =>
          2 * (Real.log 2 - shannonEntropy (positiveBiasLaw (x / 2))) / x ^ 2)
        (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    apply hCombined.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxPos : 0 < x := hx
    field_simp [hxPos.ne']
    ring
  have hInverse :
      Tendsto
        (fun x : Real =>
          (Real.sqrt
            (2 * (Real.log 2 - shannonEntropy (positiveBiasLaw (x / 2))) /
              x ^ 2))⁻¹)
        (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    simpa using hScaled.sqrt.inv₀ (by norm_num : Real.sqrt (1 : Real) ≠ 0)
  apply hInverse.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxPos : 0 < x := hx
  have hxNe : x ≠ 0 := hxPos.ne'
  have hEntropy :
      shannonEntropy (positiveBiasLaw (x / 2)) =
        Real.binEntropy (1 / 2 + x / 2) :=
    qubit_entropy_eq_bin_entropy x
  have hParameter : 1 / 2 + x / 2 ≠ (2 : Real)⁻¹ := by
    norm_num
    linarith
  have hDeficitPos :
      0 < Real.log 2 - shannonEntropy (positiveBiasLaw (x / 2)) := by
    rw [hEntropy]
    exact sub_pos.mpr (Real.binEntropy_lt_log_two.2 hParameter)
  have hNumeratorNonneg :
      0 <= 2 * (Real.log 2 - shannonEntropy (positiveBiasLaw (x / 2))) := by
    positivity
  have hRootPos :
      0 < Real.sqrt
        (2 * (Real.log 2 - shannonEntropy (positiveBiasLaw (x / 2)))) := by
    positivity
  rw [qubit_twice_total_variation_eq_abs, abs_of_pos hxPos,
    Real.sqrt_div hNumeratorNonneg, Real.sqrt_sq_eq_abs,
    abs_of_pos hxPos]
  field_simp [hxNe, hRootPos.ne']

private theorem shannon_entropy_le_log_support_card
    {n : Nat} (r : Fin n -> Real)
    (hr : (forall i, 0 <= r i) /\ ∑ i, r i = 1) :
    shannonEntropy r <=
      Real.log ((Finset.univ.filter (fun i => r i ≠ 0)).card) := by
  classical
  have hExists : ∃ i, r i ≠ 0 := by
    by_contra hNone
    push Not at hNone
    have hZero : ∑ i, r i = 0 := by simp [hNone]
    linarith [hr.2]
  let _ : Nonempty {i : Fin n // r i ≠ 0} := by
    rcases hExists with ⟨i, hi⟩
    exact ⟨⟨i, hi⟩⟩
  have hSubtypeSum : ∑ i : {i : Fin n // r i ≠ 0}, r i = 1 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun i => r i ≠ 0))
      (by simp) r]
    calc
      ∑ i ∈ Finset.univ.filter (fun i => r i ≠ 0), r i = ∑ i, r i := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : r i ≠ 0
        · simp [hi]
        · have hiZero : r i = 0 := not_ne_iff.mp hi
          simp [hiZero]
      _ = 1 := hr.2
  have hSubtypeProbability :
      (forall i : {i : Fin n // r i ≠ 0}, 0 <= r i) /\
        ∑ i : {i : Fin n // r i ≠ 0}, r i = 1 :=
    ⟨fun i => hr.1 i, hSubtypeSum⟩
  have hBound := entropy_le_log_card
    (fun i : {i : Fin n // r i ≠ 0} => r i) hSubtypeProbability
  have hEntropyEq :
      shannonEntropy r =
        shannonEntropy (fun i : {i : Fin n // r i ≠ 0} => r i) := by
    rw [shannonEntropy, shannonEntropy,
      ← Finset.sum_subtype (Finset.univ.filter (fun i => r i ≠ 0))
        (by simp) (fun i => Real.negMulLog (r i))]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : r i ≠ 0
    · simp [hi]
    · have hiZero : r i = 0 := not_ne_iff.mp hi
      simp [hiZero]
  rw [hEntropyEq]
  simpa [Fintype.card_subtype] using hBound

private theorem saturated_entropy_le_log_half
    {n : Nat} (r : Fin n -> Real)
    (hr : (forall i, 0 <= r i) /\ ∑ i, r i = 1)
    (hrMono : Antitone r) (hSharp : spectralSharpness r = 1) :
    let supportCard := (Finset.univ.filter (fun i => r i ≠ 0)).card
    supportCard <= n / 2 /\
      shannonEntropy r <= Real.log supportCard /\
      shannonEntropy r <= Real.log ((n / 2 : Nat) : Real) := by
  dsimp only
  have hCard :=
    (spectral_sharpness_one_iff_support_le_half r hr.1 hrMono hr.2).mp hSharp
  have hEntropy := shannon_entropy_le_log_support_card r hr
  have hExists : ∃ i, r i ≠ 0 := by
    by_contra hNone
    push Not at hNone
    have hZero : ∑ i, r i = 0 := by simp [hNone]
    linarith [hr.2]
  have hSupportPos : 0 < (Finset.univ.filter (fun i => r i ≠ 0)).card :=
    Finset.card_pos.mpr (by
      rcases hExists with ⟨i, hi⟩
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩)
  have hHalfPos : 0 < n / 2 := hSupportPos.trans_le hCard
  have hCast :
      ((Finset.univ.filter (fun i => r i ≠ 0)).card : Real) <=
        (n / 2 : Nat) := by
    exact_mod_cast hCard
  have hLog :
      Real.log ((Finset.univ.filter (fun i => r i ≠ 0)).card) <=
        Real.log ((n / 2 : Nat) : Real) := by
    exact Real.strictMonoOn_log.monotoneOn
      (show (0 : Real) < (Finset.univ.filter (fun i => r i ≠ 0)).card by
        exact_mod_cast hSupportPos)
      (show (0 : Real) < (n / 2 : Nat) by exact_mod_cast hHalfPos) hCast
  exact ⟨hCard, hEntropy, hEntropy.trans hLog⟩

/-- The variational spectral sharpness of a finite density state is bounded by twice its total
variation from the uniform spectrum and by the square root of twice its von Neumann entropy
deficit. Doubly stochastic forgetting decreases sharpness and every decreasing spectral pairing
capacity while increasing entropy. The bound is first-order sharp at the mixed qubit endpoint,
where its fourth-order gap has coefficient `1 / 6`; at sharpness one, rank controls entropy. -/
theorem free_negentropy_budget
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] (rho : DensityState n) :
    let r := stateSpectrum rho
    let u : Fin (Fintype.card n) -> Real :=
      fun _ => (Fintype.card n : Real)⁻¹
    let qubitSpectrum : Real -> Fin 2 -> Real := fun radius i =>
      if i = 0 then 1 / 2 + radius / 2 else 1 / 2 - radius / 2
    ((forall i, 0 <= r i) /\ ∑ i, r i = 1) /\
      Antitone r /\
      vonNeumannEntropy rho = shannonEntropy r /\
      IsGreatest
        {value : Real | ∃ a : Fin (Fintype.card n) -> Real,
          (forall i, |a i| <= 1) /\ spectralPairingCapacity r a = value}
        (spectralSharpness r) /\
      (spectralSharpness r <= 2 * totalVariation r u /\
        2 * totalVariation r u <=
          Real.sqrt
            (2 * (Real.log (Fintype.card n) - vonNeumannEntropy rho))) /\
      spectralSharpness r ^ 2 <=
        2 * (Real.log (Fintype.card n) - vonNeumannEntropy rho) /\
      (forall (sigma : DensityState n) (S : Matrix (Fin (Fintype.card n))
          (Fin (Fintype.card n)) Real),
        S ∈ doublyStochastic Real (Fin (Fintype.card n)) ->
        r = S *ᵥ stateSpectrum sigma ->
          spectralSharpness r <= spectralSharpness (stateSpectrum sigma) /\
          shannonEntropy (stateSpectrum sigma) <= shannonEntropy r /\
          Real.log (Fintype.card n) - shannonEntropy r <=
            Real.log (Fintype.card n) - shannonEntropy (stateSpectrum sigma) /\
          forall a : Fin (Fintype.card n) -> Real, Antitone a ->
            spectralPairingCapacity r a <=
              spectralPairingCapacity (stateSpectrum sigma) a) /\
      (forall radius : Real, 0 <= radius -> radius <= 1 ->
        (forall i, 0 <= qubitSpectrum radius i) /\
        ∑ i, qubitSpectrum radius i = 1 /\
        Antitone (qubitSpectrum radius) /\
        shannonEntropy (qubitSpectrum radius) =
          shannonEntropy (positiveBiasLaw (radius / 2)) /\
        spectralSharpness (qubitSpectrum radius) = radius /\
        2 * totalVariation (positiveBiasLaw (radius / 2)) (positiveBiasLaw 0) =
          radius) /\
      Tendsto
        (fun radius : Real =>
          (2 * totalVariation
              (positiveBiasLaw (radius / 2)) (positiveBiasLaw 0)) /
            Real.sqrt
              (2 * (Real.log 2 -
                shannonEntropy (positiveBiasLaw (radius / 2)))))
        (nhdsWithin 0 (Ioi 0)) (nhds 1) /\
      (fun radius : Real =>
        2 * (Real.log 2 - shannonEntropy (positiveBiasLaw (radius / 2))) -
          (2 * totalVariation
            (positiveBiasLaw (radius / 2)) (positiveBiasLaw 0)) ^ 2 -
          radius ^ 4 / 6) =O[nhds 0] (fun radius : Real => radius ^ 6) /\
      (spectralSharpness r = 1 ->
        (densityMatrix rho).rank <= Fintype.card n / 2 /\
        vonNeumannEntropy rho <= Real.log (densityMatrix rho).rank /\
        vonNeumannEntropy rho <= Real.log ((Fintype.card n / 2 : Nat) : Real)) := by
  classical
  dsimp only
  have hProbability := state_spectrum_probability rho
  have hAntitone := state_spectrum_antitone rho
  have hEntropy := von_neumann_entropy_eq_shannon_state_spectrum rho
  have hBudget := spectral_sharpness_negentropy_budget (stateSpectrum rho) hProbability
  dsimp only at hBudget
  have hSharpnessNonneg : 0 <= spectralSharpness (stateSpectrum rho) := by
    rw [spectralSharpness]
    positivity
  have hEntropyBound := entropy_le_log_card (stateSpectrum rho) hProbability
  simp only [Fintype.card_fin] at hBudget hEntropyBound
  have hRadicandNonneg :
      0 <= 2 * (Real.log (Fintype.card n) - vonNeumannEntropy rho) := by
    rw [hEntropy]
    nlinarith
  have hSquared :
      spectralSharpness (stateSpectrum rho) ^ 2 <=
        2 * (Real.log (Fintype.card n) - vonNeumannEntropy rho) := by
    have hSharpnessRoot :
        spectralSharpness (stateSpectrum rho) <=
          Real.sqrt
            (2 * (Real.log (Fintype.card n) - vonNeumannEntropy rho)) := by
      rw [hEntropy]
      exact hBudget.1.trans hBudget.2.1
    nlinarith [Real.sq_sqrt hRadicandNonneg,
      Real.sqrt_nonneg
        (2 * (Real.log (Fintype.card n) - vonNeumannEntropy rho))]
  refine ⟨hProbability, hAntitone, hEntropy,
    spectral_sharpness_isGreatest_bounded_pairing (stateSpectrum rho),
    ⟨hBudget.1, ?_⟩, hSquared, ?_, ?_, qubit_first_order, ?_, ?_⟩
  · rw [hEntropy]
    exact hBudget.2.1
  · intro sigma S hS hMixing
    have hSigmaProbability := state_spectrum_probability sigma
    have hSigmaAntitone := state_spectrum_antitone sigma
    have hEntropyMonotone :
        shannonEntropy (stateSpectrum sigma) <= shannonEntropy (stateSpectrum rho) := by
      have hSsum := hS
      rw [mem_doublyStochastic_iff_sum] at hSsum
      have hrow (i : Fin (Fintype.card n)) :
          stateSpectrum rho i * Real.log (stateSpectrum rho i) <=
            ∑ j, S i j *
              (stateSpectrum sigma j * Real.log (stateSpectrum sigma j)) := by
        have hJensen := Real.convexOn_mul_log.map_sum_le
          (t := Finset.univ) (w := fun j => S i j) (p := stateSpectrum sigma)
          (fun j _ => hSsum.1 i j) (by simpa using hSsum.2.1 i)
          (fun j _ => hSigmaProbability.1 j)
        rw [hMixing]
        simpa [Matrix.mulVec, dotProduct] using hJensen
      have hsum :
          (∑ i, stateSpectrum rho i * Real.log (stateSpectrum rho i)) <=
            ∑ i, stateSpectrum sigma i * Real.log (stateSpectrum sigma i) := by
        calc
          (∑ i, stateSpectrum rho i * Real.log (stateSpectrum rho i)) <=
              ∑ i, ∑ j, S i j *
                (stateSpectrum sigma j * Real.log (stateSpectrum sigma j)) :=
            Finset.sum_le_sum fun i _ => hrow i
          _ = ∑ j, ∑ i, S i j *
              (stateSpectrum sigma j * Real.log (stateSpectrum sigma j)) :=
            Finset.sum_comm
          _ = ∑ j, stateSpectrum sigma j * Real.log (stateSpectrum sigma j) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [← Finset.sum_mul]
            simp [hSsum.2.2 j]
      simpa [shannonEntropy, Real.negMulLog, ← Finset.sum_neg_distrib] using
        (neg_le_neg hsum)
    refine ⟨spectral_sharpness_monotone_of_doubly_stochastic
      hAntitone hSigmaAntitone hS hMixing, hEntropyMonotone, ?_, ?_⟩
    · linarith
    · intro a ha
      exact spectral_pairing_capacity_monotone_of_doubly_stochastic
        hSigmaAntitone ha hS hMixing
  · intro radius hRadiusNonneg hRadiusLe
    have hrev0 : Fin.rev (0 : Fin 2) = 1 := by decide
    have hrev1 : Fin.rev (1 : Fin 2) = 0 := by decide
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp <;> linarith
    · norm_num [Fin.sum_univ_two]
    · intro i j hij
      fin_cases i
      all_goals fin_cases j
      all_goals simp_all
      all_goals linarith
    · rw [shannonEntropy, shannonEntropy]
      norm_num [Fin.sum_univ_two, Fintype.sum_bool, positiveBiasLaw]
    · rw [spectralSharpness]
      simp only [Fin.sum_univ_two]
      norm_num [hrev0, hrev1, abs_of_nonneg hRadiusNonneg]
      rw [show 1 / 2 - radius / 2 - (1 / 2 + radius / 2) = -radius by ring,
        abs_neg, abs_of_nonneg hRadiusNonneg]
      ring
    · rw [qubit_twice_total_variation_eq_abs, abs_of_nonneg hRadiusNonneg]
  · simpa only [qubit_twice_total_variation_eq_abs, sq_abs] using qubit_fourth_order
  · intro hSharp
    have hSaturated := saturated_entropy_le_log_half
      (stateSpectrum rho) hProbability hAntitone hSharp
    have hRank := state_spectrum_support_card_eq_rank rho
    refine ⟨?_, ?_, ?_⟩
    · simpa [hRank] using hSaturated.1
    · calc
        vonNeumannEntropy rho = shannonEntropy (stateSpectrum rho) := hEntropy
        _ <= Real.log
            ((Finset.univ.filter (fun i => stateSpectrum rho i ≠ 0)).card) :=
          hSaturated.2.1
        _ = Real.log (densityMatrix rho).rank :=
          congrArg (fun k : Nat => Real.log (k : Real)) hRank
    · exact hEntropy.trans_le hSaturated.2.2

#print axioms free_negentropy_budget

end

end D5.S3.Quantum.Sharpness.FreeNegentropyBudget
