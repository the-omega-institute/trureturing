/- GID: D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/GraphDensity/FormationBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Qubit entropy concavity and convex-roof formation bounds. -/

/-
proof_shape: FormationBounds.entropy_eigenvalues: bind-only; consumer FormationBounds.qubit_entropy_det
proof_shape: FormationBounds.cost_set_nonempty_iff: bind-only; consumer FormationBounds.Selective.selective_formation, SelectiveFormationBounds.embedded_formation_lower, FormationBounds.formation_nonneg, FormationBounds.Witness.witness_lower
proof_shape: FormationBounds.Analytic.log_two_bounds: bind-only; consumer FormationBounds.Analytic.binary_lower, FormationBounds.Analytic.binary_upper
proof_shape: FormationBounds.Analytic.h_nonneg: bind-only; consumer FormationBounds.qubit_entropy_nonneg
proof_shape: FormationBounds.Analytic.h_le_one: bind-only; consumer FormationBounds.qubit_entropy_le_one
proof_shape: FormationBounds.Analytic.h_strictMonoOn: bind-only; consumer FormationBounds.Analytic.f_monotone, FormationBounds.Analytic.f_lower, FormationBounds.Analytic.star_root_upper, FormationBounds.g_antitone
proof_shape: FormationBounds.Analytic.h_concave: bind-only; consumer FormationBounds.g_concave
proof_shape: FormationBounds.Analytic.binary_lower: bind-only; consumer FormationBounds.Analytic.f_lower
proof_shape: FormationBounds.Analytic.binary_upper: bind-only; consumer FormationBounds.Analytic.star_root_upper
proof_shape: FormationBounds.Analytic.smaller_root_mem: bind-only; consumer FormationBounds.Analytic.f_monotone, FormationBounds.Analytic.f_lower, FormationBounds.Analytic.star_root_upper
proof_shape: FormationBounds.Analytic.f_monotone: bind-only; consumer FormationBounds.Witness.witness_lower
proof_shape: FormationBounds.Analytic.f_lower: bind-only; consumer FormationBounds.Analytic.lower_rational
proof_shape: FormationBounds.Analytic.star_root_upper: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.normalizedU_entropy_bound
proof_shape: FormationBounds.Analytic.lower_prefactor: bind-only; consumer FormationBounds.Analytic.lower_rational
proof_shape: FormationBounds.Analytic.lower_rational: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.family_lower
proof_shape: FormationBounds.Analytic.upper_rational: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.star_upper
proof_shape: FormationBounds.qubit_entropy_det: bind-only; consumer FormationBounds.qubit_entropy_nonneg, FormationBounds.qubit_entropy_le_one, FormationBounds.entropy_bloch, FormationBounds.Direct.pure_entropy_f, BraunsteinGhoshSeveriniStarRefutation.Star.normalizedU_entropy, BraunsteinGhoshSeveriniStarRefutation.Star.single_row_entropy
proof_shape: FormationBounds.qubit_det_bounds: bind-only; consumer FormationBounds.qubit_entropy_nonneg, FormationBounds.bloch_mem, FormationBounds.Direct.pure_concurrence_mem
proof_shape: FormationBounds.qubit_entropy_nonneg: bind-only; consumer FormationBounds.pure_qubit_nonneg
proof_shape: FormationBounds.qubit_entropy_le_one: bind-only; consumer FormationBounds.pure_qubit_le_one
proof_shape: FormationBounds.trace_outer: bind-only; consumer FormationBounds.Selective.branch_probability, FormationBounds.marginal_trace
proof_shape: FormationBounds.marginal_trace: bind-only; consumer FormationBounds.Selective.pure_measurement_entropy, FormationBounds.pure_qubit_nonneg, FormationBounds.pure_qubit_le_one, FormationBounds.Direct.pure_entropy_f, FormationBounds.Direct.pure_concurrence_mem, BraunsteinGhoshSeveriniStarRefutation.Star.normalizedU_entropy, BraunsteinGhoshSeveriniStarRefutation.Star.single_row_entropy
proof_shape: FormationBounds.pure_qubit_nonneg: bind-only; consumer FormationBounds.Selective.selective_formation, FormationBounds.formation_nonneg, FormationBounds.formation_le_cost
proof_shape: FormationBounds.pure_qubit_le_one: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.star_cost_bound
proof_shape: FormationBounds.bloch_sq: bind-only; consumer FormationBounds.bloch_mem, FormationBounds.entropy_bloch
proof_shape: FormationBounds.bloch_mem: bind-only; consumer FormationBounds.qubit_entropy_concave
proof_shape: FormationBounds.entropy_bloch: bind-only; consumer FormationBounds.qubit_entropy_concave
proof_shape: FormationBounds.g_antitone: bind-only; consumer FormationBounds.qubit_entropy_concave
proof_shape: FormationBounds.g_concave: bind-only; consumer FormationBounds.qubit_entropy_concave
proof_shape: FormationBounds.bloch_mix: bind-only; consumer FormationBounds.qubit_entropy_concave
proof_shape: FormationBounds.qubit_density_convex: bind-only; consumer FormationBounds.qubit_entropy_concave
proof_shape: FormationBounds.qubit_entropy_concave: bind-only; consumer FormationBounds.Selective.pure_measurement_entropy
proof_shape: FormationBounds.Analytic.s_bounds: bind-only; consumer FormationBounds.Analytic.deriv_f, FormationBounds.Analytic.deriv_fp, FormationBounds.Analytic.f_convex
proof_shape: FormationBounds.Analytic.deriv_s: bind-only; consumer FormationBounds.Analytic.deriv_f, FormationBounds.Analytic.deriv_fp
proof_shape: FormationBounds.Analytic.deriv_f: bind-only; consumer FormationBounds.Analytic.f_convex
proof_shape: FormationBounds.Analytic.deriv_fp: bind-only; consumer FormationBounds.Analytic.f_convex
proof_shape: FormationBounds.Analytic.L_lower: bind-only; consumer FormationBounds.Analytic.f_convex
proof_shape: FormationBounds.Analytic.f_convex: bind-only; consumer FormationBounds.Witness.witness_lower
proof_shape: FormationBounds.spectral_ensemble_nonempty: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.graph_ensemble_nonempty, BraunsteinGhoshSeveriniStarRefutation.Witness.R_lower
proof_shape: FormationBounds.formation_nonneg: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.family_lower
proof_shape: FormationBounds.formation_le_cost: bind-only; consumer FormationBounds.Selective.selective_formation, SelectiveFormationBounds.embedded_formation_lower, BraunsteinGhoshSeveriniStarRefutation.Star.star_upper
proof_shape: FormationBounds.Direct.pure_det: bind-only; consumer FormationBounds.Direct.pure_entropy_f, FormationBounds.Direct.pure_concurrence_mem
proof_shape: FormationBounds.Direct.pure_entropy_f: bind-only; consumer FormationBounds.Witness.witness_lower
proof_shape: FormationBounds.Direct.pure_concurrence_mem: bind-only; consumer FormationBounds.Direct.pure_witness, FormationBounds.Witness.witness_lower
proof_shape: FormationBounds.Direct.witnessQ_coordinates: bind-only; consumer FormationBounds.Direct.homogeneous_witness
proof_shape: FormationBounds.Direct.matrix_quadratic_det_lower: bind-only; consumer FormationBounds.Direct.homogeneous_witness
proof_shape: FormationBounds.Direct.homogeneous_witness: bind-only; consumer FormationBounds.Direct.pure_witness
proof_shape: FormationBounds.Direct.pure_witness: bind-only; consumer FormationBounds.Witness.witness_le_ensemble
proof_shape: FormationBounds.Witness.expectation_average: bind-only; consumer FormationBounds.Witness.witness_le_ensemble
proof_shape: FormationBounds.Witness.witness_le_ensemble: bind-only; consumer FormationBounds.Witness.witness_lower
proof_shape: FormationBounds.Witness.witness_lower: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Witness.R_lower
proof_shape: FormationBounds.Selective.branchMass_nonneg: bind-only; consumer FormationBounds.Selective.branchVec_unit, FormationBounds.Selective.branch_outer, FormationBounds.Selective.pure_measurement_entropy, FormationBounds.Selective.conditionalEnsemble, FormationBounds.Selective.selective_formation
proof_shape: FormationBounds.Selective.sum_branchMass: bind-only; consumer FormationBounds.Selective.pure_measurement_entropy
proof_shape: FormationBounds.Selective.restrict_zero_of_mass_zero: bind-only; consumer FormationBounds.Selective.branch_outer
proof_shape: FormationBounds.Selective.branchVec_unit: bind-only; consumer FormationBounds.Selective.pure_measurement_entropy, FormationBounds.Selective.conditionalEnsemble, FormationBounds.Selective.selective_formation
proof_shape: FormationBounds.Selective.branch_outer: bind-only; consumer FormationBounds.Selective.marginal_branch_mixture, FormationBounds.Selective.conditionalEnsemble
proof_shape: FormationBounds.Selective.marginal_partition: bind-only; consumer FormationBounds.Selective.marginal_branch_mixture
proof_shape: FormationBounds.Selective.marginal_branch_mixture: bind-only; consumer FormationBounds.Selective.pure_measurement_entropy
proof_shape: FormationBounds.Selective.pure_measurement_entropy: bind-only; consumer FormationBounds.Selective.selective_formation
proof_shape: FormationBounds.Selective.projected_average: bind-only; consumer FormationBounds.Selective.branch_probability, FormationBounds.Selective.conditionalEnsemble
proof_shape: FormationBounds.Selective.branch_probability: bind-only; consumer FormationBounds.Selective.conditionalEnsemble
proof_shape: FormationBounds.Selective.selective_formation: content; consumer BraunsteinGhoshSeveriniStarRefutation.family_lower
escape_witness: D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Selective.selective_formation; the
FormationBounds.Selective.conditionalEnsemble construction
transports each input ensemble to its normalized projected branches; the branch-cost inequality
is consumed by BraunsteinGhoshSeveriniStarRefutation.family_lower.
admission_basis: escape-witness
Direct frozen dependencies (declaration statement_id):
  D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.marginal_amplitude
    sha256:7cc4250aa55e5ad43de2a9800fc4e356e24ecb3141345daf2ffaeda4601bfe50
  D5/S3/Quantum/CloningMachine.binaryEntropyBits
    sha256:688128ab90010a81f7deda9f09bce484b31dd0c87b4be4eba0ee15f631995292
  D5/S3/Quantum/Information/PartialTraceMutualInformation.spectralEntropy
    sha256:09c9a32f68ac5469fc76809a5425f56bb1bf01e9420bbc9a5e90fe560c195bbf
  D5/S3/Quantum/Fibers/PhysicalFiber.finite_dimensional_physical_fiber
    sha256:20c3cc4b8eb976ba90fe5823cc1a6fb4ef0812d411aa5a82926a53aa578aa013
  D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity
    sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3
  D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity
    sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight
    sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77
  D5/S3/Quantum/Information/PartialTraceMutualInformation.trace_partialTraceRight
    sha256:2e0d10f59a41befee8bb5e380b1d8d7db7e14a2bbed6d47af5089807c0905813
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_posSemidef
    sha256:534be990ab7c643fd18c2a086aa7a7b696bb02a8baa49a26c15e479b63e74944
  D5/S3/Quantum/Information/ActualPureQubitGeometry.blochLinear
    sha256:84df90af4dbe5369a3e07ee6a05271fe64b966793922f7a34c93ceccef3d91cf
  D5/S3/Quantum/Information/ActualPureQubitGeometry.bloch
    sha256:cc88c714292e1a1b7f96163a344340fa2144c8b2caffc5cb2196fb9df44fd3e5
  D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.partialTransposeB
    sha256:894491a0350c31f846bcfc59cbb3e13f12eb0801f6a00517db381f0dc0ecc393
Information-escape registration is paused under CLAUDE.md §3.9 「信息逃逸登记暂缓」.
MoreauYosidaFormationSelectiveLoccRefutation.E_F uses an ENNReal infimum,
density-state ensembles and natural-log entropy; it is not this real bit-entropy sInf.
The source expression uses eigenvalues and the literal partialTraceRight.
-/

import D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
import Mathlib.Analysis.Normed.Module.Normalize
import D5.S3.Quantum.Fibers.PhysicalFiber
import D5.S3.Quantum.CloningMachine
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
import D5.S3.Quantum.Information.ActualPureQubitGeometry
import D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation

noncomputable section
open D5.S3.Quantum.CloningMachine (binaryEntropyBits)
open D5.S3.Quantum.Fibers.PhysicalFiber (physicalFiber finite_dimensional_physical_fiber)
open scoped BigOperators ComplexOrder MatrixOrder
open Set Matrix
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum (bloch blochLinear)
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight partialTraceLeft)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation (partialTransposeB)
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds
structure Ensemble {p q : ℕ} (ρ : (Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ)) where
  N : ℕ
  weight : Fin N → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  le_one : ∀ i, weight i ≤ 1
  total : ∑ i, weight i = 1
  psi : Fin N → ((Fin p × Fin q) → ℂ)
  unit : ∀ i, ∑ x, ‖psi i x‖ ^ 2 = 1
  average : ∑ i, (weight i : ℂ) • rankOneDensity (psi i) = ρ

private theorem weight_le_one_of_total {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight : ι → ℝ) (nonneg : ∀ i, 0 ≤ weight i) (total : ∑ i, weight i = 1)
    (i : ι) : weight i ≤ 1 := by
  rw [← total]
  exact Finset.single_le_sum (fun j _ => nonneg j) (Finset.mem_univ i)

def S {p : ℕ} (τ : Matrix (Fin p) (Fin p) ℂ) : ℝ :=
  if hτ : τ.IsHermitian then
    D5.S3.Quantum.Information.PartialTraceMutualInformation.spectralEntropy hτ / Real.log 2
  else 0

def ensembleCost {p q : ℕ} {ρ : (Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ)} (e : Ensemble ρ) : ℝ :=
  ∑ i, e.weight i * S (partialTraceRight (rankOneDensity (e.psi i)))

def E_F {p q : ℕ} (ρ : (Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ)) : ℝ :=
  sInf {t | ∃ e : Ensemble ρ, t = ensembleCost e}

private theorem entropy_eigenvalues {p : ℕ} (τ : Matrix (Fin p) (Fin p) ℂ)
    (hτ : τ.IsHermitian) : S τ =
    (∑ i, Real.negMulLog (hτ.eigenvalues i)) / Real.log 2 := by
  simp [S, hτ, D5.S3.Quantum.Information.PartialTraceMutualInformation.spectralEntropy]

theorem cost_set_nonempty_iff {p q : ℕ} (ρ : (Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ)) :
    {t | ∃ e : Ensemble ρ, t = ensembleCost e}.Nonempty ↔ Nonempty (Ensemble ρ) := by
  constructor
  · rintro ⟨t,e,_⟩; exact ⟨e⟩
  · rintro ⟨e⟩; exact ⟨ensembleCost e,e,rfl⟩


end D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds

namespace D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic
open D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds
def f (c : ℝ) : ℝ := binaryEntropyBits ((1-Real.sqrt (1-c^2))/2)

private theorem log_two_bounds : 1/2 < Real.log 2 ∧ Real.log 2 < 1 := by
  constructor
  · linarith [Real.log_two_gt_d9]
  · linarith [Real.log_two_lt_d9]

private theorem h_nonneg {x : ℝ} (hx : x ∈ Icc 0 1) : 0 ≤ binaryEntropyBits x := by
  have entropy_formula (x : ℝ) : binaryEntropyBits x = Real.binEntropy x / Real.log 2 := by
    simp only [binaryEntropyBits, Real.logb, Real.binEntropy, Real.log_inv]
    ring
  rw [entropy_formula]
  exact div_nonneg (Real.binEntropy_nonneg hx.1 hx.2) (by positivity)

private theorem h_le_one (x : ℝ) : binaryEntropyBits x ≤ 1 := by
  have entropy_formula (x : ℝ) : binaryEntropyBits x = Real.binEntropy x / Real.log 2 := by
    simp only [binaryEntropyBits, Real.logb, Real.binEntropy, Real.log_inv]
    ring
  rw [entropy_formula]
  exact (div_le_one (by positivity : 0 < Real.log 2)).mpr Real.binEntropy_le_log_two

private theorem h_strictMonoOn : StrictMonoOn binaryEntropyBits (Icc 0 (1/2)) := by
  have entropy_formula (x : ℝ) : binaryEntropyBits x = Real.binEntropy x / Real.log 2 := by
    simp only [binaryEntropyBits, Real.logb, Real.binEntropy, Real.log_inv]
    ring
  intro x hx y hy hxy
  rw [entropy_formula, entropy_formula]
  exact (div_lt_div_iff_of_pos_right (by positivity : 0 < Real.log 2)).mpr
    (Real.binEntropy_strictMonoOn (by simpa using hx) (by simpa using hy) hxy)

private theorem h_concave : ConcaveOn ℝ (Icc 0 1) binaryEntropyBits := by
  have entropy_formula (x : ℝ) : binaryEntropyBits x = Real.binEntropy x / Real.log 2 := by
    simp only [binaryEntropyBits, Real.logb, Real.binEntropy, Real.log_inv]
    ring
  have hc := Real.strictConcave_binEntropy.concaveOn
  refine ⟨hc.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hv := hc.2 hx hy ha hb hab
  simpa only [entropy_formula, smul_eq_mul, add_div, mul_div_assoc] using
    div_le_div_of_nonneg_right hv (by positivity : 0 ≤ Real.log 2)

private theorem binary_lower : (2303/65536 : ℝ) < binaryEntropyBits (1/256) := by
  have entropy_formula (x : ℝ) : binaryEntropyBits x = Real.binEntropy x / Real.log 2 := by
    simp only [binaryEntropyBits, Real.logb, Real.binEntropy, Real.log_inv]
    ring
  have hl2 := log_two_bounds
  have hlog : Real.log (256:ℝ) = 8 * Real.log 2 := by
    convert Real.log_pow 2 8 using 1 <;> norm_num
  have hfirst : Real.negMulLog (1/256) = (8/256) * Real.log 2 := by
    simp [Real.negMulLog, Real.log_div, hlog]
    ring
  have hlog255 := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<255/256)
    (by norm_num : (255/256:ℝ) ≠ 1)
  have hsecond : (255/65536:ℝ) < Real.negMulLog (255/256) := by
    unfold Real.negMulLog
    nlinarith
  have hh : Real.binEntropy (1/256) = Real.negMulLog (1/256)+Real.negMulLog (255/256) := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    norm_num
  rw [entropy_formula]
  rw [lt_div_iff₀ (by positivity : 0 < Real.log 2), hh, hfirst]
  nlinarith

private theorem binary_upper : binaryEntropyBits (1/250) < (1/25:ℝ) := by
  have entropy_formula (x : ℝ) : binaryEntropyBits x = Real.binEntropy x / Real.log 2 := by
    simp only [binaryEntropyBits, Real.logb, Real.binEntropy, Real.log_inv]
    ring
  have hl2 := log_two_bounds
  have hlog256 : Real.log (256:ℝ) = 8 * Real.log 2 := by
    convert Real.log_pow 2 8 using 1 <;> norm_num
  have hlog250 : Real.log (250:ℝ) < 8*Real.log 2 := by
    rw [← hlog256]
    exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  have hfirst : Real.negMulLog (1/250) < (8/250) * Real.log 2 := by
    have hi : Real.log (1/250:ℝ) = -Real.log 250 := by rw [one_div,Real.log_inv]
    unfold Real.negMulLog
    rw [hi]
    nlinarith
  have hlog : Real.log (256:ℝ) = 8*Real.log 2 := hlog256
  have hsecond : Real.negMulLog (249/250) ≤ (1/250:ℝ) := by
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<250/249)
    have he : Real.log (250/249:ℝ) = -Real.log (249/250) := by
      rw [show (250/249:ℝ) = (249/250)⁻¹ by norm_num, Real.log_inv]
    rw [he] at hl
    unfold Real.negMulLog
    nlinarith
  have hh : Real.binEntropy (1/250) = Real.negMulLog (1/250)+Real.negMulLog (249/250) := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    norm_num
  rw [entropy_formula]
  rw [div_lt_iff₀ (by positivity : 0<Real.log 2), hh]
  nlinarith

private theorem smaller_root_mem {c : ℝ} (hc : c ∈ Icc 0 1) :
    (1-Real.sqrt (1-c^2))/2 ∈ Icc 0 (1/2) := by
  have hc2 : c^2 ≤ 1 := by nlinarith [hc.1,hc.2]
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1-c^2)
  have hn := Real.sqrt_nonneg (1-c^2)
  constructor <;> nlinarith

private theorem f_monotone : MonotoneOn f (Icc 0 1) := by
  intro c hc d hd hcd
  unfold f
  apply h_strictMonoOn.monotoneOn (smaller_root_mem hc) (smaller_root_mem hd)
  have hr : Real.sqrt (1-d^2) ≤ Real.sqrt (1-c^2) := Real.sqrt_le_sqrt (by nlinarith [hc.1,hd.1])
  linarith

private theorem f_lower : (2303/65536:ℝ) < f (8/63) := by
  have hc : (8/63:ℝ) ∈ Icc 0 1 := by norm_num
  have hs := Real.sq_sqrt (by norm_num : 0 ≤ (1-(8/63:ℝ)^2))
  have hn := Real.sqrt_nonneg (1-(8/63:ℝ)^2)
  have hx : (1/256:ℝ) < (1-Real.sqrt (1-(8/63:ℝ)^2))/2 := by
    nlinarith
  exact binary_lower.trans (h_strictMonoOn (by norm_num) (smaller_root_mem hc) hx)

theorem star_root_upper {c : ℝ} (hc : 0 ≤ c) (hc2 : c^2 ≤ 1/64) :
    f c < (1/25:ℝ) := by
  have hc' : c ∈ Icc 0 1 := ⟨hc, by nlinarith⟩
  have hs := Real.sq_sqrt (by nlinarith : 0 ≤ 1-c^2)
  have hn := Real.sqrt_nonneg (1-c^2)
  have hx : (1-Real.sqrt (1-c^2))/2 < (1/250:ℝ) := by nlinarith
  exact (h_strictMonoOn (smaller_root_mem hc') (by norm_num) hx).trans binary_upper

private theorem lower_prefactor {k : ℕ} (hk : 32 ≤ k) :
    (217/254:ℝ) ≤ 7*((k:ℝ)-1)/(8*(k:ℝ)-2) := by
  have hk' : 32 ≤ (k:ℝ) := by exact_mod_cast hk
  rw [le_div_iff₀ (by linarith : (0:ℝ)<8*(k:ℝ)-2)]
  nlinarith

theorem lower_rational {k : ℕ} (hk : 32 ≤ k) :
    (499751/16646144:ℝ) < 7*((k:ℝ)-1)/(8*(k:ℝ)-2)*f (8/63) := by
  have hp := lower_prefactor hk
  have hb := f_lower
  have hf : 0 < f (8/63) := by linarith
  calc
    (499751/16646144:ℝ) = (217/254)*(2303/65536) := by norm_num
    _ < (217/254)*f (8/63) := by nlinarith
    _ ≤ 7*((k:ℝ)-1)/(8*(k:ℝ)-2)*f (8/63) := mul_le_mul_of_nonneg_right hp hf.le

theorem upper_rational {q : ℕ} (hq : 64 ≤ q) :
    ((q:ℝ)/25+1)/(2*(q:ℝ)-1) ≤ 89/3175 := by
  have hq' : 64 ≤ (q:ℝ) := by exact_mod_cast hq
  rw [div_le_iff₀ (by linarith : (0:ℝ)<2*(q:ℝ)-1)]
  nlinarith

end D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic

namespace D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds
open D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic
theorem qubit_entropy_det (τ : Matrix (Fin 2) (Fin 2) ℂ)
    (hτ : τ.PosSemidef) (ht : τ.trace = 1) :
    S τ = binaryEntropyBits ((1-Real.sqrt (1-4*τ.det.re))/2)  := by
  have entropy_formula (x : ℝ) : binaryEntropyBits x = Real.binEntropy x / Real.log 2 := by
    simp only [binaryEntropyBits, Real.logb, Real.binEntropy, Real.log_inv]
    ring
  let a : ℝ := hτ.1.eigenvalues 0
  let b : ℝ := hτ.1.eigenvalues 1
  have ha : 0 ≤ a := hτ.eigenvalues_nonneg 0
  have hb : 0 ≤ b := hτ.eigenvalues_nonneg 1
  have hab : a+b=1 := by
    have hh := congrArg Complex.re hτ.1.trace_eq_sum_eigenvalues
    simpa [ht,Fin.sum_univ_two,a,b] using hh.symm
  have hdet : τ.det.re = a*b := by
    have hh := congrArg Complex.re hτ.1.det_eq_prod_eigenvalues
    simpa [Fin.prod_univ_two,a,b] using hh
  have hroot : Real.sqrt (1-4*τ.det.re) = |a-b| := by
    rw [hdet, show 1-4*(a*b)=(a-b)^2 by nlinarith [hab], Real.sqrt_sq_eq_abs]
  rw [entropy_eigenvalues τ hτ.1, Fin.sum_univ_two]
  change (Real.negMulLog a+Real.negMulLog b)/Real.log 2 = _
  rw [hroot]
  rcases le_total a b with hab' | hba'
  · rw [abs_of_nonpos (by linarith : a-b ≤ 0)]
    have hr : (1- -(a-b))/2 = a := by linarith
    rw [hr]
    rw [entropy_formula]
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,show 1-a=b by linarith]
  · rw [abs_of_nonneg (by linarith : 0 ≤ a-b)]
    have hr : (1-(a-b))/2 = b := by linarith
    rw [hr]
    rw [entropy_formula]
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,show 1-b=a by linarith,add_comm]

private theorem qubit_det_bounds (τ : Matrix (Fin 2) (Fin 2) ℂ)
    (hτ : τ.PosSemidef) (ht : τ.trace = 1) : 0 ≤ τ.det.re ∧ τ.det.re ≤ 1/4 := by
  let a : ℝ := hτ.1.eigenvalues 0
  let b : ℝ := hτ.1.eigenvalues 1
  have ha : 0 ≤ a := hτ.eigenvalues_nonneg 0
  have hb : 0 ≤ b := hτ.eigenvalues_nonneg 1
  have hab : a+b=1 := by
    have hh := congrArg Complex.re hτ.1.trace_eq_sum_eigenvalues
    simpa [ht,Fin.sum_univ_two,a,b] using hh.symm
  have hdet : τ.det.re = a*b := by
    have hh := congrArg Complex.re hτ.1.det_eq_prod_eigenvalues
    simpa [Fin.prod_univ_two,a,b] using hh
  rw [hdet]
  constructor
  · positivity
  · nlinarith [sq_nonneg (a-b)]

private theorem qubit_entropy_nonneg (τ : Matrix (Fin 2) (Fin 2) ℂ)
    (hτ : τ.PosSemidef) (ht : τ.trace=1) : 0 ≤ S τ := by
  rw [qubit_entropy_det τ hτ ht]
  apply D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic.h_nonneg
  have hd := qubit_det_bounds τ hτ ht
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1-4*τ.det.re)
  have hn := Real.sqrt_nonneg (1-4*τ.det.re)
  constructor <;> nlinarith

private theorem qubit_entropy_le_one (τ : Matrix (Fin 2) (Fin 2) ℂ)
    (hτ : τ.PosSemidef) (ht : τ.trace=1) : S τ ≤ 1 := by
  rw [qubit_entropy_det τ hτ ht]
  exact D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic.h_le_one _

theorem trace_outer {p q : ℕ} (ψ : ((Fin p × Fin q) → ℂ)) :
    (rankOneDensity ψ).trace = ((∑ x, ‖ψ x‖^2 : ℝ) : ℂ) := by
  classical
  rw [rankOneDensity, Matrix.trace_vecMulVec]
  simp [dotProduct, Complex.mul_conj,
    Complex.normSq_eq_norm_sq,Complex.ofReal_sum]

theorem marginal_trace {p q : ℕ} (ψ : ((Fin p × Fin q) → ℂ)) :
    (partialTraceRight (rankOneDensity ψ)).trace = ((∑ x, ‖ψ x‖^2 : ℝ) : ℂ) := by
  rw [D5.S3.Quantum.Information.PartialTraceMutualInformation.trace_partialTraceRight,trace_outer]

theorem pure_qubit_nonneg {q : ℕ} (ψ : ((Fin 2 × Fin q) → ℂ)) (hψ : ∑ x, ‖ψ x‖^2 = 1) :
    0 ≤ S (partialTraceRight (rankOneDensity ψ)) := by
  apply qubit_entropy_nonneg
  · exact D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight_posSemidef
      (Matrix.posSemidef_vecMulVec_self_star ψ)
  · rw [marginal_trace,hψ]; norm_num

theorem pure_qubit_le_one {q : ℕ} (ψ : ((Fin 2 × Fin q) → ℂ)) (hψ : ∑ x, ‖ψ x‖^2 = 1) :
    S (partialTraceRight (rankOneDensity ψ)) ≤ 1 := by
  apply qubit_entropy_le_one
  · exact D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight_posSemidef
      (Matrix.posSemidef_vecMulVec_self_star ψ)
  · rw [marginal_trace,hψ]; norm_num

private def g (r : ℝ) : ℝ := binaryEntropyBits ((1-r)/2)

private theorem bloch_sq {τ : Matrix (Fin 2) (Fin 2) ℂ} (hτ : τ ∈ {τ : Matrix (Fin 2) (Fin 2) ℂ | IsDensity τ}) :
    ‖bloch τ‖^2 = 1-4*τ.det.re := by
  have h00 := congrArg Complex.im (hτ.1.1.apply 0 0)
  have h11 := congrArg Complex.im (hτ.1.1.apply 1 1)
  have h10r := congrArg Complex.re (hτ.1.1.apply 1 0)
  have h10i := congrArg Complex.im (hτ.1.1.apply 1 0)
  simp only [Complex.star_def,Complex.conj_re,Complex.conj_im] at h00 h11 h10r h10i
  have ht := congrArg Complex.re hτ.2
  simp only [Matrix.trace,Fin.sum_univ_two,Complex.add_re,Complex.one_re] at ht
  change (τ 0 0).re+(τ 1 1).re=1 at ht
  have hi00 : (τ 0 0).im=0 := by linarith
  have hi11 : (τ 1 1).im=0 := by linarith
  rw [EuclideanSpace.norm_sq_eq]
  simp [bloch,Fin.sum_univ_three,Matrix.det_fin_two,Complex.mul_re,Complex.sub_re,
    Real.norm_eq_abs,sq_abs]
  rw [hi00,hi11,← h10r,← h10i]
  nlinarith [ht]

private theorem bloch_mem {τ : Matrix (Fin 2) (Fin 2) ℂ} (hτ : τ ∈ {τ : Matrix (Fin 2) (Fin 2) ℂ | IsDensity τ}) :
    ‖bloch τ‖ ∈ Icc 0 1 := by
  have hd := qubit_det_bounds τ hτ.1 hτ.2
  have hs := bloch_sq hτ
  constructor
  · positivity
  · nlinarith [norm_nonneg (bloch τ)]

private theorem entropy_bloch {τ : Matrix (Fin 2) (Fin 2) ℂ} (hτ : τ ∈ {τ : Matrix (Fin 2) (Fin 2) ℂ | IsDensity τ}) :
    S τ = g ‖bloch τ‖ := by
  rw [qubit_entropy_det τ hτ.1 hτ.2,← bloch_sq hτ,Real.sqrt_sq (norm_nonneg _)]
  rfl

private theorem g_antitone : AntitoneOn g (Icc 0 1) := by
  intro x hx y hy hxy
  apply D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic.h_strictMonoOn.monotoneOn
  · constructor <;> linarith [hy.1,hy.2]
  · constructor <;> linarith [hx.1,hx.2]
  · linarith

private theorem g_concave : ConcaveOn ℝ (Icc 0 1) g := by
  refine ⟨convex_Icc 0 1,?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : (1-x)/2 ∈ Icc 0 1 := by constructor <;> linarith [hx.1,hx.2]
  have hy' : (1-y)/2 ∈ Icc 0 1 := by constructor <;> linarith [hy.1,hy.2]
  have hh := D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic.h_concave.2 hx' hy' ha hb hab
  have he : (1-(a*x+b*y))/2=a*((1-x)/2)+b*((1-y)/2) := by nlinarith [hab]
  simpa only [g,smul_eq_mul,he] using hh

private theorem bloch_mix (ρ σ : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℝ) :
    bloch (a • ρ+b • σ) = a • bloch ρ+b • bloch σ := by
  change blochLinear (a • ρ+b • σ) = a • blochLinear ρ+b • blochLinear σ
  simp only [map_add, map_smul]

private theorem qubit_density_convex : Convex ℝ {τ : Matrix (Fin 2) (Fin 2) ℂ | IsDensity τ} := by
  have hpone : (1 : Matrix (Fin 2) (Fin 2) ℂ).PosSemidef := Matrix.PosSemidef.one
  have hp : ((1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef :=
    hpone.smul (by norm_num [Complex.le_def])
  have ht : (((1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))).trace = 1 := by
    norm_num [Matrix.trace_smul, Matrix.trace_one]
  simpa only [physicalFiber, LinearMap.zero_apply, eq_self, true_and, IsDensity] using
    (finite_dimensional_physical_fiber (0 : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] (Empty → ℂ))
      _ hp ht).2.2

theorem qubit_entropy_concave : ConcaveOn ℝ {τ : Matrix (Fin 2) (Fin 2) ℂ | IsDensity τ} S := by
  refine ⟨qubit_density_convex,?_⟩
  intro ρ hρ σ hσ a b ha hb hab
  have hmix := qubit_density_convex hρ hσ ha hb hab
  have hr := bloch_mem hρ
  have hs := bloch_mem hσ
  have hm := bloch_mem hmix
  have hm' : a*‖bloch ρ‖+b*‖bloch σ‖ ∈ Icc 0 1 :=
    (convex_Icc 0 1) hr hs ha hb hab
  have hn : ‖bloch (a • ρ+b • σ)‖ ≤ a*‖bloch ρ‖+b*‖bloch σ‖ := by
    rw [bloch_mix]
    simpa [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb] using
      norm_add_le (a • bloch ρ) (b • bloch σ)
  rw [entropy_bloch hρ,entropy_bloch hσ,entropy_bloch hmix]
  exact (g_concave.2 hr hs ha hb hab).trans (g_antitone hm hm' hn)

end D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds

namespace D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic
open D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds
private def s (c : ℝ) : ℝ := Real.sqrt (1-c^2)

private def L (t : ℝ) : ℝ := Real.log (1+t)-Real.log (1-t)

private def fp (c : ℝ) : ℝ := c*L (s c)/(2*s c*Real.log 2)

private def fpp (c : ℝ) : ℝ := (L (s c)-2*s c)/(2*(s c)^3*Real.log 2)

private theorem s_bounds {c : ℝ} (hc : c ∈ Ioo 0 1) : 0 < s c ∧ s c < 1 := by
  have hrad : 0 < 1-c^2 := by nlinarith [hc.1,hc.2]
  have hn : 0 ≤ s c := Real.sqrt_nonneg _
  have hs : (s c)^2=1-c^2 := Real.sq_sqrt hrad.le
  constructor
  · exact Real.sqrt_pos.mpr hrad
  · nlinarith [hc.1,hc.2]

private theorem deriv_s {c : ℝ} (hc : c ∈ Ioo 0 1) : HasDerivAt s (-c/s c) c := by
  have hrad : 1-c^2 ≠ 0 := by nlinarith [hc.1,hc.2]
  exact (((hasDerivAt_const c (1:ℝ)).sub ((hasDerivAt_id c).pow 2)).sqrt hrad).congr_deriv
    (by dsimp [s]; ring)

private theorem deriv_f {c : ℝ} (hc : c ∈ Ioo 0 1) : HasDerivAt f (fp c) c := by
  have entropy_formula (x : ℝ) : binaryEntropyBits x = Real.binEntropy x / Real.log 2 := by
    simp only [binaryEntropyBits, Real.logb, Real.binEntropy, Real.log_inv]
    ring
  have hs := s_bounds hc
  have hxrange : 0 < (1-s c)/2 ∧ (1-s c)/2 < 1 := by constructor <;> linarith
  have hx : HasDerivAt (fun c => (1-s c)/2) (c/(2*s c)) c := by
    exact (((hasDerivAt_const c (1:ℝ)).sub (deriv_s hc)).div_const 2).congr_deriv (by ring)
  have hh := ((Real.hasDerivAt_binEntropy (ne_of_gt hxrange.1) (ne_of_lt hxrange.2)).comp c hx).div_const (Real.log 2)
  rw [show f = (fun x => Real.binEntropy ((1-Real.sqrt (1-x^2))/2) / Real.log 2) by
    funext x; exact entropy_formula _]
  change HasDerivAt (fun x => Real.binEntropy ((1-s x)/2) / Real.log 2) (fp c) c
  exact hh.congr_deriv (by
    unfold fp L
    rw [show 1-(1-s c)/2=(1+s c)/2 by ring,
      Real.log_div (by linarith : 1+s c ≠ 0) (by norm_num),
      Real.log_div (by linarith : 1-s c ≠ 0) (by norm_num)]
    ring)

private theorem deriv_fp {c : ℝ} (hc : c ∈ Ioo 0 1) : HasDerivAt fp (fpp c) c := by
  have hs := s_bounds hc
  have hspos := hs.1
  have hs2 : (s c)^2=1-c^2 := Real.sq_sqrt (by nlinarith [hc.1,hc.2])
  have hd := deriv_s hc
  have hL := ((hasDerivAt_const c (1:ℝ)).add hd).log (by linarith : 1+s c ≠ 0) |>.sub
    (((hasDerivAt_const c (1:ℝ)).sub hd).log (by linarith : 1-s c ≠ 0))
  have hden := (hd.const_mul 2).mul_const (Real.log 2)
  have hh := ((hasDerivAt_id c).mul hL).div hden (by positivity : 2*s c*Real.log 2 ≠ 0)
  exact hh.congr_deriv (by
    dsimp [fpp,L]
    have hl2 : Real.log 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp [hs.1.ne',hl2,show 1+s c ≠ 0 by linarith,show 1-s c ≠ 0 by linarith]
    linear_combination ((1-(s c)^2)*(Real.log (1+s c)-Real.log (1-s c))-2*s c)*hs2)

private theorem L_lower {t : ℝ} (ht : t ∈ Ico 0 1) : 2*t ≤ L t := by
  have h := Real.sum_range_le_log_div ht.1 ht.2 1
  norm_num [Finset.sum_range_one] at h
  rw [Real.log_div (by linarith [ht.1] : 1+t ≠ 0)
    (by linarith [ht.2] : 1-t ≠ 0)] at h
  dsimp [L]
  linarith

theorem f_convex : ConvexOn ℝ (Icc 0 1) f := by
  have entropy_formula (x : ℝ) : binaryEntropyBits x = Real.binEntropy x / Real.log 2 := by
    simp only [binaryEntropyBits, Real.logb, Real.binEntropy, Real.log_inv]
    ring
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := fp) (f'' := fpp) (convex_Icc 0 1)
  · rw [show f = (fun x => Real.binEntropy ((1-Real.sqrt (1-x^2))/2) / Real.log 2) by
      funext x; exact entropy_formula _]
    exact (Real.binEntropy_continuous.comp (by fun_prop)).div_const (Real.log 2) |>.continuousOn
  · intro c hc
    exact (deriv_f (by simpa only [interior_Icc] using hc)).hasDerivWithinAt
  · intro c hc
    exact (deriv_fp (by simpa only [interior_Icc] using hc)).hasDerivWithinAt
  · intro c hc
    have hs := s_bounds (by simpa only [interior_Icc] using hc)
    have hspos := hs.1
    exact div_nonneg (sub_nonneg.mpr (L_lower ⟨hs.1.le,hs.2⟩)) (by positivity)

end D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic

namespace D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds
open D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic
theorem spectral_ensemble_nonempty {p q : ℕ} (ρ : (Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ))
    (hρ : ρ.PosSemidef) (ht : ρ.trace=1) : Nonempty (Ensemble ρ) := by
  classical
  let e := Fintype.equivFin ((Fin p × Fin q))
  let U := hρ.1.eigenvectorUnitary
  have total : ∑ v, hρ.1.eigenvalues v = 1 := by
    have hh := congrArg Complex.re hρ.1.trace_eq_sum_eigenvalues
    simpa [ht,Complex.re_sum] using hh.symm
  have unit (v : (Fin p × Fin q)) : ∑ x, ‖U x v‖^2 = 1 := by
    change ∑ x, ‖(hρ.1.eigenvectorBasis v) x‖^2 = 1
    rw [← EuclideanSpace.norm_sq_eq,hρ.1.eigenvectorBasis.orthonormal.norm_eq_one]
    norm_num
  have average : ∑ v, (hρ.1.eigenvalues v : ℂ) • rankOneDensity (fun x => U x v) = ρ := by
    apply Eq.trans (b := Unitary.conjStarAlgAut ℂ _ hρ.1.eigenvectorUnitary
      (diagonal (RCLike.ofReal ∘ hρ.1.eigenvalues))) ?_ hρ.1.spectral_theorem.symm
    ext x y
    simp [Unitary.conjStarAlgAut_apply,Matrix.mul_apply,Matrix.diagonal,rankOneDensity,
      Matrix.vecMulVec_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,U]
    apply Finset.sum_congr rfl
    intro i _
    ring
  refine ⟨{
    N := Fintype.card ((Fin p × Fin q))
    weight := fun i => hρ.1.eigenvalues (e.symm i)
    nonneg := fun i => hρ.eigenvalues_nonneg _
    le_one := fun i => weight_le_one_of_total _ (fun v => hρ.eigenvalues_nonneg v) total (e.symm i)
    total := ?_
    psi := fun i x => U x (e.symm i)
    unit := fun i => unit _
    average := ?_
  }⟩
  · rw [Equiv.sum_comp e.symm]; exact total
  · exact (Equiv.sum_comp e.symm
      (fun v => (hρ.1.eigenvalues v : ℂ) • rankOneDensity (fun x => U x v))).trans average

theorem formation_nonneg {q : ℕ} (ρ : (Matrix (Fin 2 × Fin q) (Fin 2 × Fin q) ℂ)) (he : Nonempty (Ensemble ρ)) : 0 ≤ E_F ρ := by
  apply le_csInf ((cost_set_nonempty_iff ρ).mpr he)
  rintro s ⟨e,rfl⟩
  exact Finset.sum_nonneg fun i _ => mul_nonneg (e.nonneg i) (pure_qubit_nonneg _ (e.unit i))

theorem formation_le_cost {q : ℕ} {ρ : (Matrix (Fin 2 × Fin q) (Fin 2 × Fin q) ℂ)} (e : Ensemble ρ) : E_F ρ ≤ ensembleCost e := by
  apply csInf_le
  · refine ⟨0,?_⟩
    rintro s ⟨e,rfl⟩
    exact Finset.sum_nonneg fun i _ => mul_nonneg (e.nonneg i) (pure_qubit_nonneg _ (e.unit i))
  · exact ⟨e,rfl⟩

end D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds

namespace D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Witness
open D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic
def expectation (w : ((Fin 2 × Fin 2) → ℂ)) (ρ : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) : ℝ :=
  (dotProduct (star w) ((partialTransposeB ρ).mulVec w)).re

end D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Witness

namespace D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Direct
open D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Witness
private theorem pure_det (ψ : ((Fin 2 × Fin 2) → ℂ)) : (partialTraceRight (rankOneDensity ψ)).det.re = (‖(Matrix.of (Function.curry ψ)).det‖)^2 := by
  rw [D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.marginal_amplitude,
    Matrix.det_mul, Matrix.det_conjTranspose]
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow]

private theorem pure_entropy_f (ψ : ((Fin 2 × Fin 2) → ℂ)) (hψ : ∑ x, ‖ψ x‖^2=1) :
    S (partialTraceRight (rankOneDensity ψ)) = D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic.f (2*‖(Matrix.of (Function.curry ψ)).det‖) := by
  have ht : (partialTraceRight (rankOneDensity ψ)).trace=1 := by rw [marginal_trace,hψ]; norm_num
  have hp : (partialTraceRight (rankOneDensity ψ)).PosSemidef :=
    D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight_posSemidef
      (Matrix.posSemidef_vecMulVec_self_star ψ)
  rw [qubit_entropy_det _ hp ht,pure_det]
  unfold D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic.f
  congr 3
  ring

private theorem pure_concurrence_mem (ψ : ((Fin 2 × Fin 2) → ℂ)) (hψ : ∑ x, ‖ψ x‖^2=1) :
    2*‖(Matrix.of (Function.curry ψ)).det‖ ∈ Set.Icc 0 1 := by
  have ht : (partialTraceRight (rankOneDensity ψ)).trace=1 := by rw [marginal_trace,hψ]; norm_num
  have hd : 0 ≤ (partialTraceRight (rankOneDensity ψ)).det.re ∧ (partialTraceRight (rankOneDensity ψ)).det.re ≤ 1/4 := qubit_det_bounds _
    (D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight_posSemidef
      (Matrix.posSemidef_vecMulVec_self_star ψ)) ht
  rw [pure_det] at hd
  have hn : 0 ≤ ‖(Matrix.of (Function.curry ψ)).det‖ := norm_nonneg _
  constructor <;> nlinarith

private theorem witnessQ_coordinates (w ψ : ((Fin 2 × Fin 2) → ℂ)) :
    let M := (Matrix.of (Function.curry w))ᴴ * Matrix.of (Function.curry ψ)
    expectation w (rankOneDensity ψ) = ‖M 0 0‖^2 + ‖M 1 1‖^2 +
      2*(M 0 1 * star (M 1 0)).re := by
  simp_rw [← Complex.normSq_eq_norm_sq]
  simp [expectation,Function.curry,Matrix.of_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    partialTransposeB,rankOneDensity,Matrix.vecMulVec_apply,Matrix.mulVec,dotProduct,
    Fintype.sum_prod_type,Fin.sum_univ_two,Complex.normSq_apply,Complex.mul_re,
    Complex.mul_im,Complex.add_re,Complex.add_im,Complex.star_def,Complex.conj_re,
    Complex.conj_im]
  ring

private theorem matrix_quadratic_det_lower (M : Matrix (Fin 2) (Fin 2) ℂ) :
    -2*‖M.det‖ ≤ ‖M 0 0‖^2+‖M 1 1‖^2+2*(M 0 1*star (M 1 0)).re := by
  have h1 := (abs_le.mp (Complex.abs_re_le_norm (M 0 1*star (M 1 0)))).1
  rw [norm_mul,norm_star] at h1
  have h2 := norm_sub_norm_le (M 0 1*M 1 0) (M 0 0*M 1 1)
  rw [norm_mul,norm_mul,← neg_sub (M 0 0*M 1 1) (M 0 1*M 1 0),norm_neg] at h2
  rw [← Matrix.det_fin_two] at h2
  nlinarith [sq_nonneg (‖M 0 0‖-‖M 1 1‖)]

private theorem homogeneous_witness (w ψ : ((Fin 2 × Fin 2) → ℂ)) :
    -2*‖(Matrix.of (Function.curry w)).det‖*‖(Matrix.of (Function.curry ψ)).det‖ ≤ expectation w (rankOneDensity ψ) := by
  rw [witnessQ_coordinates]
  have hh := matrix_quadratic_det_lower ((Matrix.of (Function.curry w))ᴴ * Matrix.of (Function.curry ψ))
  rw [Matrix.det_mul,Matrix.det_conjTranspose,norm_mul,norm_star] at hh
  simpa [mul_assoc] using hh

private theorem pure_witness (w ψ : ((Fin 2 × Fin 2) → ℂ)) (hw : ∑ x, ‖w x‖^2=1) :
    -‖(Matrix.of (Function.curry ψ)).det‖ ≤ expectation w (rankOneDensity ψ) := by
  have hwD := (pure_concurrence_mem w hw).2
  have hh := homogeneous_witness w ψ
  have hD : 0 ≤ ‖(Matrix.of (Function.curry ψ)).det‖ := norm_nonneg _
  nlinarith

end D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Direct

namespace D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Witness
open D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Direct
def W (w : ((Fin 2 × Fin 2) → ℂ)) (ρ : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) : ℝ := max 0 (-expectation w ρ)

private theorem expectation_average {ρ : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)} (e : Ensemble ρ) (w : ((Fin 2 × Fin 2) → ℂ)) :
    expectation w ρ = ∑ i, e.weight i*expectation w (rankOneDensity (e.psi i)) := by
  have hPT : partialTransposeB ρ=∑ i, (e.weight i:ℂ) • partialTransposeB (rankOneDensity (e.psi i)) := by
    ext x y
    have hh := congrArg (fun M : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) => M (x.1,y.2) (y.1,x.2)) e.average
    simpa [partialTransposeB,Matrix.sum_apply,Matrix.smul_apply] using hh.symm
  unfold expectation
  rw [hPT,Matrix.sum_mulVec,dotProduct_sum,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,expectation]

private theorem witness_le_ensemble {ρ : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)} (e : Ensemble ρ) (w : ((Fin 2 × Fin 2) → ℂ))
    (hw : ∑ x, ‖w x‖^2=1) : W w ρ ≤ ∑ i, e.weight i*‖(Matrix.of (Function.curry (e.psi i))).det‖ := by
  apply max_le
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (e.nonneg i) (norm_nonneg _)
  · rw [expectation_average,← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hh := pure_witness w (e.psi i) hw
    nlinarith [e.nonneg i]

theorem witness_lower {ρ : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)} (he : Nonempty (Ensemble ρ)) (w : ((Fin 2 × Fin 2) → ℂ))
    (hw : ∑ x, ‖w x‖^2=1) : D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic.f (2*W w ρ) ≤ E_F ρ := by
  classical
  apply le_csInf ((cost_set_nonempty_iff ρ).mpr he)
  rintro c ⟨e,rfl⟩
  have hW := witness_le_ensemble e w hw
  have hc : ∑ i, e.weight i*(2*‖(Matrix.of (Function.curry (e.psi i))).det‖) ∈ Set.Icc 0 1 := by
    constructor
    · exact Finset.sum_nonneg fun i _ => mul_nonneg (e.nonneg i) (pure_concurrence_mem _ (e.unit i)).1
    · calc
        _ ≤ ∑ i, e.weight i*1 := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (pure_concurrence_mem _ (e.unit i)).2 (e.nonneg i)
        _ = 1 := by simp [e.total]
  have hwc : 2*W w ρ ∈ Set.Icc 0 1 := by
    constructor
    · exact mul_nonneg (by norm_num) (le_max_left _ _)
    · have hsum : ∑ i, e.weight i*(2*‖(Matrix.of (Function.curry (e.psi i))).det‖) = 2*∑ i, e.weight i*‖(Matrix.of (Function.curry (e.psi i))).det‖ := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
      rw [hsum] at hc
      linarith [hc.2]
  have hj := D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic.f_convex.map_sum_le (t := Finset.univ) (w := e.weight)
    (p := fun i => 2*‖(Matrix.of (Function.curry (e.psi i))).det‖) (fun i _ => e.nonneg i) e.total
    (fun i _ => pure_concurrence_mem _ (e.unit i))
  calc
    _ ≤ D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic.f (∑ i, e.weight i*(2*‖(Matrix.of (Function.curry (e.psi i))).det‖)) :=
      D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic.f_monotone hwc hc (by
        calc
          _ ≤ 2*∑ i, e.weight i*‖(Matrix.of (Function.curry (e.psi i))).det‖ := by linarith
          _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring)
    _ ≤ ensembleCost e := by
      unfold ensembleCost
      have hpure (i : Fin e.N) := pure_entropy_f (e.psi i) (e.unit i)
      simp_rw [hpure]
      simpa only [smul_eq_mul] using hj

end D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Witness

namespace D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Selective
open D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Witness

def restrictVec {q k : ℕ} (part : Fin q → Fin k) (j : Fin k) (ψ : ((Fin 2 × Fin q) → ℂ)) : ((Fin 2 × Fin q) → ℂ) :=
  Set.indicator {x | part x.2=j} ψ

def branchMass {q k : ℕ} (part : Fin q → Fin k) (j : Fin k) (ψ : ((Fin 2 × Fin q) → ℂ)) : ℝ :=
  ∑ x, ‖restrictVec part j ψ x‖^2

def branchVec {q k : ℕ} (part : Fin q → Fin k) (j : Fin k) (ψ : ((Fin 2 × Fin q) → ℂ)) : ((Fin 2 × Fin q) → ℂ) :=
  if branchMass part j ψ=0 then ψ else
    (NormedSpace.normalize
      (WithLp.toLp 2 (restrictVec part j ψ) : EuclideanSpace ℂ (Fin 2 × Fin q))).ofLp

private theorem branchMass_nonneg {q k : ℕ} (part : Fin q → Fin k) (j : Fin k) (ψ : ((Fin 2 × Fin q) → ℂ)) :
    0 ≤ branchMass part j ψ := Finset.sum_nonneg (fun x _ => sq_nonneg _)

private theorem sum_branchMass {q k : ℕ} (part : Fin q → Fin k) (ψ : ((Fin 2 × Fin q) → ℂ)) :
    ∑ j, branchMass part j ψ = ∑ x, ‖ψ x‖^2 := by
  classical
  unfold branchMass restrictVec Set.indicator
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [apply_ite,eq_comm]

private theorem restrict_zero_of_mass_zero {q k : ℕ} (part : Fin q → Fin k) (j : Fin k) (ψ : ((Fin 2 × Fin q) → ℂ))
    (hz : branchMass part j ψ=0) : restrictVec part j ψ=0 := by
  ext x
  have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg _)).mp hz x (Finset.mem_univ x)
  simpa using hh

private theorem branchVec_unit {q k : ℕ} (part : Fin q → Fin k) (j : Fin k) (ψ : ((Fin 2 × Fin q) → ℂ))
    (hψ : ∑ x, ‖ψ x‖^2=1) : ∑ x, ‖branchVec part j ψ x‖^2=1 := by
  classical
  by_cases hz : branchMass part j ψ=0
  · simpa [branchVec,hz] using hψ
  have hnz : (WithLp.toLp 2 (restrictVec part j ψ) : EuclideanSpace ℂ (Fin 2 × Fin q)) ≠ 0 := by
    intro hzero
    have hnorm : ‖(WithLp.toLp 2 (restrictVec part j ψ) : EuclideanSpace ℂ (Fin 2 × Fin q))‖^2 = 0 := by
      rw [hzero]
      simp
    exact hz (by simpa [branchMass, EuclideanSpace.norm_sq_eq] using hnorm)
  have hn := NormedSpace.norm_normalize hnz
  have hs := EuclideanSpace.norm_sq_eq
    (NormedSpace.normalize (WithLp.toLp 2 (restrictVec part j ψ) : EuclideanSpace ℂ (Fin 2 × Fin q)))
  simpa only [branchVec, hz, if_false, hn, one_pow] using hs.symm

private theorem branch_outer {q k : ℕ} (part : Fin q → Fin k) (j : Fin k) (ψ : ((Fin 2 × Fin q) → ℂ)) :
    rankOneDensity (restrictVec part j ψ) = (branchMass part j ψ:ℂ) • rankOneDensity (branchVec part j ψ) := by
  classical
  have branch_formula : branchVec part j ψ =
      if branchMass part j ψ=0 then ψ else
        (((1/Real.sqrt (branchMass part j ψ)):ℝ):ℂ) • restrictVec part j ψ := by
    simp only [branchVec, NormedSpace.normalize, EuclideanSpace.norm_eq,
      WithLp.ofLp_smul, WithLp.ofLp_toLp, one_div]
    rfl
  rw [branch_formula]
  by_cases hz : branchMass part j ψ=0
  · rw [restrict_zero_of_mass_zero part j ψ hz,hz]; simp [rankOneDensity]
  have hp : 0 < branchMass part j ψ := lt_of_le_of_ne (branchMass_nonneg part j ψ) (Ne.symm hz)
  have hs := Real.sq_sqrt hp.le
  have he : branchMass part j ψ*(1/Real.sqrt (branchMass part j ψ))^2=1 := by
    field_simp
    exact hs.symm
  have hec := congrArg Complex.ofReal he
  push_cast at hec
  ext x y
  simp [branchVec,hz,rankOneDensity,Matrix.vecMulVec_apply,Matrix.smul_apply,Pi.smul_apply,
    smul_eq_mul,map_mul,map_div₀]
  symm
  calc
    _ = ((branchMass part j ψ:ℂ)*(1/(Real.sqrt (branchMass part j ψ):ℂ))^2)*
        (restrictVec part j ψ x*star (restrictVec part j ψ y)) := by rw [Complex.star_def]; ring
    _ = _ := by rw [hec]; simp

private theorem marginal_partition {q k : ℕ} (part : Fin q → Fin k) (ψ : ((Fin 2 × Fin q) → ℂ)) :
    partialTraceRight (rankOneDensity ψ) = ∑ j, partialTraceRight (rankOneDensity (restrictVec part j ψ)) := by
  classical
  ext a a'
  simp only [partialTraceRight,D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
    Matrix.sum_apply,rankOneDensity,Matrix.vecMulVec_apply,Pi.star_apply,restrictVec,Set.indicator,Function.curry,Function.uncurry,Set.mem_ofPred_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp

private theorem marginal_branch_mixture {q k : ℕ} (part : Fin q → Fin k) (ψ : ((Fin 2 × Fin q) → ℂ)) :
    partialTraceRight (rankOneDensity ψ) = ∑ j, branchMass part j ψ • partialTraceRight (rankOneDensity (branchVec part j ψ)) := by
  classical
  rw [marginal_partition part ψ]
  apply Finset.sum_congr rfl
  intro j _
  rw [branch_outer part j ψ]
  ext a a'
  simp [partialTraceRight,D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
    Matrix.smul_apply,Finset.mul_sum,Complex.real_smul]

private theorem pure_measurement_entropy {q k : ℕ} (part : Fin q → Fin k) (ψ : ((Fin 2 × Fin q) → ℂ))
    (hψ : ∑ x, ‖ψ x‖^2=1) :
    (∑ j, branchMass part j ψ * S (partialTraceRight (rankOneDensity (branchVec part j ψ)))) ≤ S (partialTraceRight (rankOneDensity ψ)) := by
  classical
  have hh := qubit_entropy_concave.le_map_sum
    (t := Finset.univ) (w := fun j => branchMass part j ψ)
    (p := fun j => partialTraceRight (rankOneDensity (branchVec part j ψ)))
    (fun j _ => branchMass_nonneg part j ψ)
    (by simpa [sum_branchMass] using hψ) (by
      intro j _
      constructor
      · exact D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight_posSemidef
          (Matrix.posSemidef_vecMulVec_self_star _)
      · rw [marginal_trace,branchVec_unit part j ψ hψ]; norm_num)
  rw [← marginal_branch_mixture part ψ] at hh
  simpa [smul_eq_mul] using hh

def projectBlock {q k : ℕ} (part : Fin q → Fin k) (j : Fin k) (ρ : (Matrix (Fin 2 × Fin q) (Fin 2 × Fin q) ℂ)) : (Matrix (Fin 2 × Fin q) (Fin 2 × Fin q) ℂ) :=
  Function.curry (Set.indicator {xy | part xy.1.2=j ∧ part xy.2.2=j} (Function.uncurry ρ))

private theorem projected_average {q k : ℕ} {ρ : (Matrix (Fin 2 × Fin q) (Fin 2 × Fin q) ℂ)} (e : Ensemble ρ)
    (part : Fin q → Fin k) (j : Fin k) :
    ∑ i, (e.weight i:ℂ) • rankOneDensity (restrictVec part j (e.psi i)) = projectBlock part j ρ := by
  classical
  ext x y
  have hh := congrArg (fun M : (Matrix (Fin 2 × Fin q) (Fin 2 × Fin q) ℂ) => M x y) e.average
  simp only [Matrix.sum_apply,Matrix.smul_apply,rankOneDensity,Matrix.vecMulVec_apply,
    Pi.star_apply,smul_eq_mul] at hh ⊢
  by_cases hx : part x.2=j <;> by_cases hy : part y.2=j
  · simpa [restrictVec,projectBlock,hx,hy,Set.indicator,Function.curry,Function.uncurry,Set.mem_ofPred_eq] using hh
  all_goals simp [restrictVec,projectBlock,hx,hy,Set.indicator,Function.curry,Function.uncurry,Set.mem_ofPred_eq]

private theorem branch_probability {q k : ℕ} {ρ : (Matrix (Fin 2 × Fin q) (Fin 2 × Fin q) ℂ)} (e : Ensemble ρ)
    (part : Fin q → Fin k) (j : Fin k) :
    ∑ i, e.weight i*branchMass part j (e.psi i) = (projectBlock part j ρ).trace.re := by
  have hh := congrArg (fun M : (Matrix (Fin 2 × Fin q) (Fin 2 × Fin q) ℂ) => M.trace.re) (projected_average e part j)
  simp only [Matrix.trace_sum,Matrix.trace_smul,trace_outer,Complex.re_sum,smul_eq_mul,
    ← Complex.ofReal_mul,Complex.ofReal_re] at hh
  exact hh

def conditionalEnsemble {q k : ℕ} {ρ : (Matrix (Fin 2 × Fin q) (Fin 2 × Fin q) ℂ)} (e : Ensemble ρ)
    (part : Fin q → Fin k) (j : Fin k) (p : ℝ) (hp : 0<p)
    (ρj : (Matrix (Fin 2 × Fin q) (Fin 2 × Fin q) ℂ)) (htr : ρj.trace=1)
    (hav : projectBlock part j ρ=(p:ℂ) • ρj) : Ensemble ρj := by
  classical
  have htotal : ∑ i, e.weight i*branchMass part j (e.psi i)=p := by
    rw [branch_probability,hav,Matrix.trace_smul,htr]
    simp
  refine {
    N := e.N
    weight := fun i => e.weight i*branchMass part j (e.psi i)/p
    nonneg := fun i => div_nonneg (mul_nonneg (e.nonneg i) (branchMass_nonneg part j _)) hp.le
    le_one := fun i => weight_le_one_of_total _
      (fun i => div_nonneg (mul_nonneg (e.nonneg i) (branchMass_nonneg part j _)) hp.le)
      (by rw [← Finset.sum_div, htotal]; exact div_self hp.ne') i
    total := by rw [← Finset.sum_div,htotal]; exact div_self hp.ne'
    psi := fun i => branchVec part j (e.psi i)
    unit := fun i => branchVec_unit part j _ (e.unit i)
    average := ?_
  }
  have hh := projected_average e part j
  simp_rw [branch_outer,smul_smul,← Complex.ofReal_mul] at hh
  rw [hav] at hh
  have hpC : (p:ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  calc
    _ = (p:ℂ)⁻¹ • ∑ i, (e.weight i*branchMass part j (e.psi i):ℂ) •
        rankOneDensity (branchVec part j (e.psi i)) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul,Complex.ofReal_div,Complex.ofReal_mul]
      congr 1
      ring
    _ = ρj := by simp_rw [← Complex.ofReal_mul]; rw [hh,smul_smul,inv_mul_cancel₀ hpC,one_smul]

theorem selective_formation {q k : ℕ} {ρ : (Matrix (Fin 2 × Fin q) (Fin 2 × Fin q) ℂ)}
    (he : Nonempty (Ensemble ρ)) (part : Fin q → Fin k)
    (p : Fin k → ℝ) (hp : ∀ j, 0 ≤ p j) (ρj : Fin k → (Matrix (Fin 2 × Fin q) (Fin 2 × Fin q) ℂ))
    (htr : ∀ j, (ρj j).trace=1)
    (hav : ∀ j, projectBlock part j ρ=(p j:ℂ) • ρj j) :
    ∑ j, p j * E_F (ρj j) ≤ E_F ρ := by
  classical
  apply le_csInf ((cost_set_nonempty_iff ρ).mpr he)
  rintro c ⟨e,rfl⟩
  calc
    ∑ j, p j*E_F (ρj j) ≤
        ∑ j, ∑ i, e.weight i*branchMass part j (e.psi i)*
          S (partialTraceRight (rankOneDensity (branchVec part j (e.psi i)))) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hz : p j=0
      · simp only [hz,zero_mul]
        exact Finset.sum_nonneg fun i _ => mul_nonneg
          (mul_nonneg (e.nonneg i) (branchMass_nonneg part j _))
          (pure_qubit_nonneg _ (branchVec_unit part j _ (e.unit i)))
      have hpos := lt_of_le_of_ne (hp j) (Ne.symm hz)
      have hh := mul_le_mul_of_nonneg_left
        (formation_le_cost (conditionalEnsemble e part j (p j) hpos (ρj j) (htr j) (hav j))) (hp j)
      convert hh using 1
      simp only [ensembleCost,conditionalEnsemble]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp
    _ ≤ ensembleCost e := by
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro i _
      rw [show (∑ j, e.weight i*branchMass part j (e.psi i)*
          S (partialTraceRight (rankOneDensity (branchVec part j (e.psi i))))) =
          e.weight i * ∑ j, branchMass part j (e.psi i)*
          S (partialTraceRight (rankOneDensity (branchVec part j (e.psi i)))) by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring]
      exact mul_le_mul_of_nonneg_left (pure_measurement_entropy part _ (e.unit i)) (e.nonneg i)

end D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Selective
