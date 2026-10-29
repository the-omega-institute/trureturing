/- GID: D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A symmetric qubit channel improves the one-site purify-and-clone worst-case risk. -/

/-
admission_basis: open-problem-resolution (#19410; Refuted)
escape_witness: none
The conjecture is refuted at d = r = 2; no universal strict-improvement family is asserted.
The public statement retains the raw matrix formulas; the symmetric projector is written
inline as (I + F)/2. Proofs use existing conversion, permutation and rank-one constructions.
FiniteDensityPurification is unfrozen. The purification vector consists of CFC.sqrt entries;
its marginal follows from ptrace2_pure and the pinned Mathlib square-root identity.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19490.
All proof_shape labels below use bind-only conservatively; no helper supplies an escape witness.
Direct frozen dependencies use declaration statement_ids from the baseline Lean report:
F1: D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics.diagonalState; statement_id=sha256:013cba828a03ee76551ea835a546d37fc9ec5e1fa7e7ece2b17cefe093a661e9
F2: D5/S3/Quantum/FiniteDimensional.QubitMatrix; statement_id=sha256:e376bbe008ddbbc49fcf9763247304ed70ec54ac5cf49af3c6f7fb58fa626f30
F3: D5/S3/Quantum/FiniteDimensional.qubitX; statement_id=sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7
F4: D5/S3/Quantum/FiniteDimensional.qubitZ; statement_id=sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
F5: D5/S3/Quantum/Foundation/FiniteKrausChannel.finite_kraus_quantum_channel; statement_id=sha256:0ede64813b26e6161a0898eec4e0ff5c4fffc9727c0094b5bcfbc6a77c6ef9a0
F6: D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState; statement_id=sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5
F7: D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState.trace_eq_one; statement_id=sha256:d80deeaa4c3231a2a870534c321c04597f47aee8100cee1c643231022da56e40
F8: D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel; statement_id=sha256:b7b2554d55122b11b177ecdf92367d243e4d35ec1e3897c844deba5df1285d05
F9: D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel.toCompletelyPositiveMap; statement_id=sha256:7e2eefba0a4c0a6af6a4d36e7168066ad5899f2ba2622c43f082056bec8fb7dc
F10: D5/S3/Quantum/Information/PartialTraceMutualInformation.density_posSemidef; statement_id=sha256:b799be7b0c6e16bb8e03b4bcf99946d7abbc95ac0078be4a08391bec19c88bdc
F11: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft; statement_id=sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d
F12: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft_posSemidef; statement_id=sha256:57037555d268cd6c22ff19563a5f64496a1d89f7e5d8b6b98943b78b84af873d
F13: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight; statement_id=sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77
F14: D5/S3/Quantum/Information/PartialTraceMutualInformation.trace_partialTraceLeft; statement_id=sha256:70e429b7996075b0f25052d5fb6f603c2ac2556abcf0d2510142499e0c5d267c
F15: D5/S3/Quantum/Information/PartialTraceMutualInformation.trace_partialTraceRight; statement_id=sha256:2e0d10f59a41befee8bb5e380b1d8d7db7e14a2bbed6d47af5089807c0905813
F16: D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.density_le_one; same-delivery public declaration; no baseline public statement_id.
F17: D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity; statement_id=sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3
F18: D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.couplings; statement_id=sha256:b3818938be45b4647e8c52bd9e2f1194793166414204c732db4d8ab2c092d6b1
F19: D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.pure_diag_coupling; same-delivery public declaration; no baseline public statement_id.
F20: D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.trace_sqrt_sq_le_two; same-delivery public declaration; no baseline public statement_id.
F21: D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.Commutant.replicaSwap_apply; statement_id=sha256:e3427bb6efbbe3e9b723be03b86574ca66e788ed2d360508fdb706fa7b764080
F22: D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity; statement_id=sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988
F23: D5/S3/Quantum/Subentropy/PinchingGap.matrix_subentropy_concave; statement_id=sha256:a3c0c4aa2461c19b43948a67d489579d99acba03c8f96d5ec5a6bed418760287
F24: D5/S3/Quantum/Subentropy/Basic.matrixSubentropy; statement_id=sha256:1c5fdaf526e28e3e61827e243def4b593a85eee0439ad39231d25b0d4934f852
F25: D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.pureCoupling; statement_id=sha256:01498e38dfd279fe3d1d6f48fca7c1397ee4f85db71f3237bbc6d6954c3f6c5d
F26: D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.ptrace2_pure; statement_id=sha256:b1180afbd843f0b872ce14e13c61a53b7b54a82ebc4b05e4d2366e0c6b94214d
F27: D5/S3/Quantum/FiniteDimensional.qubit_weyl_star; statement_id=sha256:be07b0533dfdb8741136a43d8272fd7a664770fb9b4a851805c5db573532362d
F28: D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.discardMemory; statement_id=sha256:43c7ae3e2c44c9166d32991ff5c36e5a998ba131201c6826c5ca2321ad619e33
proof_shape: sqFidelity: bind-only; consumers: oneSiteLoss,sqFidelity_ge_of_order,sqFidelity_tensor_same_density,oneSiteLoss_le_of_fidelity,oneSiteLoss_ge_of_fidelity,pure_target_fidelity_bound,purifyAndClone_loss_lower,competitor_fidelity_lower; escape_witness: none; Direct frozen dependencies: none.
proof_shape: purifications: bind-only; consumers: oneSiteLoss,target_density_and_marginal,pauli_purifications,randomPurify_mem_target,oneSiteLoss_le_of_fidelity,oneSiteLoss_ge_of_fidelity; escape_witness: none; Direct frozen dependencies: F6,F13.
proof_shape: oneSiteMarginal: bind-only; consumers: oneSiteLoss,oneSiteLoss_le_of_fidelity,oneSiteLoss_ge_of_fidelity,purifyAndClone_pure_marginal,purifyAndClone_loss_lower,competitor_loss_upper; escape_witness: none; Direct frozen dependencies: F11,F13.
proof_shape: oneSiteLoss: bind-only; consumers: worstCaseOneSiteRisk,oneSiteLoss_le_of_fidelity,oneSiteLoss_ge_of_fidelity,worstCase_le_of_loss,loss_le_worstCase,purifyAndClone_loss_lower,competitor_loss_upper; escape_witness: none; Direct frozen dependencies: F6,F11,F13.
proof_shape: worstCaseOneSiteRisk: bind-only; consumers: claim,worstCase_le_of_loss,loss_le_worstCase,refute_of_risk_bounds,purifyAndClone_risk_lower,competitor_risk_upper; escape_witness: none; Direct frozen dependencies: F6,F11,F13.
proof_shape: TotallySymmetricSupport: bind-only; consumers: AdmissibleChannel,competitor_support; escape_witness: none; Direct frozen dependencies: none.
proof_shape: wernerOneToTwo: bind-only; consumers: purifyAndClone,competitor,kraus_action,werner_swap_left,werner_swap_right,competitor_support,competitor_marginal_right,competitor_marginal_left,purifyAndClone_pure_marginal; escape_witness: none; Direct frozen dependencies: none.
proof_shape: randomPurifyOne: bind-only; consumers: purifyAndClone,competitor_marginal_right,competitor_marginal_left,pauli_average,randomPurify_mem_target,pure_target_fidelity_bound,purifyAndClone_pure_marginal,competitor_fidelity_lower,competitor_loss_upper; escape_witness: none; Direct frozen dependencies: none.
proof_shape: purifyAndClone: bind-only; consumers: claim,refute_of_risk_bounds,purifyAndClone_pure_marginal,purifyAndClone_loss_lower,purifyAndClone_risk_lower; escape_witness: none; Direct frozen dependencies: none.
proof_shape: AdmissibleChannel: bind-only; consumers: claim,competitor_admissible,refute_of_risk_bounds; escape_witness: none; Direct frozen dependencies: F6,F8,F9.
proof_shape: claim: bind-only; consumers: refute_of_risk_bounds,result; escape_witness: none; Direct frozen dependencies: F6,F8,F9,F11,F13.
proof_shape: trace_re_mono: bind-only; consumers: sqFidelity_ge_of_order; escape_witness: none; Direct frozen dependencies: none.
proof_shape: sqrt_sandwich_self: bind-only; consumers: sqFidelity_ge_of_order,sqFidelity_tensor_same_density; escape_witness: none; Direct frozen dependencies: none.
proof_shape: sqFidelity_ge_of_order: bind-only; consumers: competitor_fidelity_lower; escape_witness: none; Direct frozen dependencies: none.
proof_shape: symmetricProjector_apply: bind-only; consumers: kraus_complete,kraus_action,symmetricProjector_swap_left,symmetricProjector_swap_right,competitor_marginal_right; escape_witness: none; Direct frozen dependencies: F21.
proof_shape: competitor: bind-only; consumers: kraus_action,competitor_channel,competitor_support,competitor_admissible,competitor_marginal_right,competitor_marginal_left,competitor_loss_upper,competitor_risk_upper,result; escape_witness: none; Direct frozen dependencies: none.
proof_shape: kraus: bind-only; consumers: kraus_complete,kraus_action,competitor_channel; escape_witness: none; Direct frozen dependencies: none.
proof_shape: sqrtTwo_sq: bind-only; consumers: kraus_complete,kraus_action; escape_witness: none; Direct frozen dependencies: none.
proof_shape: kraus_complete: bind-only; consumers: competitor_channel; escape_witness: none; Direct frozen dependencies: none.
proof_shape: kraus_action: bind-only; consumers: competitor_channel; escape_witness: none; Direct frozen dependencies: none.
proof_shape: competitor_channel: bind-only; consumers: competitor_admissible; escape_witness: none; Direct frozen dependencies: F5,F8,F9.
proof_shape: symmetricProjector_swap_left: bind-only; consumers: werner_swap_left,competitor_support,competitor_marginal_left; escape_witness: none; Direct frozen dependencies: F21.
proof_shape: symmetricProjector_swap_right: bind-only; consumers: werner_swap_right,competitor_support,competitor_marginal_left; escape_witness: none; Direct frozen dependencies: F21.
proof_shape: werner_swap_left: bind-only; consumers: competitor_support,competitor_marginal_left; escape_witness: none; Direct frozen dependencies: F21.
proof_shape: werner_swap_right: bind-only; consumers: competitor_support,competitor_marginal_left; escape_witness: none; Direct frozen dependencies: F21.
proof_shape: pairSwap_mul_apply: bind-only; consumers: competitor_support; escape_witness: none; Direct frozen dependencies: none.
proof_shape: mul_pairSwap_apply: bind-only; consumers: competitor_support; escape_witness: none; Direct frozen dependencies: none.
proof_shape: competitor_support: bind-only; consumers: competitor_admissible; escape_witness: none; Direct frozen dependencies: F21.
proof_shape: competitor_admissible: bind-only; consumers: result; escape_witness: none; Direct frozen dependencies: F5,F6,F8,F9,F21.
proof_shape: competitor_marginal_right: bind-only; consumers: competitor_loss_upper,competitor_marginal_left; escape_witness: none; Direct frozen dependencies: F13.
proof_shape: competitor_marginal_left: bind-only; consumers: competitor_loss_upper; escape_witness: none; Direct frozen dependencies: F11,F13,F21.
proof_shape: mem_densityMatrices_iff: bind-only; consumers: convex_densityMatrices,target_density_and_marginal,pauli_purifications; escape_witness: none; Direct frozen dependencies: F6,F7,F10.
proof_shape: convex_densityMatrices: bind-only; consumers: target_density_and_marginal; escape_witness: none; Direct frozen dependencies: F6,F7,F10,F23,F24.
proof_shape: convex_fixed_marginal: bind-only; consumers: target_density_and_marginal; escape_witness: none; Direct frozen dependencies: F6,F13,F28.
proof_shape: target_density_and_marginal: bind-only; consumers: purifyAndClone_loss_lower; escape_witness: none; Direct frozen dependencies: F6,F7,F10,F13,F23,F24,F28.
proof_shape: rank_pos_of_trace_one: bind-only; consumers: vecPure_rank_one; escape_witness: none; Direct frozen dependencies: none.
proof_shape: vecPure_rank_one: bind-only; consumers: pauli_purifications; escape_witness: none; Direct frozen dependencies: none.
proof_shape: pauliKet: bind-only; consumers: pauliKet_apply,pauli_marginal,pauli_purifications,pauli_average,randomPurify_mem_target; escape_witness: none; Direct frozen dependencies: F2,F3,F4.
proof_shape: pauliKet_apply: bind-only; consumers: pauli_average; escape_witness: none; Direct frozen dependencies: F2,F3,F4.
proof_shape: pauli_marginal: bind-only; consumers: pauli_purifications; escape_witness: none; Direct frozen dependencies: F2,F3,F4,F13,F17,F25,F26,F27.
proof_shape: pauli_purifications: bind-only; consumers: randomPurify_mem_target; escape_witness: none; Direct frozen dependencies: F2,F3,F4,F6,F7,F10,F13,F15,F17,F25,F26,F27.
proof_shape: pauli_average: bind-only; consumers: randomPurify_mem_target; escape_witness: none; Direct frozen dependencies: F2,F3,F4,F6,F13,F17.
proof_shape: randomPurify_mem_target: bind-only; consumers: competitor_loss_upper; escape_witness: none; Direct frozen dependencies: F2,F3,F4,F6,F7,F10,F13,F15,F17,F25,F26,F27.
proof_shape: sqrt_kronecker: bind-only; consumers: sqFidelity_tensor_same_density,pure_target_fidelity_bound; escape_witness: none; Direct frozen dependencies: none.
proof_shape: sqFidelity_tensor_same_density: bind-only; consumers: competitor_fidelity_lower; escape_witness: none; Direct frozen dependencies: none.
proof_shape: sqrt_real_smul: bind-only; consumers: pure_target_fidelity_bound; escape_witness: none; Direct frozen dependencies: none.
proof_shape: oneSiteLoss_le_of_fidelity: bind-only; consumers: competitor_loss_upper; escape_witness: none; Direct frozen dependencies: F6,F11,F13.
proof_shape: oneSiteLoss_ge_of_fidelity: bind-only; consumers: purifyAndClone_loss_lower; escape_witness: none; Direct frozen dependencies: F6,F11,F13.
proof_shape: worstCase_le_of_loss: bind-only; consumers: competitor_risk_upper; escape_witness: none; Direct frozen dependencies: F6,F11,F13.
proof_shape: loss_le_worstCase: bind-only; consumers: purifyAndClone_risk_lower; escape_witness: none; Direct frozen dependencies: F6,F11,F13.
proof_shape: refute_of_risk_bounds: bind-only; consumers: result; escape_witness: none; Direct frozen dependencies: F6,F8,F9,F11,F13.
proof_shape: pureZero: bind-only; consumers: pureZero_pos,pureZero_trace,pureZero_sq,pureZeroDensity,pure_marginal_representation,pure_target_fidelity_bound,purifyAndClone_pure_marginal,purifyAndClone_loss_lower; escape_witness: none; Direct frozen dependencies: none.
proof_shape: pureZero_pos: bind-only; consumers: pureZeroDensity,pure_target_fidelity_bound; escape_witness: none; Direct frozen dependencies: none.
proof_shape: pureZero_trace: bind-only; consumers: pureZeroDensity,pure_target_fidelity_bound; escape_witness: none; Direct frozen dependencies: none.
proof_shape: pureZero_sq: bind-only; consumers: pure_target_fidelity_bound; escape_witness: none; Direct frozen dependencies: none.
proof_shape: pureZeroDensity: bind-only; consumers: purifyAndClone_loss_lower,purifyAndClone_risk_lower; escape_witness: none; Direct frozen dependencies: F6.
proof_shape: pure_marginal_representation: bind-only; consumers: pure_target_fidelity_bound; escape_witness: none; Direct frozen dependencies: F1,F11,F13,F18,F19.
proof_shape: pure_target_fidelity_bound: bind-only; consumers: purifyAndClone_loss_lower; escape_witness: none; Direct frozen dependencies: F1,F11,F12,F13,F14,F18,F19,F20,F22.
proof_shape: purifyAndClone_pure_marginal: bind-only; consumers: purifyAndClone_loss_lower; escape_witness: none; Direct frozen dependencies: F11,F13.
proof_shape: purifyAndClone_loss_lower: bind-only; consumers: purifyAndClone_risk_lower; escape_witness: none; Direct frozen dependencies: F1,F6,F7,F10,F11,F12,F13,F14,F18,F19,F20,F22,F23,F24,F28.
proof_shape: purifyAndClone_risk_lower: bind-only; consumers: result; escape_witness: none; Direct frozen dependencies: F1,F6,F7,F10,F11,F12,F13,F14,F18,F19,F20,F22,F23,F24,F28.
proof_shape: competitor_fidelity_lower: bind-only; consumers: competitor_loss_upper; escape_witness: none; Direct frozen dependencies: F6,F7,F10,F16.
proof_shape: competitor_loss_upper: bind-only; consumers: competitor_risk_upper; escape_witness: none; Direct frozen dependencies: F2,F3,F4,F6,F7,F10,F11,F13,F15,F16,F17,F25,F26,F27.
proof_shape: competitor_risk_upper: bind-only; consumers: result; escape_witness: none; Direct frozen dependencies: F2,F3,F4,F6,F7,F10,F11,F13,F15,F16,F17,F25,F26,F27.
proof_shape: result: bind-only; consumers: settlement; escape_witness: none; Direct frozen dependencies: F1,F2,F3,F4,F5,F6,F7,F8,F9,F10,F11,F12,F13,F14,F15,F16,F17,F18,F19,F20,F21,F22,F23,F24,F25,F26,F27,F28.
-/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation
import D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
import D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.FiniteDimensional
import D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
import D5.S3.Quantum.QuantumChannels.WassersteinComplexityNonconvex
import D5.S3.Quantum.Measurements.BroadcastingChannelExtremaRefutation
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Subentropy.Basic
import D5.S3.Quantum.Subentropy.PinchingGap
import D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation

/- One-site worst-case squared-infidelity risk for arXiv:2605.21457v2,
   equations (S13), (S34) and (S35), with n = 1 and m = 2.
   A site includes its system and environment registers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open scoped ComplexOrder MatrixOrder Kronecker




/-- Squared Uhlmann fidelity; on density matrices the trace under the square is real. -/
def sqFidelity {a : Type*} [Fintype a] [DecidableEq a]
    (α β : (Matrix a a ℂ)) : ℝ :=
  (Matrix.trace (CFC.sqrt (CFC.sqrt α * β * CFC.sqrt α))).re ^ 2

/-- Pure densities with environment (right factor) traced out to the input density.
    Rank one means purity; no choice of vector phase or basis is fixed. -/
def purifications {d : ℕ} (r : ℕ) (ρ : DensityState (Fin d)) : Set ((Matrix ((Fin d × Fin r)) ((Fin d × Fin r)) ℂ)) :=
  {Ψ | Ψ ∈ (Set.range (fun ρ : DensityState ((Fin d × Fin r)) => CStarMatrix.ofMatrix.symm ρ.1)) ∧ Ψ.rank = 1 ∧
    partialTraceRight Ψ = (CStarMatrix.ofMatrix.symm ρ.1)}

/-- Retain the first or second AE pair, respectively; never trace out E_i. -/
def oneSiteMarginal {d r : ℕ} (Ξ : (Matrix (((Fin d × Fin r) × (Fin d × Fin r))) (((Fin d × Fin r) × (Fin d × Fin r))) ℂ)) (i : Fin 2) : (Matrix ((Fin d × Fin r)) ((Fin d × Fin r)) ℂ) :=
  if i = 0 then partialTraceRight Ξ else partialTraceLeft Ξ

/-- Equation (S13): one COMMON γ is chosen before taking the maximum over sites.
    EReal is a complete lattice: no real sInf default or clipping is used. -/
def oneSiteLoss {d r : ℕ} (ρ : DensityState (Fin d)) (Ξ : (Matrix (((Fin d × Fin r) × (Fin d × Fin r))) (((Fin d × Fin r) × (Fin d × Fin r))) ℂ)) : EReal :=
  sInf ((fun γ : (Matrix ((Fin d × Fin r)) ((Fin d × Fin r)) ℂ) =>
    ((max (1 - sqFidelity γ (oneSiteMarginal Ξ 0))
      (1 - sqFidelity γ (oneSiteMarginal Ξ 1)) : ℝ) : EReal)) ''
    convexHull ℝ (purifications r ρ))

/-- Equation (7) at n=1: supremum over all densities of rank at most r.
    The carrier admits arbitrary matrix maps; the claim restricts competitors to CPTP. -/
def worstCaseOneSiteRisk {d r : ℕ} (T : (Matrix (Fin d) (Fin d) ℂ) → (Matrix (((Fin d × Fin r) × (Fin d × Fin r))) (((Fin d × Fin r) × (Fin d × Fin r))) ℂ)) : EReal :=
  sSup {x | ∃ ρ : DensityState (Fin d), ((CStarMatrix.ofMatrix.symm ρ.1)).rank ≤ r ∧
    x = oneSiteLoss ρ (T ((CStarMatrix.ofMatrix.symm ρ.1)))}


/-- Both-sided support in Sym²(a); mere F Ξ F = Ξ would be insufficient. -/
def TotallySymmetricSupport {a : Type*} [Fintype a] [DecidableEq a]
    (Ξ : (Matrix (a × a) (a × a) ℂ)) : Prop :=
  ((1 / 2 : ℂ) • (1 + Equiv.Perm.permMatrix ℂ (Equiv.prodComm a a))) * Ξ * ((1 / 2 : ℂ) • (1 + Equiv.Perm.permMatrix ℂ (Equiv.prodComm a a))) = Ξ

/-- Werner's 1→2 cloner, D=card a: 2/(D+1) S (X⊗I) S. -/
def wernerOneToTwo {a : Type*} [Fintype a] [DecidableEq a]
    (X : (Matrix a a ℂ)) : (Matrix (a × a) (a × a) ℂ) :=
  (2 / ((Fintype.card a : ℂ) + 1)) •
    (((1 / 2 : ℂ) • (1 + Equiv.Perm.permMatrix ℂ (Equiv.prodComm a a))) * (X ⊗ₖ (1 : (Matrix a a ℂ))) * ((1 / 2 : ℂ) • (1 + Equiv.Perm.permMatrix ℂ (Equiv.prodComm a a))))

/-- The n=1 random-purification map, ρ ↦ ρ ⊗ I_r/r (S37c), (S38). -/
def randomPurifyOne {d : ℕ} (r : ℕ) (X : (Matrix (Fin d) (Fin d) ℂ)) : (Matrix ((Fin d × Fin r)) ((Fin d × Fin r)) ℂ) :=
  X ⊗ₖ ((r : ℂ)⁻¹ • (1 : (Matrix (Fin r) (Fin r) ℂ)))

/-- Equation (S35) at n=1,m=2, with cloning dimension D=dr. -/
def purifyAndClone (d r : ℕ) (X : (Matrix (Fin d) (Fin d) ℂ)) : (Matrix (((Fin d × Fin r) × (Fin d × Fin r))) (((Fin d × Fin r) × (Fin d × Fin r))) ℂ) :=
  wernerOneToTwo (randomPurifyOne r X)


/-- The output restriction of S3 A, imposed on every admissible input. -/
def AdmissibleChannel {d r : ℕ} (Φ : QuantumChannel (Fin d) (((Fin d × Fin r) × (Fin d × Fin r)))) : Prop :=
  ∀ ρ : DensityState (Fin d), ((CStarMatrix.ofMatrix.symm ρ.1)).rank ≤ r →
    TotallySymmetricSupport ((fun X => CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))) ((CStarMatrix.ofMatrix.symm ρ.1)))

/-- One-site worst-case infidelity optimality for positive dimensions 1≤r≤d.
    This fixes a reading of the source's unqualified word "optimal". -/
def claim : Prop :=
  ∀ (d r : ℕ), 1 ≤ r → r ≤ d →
    ∀ Φ : QuantumChannel (Fin d) (((Fin d × Fin r) × (Fin d × Fin r))), AdmissibleChannel Φ →
      worstCaseOneSiteRisk (purifyAndClone d r) ≤ worstCaseOneSiteRisk ((fun X => CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))))

end D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation

namespace D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
noncomputable section

private theorem trace_re_mono {a : Type*} [Fintype a] [DecidableEq a]
    {A B : (Matrix a a ℂ)} (h : A ≤ B) : A.trace.re ≤ B.trace.re := by
  exact (Complex.le_def.mp ((Matrix.tracePositiveLinearMap a ℝ ℂ).monotone h)).1

private theorem sqrt_sandwich_self {a : Type*} [Fintype a] [DecidableEq a]
    (A : Matrix a a ℂ) (hA : A.PosSemidef) :
    CFC.sqrt A * A * CFC.sqrt A = A * A := by
  have hh := CFC.sqrt_mul_sqrt_self A hA.nonneg
  calc
    CFC.sqrt A * A * CFC.sqrt A =
      CFC.sqrt A * (CFC.sqrt A * CFC.sqrt A) * CFC.sqrt A := by rw [hh]
    _ = (CFC.sqrt A * CFC.sqrt A) * (CFC.sqrt A * CFC.sqrt A) := by
      simp only [mul_assoc]
    _ = A * A := by rw [hh]

private theorem sqFidelity_ge_of_order {a : Type*} [Fintype a] [DecidableEq a]
    (A B : (Matrix a a ℂ)) (hA : A.PosSemidef) (htr : A.trace = 1)
    (t : ℝ) (ht : 0 ≤ t) (hBA : (B - t^2 • A).PosSemidef) :
    t^2 ≤ sqFidelity A B := by
  have hs := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hself := sqrt_sandwich_self A hA
  have hpos := hBA.mul_mul_conjTranspose_same (CFC.sqrt A)
  rw [hs.isHermitian.eq] at hpos
  have hdiff : CFC.sqrt A * (B - t^2 • A) * CFC.sqrt A =
      CFC.sqrt A * B * CFC.sqrt A - (t • A) * (t • A) := by
    simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      hself, pow_two]
  rw [hdiff] at hpos
  have hle : (t • A) * (t • A) ≤ CFC.sqrt A * B * CFC.sqrt A := Matrix.le_iff.mpr hpos
  have hroot := CFC.sqrt_le_sqrt _ _ hle
  rw [CFC.sqrt_mul_self (t • A) (hA.smul ht).nonneg] at hroot
  have htrace := trace_re_mono hroot
  have hval : (Matrix.trace (t • A)).re = t := by
    simp [Matrix.trace_smul, htr, Complex.smul_re]
  rw [hval] at htrace
  unfold sqFidelity
  nlinarith

end
end D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation



namespace D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open scoped ComplexOrder MatrixOrder Kronecker
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private theorem symmetricProjector_apply (a : Type*) [Fintype a] [DecidableEq a]
    (i j k l : a) : ((1 / 2 : ℂ) • (1 + Equiv.Perm.permMatrix ℂ (Equiv.prodComm a a))) (i,j) (k,l) =
      (1/2 : ℂ) * ((if i = k ∧ j = l then 1 else 0) +
        (if j = k ∧ i = l then 1 else 0)) := by
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
    D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.Commutant.replicaSwap_apply,
    Matrix.one_apply, Prod.swap_prod_mk, Prod.mk.injEq]


private def competitor (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℂ :=
  Matrix.reindex (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2))
    (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2))
    (wernerOneToTwo X ⊗ₖ ((1 / 3 : ℂ) • ((1 / 2 : ℂ) • (1 + Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin 2) (Fin 2))))))

private def kraus (k : (Fin 2) × ((Fin 2) × (Fin 2))) : Matrix (((Fin 2 × Fin 2) × (Fin 2 × Fin 2))) (Fin 2) ℂ := fun x i =>
  ((Real.sqrt 2 : ℂ) / 3) *
    ((1 / 2 : ℂ) • (1 + Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin 2) (Fin 2)))) (x.1.1,x.2.1) (i,k.1) *
    ((1 / 2 : ℂ) • (1 + Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin 2) (Fin 2)))) (x.1.2,x.2.2) k.2

private theorem sqrtTwo_sq : (Real.sqrt 2 : ℂ)^2 = 2 := by
  exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))

private theorem kraus_complete : (∑ k, (kraus k).conjTranspose * kraus k) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, kraus, symmetricProjector_apply,
      Matrix.one_apply, map_div₀, map_ofNat, RCLike.star_def] <;>
    ring_nf <;> simp [sqrtTwo_sq]

private theorem kraus_action (X : (Matrix (Fin 2) (Fin 2) ℂ)) :
    (∑ k, kraus k * X * (kraus k).conjTranspose) = competitor X := by
  ext ⟨⟨a,e⟩,⟨b,f⟩⟩ ⟨⟨c,g⟩,⟨d,h⟩⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    fin_cases e <;> fin_cases f <;> fin_cases g <;> fin_cases h <;>
    norm_num [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, kraus, competitor, Matrix.reindex_apply, Equiv.prodProdProdComm_symm,
      Equiv.prodProdProdComm_apply, Matrix.submatrix_apply,
      wernerOneToTwo, symmetricProjector_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply, map_div₀, map_ofNat, RCLike.star_def] <;>
    ring_nf <;> simp [sqrtTwo_sq] <;> ring

private theorem competitor_channel : ∃ Φ : QuantumChannel (Fin 2) (((Fin 2 × Fin 2) × (Fin 2 × Fin 2))),
    ∀ X, (fun X => CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))) X = competitor X := by
  obtain ⟨Φ,hΦ⟩ := finite_kraus_quantum_channel kraus kraus_complete
  refine ⟨Φ, fun X => ?_⟩
  exact (hΦ X).trans (kraus_action X)

end
end D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation


namespace D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open scoped ComplexOrder MatrixOrder Kronecker
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

private theorem symmetricProjector_swap_left (a : Type*) [Fintype a] [DecidableEq a]
    (x y : a × a) : ((1 / 2 : ℂ) • (1 + Equiv.Perm.permMatrix ℂ (Equiv.prodComm a a))) x.swap y = ((1 / 2 : ℂ) • (1 + Equiv.Perm.permMatrix ℂ (Equiv.prodComm a a))) x y := by
  rcases x with ⟨i,j⟩
  rcases y with ⟨k,l⟩
  simp only [Prod.swap_prod_mk,symmetricProjector_apply]
  ring

private theorem symmetricProjector_swap_right (a : Type*) [Fintype a] [DecidableEq a]
    (x y : a × a) : ((1 / 2 : ℂ) • (1 + Equiv.Perm.permMatrix ℂ (Equiv.prodComm a a))) x y.swap = ((1 / 2 : ℂ) • (1 + Equiv.Perm.permMatrix ℂ (Equiv.prodComm a a))) x y := by
  rcases x with ⟨i,j⟩
  rcases y with ⟨k,l⟩
  simp only [Prod.swap_prod_mk,symmetricProjector_apply]
  simp only [and_comm]
  ring

private theorem werner_swap_left {a : Type*} [Fintype a] [DecidableEq a]
    (X : (Matrix a a ℂ)) (x y : a × a) : wernerOneToTwo X x.swap y = wernerOneToTwo X x y := by
  unfold wernerOneToTwo
  rw [Matrix.smul_apply, Matrix.smul_apply]
  simp only [Matrix.mul_apply]
  simp_rw [symmetricProjector_swap_left]

private theorem werner_swap_right {a : Type*} [Fintype a] [DecidableEq a]
    (X : (Matrix a a ℂ)) (x y : a × a) : wernerOneToTwo X x y.swap = wernerOneToTwo X x y := by
  unfold wernerOneToTwo
  rw [Matrix.smul_apply, Matrix.smul_apply]
  simp only [Matrix.mul_apply]
  simp_rw [symmetricProjector_swap_right]

private theorem pairSwap_mul_apply {a b : Type*} [Fintype a] [DecidableEq a]
    (M : Matrix (a × a) b ℂ) (x : a × a) (y : b) :
    ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm a a)) * M) x y = M x.swap y := by
  simp [Equiv.Perm.permMatrix,PEquiv.toMatrix_toPEquiv_mul]

private theorem mul_pairSwap_apply {a b : Type*} [Fintype a] [DecidableEq a]
    (M : Matrix b (a × a) ℂ) (x : b) (y : a × a) :
    (M * (Equiv.Perm.permMatrix ℂ (Equiv.prodComm a a))) x y = M x y.swap := by
  simp [Equiv.Perm.permMatrix,PEquiv.mul_toMatrix_toPEquiv]

private theorem competitor_support (X : (Matrix (Fin 2) (Fin 2) ℂ)) : TotallySymmetricSupport (competitor X) := by
  have hl : (Equiv.Perm.permMatrix ℂ (Equiv.prodComm ((Fin 2 × Fin 2)) ((Fin 2 × Fin 2)))) * competitor X = competitor X := by
    ext ⟨⟨a,e⟩,⟨b,f⟩⟩ ⟨⟨c,g⟩,⟨d,h⟩⟩
    rw [pairSwap_mul_apply]
    change wernerOneToTwo X (b,a) (c,d) *
      ((1/3:ℂ)*((1 / 2 : ℂ) • (1 + Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin 2) (Fin 2)))) (f,e) (g,h)) = _
    rw [show (b,a) = (a,b).swap from rfl,werner_swap_left,
      show (f,e) = (e,f).swap from rfl,symmetricProjector_swap_left]
    rfl
  have hr : competitor X * (Equiv.Perm.permMatrix ℂ (Equiv.prodComm ((Fin 2 × Fin 2)) ((Fin 2 × Fin 2)))) = competitor X := by
    ext ⟨⟨a,e⟩,⟨b,f⟩⟩ ⟨⟨c,g⟩,⟨d,h⟩⟩
    rw [mul_pairSwap_apply]
    change wernerOneToTwo X (a,b) (d,c) *
      ((1/3:ℂ)*((1 / 2 : ℂ) • (1 + Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin 2) (Fin 2)))) (e,f) (h,g)) = _
    rw [show (d,c) = (c,d).swap from rfl,werner_swap_right,
      show (h,g) = (g,h).swap from rfl,symmetricProjector_swap_right]
    rfl
  unfold TotallySymmetricSupport
  simp only [Matrix.smul_mul,Matrix.mul_smul,add_mul,mul_add,one_mul,mul_one,hl,hr]
  module

private theorem competitor_admissible : ∃ Φ : QuantumChannel (Fin 2) (((Fin 2 × Fin 2) × (Fin 2 × Fin 2))),
    AdmissibleChannel Φ ∧ ∀ X, (fun X => CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))) X = competitor X := by
  obtain ⟨Φ,hΦ⟩ := competitor_channel
  exact ⟨Φ,fun ρ _ => by rw [hΦ]; exact competitor_support _,hΦ⟩

private theorem competitor_marginal_right (X : (Matrix (Fin 2) (Fin 2) ℂ)) : partialTraceRight (competitor X) =
    randomPurifyOne 2 ((2/3 : ℂ) • X + ((1/6 : ℂ) * X.trace) • (1 : (Matrix (Fin 2) (Fin 2) ℂ))) := by
  ext ⟨a,e⟩ ⟨b,f⟩
  fin_cases a <;> fin_cases e <;> fin_cases b <;> fin_cases f <;>
    norm_num [partialTraceRight,competitor,Matrix.reindex_apply, Equiv.prodProdProdComm_symm,
      Equiv.prodProdProdComm_apply, Matrix.submatrix_apply,wernerOneToTwo,symmetricProjector_apply,
      randomPurifyOne,Matrix.trace,Matrix.mul_apply,Fintype.sum_prod_type,
      Fin.sum_univ_two,Matrix.kroneckerMap_apply,Matrix.one_apply] <;> ring

private theorem competitor_marginal_left (X : (Matrix (Fin 2) (Fin 2) ℂ)) : partialTraceLeft (competitor X) =
    randomPurifyOne 2 ((2/3 : ℂ) • X + ((1/6 : ℂ) * X.trace) • (1 : (Matrix (Fin 2) (Fin 2) ℂ))) := by
  rw [← competitor_marginal_right X]
  ext a b
  change (∑ k : Fin 2 × Fin 2, competitor X (k,a) (k,b)) =
    (∑ k : Fin 2 × Fin 2, competitor X (a,k) (b,k))
  apply Finset.sum_congr rfl
  intro k _
  rcases a with ⟨i,e⟩
  rcases b with ⟨j,f⟩
  rcases k with ⟨l,g⟩
  change wernerOneToTwo X (l,i) (l,j) *
      ((1/3 : ℂ) * ((1/2 : ℂ) • (1 + Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin 2) (Fin 2)))) (g,e) (g,f)) =
    wernerOneToTwo X (i,l) (j,l) *
      ((1/3 : ℂ) * ((1/2 : ℂ) • (1 + Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin 2) (Fin 2)))) (e,g) (f,g))
  rw [show (l,i) = (i,l).swap from rfl, werner_swap_left,
    show (l,j) = (j,l).swap from rfl, werner_swap_right,
    show (g,e) = (e,g).swap from rfl, symmetricProjector_swap_left,
    show (g,f) = (f,g).swap from rfl, symmetricProjector_swap_right]

end
end D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation


namespace D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open scoped ComplexOrder MatrixOrder Kronecker
noncomputable section
set_option maxHeartbeats 800000

private theorem mem_densityMatrices_iff {a : Type*} [Fintype a] [DecidableEq a]
    (A : (Matrix a a ℂ)) : A ∈ (Set.range (fun ρ : DensityState a => CStarMatrix.ofMatrix.symm ρ.1)) ↔ A.PosSemidef ∧ A.trace = 1 := by
  constructor
  · rintro ⟨ρ,rfl⟩
    exact ⟨density_posSemidef ρ,DensityState.trace_eq_one ρ⟩
  · rintro ⟨hpos,htr⟩
    exact ⟨⟨CStarMatrix.ofMatrix A,
      map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hpos.nonneg,htr⟩,rfl⟩

private theorem convex_densityMatrices (a : Type*) [Fintype a] [DecidableEq a] :
    Convex ℝ ((Set.range (fun ρ : DensityState a => CStarMatrix.ofMatrix.symm ρ.1))) := by
  classical
  have hset : Set.range (fun ρ : DensityState a => CStarMatrix.ofMatrix.symm ρ.1) =
      {A : Matrix a a ℂ | A.PosSemidef ∧ A.trace = 1} := by
    ext A
    exact mem_densityMatrices_iff A
  rw [hset]
  cases isEmpty_or_nonempty a with
  | inl h =>
      letI := h
      have hempty : {A : Matrix a a ℂ | A.PosSemidef ∧ A.trace = 1} = ∅ := by
        ext A
        simp [Matrix.trace]
      rw [hempty]
      exact convex_empty
  | inr h =>
      letI := h
      exact (D5.S3.Quantum.Subentropy.PinchingGap.matrix_subentropy_concave
        (Classical.choice h)).1

private theorem convex_fixed_marginal {d r : ℕ} (ρ : DensityState (Fin d)) :
    Convex ℝ {A : (Matrix ((Fin d × Fin r)) ((Fin d × Fin r)) ℂ) | partialTraceRight A = (CStarMatrix.ofMatrix.symm ρ.1)} := by
  let T := (D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.discardMemory
    (d := d) (r := r)).restrictScalars ℝ
  change Convex ℝ (T ⁻¹' {CStarMatrix.ofMatrix.symm ρ.1})
  exact (convex_singleton _).linear_preimage T

private theorem target_density_and_marginal {d r : ℕ} (ρ : DensityState (Fin d))
    {A : (Matrix ((Fin d × Fin r)) ((Fin d × Fin r)) ℂ)} (hA : A ∈ convexHull ℝ (purifications r ρ)) :
    A.PosSemidef ∧ A.trace = 1 ∧ partialTraceRight A = (CStarMatrix.ofMatrix.symm ρ.1) := by
  have hden : A ∈ (Set.range (fun ρ : DensityState ((Fin d × Fin r)) => CStarMatrix.ofMatrix.symm ρ.1)) :=
    convexHull_min (fun _ h => h.1) (convex_densityMatrices _) hA
  have hmarg : partialTraceRight A = (CStarMatrix.ofMatrix.symm ρ.1) :=
    convexHull_min (fun _ h => h.2.2) (convex_fixed_marginal ρ) hA
  exact ⟨(mem_densityMatrices_iff A).mp hden |>.1,
    (mem_densityMatrices_iff A).mp hden |>.2, hmarg⟩

theorem rank_pos_of_trace_one {a : Type*} [Fintype a] [DecidableEq a]
    {A : (Matrix a a ℂ)} (htr : A.trace = 1) : 0 < A.rank := by
  by_contra hn
  have hz : A.rank = 0 := Nat.eq_zero_of_not_pos hn
  have hrange : LinearMap.range A.mulVecLin = ⊥ := by
    exact Submodule.finrank_eq_zero.mp hz
  have hlin : A.mulVecLin = 0 := LinearMap.range_eq_bot.mp hrange
  have hA : A = 0 := by
    apply Matrix.toLin'.injective
    simpa only [Matrix.toLin'_apply', Matrix.mulVecLin_zero] using hlin
  simp [hA] at htr

private theorem vecPure_rank_one {a : Type*} [Fintype a] [DecidableEq a]
    (v : a → ℂ) (htr : (Matrix.vecMulVec v (star v)).trace = 1) :
    (Matrix.vecMulVec v (star v)).rank = 1 := by
  have hl := Matrix.rank_vecMulVec_le v (star v)
  have hp := rank_pos_of_trace_one htr
  omega

end
end D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation


namespace D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open scoped ComplexOrder MatrixOrder Kronecker
noncomputable section
set_option maxHeartbeats 1000000


private def pauliKet (k : Fin 2 × Fin 2) (ψ : (Fin 2 × Fin 2) → ℂ) :
    (Fin 2 × Fin 2) → ℂ := fun p =>
  ((D5.S3.Quantum.FiniteDimensional.qubitZ ^ k.2.val *
      D5.S3.Quantum.FiniteDimensional.qubitX ^ k.1.val).mulVec
    (fun e => ψ (p.1, e))) p.2

private theorem pauliKet_apply (k : Fin 2 × Fin 2) (ψ : (Fin 2 × Fin 2) → ℂ)
    (p : Fin 2 × Fin 2) : pauliKet k ψ p =
      (if k.2 = 0 ∨ p.2 = 0 then (1 : ℂ) else -1) *
        ψ (p.1, if k.1 = 0 then p.2 else if p.2 = 0 then 1 else 0) := by
  rcases k with ⟨s, t⟩
  rcases p with ⟨a, e⟩
  fin_cases s <;> fin_cases t <;> fin_cases e <;>
    simp [pauliKet, D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Fin.sum_univ_two]

private theorem pauli_marginal (k : Fin 2 × Fin 2) (ψ : (Fin 2 × Fin 2) → ℂ) :
    partialTraceRight (D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity (pauliKet k ψ)) = partialTraceRight (D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity ψ) := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := fun i e => ψ (i,e)
  let V := D5.S3.Quantum.FiniteDimensional.qubitZ ^ k.2.val * D5.S3.Quantum.FiniteDimensional.qubitX ^ k.1.val
  have hket : pauliKet k ψ = Function.uncurry (A * V.transpose) := by
    funext p
    simp only [pauliKet, A, V, Function.uncurry, Matrix.mulVec, dotProduct,
      Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rcases D5.S3.Quantum.FiniteDimensional.qubit_weyl_star with ⟨_, hX, hZ, hXX, hZZ⟩
  have hXXmul : D5.S3.Quantum.FiniteDimensional.qubitX * D5.S3.Quantum.FiniteDimensional.qubitX = 1 := by simpa only [pow_two] using hXX
  have hZZmul : D5.S3.Quantum.FiniteDimensional.qubitZ * D5.S3.Quantum.FiniteDimensional.qubitZ = 1 := by simpa only [pow_two] using hZZ
  have hXpow (s : Fin 2) : (D5.S3.Quantum.FiniteDimensional.qubitX ^ s.val).conjTranspose * (D5.S3.Quantum.FiniteDimensional.qubitX ^ s.val) = 1 := by
    fin_cases s <;> simp [← Matrix.star_eq_conjTranspose, hX, hXXmul]
  have hZpow (t : Fin 2) : (D5.S3.Quantum.FiniteDimensional.qubitZ ^ t.val).conjTranspose * (D5.S3.Quantum.FiniteDimensional.qubitZ ^ t.val) = 1 := by
    fin_cases t <;> simp [← Matrix.star_eq_conjTranspose, hZ, hZZmul]
  have hU : V.conjTranspose * V = 1 := by
    simp only [V, Matrix.conjTranspose_mul, mul_assoc]
    rw [← mul_assoc (D5.S3.Quantum.FiniteDimensional.qubitZ ^ k.2.val).conjTranspose (D5.S3.Quantum.FiniteDimensional.qubitZ ^ k.2.val) (D5.S3.Quantum.FiniteDimensional.qubitX ^ k.1.val),
      hZpow k.2, one_mul, hXpow k.1]
  have hUtr : V.transpose * V.transpose.conjTranspose = 1 := by
    rw [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
      ← Matrix.transpose_mul, hU, Matrix.transpose_one]
  rw [hket]
  change partialTraceRight (D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.pureCoupling (A * V.transpose)) =
    partialTraceRight (D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.pureCoupling A)
  rw [D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.ptrace2_pure, D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.ptrace2_pure]
  calc
    (A * V.transpose) * (A * V.transpose).conjTranspose =
        A * (V.transpose * V.transpose.conjTranspose) * A.conjTranspose := by
      simp only [Matrix.conjTranspose_mul, mul_assoc]
    _ = A * A.conjTranspose := by rw [hUtr, mul_one]

private theorem pauli_purifications (ρ : DensityState (Fin 2)) (ψ : (Fin 2 × Fin 2) → ℂ)
    (hm : partialTraceRight (D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity ψ) = (CStarMatrix.ofMatrix.symm ρ.1))
    (k : Fin 2 × Fin 2) : D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity (pauliKet k ψ) ∈ purifications 2 ρ := by
  have hm' : partialTraceRight (D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity (pauliKet k ψ)) = (CStarMatrix.ofMatrix.symm ρ.1) :=
    (pauli_marginal k ψ).trans hm
  have htr : (D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity (pauliKet k ψ)).trace = 1 := by
    rw [← trace_partialTraceRight, hm']
    exact DensityState.trace_eq_one ρ
  refine ⟨(mem_densityMatrices_iff _).mpr ?_, vecPure_rank_one _ htr, hm'⟩
  exact ⟨Matrix.posSemidef_vecMulVec_self_star _,htr⟩

private theorem pauli_average (ρ : DensityState (Fin 2)) (ψ : (Fin 2 × Fin 2) → ℂ)
    (hm : partialTraceRight (D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity ψ) = (CStarMatrix.ofMatrix.symm ρ.1)) :
    (∑ k : Fin 2 × Fin 2, (1/4 : ℝ) • D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity (pauliKet k ψ)) =
      randomPurifyOne 2 ((CStarMatrix.ofMatrix.symm ρ.1)) := by
  ext ⟨i,e⟩ ⟨j,f⟩
  have he := congrFun (congrFun hm i) j
  simp only [partialTraceRight,D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity,Fin.sum_univ_two,Matrix.vecMulVec_apply,
    Pi.star_apply, RCLike.star_def, CStarMatrix.ofMatrix_symm_apply] at he
  fin_cases e <;> fin_cases f <;>
    norm_num [Matrix.sum_apply,Fintype.sum_prod_type,Fin.sum_univ_two,
      D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity,pauliKet_apply,randomPurifyOne,Matrix.kroneckerMap_apply,
      Matrix.smul_apply,Matrix.one_apply,Matrix.vecMulVec_apply,Pi.star_apply] <;>
    first | linear_combination (1/2 : ℂ) * he | ring

private theorem randomPurify_mem_target (ρ : DensityState (Fin 2)) :
    randomPurifyOne 2 ((CStarMatrix.ofMatrix.symm ρ.1)) ∈ convexHull ℝ (purifications 2 ρ) := by
  let X := CStarMatrix.ofMatrix.symm ρ.1
  let ψ : (Fin 2 × Fin 2) → ℂ := fun p => CFC.sqrt X p.1 p.2
  have hX := density_posSemidef ρ
  have hs := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg X)
  have hm : partialTraceRight
      (D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity ψ) = X := by
    calc
      partialTraceRight (D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity ψ) =
          CFC.sqrt X * (CFC.sqrt X).conjTranspose := by
        exact D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.ptrace2_pure
          (CFC.sqrt X)
      _ = X := by
        rw [hs.isHermitian.eq, CFC.sqrt_mul_sqrt_self X hX.nonneg]
  rw [← pauli_average ρ ψ hm]
  have hmem := (convex_convexHull ℝ (purifications 2 ρ)).sum_mem
    (t := Finset.univ) (w := fun _ : Fin 2 × Fin 2 => (1/4 : ℝ))
    (z := fun k => D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity (pauliKet k ψ))
    (by intro k hk; norm_num)
    (by norm_num [Fintype.sum_prod_type, Fin.sum_univ_two])
    (by intro k hk; exact subset_convexHull ℝ _ (pauli_purifications ρ ψ hm k))
  simpa using hmem

end
end D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation


namespace D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
noncomputable section

private theorem sqrt_kronecker {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (A : (Matrix a a ℂ)) (B : (Matrix b b ℂ))
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    CFC.sqrt (A ⊗ₖ B) = CFC.sqrt A ⊗ₖ CFC.sqrt B := by
  apply CFC.sqrt_unique
  · rw [← Matrix.mul_kronecker_mul, CFC.sqrt_mul_sqrt_self A hA.nonneg,
      CFC.sqrt_mul_sqrt_self B hB.nonneg]
  · exact ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).kronecker
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B))).nonneg

private theorem sqFidelity_tensor_same_density {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (A B : (Matrix a a ℂ)) (E : (Matrix b b ℂ))
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hE : E.PosSemidef)
    (htrE : E.trace = 1) :
    sqFidelity (A ⊗ₖ E) (B ⊗ₖ E) = sqFidelity A B := by
  have hsA := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hAE := sqrt_sandwich_self E hE
  have hsandA : (CFC.sqrt A * B * CFC.sqrt A).PosSemidef := by
    simpa only [hsA.isHermitian.eq] using hB.mul_mul_conjTranspose_same (CFC.sqrt A)
  have hEE : (E * E).PosSemidef := by
    simpa only [hE.isHermitian.eq] using Matrix.posSemidef_self_mul_conjTranspose E
  unfold sqFidelity
  rw [sqrt_kronecker A E hA hE, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, hAE, sqrt_kronecker _ _ hsandA hEE,
    CFC.sqrt_mul_self E hE.nonneg, Matrix.trace_kronecker, htrE,mul_one]

end
end D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation

namespace D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation
open scoped ComplexOrder MatrixOrder Kronecker
noncomputable section
private theorem sqrt_real_smul {a : Type*} [Fintype a] [DecidableEq a]
    (A : (Matrix a a ℂ)) (hA : A.PosSemidef) (c : ℝ) (hc : 0 ≤ c) :
    CFC.sqrt (c • A) = Real.sqrt c • CFC.sqrt A := by
  apply CFC.sqrt_unique
  · simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,
      Real.mul_self_sqrt hc,CFC.sqrt_mul_sqrt_self A hA.nonneg]
  · exact ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).smul
      (Real.sqrt_nonneg c)).nonneg
end
end D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation


namespace D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open scoped ComplexOrder MatrixOrder Kronecker
noncomputable section

private theorem oneSiteLoss_le_of_fidelity {d r : ℕ} (ρ : DensityState (Fin d))
    (Ξ : (Matrix (((Fin d × Fin r) × (Fin d × Fin r))) (((Fin d × Fin r) × (Fin d × Fin r))) ℂ)) (γ : (Matrix ((Fin d × Fin r)) ((Fin d × Fin r)) ℂ))
    (hγ : γ ∈ convexHull ℝ (purifications r ρ)) (c : ℝ)
    (h0 : 1-c ≤ sqFidelity γ (oneSiteMarginal Ξ 0))
    (h1 : 1-c ≤ sqFidelity γ (oneSiteMarginal Ξ 1)) :
    oneSiteLoss ρ Ξ ≤ (c : EReal) := by
  have hm : max (1-sqFidelity γ (oneSiteMarginal Ξ 0))
      (1-sqFidelity γ (oneSiteMarginal Ξ 1)) ≤ c := by
    exact max_le (by linarith) (by linarith)
  have hs : oneSiteLoss ρ Ξ ≤
      ((max (1-sqFidelity γ (oneSiteMarginal Ξ 0))
        (1-sqFidelity γ (oneSiteMarginal Ξ 1)) : ℝ) : EReal) := sInf_le ⟨γ,hγ,rfl⟩
  exact hs.trans (EReal.coe_le_coe_iff.mpr hm)

private theorem oneSiteLoss_ge_of_fidelity {d r : ℕ} (ρ : DensityState (Fin d))
    (Ξ : (Matrix (((Fin d × Fin r) × (Fin d × Fin r))) (((Fin d × Fin r) × (Fin d × Fin r))) ℂ)) (c : ℝ)
    (h : ∀ γ ∈ convexHull ℝ (purifications r ρ),
      sqFidelity γ (oneSiteMarginal Ξ 0) ≤ 1-c) :
    (c : EReal) ≤ oneSiteLoss ρ Ξ := by
  apply le_sInf
  rintro x ⟨γ,hγ,rfl⟩
  apply EReal.coe_le_coe_iff.mpr
  exact (show c ≤ 1-sqFidelity γ (oneSiteMarginal Ξ 0) by linarith [h γ hγ]).trans
    (le_max_left _ _)

private theorem worstCase_le_of_loss {d r : ℕ} (T : (Matrix (Fin d) (Fin d) ℂ) → (Matrix (((Fin d × Fin r) × (Fin d × Fin r))) (((Fin d × Fin r) × (Fin d × Fin r))) ℂ)) (c : EReal)
    (h : ∀ ρ : DensityState (Fin d), ((CStarMatrix.ofMatrix.symm ρ.1)).rank ≤ r →
      oneSiteLoss ρ (T ((CStarMatrix.ofMatrix.symm ρ.1))) ≤ c) :
    worstCaseOneSiteRisk T ≤ c := by
  apply sSup_le
  rintro x ⟨ρ,hr,rfl⟩
  exact h ρ hr

private theorem loss_le_worstCase {d r : ℕ} (T : (Matrix (Fin d) (Fin d) ℂ) → (Matrix (((Fin d × Fin r) × (Fin d × Fin r))) (((Fin d × Fin r) × (Fin d × Fin r))) ℂ))
    (ρ : DensityState (Fin d)) (hr : ((CStarMatrix.ofMatrix.symm ρ.1)).rank ≤ r) :
    oneSiteLoss ρ (T ((CStarMatrix.ofMatrix.symm ρ.1))) ≤ worstCaseOneSiteRisk T := by
  exact le_sSup ⟨ρ,hr,rfl⟩

private theorem refute_of_risk_bounds (Φ : QuantumChannel (Fin 2) (((Fin 2 × Fin 2) × (Fin 2 × Fin 2))))
    (hΦ : AdmissibleChannel Φ)
    (hP : (((1/5 : ℝ) : EReal)) ≤ worstCaseOneSiteRisk (purifyAndClone 2 2))
    (hT : worstCaseOneSiteRisk ((fun X => CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)))) ≤ (((1/6 : ℝ) : EReal))) :
    ¬ claim := by
  intro hclaim
  have h := hP.trans ((hclaim 2 2 (by norm_num) (by norm_num) Φ hΦ).trans hT)
  norm_num at h

end
end D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation


namespace D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open scoped ComplexOrder MatrixOrder Kronecker
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private def pureZero : (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.diagonal ![1,0]

private theorem pureZero_pos : pureZero.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num

private theorem pureZero_trace : pureZero.trace = 1 := by
  norm_num [pureZero,Matrix.trace,Fin.sum_univ_two]

private theorem pureZero_sq : pureZero * pureZero = pureZero := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pureZero,Matrix.mul_apply,Fin.sum_univ_two]

private def pureZeroDensity : DensityState (Fin 2) :=
  ⟨CStarMatrix.ofMatrix pureZero,
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv pureZero_pos.nonneg,pureZero_trace⟩

open D5.S3.Quantum.QuantumChannels.WassersteinComplexityNonconvex (trace_sqrt_sq_le_two pure_diag_coupling)

private theorem pure_marginal_representation {G : (Matrix ((Fin 2 × Fin 2)) ((Fin 2 × Fin 2)) ℂ)} (hG : G.PosSemidef)
    (htr : G.trace = 1) (hm : partialTraceRight G = pureZero) :
    G = pureZero ⊗ₖ partialTraceLeft G := by
  let H : (Matrix ((Fin 2 × Fin 2)) ((Fin 2 × Fin 2)) ℂ) := G.submatrix Prod.swap Prod.swap
  have hH : H.PosSemidef := hG.submatrix Prod.swap
  have hHt : H.trace = 1 := by
    calc
      _ = G.trace := (Equiv.prodComm (Fin 2) (Fin 2)).sum_comp (fun p => G p p)
      _ = 1 := htr
  have hr : partialTraceRight H = partialTraceLeft G := rfl
  have hl : partialTraceLeft H =
      (D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState ![1,0]).transpose := by
    change partialTraceRight G = _
    rw [hm]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pureZero,D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState,Matrix.transpose_apply]
  have hp : H ∈ D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.couplings
      (D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState ![1,0])
      (partialTraceLeft G) := ⟨⟨hH,hHt⟩,hr,hl⟩
  have he := pure_diag_coupling hp
  ext ⟨a,e⟩ ⟨b,f⟩
  have hv := congrFun (congrFun he (e,a)) (f,b)
  fin_cases a <;> fin_cases b <;>
    simpa [H,Matrix.kroneckerMap_apply,pureZero,
    D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState,
    Matrix.transpose_apply,mul_comm] using hv

private theorem pure_target_fidelity_bound {G : (Matrix ((Fin 2 × Fin 2)) ((Fin 2 × Fin 2)) ℂ)} (hG : G.PosSemidef)
    (htr : G.trace = 1) (hm : partialTraceRight G = pureZero) :
    sqFidelity G (randomPurifyOne 2 ((3/5 : ℂ) • pureZero + (1/5 : ℂ) • 1)) ≤ 4/5 := by
  let E := partialTraceLeft G
  have hE : E.PosSemidef := partialTraceLeft_posSemidef hG
  have hEt : E.trace = 1 := (trace_partialTraceLeft G).trans htr
  have hrep : G = pureZero ⊗ₖ E := pure_marginal_representation hG htr hm
  have hpRoot : CFC.sqrt pureZero = pureZero := CFC.sqrt_unique pureZero_sq pureZero_pos.nonneg
  have hrootG : CFC.sqrt G = pureZero ⊗ₖ CFC.sqrt E := by
    rw [hrep,sqrt_kronecker _ _ pureZero_pos hE,hpRoot]
  have hfirst : pureZero * ((3/5 : ℂ) • pureZero + (1/5 : ℂ) • (1 : (Matrix (Fin 2) (Fin 2) ℂ))) * pureZero =
      (4/5 : ℂ) • pureZero := by
    simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul,
      pureZero_sq, mul_one, one_mul, smul_smul, ← add_smul]
    norm_num
  have hsecond : CFC.sqrt E * ((1/2 : ℂ) • (1 : (Matrix (Fin 2) (Fin 2) ℂ))) * CFC.sqrt E =
      (1/2 : ℂ) • E := by
    simp only [Matrix.mul_smul,Matrix.smul_mul,mul_one,
      CFC.sqrt_mul_sqrt_self E hE.nonneg]
  have hsand : CFC.sqrt G *
      randomPurifyOne 2 ((3/5 : ℂ) • pureZero + (1/5 : ℂ) • 1) * CFC.sqrt G =
      (2/5 : ℝ) • G := by
    rw [hrootG]
    unfold randomPurifyOne
    norm_num only [Nat.cast_ofNat,invOf_eq_inv,inv_div]
    rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,hfirst]
    rw [hsecond,hrep]
    ext i j
    norm_num [Matrix.kroneckerMap_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  have ht := trace_sqrt_sq_le_two (show D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity E
    from ⟨hE,hEt⟩)
  unfold sqFidelity
  rw [hsand,sqrt_real_smul G hG (2/5) (by norm_num),hrootG,
    Matrix.trace_smul,Matrix.trace_kronecker,pureZero_trace,one_mul]
  simp only [Complex.smul_re,smul_eq_mul,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2/5)]
  nlinarith

private theorem purifyAndClone_pure_marginal :
    oneSiteMarginal (purifyAndClone 2 2 pureZero) 0 =
      randomPurifyOne 2 ((3/5 : ℂ) • pureZero + (1/5 : ℂ) • 1) := by
  ext ⟨a,e⟩ ⟨b,f⟩
  fin_cases a <;> fin_cases e <;> fin_cases b <;> fin_cases f <;>
    norm_num [oneSiteMarginal,partialTraceRight,purifyAndClone,wernerOneToTwo,
      randomPurifyOne,pureZero,Matrix.trace,Matrix.mul_apply,
      Fintype.sum_prod_type,Fin.sum_univ_two,Matrix.kroneckerMap_apply,
      Matrix.smul_apply,smul_eq_mul,Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply,Matrix.one_apply,Matrix.diagonal]

private theorem purifyAndClone_loss_lower : (((1/5 : ℝ) : EReal)) ≤
    oneSiteLoss pureZeroDensity (purifyAndClone 2 2 ((CStarMatrix.ofMatrix.symm pureZeroDensity.1))) := by
  apply oneSiteLoss_ge_of_fidelity
  intro G hG
  obtain ⟨hp,ht,hm⟩ := target_density_and_marginal pureZeroDensity hG
  change partialTraceRight G = pureZero at hm
  change sqFidelity G (oneSiteMarginal (purifyAndClone 2 2 pureZero) 0) ≤ 1-1/5
  rw [purifyAndClone_pure_marginal]
  convert pure_target_fidelity_bound hp ht hm using 1 <;> norm_num

private theorem purifyAndClone_risk_lower : (((1/5 : ℝ) : EReal)) ≤
    worstCaseOneSiteRisk (purifyAndClone 2 2) := by
  exact purifyAndClone_loss_lower.trans (loss_le_worstCase _ pureZeroDensity
    (by simpa using Matrix.rank_le_card_width ((CStarMatrix.ofMatrix.symm pureZeroDensity.1))))

end
end D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation



namespace D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open scoped ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Measurements.BroadcastingChannelExtremaRefutation (density_le_one)
noncomputable section
set_option maxHeartbeats 800000

private theorem competitor_fidelity_lower (ρ : DensityState (Fin 2)) :
    (5/6 : ℝ) ≤ sqFidelity (randomPurifyOne 2 ((CStarMatrix.ofMatrix.symm ρ.1)))
      (randomPurifyOne 2 ((2/3 : ℂ) • (CStarMatrix.ofMatrix.symm ρ.1) + (1/6 : ℂ) • 1)) := by
  let X := (CStarMatrix.ofMatrix.symm ρ.1)
  let Y : (Matrix (Fin 2) (Fin 2) ℂ) := (2/3 : ℂ) • X + (1/6 : ℂ) • 1
  let E : (Matrix (Fin 2) (Fin 2) ℂ) := (2 : ℂ)⁻¹ • 1
  have hX := density_posSemidef ρ
  have hY : Y.PosSemidef :=
    (hX.smul (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 2/3)).add
      (Matrix.PosSemidef.one.smul (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 1/6))
  have hd := density_le_one hX (DensityState.trace_eq_one ρ)
  have hE : E.PosSemidef := Matrix.PosSemidef.one.smul
    (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ (2 : ℂ)⁻¹)
  have hEt : E.trace = 1 := by norm_num [E,Matrix.trace,Fin.sum_univ_two]
  have hpos : (Y - (5/6 : ℝ) • X).PosSemidef := by
    convert hd.smul (by norm_num : (0 : ℝ) ≤ 1/6) using 1
    ext a b
    simp [X,Y,Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply,smul_eq_mul]
    ring
  have ht : Real.sqrt (5/6 : ℝ)^2 = 5/6 := Real.sq_sqrt (by norm_num)
  have hb : (Y - Real.sqrt (5/6 : ℝ)^2 • X).PosSemidef := ht.symm ▸ hpos
  have hf := sqFidelity_ge_of_order X Y hX (DensityState.trace_eq_one ρ)
    (Real.sqrt (5/6)) (Real.sqrt_nonneg _) hb
  change (5/6 : ℝ) ≤ sqFidelity (X ⊗ₖ E) (Y ⊗ₖ E)
  rw [sqFidelity_tensor_same_density X Y E hX hY hE hEt]
  simpa only [ht] using hf

private theorem competitor_loss_upper (ρ : DensityState (Fin 2)) :
    oneSiteLoss ρ (competitor ((CStarMatrix.ofMatrix.symm ρ.1))) ≤ (((1/6 : ℝ) : EReal)) := by
  let B := randomPurifyOne 2 ((2/3 : ℂ) • (CStarMatrix.ofMatrix.symm ρ.1) + (1/6 : ℂ) • 1)
  have htrace : (CStarMatrix.ofMatrix.symm ρ.1).trace = 1 := DensityState.trace_eq_one ρ
  have h0 : oneSiteMarginal (competitor ((CStarMatrix.ofMatrix.symm ρ.1))) 0 = B := by
    simp [oneSiteMarginal,competitor_marginal_right,htrace,B]
  have h1 : oneSiteMarginal (competitor ((CStarMatrix.ofMatrix.symm ρ.1))) 1 = B := by
    simp [oneSiteMarginal,competitor_marginal_left,htrace,B]
  apply oneSiteLoss_le_of_fidelity ρ _ (randomPurifyOne 2 ((CStarMatrix.ofMatrix.symm ρ.1)))
    (randomPurify_mem_target ρ) (1/6)
  · rw [h0]
    convert competitor_fidelity_lower ρ using 1 <;> norm_num
  · rw [h1]
    convert competitor_fidelity_lower ρ using 1 <;> norm_num

private theorem competitor_risk_upper : worstCaseOneSiteRisk competitor ≤ (((1/6 : ℝ) : EReal)) := by
  exact worstCase_le_of_loss competitor _ (fun ρ _ => competitor_loss_upper ρ)

end
end D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation

namespace D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation
open D5.S3.Quantum.Foundation.FiniteStateChannel
noncomputable section

theorem result : ¬ claim := by
  obtain ⟨Φ,hAd,hAct⟩ := competitor_admissible
  have heq : (fun X => CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))) = competitor := funext hAct
  apply refute_of_risk_bounds Φ hAd purifyAndClone_risk_lower
  rw [heq]
  exact competitor_risk_upper

end
end D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation
