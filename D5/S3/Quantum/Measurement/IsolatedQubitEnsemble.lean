/- GID: D5/S3/Quantum/Measurement/IsolatedQubitEnsemble
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/IsolatedQubitEnsemble
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/IsolatedQubitEnsemble.claim; result=D5/S3/Quantum/Measurement/IsolatedQubitEnsemble.result; claim=D5/S3/Quantum/Measurement/IsolatedQubitEnsemble.claim
   digest: A four-state qubit ensemble is isolated under all CPTP channels. -/

/-
proof_shape: result: content; the positive POVM variation supplies the
  first-order equality used to reconstruct the channel.
escape_witness: D5/S3/Quantum/Measurement/QuadraticPovmStationarity.quadratic_stationarity
admission_basis: open-problem-resolution (#15684; Refuted)
Dependencies owned by modules pinned at the searched dev revision
(declaration GID, full Lean name and declaration statement_id):
  F1 = D5/S3/Quantum/FiniteDimensional.qubitZ
    D5.S3.Quantum.FiniteDimensional.qubitZ
    sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
  F2 = D5/S3/Quantum/Foundation/FiniteKrausChannel.MatrixMap
    D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap
    sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
  F3 = D5/S3/Quantum/Foundation/FiniteKrausChannel.IsCompletelyPositive
    D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsCompletelyPositive
    sha256:39e2682fd93035c705a08181bb7fdfb77067eba43afcc98c200c30543b913ed4
  F4 = D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.IsPositive
    D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsCompletelyPositive.IsPositive
    sha256:e3b106b55850a300cff6beca72b575076df897ca795294683afb94780349e0d7
  F5 = D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix
    D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix
    sha256:ee496966fe099c646fb0f51761f3b1e446ac73f2e7b579da5586731706e8c52d
  F6 = D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM
    D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM
    sha256:218e2b42c4dc29468db56af33ad277eb32b8ed575533012439ed233131c5efa1
  F7 = D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.density_coordinates
    D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.Pauli.density_coordinates
    sha256:a3912ad9b3ea3905409b2d9b92617f75f4d5a6cde906eeaf3782b58109a92582
  F8 = D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.choi_psd_of_cp
    D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence.choi_psd_of_cp
    sha256:adf2e5253c9f32677833dfbdd8ee4e2e504bd802b346fca78831e275bf1701a5
  F9 = D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsCPTP
    D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsCPTP
    sha256:1440f7e681ed2017e7c90aedfe54aa0ad218d57311655f9d554863853dd8f53c
  F10 = D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity
    D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity
    sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988
  F11 = D5/S3/QuantumStates/ZeroWeightSupportFace.zero_weight_support_face
    D5.S3.QuantumStates.ZeroWeightSupportFace.zero_weight_support_face
    sha256:c21f5826b1569f02708c19839f076c2ce1484bce1cbb7dbe8279a52fd19c8092
  F12 = D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.trace_mul_nonneg
    Matrix.PosSemidef.trace_mul_nonneg
    sha256:5b79352efb25c3e4916c5e2b342665b58d22929da0d0b37182a2d93ccd0e991b
Per-declaration classification (F-labels name the identities above):
  IsOptimalPOVM: bind-only; consumers: IsOMP, channel_affine, images_affine, isolated, slack_zero_of_optimal, stationarity_constraints, unique_optimal
    frozen-owner dependencies: F6; escape_witness: none
  IsOMP: bind-only; consumers: IsIsolated, isolated
    frozen-owner dependencies: F2, F6; escape_witness: none
  IsIsolated: bind-only; consumers: claim
    frozen-owner dependencies: F2, F6, F9; escape_witness: none
  claim: bind-only; consumers: result
    frozen-owner dependencies: F2, F6, F9, F10; escape_witness: none
  q: bind-only; consumers: result, channel_affine, coordinate_stationarity, images_affine, isolated, kernel_of_slack_zero, optimal_measurement, priors_valid, score_certificate, slack, slack_zero_of_optimal, stationarity_constraints, unique_optimal
    frozen-owner dependencies: none; escape_witness: none
  v: bind-only; consumers: Q, Q_pos, complementary, coordinate_stationarity, curvature_expansion, curve_positive, images_affine, measurement_valid, rho_spanning, slack, states_valid, tangent, tangent_expansion, unique_optimal
    frozen-owner dependencies: none; escape_witness: none
  u: bind-only; consumers: P, P_pos, complementary, coordinate_stationarity, curvature_expansion, direction, images_affine, kernel_of_slack_zero, rho_spanning, slack, states_valid, tangent_expansion, unique_optimal
    frozen-owner dependencies: none; escape_witness: none
  Q: bind-only; consumers: M, complementary, coordinate_stationarity, curvature_expansion, curve_positive, images_affine, measurement_valid, rho, rho_spanning, slack, states_valid, tangent_expansion, unique_optimal
    frozen-owner dependencies: none; escape_witness: none
  P: bind-only; consumers: complementary, images_affine, kernel_of_slack_zero, optimal_measurement, rho, rho_spanning, slack, slack_zero_of_optimal, states_valid
    frozen-owner dependencies: none; escape_witness: none
  M: bind-only; consumers: channel_affine, complementary, coordinate_stationarity, curvature_expansion, curve_positive, images_affine, isolated, measurement_valid, optimal_measurement, slack_zero_of_optimal, stationarity_constraints, tangent_expansion, unique_optimal
    frozen-owner dependencies: none; escape_witness: none
  a: bind-only; consumers: images_affine, kernel_of_slack_zero, optimal_measurement, rho, rho_spanning, slack, slack_zero_of_optimal, states_valid
    frozen-owner dependencies: none; escape_witness: none
  rho: bind-only; consumers: result, channel_affine, channel_eps, channel_tx, channel_ty, channel_tz, images_affine, isolated, kernel_of_slack_zero, optimal_measurement, rho_spanning, score_certificate, slack, slack_zero_of_optimal, states_valid, stationarity_constraints, unique_optimal
    frozen-owner dependencies: none; escape_witness: none
  K: bind-only; consumers: kernel_of_slack_zero, optimal_measurement, score_certificate, slack, slack_zero_of_optimal, unique_optimal
    frozen-owner dependencies: none; escape_witness: none
  priors_valid: bind-only; consumers: result
    frozen-owner dependencies: none; escape_witness: none
  P_pos: bind-only; consumers: kernel_of_slack_zero, optimal_measurement, slack_zero_of_optimal, states_valid
    frozen-owner dependencies: none; escape_witness: none
  Q_pos: bind-only; consumers: measurement_valid, states_valid
    frozen-owner dependencies: none; escape_witness: none
  states_valid: bind-only; consumers: result, images_affine
    frozen-owner dependencies: none; escape_witness: none
  measurement_valid: bind-only; consumers: curvature_expansion, optimal_measurement, slack_zero_of_optimal, stationarity_constraints
    frozen-owner dependencies: none; escape_witness: none
  slack: bind-only; consumers: kernel_of_slack_zero, optimal_measurement, slack_zero_of_optimal
    frozen-owner dependencies: none; escape_witness: none
  complementary: bind-only; consumers: optimal_measurement, slack_zero_of_optimal
    frozen-owner dependencies: none; escape_witness: none
  score_certificate: bind-only; consumers: optimal_measurement, slack_zero_of_optimal
    frozen-owner dependencies: none; escape_witness: none
  optimal_measurement: bind-only; consumers: slack_zero_of_optimal
    frozen-owner dependencies: F6, F12; escape_witness: none
  kernel_of_slack_zero: bind-only; consumers: unique_optimal
    frozen-owner dependencies: F11, F12; escape_witness: none
  slack_zero_of_optimal: bind-only; consumers: unique_optimal
    frozen-owner dependencies: F6, F12; escape_witness: none
  unique_optimal: bind-only; consumers: isolated
    frozen-owner dependencies: F6, F11, F12; escape_witness: none
  affine: bind-only; consumers: channel_affine, choi_eps_nonneg, choi_identity, choi_sum, images_affine, isolated
    frozen-owner dependencies: F2; escape_witness: none
  cw: bind-only; consumers: choi_identity, choi_sum
    frozen-owner dependencies: none; escape_witness: none
  choi_positive: bind-only; consumers: choi_eps_nonneg, choi_identity
    frozen-owner dependencies: F2, F3, F8; escape_witness: none
  choi_sum: bind-only; consumers: choi_identity
    frozen-owner dependencies: F1, F2; escape_witness: none
  choi_eps_nonneg: bind-only; consumers: choi_identity
    frozen-owner dependencies: F1, F2, F3, F8; escape_witness: none
  choi_identity: bind-only; consumers: isolated
    frozen-owner dependencies: F1, F2, F3, F8; escape_witness: none
  direction: bind-only; consumers: coordinate_stationarity, curvature, curvature_expansion, curve_positive, tangent, tangent_expansion
    frozen-owner dependencies: none; escape_witness: none
  tangent: bind-only; consumers: coordinate_stationarity, curve_positive, images_affine, stationarity_constraints, tangent_expansion
    frozen-owner dependencies: none; escape_witness: none
  curvature: bind-only; consumers: curvature_expansion, curve_positive, stationarity_constraints
    frozen-owner dependencies: none; escape_witness: none
  dc: bind-only; consumers: coordinate_stationarity, images_affine, stationarity_constraints, tangent_expansion
    frozen-owner dependencies: none; escape_witness: none
  ec: bind-only; consumers: curvature_expansion, stationarity_constraints
    frozen-owner dependencies: none; escape_witness: none
  tangent_expansion: bind-only; consumers: stationarity_constraints
    frozen-owner dependencies: none; escape_witness: none
  curvature_expansion: bind-only; consumers: stationarity_constraints
    frozen-owner dependencies: none; escape_witness: none
  curve_positive: bind-only; consumers: stationarity_constraints
    frozen-owner dependencies: none; escape_witness: none
  channel_tx: bind-only; consumers: channel_affine, images_affine, isolated
    frozen-owner dependencies: F2; escape_witness: none
  channel_ty: bind-only; consumers: channel_affine, images_affine, isolated
    frozen-owner dependencies: F2; escape_witness: none
  channel_tz: bind-only; consumers: channel_affine, images_affine, isolated
    frozen-owner dependencies: F2; escape_witness: none
  channel_eps: bind-only; consumers: channel_affine, images_affine, isolated
    frozen-owner dependencies: F2; escape_witness: none
  stationarity_constraints: content; consumers: images_affine
    frozen-owner dependencies: F2, F6; escape_witness: D5/S3/Quantum/Measurement/QuadraticPovmStationarity.quadratic_stationarity
  g: bind-only; consumers: coordinate_stationarity, images_affine
    frozen-owner dependencies: none; escape_witness: none
  coordinate_stationarity: bind-only; consumers: images_affine
    frozen-owner dependencies: F5; escape_witness: none
  images_affine: content; consumers: channel_affine
    frozen-owner dependencies: F2, F3, F4, F5, F6, F7, F9; escape_witness: D5/S3/Quantum/Measurement/QuadraticPovmStationarity.quadratic_stationarity
  basis_coeff: bind-only; consumers: channel_affine, rho_spanning
    frozen-owner dependencies: none; escape_witness: none
  rho_spanning: bind-only; consumers: channel_affine
    frozen-owner dependencies: none; escape_witness: none
  channel_affine: content; consumers: isolated
    frozen-owner dependencies: F2, F3, F4, F5, F6, F7, F9; escape_witness: D5/S3/Quantum/Measurement/QuadraticPovmStationarity.quadratic_stationarity
  isolated: content; consumers: result
    frozen-owner dependencies: F1, F2, F3, F4, F5, F6, F7, F8, F9, F11, F12; escape_witness: D5/S3/Quantum/Measurement/QuadraticPovmStationarity.quadratic_stationarity
  result: content; consumers: none
    frozen-owner dependencies: F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12; escape_witness: D5/S3/Quantum/Measurement/QuadraticPovmStationarity.quadratic_stationarity
The supporting first-order stationarity theorem is same-delivery content.
The density-coordinate and Choi-positivity declarations are same-delivery
publicizations of private theorems in pinned owner modules.
Their escape audits are unfinished under issue #16207.
The supporting stationarity audit is unfinished under issue #15773.
These audits require source reconstruction, lawful enrolled readouts,
variation, sensitivity and observational-dependence evidence.
The designated refutation result is exempt from four-slot registration.
The claim states the optimality, OMP and isolation formulas of issue #15684.
IsDensity, IsCPTP and IsPOVM use their existing owners.
The closed, unfrozen FiniteKrausRepresentation module is in the imported
IptPptSquaredEquivalence owner's dependency closure. The Choi positivity
proof applies that owner and normalizes its tensor order.
ZeroWeightSupportFace.zero_weight_support_face supplies the complementary
support annihilation used by kernel_of_slack_zero.
-/

import D5.S3.Quantum.Measurement.QuadraticPovmStationarity
import D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction
import D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
import D5.S3.QuantumStates.ZeroWeightSupportFace

set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.FiniteDimensional (qubitZ)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity IsCPTP)
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
open D5.S3.Quantum.Measurement.QuadraticPovmStationarity (quadratic_stationarity)
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum (blochMatrix)
noncomputable section
namespace D5.S3.Quantum.Measurement.IsolatedQubitEnsemble

def IsOptimalPOVM {n : ℕ} (q : Fin n → ℝ) (rho : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  IsPOVM M ∧ ∀ F, IsPOVM F →
    ∑ i, q i * (Matrix.trace (rho i * F i)).re ≤
    ∑ i, q i * (Matrix.trace (rho i * M i)).re

def IsOMP {n : ℕ} (q : Fin n → ℝ) (rho : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (N : MatrixMap (Fin 2) (Fin 2) ℂ) : Prop :=
  ∃ M, IsOptimalPOVM q rho M ∧ IsOptimalPOVM q (fun i => N (rho i)) M

def IsIsolated {n : ℕ} (q : Fin n → ℝ) (rho : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ N, IsCPTP N → IsOMP q rho N → N = LinearMap.id

def claim : Prop := ∀ (n : ℕ) (q : Fin n → ℝ) (rho : Fin n → Matrix (Fin 2) (Fin 2) ℂ),
  (∀ i, 0 < q i) → ∑ i, q i = 1 → (∀ i, IsDensity (rho i)) →
    ¬ IsIsolated q rho


private def q : Fin 4 → ℝ := ![9/28,9/28,5/28,5/28]
private def v : Fin 4 → Fin 2 → ℂ := ![![1,-3],![1,3],![3,-Complex.I],![3,Complex.I]]
private def u : Fin 4 → Fin 2 → ℂ := ![![3,1],![-3,1],![-Complex.I,3],![Complex.I,3]]
private def Q (i : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ := (1/10 : ℂ) • vecMulVec (v i) (star (v i))
private def P (i : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ := (1/10 : ℂ) • vecMulVec (u i) (star (u i))
private def M (i : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ := (1/2 : ℂ) • Q i
private def a : Fin 4 → ℝ := ![1,1,9,9]
private def rho (i : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 - a i / (19 - a i))/2 : ℝ) • P i +
  ((1 + a i / (19 - a i))/2 : ℝ) • Q i
private def K : Matrix (Fin 2) (Fin 2) ℂ := (19/112 : ℂ) • 1

private theorem priors_valid : (∀ i, 0 < q i) ∧ ∑ i, q i = 1 := by
  constructor
  · intro i; fin_cases i <;> norm_num [q]
  · norm_num [q, Fin.sum_univ_succ]

private theorem P_pos (i : Fin 4) : (P i).PosSemidef :=
  (posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.nonneg_iff])
private theorem Q_pos (i : Fin 4) : (Q i).PosSemidef :=
  (posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.nonneg_iff])
private theorem states_valid (i : Fin 4) : IsDensity (rho i) := by
  constructor
  · apply PosSemidef.add
    · apply (P_pos i).smul
      fin_cases i <;> norm_num [a]
    · apply (Q_pos i).smul
      fin_cases i <;> norm_num [a]
  · fin_cases i <;> norm_num [rho,P,Q,u,v,a,trace,Fin.sum_univ_two,vecMulVec,
      Complex.ext_iff,Complex.real_smul]

private theorem measurement_valid : IsPOVM M := by
  constructor
  · intro i; exact (Q_pos i).smul (by norm_num [Complex.nonneg_iff])
  · ext x y; fin_cases x <;> fin_cases y <;>
      norm_num [M,Q,v,Fin.sum_univ_succ,vecMulVec,Complex.ext_iff]

private theorem slack (i : Fin 4) : K - (q i : ℂ) • rho i = (a i / 56 : ℝ) • P i := by
  fin_cases i <;> ext x y <;> fin_cases x <;> fin_cases y <;>
    norm_num [K,q,rho,P,Q,u,v,a,vecMulVec,Complex.real_smul,Complex.ext_iff]

private theorem complementary (i : Fin 4) : P i * M i = 0 := by
  fin_cases i <;> ext x y <;> fin_cases x <;> fin_cases y <;>
    norm_num [P,M,Q,u,v,vecMulVec,Matrix.mul_apply,Fin.sum_univ_two,Complex.ext_iff]

private theorem score_certificate (F : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) (hF : ∑ i, F i = 1) :
    (∑ i, q i * (trace (rho i * F i)).re) = (trace K).re -
      ∑ i, (trace ((K - (q i : ℂ) • rho i) * F i)).re := by
  have hk : ∑ i, (trace (K * F i)).re = (trace K).re := by
    rw [← Complex.re_sum, ← trace_sum, ← Finset.mul_sum, hF, mul_one]
  simp only [sub_mul, trace_sub, Complex.sub_re, Finset.sum_sub_distrib,hk,
    smul_mul_assoc,trace_smul,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  ring

private theorem optimal_measurement : IsOptimalPOVM q rho M := by
  refine ⟨measurement_valid, ?_⟩
  intro F hF
  change (∑ i, q i * (trace (rho i * F i)).re) ≤ (∑ i, q i * (trace (rho i * M i)).re)
  rw [score_certificate F hF.2,score_certificate M measurement_valid.2]
  have hz : ∀ i, (K - (q i : ℂ) • rho i) * M i = 0 := by
    intro i; rw [slack,smul_mul_assoc,complementary,smul_zero]
  simp only [hz,trace_zero,Complex.zero_re,Finset.sum_const_zero,sub_zero]
  have hn : 0 ≤ ∑ i, (trace ((K - (q i : ℂ) • rho i) * F i)).re := by
    apply Finset.sum_nonneg
    intro i _
    apply (Complex.nonneg_iff.mp (Matrix.PosSemidef.trace_mul_nonneg ?_ (hF.1 i))).1
    rw [slack]
    apply (P_pos i).smul
    fin_cases i <;> norm_num [a]
  linarith

private theorem kernel_of_slack_zero (i : Fin 4) (F : Matrix (Fin 2) (Fin 2) ℂ) (hF : F.PosSemidef)
    (hz : (trace ((K - (q i : ℂ) • rho i) * F)).re = 0) :
    F *ᵥ u i = 0 := by
  have he : (trace ((K - (q i : ℂ) • rho i) * F)).re =
      (a i / 56) * (trace (P i * F)).re := by
    rw [slack, smul_mul_assoc, trace_smul, Complex.real_smul]
    simp [Complex.mul_re]
  rw [he] at hz
  have ha : a i / 56 ≠ 0 := by fin_cases i <;> norm_num [a]
  have hr : (trace (P i * F)).re = 0 := (mul_eq_zero.mp hz).resolve_left ha
  have hi := (Complex.nonneg_iff.mp ((P_pos i).trace_mul_nonneg hF)).2
  have ht : trace (F * P i) = 0 := by
    rw [trace_mul_comm]
    exact Complex.ext hr hi.symm
  have hid : P i * P i = P i := by
    fin_cases i <;> ext x y <;> fin_cases x <;> fin_cases y <;>
      norm_num [P, u, vecMulVec, Matrix.mul_apply, Fin.sum_univ_two,
        Complex.ext_iff, Complex.conj_ofNat]
  have hzP := (D5.S3.QuantumStates.ZeroWeightSupportFace.zero_weight_support_face
    F (P i) hF (P_pos i).isHermitian.eq hid ht).1.2
  have hu : P i *ᵥ u i = u i := by
    fin_cases i <;> ext x <;> fin_cases x <;>
      norm_num [P, u, vecMulVec, mulVec, dotProduct, Fin.sum_univ_two,
        Complex.ext_iff, Complex.conj_ofNat]
  calc
    F *ᵥ u i = F *ᵥ (P i *ᵥ u i) := by rw [hu]
    _ = (F * P i) *ᵥ u i := mulVec_mulVec (u i) F (P i)
    _ = 0 := by rw [hzP]; exact zero_mulVec _

private theorem slack_zero_of_optimal (F : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) (hF : IsOptimalPOVM q rho F) :
    ∀ i, (trace ((K - (q i : ℂ) • rho i) * F i)).re = 0 := by
  have hscoreEq : (∑ i, q i * (trace (rho i * F i)).re) = (∑ i, q i * (trace (rho i * M i)).re) :=
    le_antisymm (optimal_measurement.2 F hF.1) (hF.2 M measurement_valid)
  have hle : (∑ i, q i * (trace (rho i * M i)).re) ≤ (∑ i, q i * (trace (rho i * F i)).re) := le_of_eq hscoreEq.symm
  rw [score_certificate F hF.1.2, score_certificate M measurement_valid.2] at hle
  have hz : ∀ i, (K - (q i : ℂ) • rho i) * M i = 0 := by
    intro i; rw [slack,smul_mul_assoc,complementary,smul_zero]
  simp only [hz,trace_zero,Complex.zero_re,Finset.sum_const_zero,sub_zero] at hle
  have hn (i : Fin 4) : 0 ≤ (trace ((K - (q i : ℂ) • rho i) * F i)).re := by
    apply (Complex.nonneg_iff.mp (Matrix.PosSemidef.trace_mul_nonneg ?_ (hF.1.1 i))).1
    rw [slack]; apply (P_pos i).smul
    fin_cases i <;> norm_num [a]
  have hs : ∑ i, (trace ((K - (q i : ℂ) • rho i) * F i)).re = 0 := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hn i)
    linarith
  exact fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp hs i
    (Finset.mem_univ i)

private theorem unique_optimal (F : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) (hF : IsOptimalPOVM q rho F) : F = M := by
  have hz := slack_zero_of_optimal F hF
  have hk (i : Fin 4) : F i *ᵥ u i = 0 :=
    kernel_of_slack_zero i (F i) (hF.1.1 i) (hz i)
  have hh (i : Fin 4) (x y : Fin 2) : star (F i y x) = F i x y := by
    exact congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A x y) (hF.1.1 i).isHermitian.eq
  have hleft (i : Fin 4) (a : Fin 2) :
      star (u i 0) * F i 0 a + star (u i 1) * F i 1 a = 0 := by
    have h := congrArg (fun z : ℂ => star z) (congrFun (hk i) a)
    simp only [mulVec,dotProduct,Fin.sum_univ_two,Pi.zero_apply,star_add,star_mul,hh,star_zero] at h
    simpa only [mul_comm] using h
  have hr00 := congrFun (hk 0) 0
  simp only [mulVec,dotProduct,Fin.sum_univ_two,Pi.zero_apply] at hr00
  change F 0 0 0 * (3) + F 0 0 1 * 1 = 0 at hr00
  norm_num at hr00
  have hr01 := congrFun (hk 0) 1
  simp only [mulVec,dotProduct,Fin.sum_univ_two,Pi.zero_apply] at hr01
  change F 0 1 0 * (3) + F 0 1 1 * 1 = 0 at hr01
  norm_num at hr01
  have hl00 := hleft 0 0
  change star (3 : ℂ) * F 0 0 0 + star (1 : ℂ) * F 0 1 0 = 0 at hl00
  norm_num at hl00
  have hl01 := hleft 0 1
  change star (3 : ℂ) * F 0 0 1 + star (1 : ℂ) * F 0 1 1 = 0 at hl01
  norm_num at hl01
  have hr10 := congrFun (hk 1) 0
  simp only [mulVec,dotProduct,Fin.sum_univ_two,Pi.zero_apply] at hr10
  change F 1 0 0 * (-3) + F 1 0 1 * 1 = 0 at hr10
  norm_num at hr10
  have hr11 := congrFun (hk 1) 1
  simp only [mulVec,dotProduct,Fin.sum_univ_two,Pi.zero_apply] at hr11
  change F 1 1 0 * (-3) + F 1 1 1 * 1 = 0 at hr11
  norm_num at hr11
  have hl10 := hleft 1 0
  change star (-3 : ℂ) * F 1 0 0 + star (1 : ℂ) * F 1 1 0 = 0 at hl10
  norm_num at hl10
  have hl11 := hleft 1 1
  change star (-3 : ℂ) * F 1 0 1 + star (1 : ℂ) * F 1 1 1 = 0 at hl11
  norm_num at hl11
  have hr20 := congrFun (hk 2) 0
  simp only [mulVec,dotProduct,Fin.sum_univ_two,Pi.zero_apply] at hr20
  change F 2 0 0 * (-Complex.I) + F 2 0 1 * 3 = 0 at hr20
  norm_num at hr20
  have hr21 := congrFun (hk 2) 1
  simp only [mulVec,dotProduct,Fin.sum_univ_two,Pi.zero_apply] at hr21
  change F 2 1 0 * (-Complex.I) + F 2 1 1 * 3 = 0 at hr21
  norm_num at hr21
  have hl20 := hleft 2 0
  change star (-Complex.I : ℂ) * F 2 0 0 + star (3 : ℂ) * F 2 1 0 = 0 at hl20
  norm_num at hl20
  have hl21 := hleft 2 1
  change star (-Complex.I : ℂ) * F 2 0 1 + star (3 : ℂ) * F 2 1 1 = 0 at hl21
  norm_num at hl21
  have hr30 := congrFun (hk 3) 0
  simp only [mulVec,dotProduct,Fin.sum_univ_two,Pi.zero_apply] at hr30
  change F 3 0 0 * (Complex.I) + F 3 0 1 * 3 = 0 at hr30
  have hr31 := congrFun (hk 3) 1
  simp only [mulVec,dotProduct,Fin.sum_univ_two,Pi.zero_apply] at hr31
  change F 3 1 0 * (Complex.I) + F 3 1 1 * 3 = 0 at hr31
  have hl30 := hleft 3 0
  change star (Complex.I : ℂ) * F 3 0 0 + star (3 : ℂ) * F 3 1 0 = 0 at hl30
  norm_num at hl30
  have hl31 := hleft 3 1
  change star (Complex.I : ℂ) * F 3 0 1 + star (3 : ℂ) * F 3 1 1 = 0 at hl31
  norm_num at hl31
  have hs00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) hF.1.2
  norm_num [Fin.sum_univ_succ] at hs00
  change F 0 0 0 + (F 1 0 0 + (F 2 0 0 + F 3 0 0)) = 1 at hs00
  have hs01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) hF.1.2
  norm_num [Fin.sum_univ_succ] at hs01
  change F 0 0 1 + (F 1 0 1 + (F 2 0 1 + F 3 0 1)) = 0 at hs01
  have hs10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 0) hF.1.2
  norm_num [Fin.sum_univ_succ] at hs10
  change F 0 1 0 + (F 1 1 0 + (F 2 1 0 + F 3 1 0)) = 0 at hs10
  have hs11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 1) hF.1.2
  norm_num [Fin.sum_univ_succ] at hs11
  change F 0 1 1 + (F 1 1 1 + (F 2 1 1 + F 3 1 1)) = 1 at hs11
  ext i a b
  fin_cases i <;> fin_cases a <;> fin_cases b
  · norm_num [M,Q,v,vecMulVec,Complex.conj_ofNat]
    linear_combination (norm := (ring_nf <;> simp [Complex.I_sq])) (1/12 : ℂ) * hr00 + (-9/160 : ℂ) * hr01 + (121/480 : ℂ) * hl00 + (1/12 : ℂ) * hr10 + (-9/160 : ℂ) * hr11 + (-41/480 : ℂ) * hl10 + (1/36 : ℂ) * hr20 + (-3/160 : ℂ) * hr21 + ((1/36 : ℂ) + (-1/160 : ℂ) * Complex.I) * hl20 + (1/36 : ℂ) * hr30 + (-3/160 : ℂ) * hr31 + ((1/36 : ℂ) + (1/160 : ℂ) * Complex.I) * hl30 + (-1/160 : ℂ) * hs00 + (-1/12 : ℂ) * hs01 + (-1/12 : ℂ) * hs10 + (9/160 : ℂ) * hs11
  · norm_num [M,Q,v,vecMulVec,Complex.conj_ofNat]
    linear_combination (norm := (ring_nf <;> simp [Complex.I_sq])) (3/4 : ℂ) * hr00 + (27/160 : ℂ) * hr01 + (-121/160 : ℂ) * hl00 + (-1/4 : ℂ) * hr10 + (27/160 : ℂ) * hr11 + (41/160 : ℂ) * hl10 + (-1/12 : ℂ) * hr20 + (9/160 : ℂ) * hr21 + ((-1/12 : ℂ) + (3/160 : ℂ) * Complex.I) * hl20 + (-1/12 : ℂ) * hr30 + (9/160 : ℂ) * hr31 + ((-1/12 : ℂ) + (-3/160 : ℂ) * Complex.I) * hl30 + (3/160 : ℂ) * hs00 + (1/4 : ℂ) * hs01 + (1/4 : ℂ) * hs10 + (-27/160 : ℂ) * hs11
  · norm_num [M,Q,v,vecMulVec,Complex.conj_ofNat]
    linear_combination (norm := (ring_nf <;> simp [Complex.I_sq])) (-1/4 : ℂ) * hr00 + (27/160 : ℂ) * hr01 + (39/160 : ℂ) * hl00 + (-1/4 : ℂ) * hr10 + (27/160 : ℂ) * hr11 + (41/160 : ℂ) * hl10 + (-1/12 : ℂ) * hr20 + (9/160 : ℂ) * hr21 + ((-1/12 : ℂ) + (3/160 : ℂ) * Complex.I) * hl20 + (-1/12 : ℂ) * hr30 + (9/160 : ℂ) * hr31 + ((-1/12 : ℂ) + (-3/160 : ℂ) * Complex.I) * hl30 + (3/160 : ℂ) * hs00 + (1/4 : ℂ) * hs01 + (1/4 : ℂ) * hs10 + (-27/160 : ℂ) * hs11
  · norm_num [M,Q,v,vecMulVec,Complex.conj_ofNat]
    linear_combination (norm := (ring_nf <;> simp [Complex.I_sq])) (3/4 : ℂ) * hr00 + (79/160 : ℂ) * hr01 + (-117/160 : ℂ) * hl00 + (3/4 : ℂ) * hr10 + (-81/160 : ℂ) * hr11 + (-123/160 : ℂ) * hl10 + (1/4 : ℂ) * hr20 + (-27/160 : ℂ) * hr21 + ((1/4 : ℂ) + (-9/160 : ℂ) * Complex.I) * hl20 + (1/4 : ℂ) * hr30 + (-27/160 : ℂ) * hr31 + ((1/4 : ℂ) + (9/160 : ℂ) * Complex.I) * hl30 + (-9/160 : ℂ) * hs00 + (-3/4 : ℂ) * hs01 + (-3/4 : ℂ) * hs10 + (81/160 : ℂ) * hs11
  · norm_num [M,Q,v,vecMulVec,Complex.conj_ofNat]
    linear_combination (norm := (ring_nf <;> simp [Complex.I_sq])) (-1/12 : ℂ) * hr00 + (-9/160 : ℂ) * hr01 + (41/480 : ℂ) * hl00 + (-1/12 : ℂ) * hr10 + (-9/160 : ℂ) * hr11 + (-121/480 : ℂ) * hl10 + (-1/36 : ℂ) * hr20 + (-3/160 : ℂ) * hr21 + ((-1/36 : ℂ) + (-1/160 : ℂ) * Complex.I) * hl20 + (-1/36 : ℂ) * hr30 + (-3/160 : ℂ) * hr31 + ((-1/36 : ℂ) + (1/160 : ℂ) * Complex.I) * hl30 + (-1/160 : ℂ) * hs00 + (1/12 : ℂ) * hs01 + (1/12 : ℂ) * hs10 + (9/160 : ℂ) * hs11
  · norm_num [M,Q,v,vecMulVec,Complex.conj_ofNat]
    linear_combination (norm := (ring_nf <;> simp [Complex.I_sq])) (-1/4 : ℂ) * hr00 + (-27/160 : ℂ) * hr01 + (41/160 : ℂ) * hl00 + (3/4 : ℂ) * hr10 + (-27/160 : ℂ) * hr11 + (-121/160 : ℂ) * hl10 + (-1/12 : ℂ) * hr20 + (-9/160 : ℂ) * hr21 + ((-1/12 : ℂ) + (-3/160 : ℂ) * Complex.I) * hl20 + (-1/12 : ℂ) * hr30 + (-9/160 : ℂ) * hr31 + ((-1/12 : ℂ) + (3/160 : ℂ) * Complex.I) * hl30 + (-3/160 : ℂ) * hs00 + (1/4 : ℂ) * hs01 + (1/4 : ℂ) * hs10 + (27/160 : ℂ) * hs11
  · norm_num [M,Q,v,vecMulVec,Complex.conj_ofNat]
    linear_combination (norm := (ring_nf <;> simp [Complex.I_sq])) (-1/4 : ℂ) * hr00 + (-27/160 : ℂ) * hr01 + (41/160 : ℂ) * hl00 + (-1/4 : ℂ) * hr10 + (-27/160 : ℂ) * hr11 + (39/160 : ℂ) * hl10 + (-1/12 : ℂ) * hr20 + (-9/160 : ℂ) * hr21 + ((-1/12 : ℂ) + (-3/160 : ℂ) * Complex.I) * hl20 + (-1/12 : ℂ) * hr30 + (-9/160 : ℂ) * hr31 + ((-1/12 : ℂ) + (3/160 : ℂ) * Complex.I) * hl30 + (-3/160 : ℂ) * hs00 + (1/4 : ℂ) * hs01 + (1/4 : ℂ) * hs10 + (27/160 : ℂ) * hs11
  · norm_num [M,Q,v,vecMulVec,Complex.conj_ofNat]
    linear_combination (norm := (ring_nf <;> simp [Complex.I_sq])) (-3/4 : ℂ) * hr00 + (-81/160 : ℂ) * hr01 + (123/160 : ℂ) * hl00 + (-3/4 : ℂ) * hr10 + (79/160 : ℂ) * hr11 + (117/160 : ℂ) * hl10 + (-1/4 : ℂ) * hr20 + (-27/160 : ℂ) * hr21 + ((-1/4 : ℂ) + (-9/160 : ℂ) * Complex.I) * hl20 + (-1/4 : ℂ) * hr30 + (-27/160 : ℂ) * hr31 + ((-1/4 : ℂ) + (9/160 : ℂ) * Complex.I) * hl30 + (-9/160 : ℂ) * hs00 + (3/4 : ℂ) * hs01 + (3/4 : ℂ) * hs10 + (81/160 : ℂ) * hs11
  · norm_num [M,Q,v,vecMulVec,Complex.conj_ofNat]
    linear_combination (norm := (ring_nf <;> simp [Complex.I_sq] <;> ring)) ((3/4 : ℂ) * Complex.I) * hr00 + (9/160 : ℂ) * hr01 + ((-27/160 : ℂ) + (-3/4 : ℂ) * Complex.I) * hl00 + ((3/4 : ℂ) * Complex.I) * hr10 + (9/160 : ℂ) * hr11 + ((27/160 : ℂ) + (-3/4 : ℂ) * Complex.I) * hl10 + ((1/4 : ℂ) * Complex.I) * hr20 + (3/160 : ℂ) * hr21 + ((-39/160 : ℂ) * Complex.I) * hl20 + ((1/4 : ℂ) * Complex.I) * hr30 + (3/160 : ℂ) * hr31 + ((-41/160 : ℂ) * Complex.I) * hl30 + (81/160 : ℂ) * hs00 + ((-3/4 : ℂ) * Complex.I) * hs01 + ((3/4 : ℂ) * Complex.I) * hs10 + (-9/160 : ℂ) * hs11
  · norm_num [M,Q,v,vecMulVec,Complex.conj_ofNat]
    linear_combination (norm := (ring_nf <;> simp [Complex.I_sq] <;> ring)) (-1/4 : ℂ) * hr00 + ((3/160 : ℂ) * Complex.I) * hr01 + ((1/4 : ℂ) + (-9/160 : ℂ) * Complex.I) * hl00 + (-1/4 : ℂ) * hr10 + ((3/160 : ℂ) * Complex.I) * hr11 + ((1/4 : ℂ) + (9/160 : ℂ) * Complex.I) * hl10 + (1/4 : ℂ) * hr20 + ((1/160 : ℂ) * Complex.I) * hr21 + (13/160 : ℂ) * hl20 + (-1/12 : ℂ) * hr30 + ((1/160 : ℂ) * Complex.I) * hr31 + (41/480 : ℂ) * hl30 + ((27/160 : ℂ) * Complex.I) * hs00 + (1/4 : ℂ) * hs01 + (-1/4 : ℂ) * hs10 + ((-3/160 : ℂ) * Complex.I) * hs11
  · norm_num [M,Q,v,vecMulVec,Complex.conj_ofNat]
    linear_combination (norm := (ring_nf <;> simp [Complex.I_sq] <;> ring)) (1/4 : ℂ) * hr00 + ((-3/160 : ℂ) * Complex.I) * hr01 + ((-1/4 : ℂ) + (9/160 : ℂ) * Complex.I) * hl00 + (1/4 : ℂ) * hr10 + ((-3/160 : ℂ) * Complex.I) * hr11 + ((-1/4 : ℂ) + (-9/160 : ℂ) * Complex.I) * hl10 + (1/12 : ℂ) * hr20 + ((-1/160 : ℂ) * Complex.I) * hr21 + (121/480 : ℂ) * hl20 + (1/12 : ℂ) * hr30 + ((-1/160 : ℂ) * Complex.I) * hr31 + (-41/480 : ℂ) * hl30 + ((-27/160 : ℂ) * Complex.I) * hs00 + (-1/4 : ℂ) * hs01 + (1/4 : ℂ) * hs10 + ((3/160 : ℂ) * Complex.I) * hs11
  · norm_num [M,Q,v,vecMulVec,Complex.conj_ofNat]
    linear_combination (norm := (ring_nf <;> simp [Complex.I_sq] <;> ring)) ((1/12 : ℂ) * Complex.I) * hr00 + (1/160 : ℂ) * hr01 + ((-3/160 : ℂ) + (-1/12 : ℂ) * Complex.I) * hl00 + ((1/12 : ℂ) * Complex.I) * hr10 + (1/160 : ℂ) * hr11 + ((3/160 : ℂ) + (-1/12 : ℂ) * Complex.I) * hl10 + ((1/36 : ℂ) * Complex.I) * hr20 + (161/480 : ℂ) * hr21 + ((121/1440 : ℂ) * Complex.I) * hl20 + ((1/36 : ℂ) * Complex.I) * hr30 + (1/480 : ℂ) * hr31 + ((-41/1440 : ℂ) * Complex.I) * hl30 + (9/160 : ℂ) * hs00 + ((-1/12 : ℂ) * Complex.I) * hs01 + ((1/12 : ℂ) * Complex.I) * hs10 + (-1/160 : ℂ) * hs11
  · norm_num [M,Q,v,vecMulVec,Complex.conj_ofNat]
    linear_combination (norm := (ring_nf <;> simp [Complex.I_sq] <;> ring)) ((-3/4 : ℂ) * Complex.I) * hr00 + (9/160 : ℂ) * hr01 + ((-27/160 : ℂ) + (3/4 : ℂ) * Complex.I) * hl00 + ((-3/4 : ℂ) * Complex.I) * hr10 + (9/160 : ℂ) * hr11 + ((27/160 : ℂ) + (3/4 : ℂ) * Complex.I) * hl10 + ((-1/4 : ℂ) * Complex.I) * hr20 + (3/160 : ℂ) * hr21 + ((41/160 : ℂ) * Complex.I) * hl20 + ((-1/4 : ℂ) * Complex.I) * hr30 + (3/160 : ℂ) * hr31 + ((39/160 : ℂ) * Complex.I) * hl30 + (81/160 : ℂ) * hs00 + ((3/4 : ℂ) * Complex.I) * hs01 + ((-3/4 : ℂ) * Complex.I) * hs10 + (-9/160 : ℂ) * hs11
  · norm_num [M,Q,v,vecMulVec,Complex.conj_ofNat]
    linear_combination (norm := (ring_nf <;> simp [Complex.I_sq] <;> ring)) (-1/4 : ℂ) * hr00 + ((-3/160 : ℂ) * Complex.I) * hr01 + ((1/4 : ℂ) + (9/160 : ℂ) * Complex.I) * hl00 + (-1/4 : ℂ) * hr10 + ((-3/160 : ℂ) * Complex.I) * hr11 + ((1/4 : ℂ) + (-9/160 : ℂ) * Complex.I) * hl10 + (-1/12 : ℂ) * hr20 + ((-1/160 : ℂ) * Complex.I) * hr21 + (41/480 : ℂ) * hl20 + (1/4 : ℂ) * hr30 + ((-1/160 : ℂ) * Complex.I) * hr31 + (13/160 : ℂ) * hl30 + ((-27/160 : ℂ) * Complex.I) * hs00 + (1/4 : ℂ) * hs01 + (-1/4 : ℂ) * hs10 + ((3/160 : ℂ) * Complex.I) * hs11
  · norm_num [M,Q,v,vecMulVec,Complex.conj_ofNat]
    linear_combination (norm := (ring_nf <;> simp [Complex.I_sq] <;> ring)) (1/4 : ℂ) * hr00 + ((3/160 : ℂ) * Complex.I) * hr01 + ((-1/4 : ℂ) + (-9/160 : ℂ) * Complex.I) * hl00 + (1/4 : ℂ) * hr10 + ((3/160 : ℂ) * Complex.I) * hr11 + ((-1/4 : ℂ) + (9/160 : ℂ) * Complex.I) * hl10 + (1/12 : ℂ) * hr20 + ((1/160 : ℂ) * Complex.I) * hr21 + (-41/480 : ℂ) * hl20 + (1/12 : ℂ) * hr30 + ((1/160 : ℂ) * Complex.I) * hr31 + (121/480 : ℂ) * hl30 + ((27/160 : ℂ) * Complex.I) * hs00 + (-1/4 : ℂ) * hs01 + (1/4 : ℂ) * hs10 + ((-3/160 : ℂ) * Complex.I) * hs11
  · norm_num [M,Q,v,vecMulVec,Complex.conj_ofNat]
    linear_combination (norm := (ring_nf <;> simp [Complex.I_sq] <;> ring)) ((-1/12 : ℂ) * Complex.I) * hr00 + (1/160 : ℂ) * hr01 + ((-3/160 : ℂ) + (1/12 : ℂ) * Complex.I) * hl00 + ((-1/12 : ℂ) * Complex.I) * hr10 + (1/160 : ℂ) * hr11 + ((3/160 : ℂ) + (1/12 : ℂ) * Complex.I) * hl10 + ((-1/36 : ℂ) * Complex.I) * hr20 + (1/480 : ℂ) * hr21 + ((41/1440 : ℂ) * Complex.I) * hl20 + ((-1/36 : ℂ) * Complex.I) * hr30 + (161/480 : ℂ) * hr31 + ((-121/1440 : ℂ) * Complex.I) * hl30 + (9/160 : ℂ) * hs00 + ((1/12 : ℂ) * Complex.I) * hs01 + ((-1/12 : ℂ) * Complex.I) * hs10 + (-1/160 : ℂ) * hs11


private def affine (eps tx ty tz : ℝ) : MatrixMap (Fin 2) (Fin 2) ℂ :=
  let entry (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) j).comp
      (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => Fin 2 → ℂ) i)
  let f : MatrixMap (Fin 2) (Fin 2) ℂ := LinearMap.pi ![
    LinearMap.pi ![
      (1/2 : ℂ) • (entry 0 0 + entry 1 1 +
        ((1-9*eps/5+tz : ℝ):ℂ) • (entry 0 0-entry 1 1) +
        (tz:ℂ) • (entry 0 0+entry 1 1)),
      (1/2 : ℂ) • (((1-9*eps : ℝ):ℂ) • (entry 0 1+entry 1 0) +
        (tx:ℂ) • (entry 0 0-entry 1 1) + (tx:ℂ) • (entry 0 0+entry 1 1) -
        Complex.I • (((1-eps : ℝ):ℂ) • (Complex.I • (entry 0 1-entry 1 0)) +
          (ty:ℂ) • (entry 0 0-entry 1 1) + (ty:ℂ) • (entry 0 0+entry 1 1)))],
    LinearMap.pi ![
      (1/2 : ℂ) • (((1-9*eps : ℝ):ℂ) • (entry 0 1+entry 1 0) +
        (tx:ℂ) • (entry 0 0-entry 1 1) + (tx:ℂ) • (entry 0 0+entry 1 1) +
        Complex.I • (((1-eps : ℝ):ℂ) • (Complex.I • (entry 0 1-entry 1 0)) +
          (ty:ℂ) • (entry 0 0-entry 1 1) + (ty:ℂ) • (entry 0 0+entry 1 1))),
      (1/2 : ℂ) • (entry 0 0 + entry 1 1 -
        ((1-9*eps/5+tz : ℝ):ℂ) • (entry 0 0-entry 1 1) -
        (tz:ℂ) • (entry 0 0+entry 1 1))]]

  f.copy (fun A => !![
    (A 0 0 + A 1 1 + ((1-9*eps/5+tz : ℝ):ℂ)*(A 0 0-A 1 1) + (tz:ℂ)*(A 0 0+A 1 1))/2,
    (((1-9*eps : ℝ):ℂ)*(A 0 1+A 1 0)+(tx:ℂ)*(A 0 0-A 1 1)+(tx:ℂ)*(A 0 0+A 1 1)
      - Complex.I*(((1-eps : ℝ):ℂ)*(Complex.I*(A 0 1-A 1 0))+(ty:ℂ)*(A 0 0-A 1 1)+(ty:ℂ)*(A 0 0+A 1 1)))/2;
    (((1-9*eps : ℝ):ℂ)*(A 0 1+A 1 0)+(tx:ℂ)*(A 0 0-A 1 1)+(tx:ℂ)*(A 0 0+A 1 1)
      + Complex.I*(((1-eps : ℝ):ℂ)*(Complex.I*(A 0 1-A 1 0))+(ty:ℂ)*(A 0 0-A 1 1)+(ty:ℂ)*(A 0 0+A 1 1)))/2,
    (A 0 0 + A 1 1 - ((1-9*eps/5+tz : ℝ):ℂ)*(A 0 0-A 1 1) - (tz:ℂ)*(A 0 0+A 1 1))/2]) (by
      funext A
      symm
      ext i j
      fin_cases i <;> fin_cases j
      · change (1/2 : ℂ) * (A 0 0 + A 1 1 + ((1-9*eps/5+tz : ℝ):ℂ)*(A 0 0-A 1 1) + (tz:ℂ)*(A 0 0+A 1 1)) = (A 0 0 + A 1 1 + ((1-9*eps/5+tz : ℝ):ℂ)*(A 0 0-A 1 1) + (tz:ℂ)*(A 0 0+A 1 1)) / 2
        ring
      · change (1/2 : ℂ) * (((1-9*eps : ℝ):ℂ)*(A 0 1+A 1 0)+(tx:ℂ)*(A 0 0-A 1 1)+(tx:ℂ)*(A 0 0+A 1 1) - Complex.I*(((1-eps : ℝ):ℂ)*(Complex.I*(A 0 1-A 1 0))+(ty:ℂ)*(A 0 0-A 1 1)+(ty:ℂ)*(A 0 0+A 1 1))) = (((1-9*eps : ℝ):ℂ)*(A 0 1+A 1 0)+(tx:ℂ)*(A 0 0-A 1 1)+(tx:ℂ)*(A 0 0+A 1 1) - Complex.I*(((1-eps : ℝ):ℂ)*(Complex.I*(A 0 1-A 1 0))+(ty:ℂ)*(A 0 0-A 1 1)+(ty:ℂ)*(A 0 0+A 1 1))) / 2
        ring
      · change (1/2 : ℂ) * (((1-9*eps : ℝ):ℂ)*(A 0 1+A 1 0)+(tx:ℂ)*(A 0 0-A 1 1)+(tx:ℂ)*(A 0 0+A 1 1) + Complex.I*(((1-eps : ℝ):ℂ)*(Complex.I*(A 0 1-A 1 0))+(ty:ℂ)*(A 0 0-A 1 1)+(ty:ℂ)*(A 0 0+A 1 1))) = (((1-9*eps : ℝ):ℂ)*(A 0 1+A 1 0)+(tx:ℂ)*(A 0 0-A 1 1)+(tx:ℂ)*(A 0 0+A 1 1) + Complex.I*(((1-eps : ℝ):ℂ)*(Complex.I*(A 0 1-A 1 0))+(ty:ℂ)*(A 0 0-A 1 1)+(ty:ℂ)*(A 0 0+A 1 1))) / 2
        ring
      · change (1/2 : ℂ) * (A 0 0 + A 1 1 - ((1-9*eps/5+tz : ℝ):ℂ)*(A 0 0-A 1 1) - (tz:ℂ)*(A 0 0+A 1 1)) = (A 0 0 + A 1 1 - ((1-9*eps/5+tz : ℝ):ℂ)*(A 0 0-A 1 1) - (tz:ℂ)*(A 0 0+A 1 1)) / 2
        ring
      )

private def cw (p : Fin 2 × Fin 2) : ℂ :=
  if p = (0,1) then 2 else if p = (1,0) then 1 else 0

private theorem choi_positive (N : MatrixMap (Fin 2) (Fin 2) ℂ)
    (hN : N.IsCompletelyPositive) :
    Matrix.PosSemidef (fun (p r : Fin 2 × Fin 2) =>
      N (Matrix.single p.2 r.2 1) p.1 r.1) := by
  have h :=
    (D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence.choi_psd_of_cp N hN).submatrix Prod.swap
  have he : ((N.choi_matrix.submatrix Prod.swap Prod.swap).submatrix Prod.swap Prod.swap) =
      (fun (p r : Fin 2 × Fin 2) => N (Matrix.single p.2 r.2 1) p.1 r.1) := by
    ext p r
    rfl
  rw [he] at h
  exact h

private theorem choi_sum (eps tx ty tz : ℝ) :
    (star (fun p : Fin 2 × Fin 2 => qubitZ p.1 p.2) ⬝ᵥ ((fun (p r : Fin 2 × Fin 2) => affine eps tx ty tz (Matrix.single p.2 r.2 1) p.1 r.1) *ᵥ (fun p : Fin 2 × Fin 2 => qubitZ p.1 p.2))).re +
    (star cw ⬝ᵥ ((fun (p r : Fin 2 × Fin 2) => affine eps tx ty tz (Matrix.single p.2 r.2 1) p.1 r.1) *ᵥ cw)).re = -33*eps/10 := by
  simp [dotProduct,mulVec,Fintype.sum_prod_type,Fin.sum_univ_two,qubitZ,cw,
    affine,LinearMap.copy,Matrix.single,Complex.mul_re,Complex.mul_im]
  ring


private theorem choi_eps_nonneg (eps tx ty tz : ℝ)
    (hCP : (affine eps tx ty tz).IsCompletelyPositive) : 0 ≤ eps := by
  have hC := choi_positive _ hCP
  have h1 := (Complex.nonneg_iff.mp (hC.dotProduct_mulVec_nonneg (fun p : Fin 2 × Fin 2 => qubitZ p.1 p.1))).1
  have h2 := (Complex.nonneg_iff.mp (hC.dotProduct_mulVec_nonneg (fun p : Fin 2 × Fin 2 => qubitZ p.2 p.2))).1
  have hs : (star (fun p : Fin 2 × Fin 2 => qubitZ p.1 p.1) ⬝ᵥ ((fun (p r : Fin 2 × Fin 2) => affine eps tx ty tz (Matrix.single p.2 r.2 1) p.1 r.1) *ᵥ (fun p : Fin 2 × Fin 2 => qubitZ p.1 p.1))).re +
      (star (fun p : Fin 2 × Fin 2 => qubitZ p.2 p.2) ⬝ᵥ ((fun (p r : Fin 2 × Fin 2) => affine eps tx ty tz (Matrix.single p.2 r.2 1) p.1 r.1) *ᵥ (fun p : Fin 2 × Fin 2 => qubitZ p.2 p.2))).re = 36*eps := by
    simp [dotProduct,mulVec,Fintype.sum_prod_type,Fin.sum_univ_two,qubitZ,
      affine,LinearMap.copy,Matrix.single,Complex.mul_re,Complex.mul_im]
    ring
  linarith

private theorem choi_identity (eps tx ty tz : ℝ)
    (hCP : (affine eps tx ty tz).IsCompletelyPositive) :
    affine eps tx ty tz = LinearMap.id := by
  have heps := choi_eps_nonneg eps tx ty tz hCP
  have hC := choi_positive _ hCP
  have hv := (Complex.nonneg_iff.mp (hC.dotProduct_mulVec_nonneg (fun p : Fin 2 × Fin 2 => qubitZ p.1 p.2))).1
  have hw := (Complex.nonneg_iff.mp (hC.dotProduct_mulVec_nonneg cw)).1
  have hs := choi_sum eps tx ty tz
  have he : eps = 0 := by linarith
  subst eps
  have hvz : (star (fun p : Fin 2 × Fin 2 => qubitZ p.1 p.2) ⬝ᵥ ((fun (p r : Fin 2 × Fin 2) => affine 0 tx ty tz (Matrix.single p.2 r.2 1) p.1 r.1) *ᵥ (fun p : Fin 2 × Fin 2 => qubitZ p.1 p.2))).re = tz := by
    simp [dotProduct,mulVec,Fintype.sum_prod_type,Fin.sum_univ_two,qubitZ,
      affine,LinearMap.copy,Matrix.single]
    ring
  have hd := (Complex.nonneg_iff.mp (hC.diag_nonneg (i := (1,0)))).1
  have hdz : ((fun (p r : Fin 2 × Fin 2) => affine 0 tx ty tz (Matrix.single p.2 r.2 1) p.1 r.1) (1,0) (1,0)).re = -tz := by
    simp [affine,LinearMap.copy,Matrix.single]
    ring
  rw [hvz] at hv
  rw [hdz] at hd
  have ht : tz = 0 := by linarith
  subst tz
  let z : Fin 2 × Fin 2 → ℂ := Pi.single (1,0) 1
  have hz : star z ⬝ᵥ ((fun (p r : Fin 2 × Fin 2) => affine 0 tx ty 0 (Matrix.single p.2 r.2 1) p.1 r.1) *ᵥ z) = 0 := by
    simp [z,dotProduct,mulVec,Fintype.sum_prod_type,Fin.sum_univ_two,
      affine,LinearMap.copy,Matrix.single]
  have hk := (hC.dotProduct_mulVec_zero_iff (x := z)).mp hz
  have hxy := congrFun hk (0,0)
  simp [z,mulVec,affine,LinearMap.copy,Matrix.single] at hxy
  have hx := congrArg Complex.re hxy
  have hy := congrArg Complex.im hxy
  simp [Complex.mul_re,Complex.mul_im] at hx hy
  subst tx
  subst ty
  ext A i j
  fin_cases i <;> fin_cases j <;> simp [affine,LinearMap.copy]
  all_goals try ring
  all_goals simp
  all_goals ring


private def direction (i : Fin 4) (k : Fin 2) : Fin 2 → ℂ :=
  if k = 0 then u i else Complex.I • u i

private def tangent (i : Fin 4) (k : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ := (1/20 : ℂ) •
  (vecMulVec (v i) (star (direction i k)) + vecMulVec (direction i k) (star (v i)))
private def curvature (i : Fin 4) (k : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1/20 : ℂ) • vecMulVec (direction i k) (star (direction i k))
private def dc : Fin 4 → Fin 2 → Fin 4 → ℝ :=
  ![![![(23/24),(-41/24),(3/8),(3/8)],![0,0,(-5/3),(5/3)]],![![(41/24),(-23/24),(-3/8),(-3/8)],![0,0,(-5/3),(5/3)]],![![(-5/3),(5/3),0,0],![(-3/8),(-3/8),(-23/24),(41/24)]],![![(-5/3),(5/3),0,0],![(3/8),(3/8),(-41/24),(23/24)]]]
private def ec (i : Fin 4) : Fin 4 → ℝ := fun j => 1/2 - if j = i then 1 else 0

private theorem tangent_expansion (i : Fin 4) (k : Fin 2) : ∑ j, dc i k j • M j = tangent i k := by
  fin_cases i <;> fin_cases k <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [dc,tangent,direction,M,Q,u,v,vecMulVec,Fin.sum_univ_succ,
      Complex.real_smul,Complex.ext_iff]

private theorem curvature_expansion (i : Fin 4) (k : Fin 2) : ∑ j, ec i j • M j = curvature i k := by
  have hs : ∑ j, ec i j • M j = (1/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - M i := by
    simp only [ec,sub_smul,Finset.sum_sub_distrib,← Finset.smul_sum,
      measurement_valid.2,ite_smul,one_smul,zero_smul,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [hs]
  fin_cases i <;> fin_cases k <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [curvature,direction,M,Q,u,v,vecMulVec,Complex.real_smul,Complex.ext_iff]

private theorem curve_positive (i : Fin 4) (k : Fin 2) (t : ℝ) :
    (M i + t • tangent i k + t^2 • curvature i k).PosSemidef := by
  have he : M i + t • tangent i k + t^2 • curvature i k =
      (1/20 : ℂ) • vecMulVec (v i + (t:ℂ) • direction i k)
        (star (v i + (t:ℂ) • direction i k)) := by
    ext a b
    simp [M,Q,tangent,curvature,vecMulVec,Complex.real_smul]
    ring
  rw [he]
  exact (posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.nonneg_iff])

private def channel_tx (N : MatrixMap (Fin 2) (Fin 2) ℂ) : ℝ :=
  81/86*((N (rho 0)) 0 1).re+81/86*((N (rho 1)) 0 1).re+
  5/86*((N (rho 2)) 0 1).re+5/86*((N (rho 3)) 0 1).re
private def channel_ty (N : MatrixMap (Fin 2) (Fin 2) ℂ) : ℝ :=
  -(81/86*((N (rho 0)) 0 1).im+81/86*((N (rho 1)) 0 1).im+
  5/86*((N (rho 2)) 0 1).im+5/86*((N (rho 3)) 0 1).im)
private def channel_tz (N : MatrixMap (Fin 2) (Fin 2) ℂ) : ℝ :=
  81/86*((N (rho 0)) 0 0).re+81/86*((N (rho 1)) 0 0).re+
  5/86*((N (rho 2)) 0 0).re+5/86*((N (rho 3)) 0 0).re-1
private def channel_eps (N : MatrixMap (Fin 2) (Fin 2) ℂ) : ℝ :=
  1-50/27*(((N (rho 2)) 0 1).im-((N (rho 3)) 0 1).im)

private theorem stationarity_constraints (N : MatrixMap (Fin 2) (Fin 2) ℂ)
    (hopt : IsOptimalPOVM q (fun i => N (rho i)) M) (i : Fin 4) (k : Fin 2) :
    (trace (((q i:ℂ) • N (rho i)) * tangent i k)).re =
      ∑ j, dc i k j * (trace (((q j:ℂ) • N (rho j)) * M j)).re := by
  apply quadratic_stationarity (fun j => (q j:ℂ) • N (rho j)) M i measurement_valid
    _ (tangent i k) (curvature i k) (dc i k) (ec i)
    (tangent_expansion i k) (curvature_expansion i k) (curve_positive i k)
  intro F hF
  simpa only [smul_mul_assoc,trace_smul,smul_eq_mul,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hopt.2 F hF


private def g (x y z : Fin 4 → ℝ) : Fin 4 → Fin 2 → ℝ :=
  ![![(3/560) + (-369/2240) * y 0 + (-123/560) * x 1 + (-9/448) * z 2 + (-3/112) * x 2 + (-3/112) * x 3 + (9/448) * z 3 + (177/560) * x 0 + (369/2240) * y 1,(-9/28) * z 0 + (-5/42) * x 3 + (5/42) * x 2 + (5/56) * z 2 + (5/56) * z 3],![(-3/560) + (-369/2240) * y 1 + (-177/560) * x 1 + (-9/448) * z 3 + (3/112) * x 2 + (3/112) * x 3 + (9/448) * z 2 + (123/560) * x 0 + (369/2240) * y 0,(-9/28) * z 1 + (-5/42) * x 3 + (5/42) * x 2 + (5/56) * z 2 + (5/56) * z 3],![(-9/56) * y 0 + (-9/56) * y 1 + (-3/14) * x 0 + (3/14) * x 1 + (5/28) * y 2,(27/560) + (-81/2240) * y 0 + (-41/336) * x 3 + (-41/448) * z 2 + (-27/560) * x 0 + (-27/560) * x 1 + (41/448) * z 3 + (59/336) * x 2 + (81/2240) * y 1],![(-9/56) * y 0 + (-9/56) * y 1 + (-3/14) * x 0 + (3/14) * x 1 + (5/28) * y 3,(-27/560) + (-81/2240) * y 1 + (-59/336) * x 3 + (-41/448) * z 3 + (27/560) * x 0 + (27/560) * x 1 + (41/336) * x 2 + (41/448) * z 2 + (81/2240) * y 0]]
private theorem coordinate_stationarity (x y z : Fin 4 → ℝ)
    (h : ∀ i k, (trace (((q i:ℂ) • (blochMatrix 1 (WithLp.toLp 2 ![2 * y i, -2 * z i, 2 * x i - 1]))) * tangent i k)).re =
      ∑ j, dc i k j *
        (trace (((q j:ℂ) • (blochMatrix 1 (WithLp.toLp 2 ![2 * y j, -2 * z j, 2 * x j - 1]))) * M j)).re) :
    ∀ i k, g x y z i k = 0 := by
  intro i k
  have hi := h i k
  fin_cases i <;> fin_cases k <;>
    norm_num [Matrix.smul_apply,Matrix.vecHead,Matrix.vecTail,q,blochMatrix,dc,tangent,direction,M,Q,u,v,trace,mul_apply,
      Fin.sum_univ_succ,Fin.sum_univ_two,vecMulVec,Complex.real_smul,
      Complex.mul_re,Complex.mul_im,Complex.conj_ofNat,Fin.succ] at hi <;>
    norm_num [g,Matrix.vecHead,Matrix.vecTail,Fin.succ] <;>
    linear_combination (norm := skip) hi <;> ring_nf <;> simp <;> ring

private theorem images_affine (N : MatrixMap (Fin 2) (Fin 2) ℂ) (hN : IsCPTP N)
    (hopt : IsOptimalPOVM q (fun i => N (rho i)) M) :
    ∀ i, N (rho i) = affine (channel_eps N) (channel_tx N) (channel_ty N) (channel_tz N) (rho i) := by
  let x : Fin 4 → ℝ := fun i => ((N (rho i)) 0 0).re
  let y : Fin 4 → ℝ := fun i => ((N (rho i)) 0 1).re
  let z : Fin 4 → ℝ := fun i => ((N (rho i)) 0 1).im
  have ho (i : Fin 4) : N (rho i) = (blochMatrix 1 (WithLp.toLp 2 ![2 * y i, -2 * z i, 2 * x i - 1])) :=
    D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.Pauli.density_coordinates _
      (hN.1.IsPositive (states_valid i).1).isHermitian
      (by rw [hN.2]; exact (states_valid i).2)
  have hc : ∀ i k, g x y z i k = 0 := by
    apply coordinate_stationarity
    intro i k
    have h := stationarity_constraints N hopt i k
    simpa only [ho] using h
  have h00 := hc 0 0
  change (3/560) + (-369/2240) * y 0 + (-123/560) * x 1 + (-9/448) * z 2 + (-3/112) * x 2 + (-3/112) * x 3 + (9/448) * z 3 + (177/560) * x 0 + (369/2240) * y 1 = 0 at h00
  have h01 := hc 0 1
  change (-9/28) * z 0 + (-5/42) * x 3 + (5/42) * x 2 + (5/56) * z 2 + (5/56) * z 3 = 0 at h01
  have h10 := hc 1 0
  change (-3/560) + (-369/2240) * y 1 + (-177/560) * x 1 + (-9/448) * z 3 + (3/112) * x 2 + (3/112) * x 3 + (9/448) * z 2 + (123/560) * x 0 + (369/2240) * y 0 = 0 at h10
  have h11 := hc 1 1
  change (-9/28) * z 1 + (-5/42) * x 3 + (5/42) * x 2 + (5/56) * z 2 + (5/56) * z 3 = 0 at h11
  have h20 := hc 2 0
  change (-9/56) * y 0 + (-9/56) * y 1 + (-3/14) * x 0 + (3/14) * x 1 + (5/28) * y 2 = 0 at h20
  have h21 := hc 2 1
  change (27/560) + (-81/2240) * y 0 + (-41/336) * x 3 + (-41/448) * z 2 + (-27/560) * x 0 + (-27/560) * x 1 + (41/448) * z 3 + (59/336) * x 2 + (81/2240) * y 1 = 0 at h21
  have h30 := hc 3 0
  change (-9/56) * y 0 + (-9/56) * y 1 + (-3/14) * x 0 + (3/14) * x 1 + (5/28) * y 3 = 0 at h30
  have h31 := hc 3 1
  change (-27/560) + (-81/2240) * y 1 + (-59/336) * x 3 + (-41/448) * z 3 + (27/560) * x 0 + (27/560) * x 1 + (41/336) * x 2 + (41/448) * z 2 + (81/2240) * y 0 = 0 at h31
  intro i
  rw [ho]
  change (blochMatrix 1 (WithLp.toLp 2 ![2 * y i, -2 * z i, 2 * x i - 1])) =
    affine (1-50/27*(z 2-z 3))
      (81/86*y 0+81/86*y 1+5/86*y 2+5/86*y 3)
      (-(81/86*z 0+81/86*z 1+5/86*z 2+5/86*z 3))
      (81/86*x 0+81/86*x 1+5/86*x 2+5/86*x 3-1) (rho i)
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> apply Complex.ext
  all_goals norm_num [Matrix.cons_val_two, PiLp.toLp_apply, Matrix.vecHead, Matrix.vecTail,
    Fin.succ, blochMatrix, affine,LinearMap.copy, rho, P, Q, u, v, a, vecMulVec, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.conj_ofNat]
  all_goals ring_nf
  all_goals try simp
  all_goals linarith only [h00,h01,h10,h11,h20,h21,h30,h31]


private def basis_coeff (A : Matrix (Fin 2) (Fin 2) ℂ) : Fin 4 → ℂ :=
  ![((-63/344) : ℂ) * A 0 0 + (-15 : ℂ) * A 0 1 + (-15 : ℂ) * A 1 0 + ((9/8) : ℂ) * A 1 1,((-63/344) : ℂ) * A 0 0 + (15 : ℂ) * A 0 1 + (15 : ℂ) * A 1 0 + ((9/8) : ℂ) * A 1 1,((235/344) : ℂ) * A 0 0 + (((-25/27) * Complex.I) : ℂ) * A 0 1 + (((25/27) * Complex.I) : ℂ) * A 1 0 + ((-5/8) : ℂ) * A 1 1,((235/344) : ℂ) * A 0 0 + (((25/27) * Complex.I) : ℂ) * A 0 1 + (((-25/27) * Complex.I) : ℂ) * A 1 0 + ((-5/8) : ℂ) * A 1 1]

private theorem rho_spanning (A : Matrix (Fin 2) (Fin 2) ℂ) : A = ∑ i, basis_coeff A i • rho i := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [basis_coeff,rho,P,Q,u,v,a,vecMulVec,Complex.real_smul,
      Complex.conj_ofNat,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]
  all_goals ring

private theorem channel_affine (N : MatrixMap (Fin 2) (Fin 2) ℂ) (hN : IsCPTP N)
    (hopt : IsOptimalPOVM q (fun i => N (rho i)) M) :
    N = affine (channel_eps N) (channel_tx N) (channel_ty N) (channel_tz N) := by
  have he := images_affine N hN hopt
  apply LinearMap.ext
  intro A
  rw [rho_spanning A]
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [he]

private theorem isolated : IsIsolated q rho := by
  intro N hN hOMP
  obtain ⟨F,hF,hout⟩ := hOMP
  have hFM := unique_optimal F hF
  subst F
  have he := channel_affine N hN hout
  have hc : (affine (channel_eps N) (channel_tx N) (channel_ty N) (channel_tz N)).IsCompletelyPositive := by
    rw [← he]
    exact hN.1
  exact he.trans (choi_identity _ _ _ _ hc)

theorem result : ¬ claim := by
  intro h
  exact (h 4 q rho priors_valid.1 priors_valid.2 states_valid) isolated

end D5.S3.Quantum.Measurement.IsolatedQubitEnsemble
