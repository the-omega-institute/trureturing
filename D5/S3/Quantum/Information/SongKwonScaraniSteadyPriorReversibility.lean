/- GID: D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.claim; result=D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.result; claim=D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.claim
   digest: A full-rank steady qutrit prior need not admit fixed-dilation tabletop reversal. -/

/-
result:
  proof_shape: bind-only (finite matrix normalization and diagonal square-root owners)
  escape_witness: none
  admission_basis: open-problem-resolution (#20652; Refuted)
The public result is the designated refutation result (`basis=refutes`) and is exempt from
four-slot escape registration (CLAUDE.md §3.9).
The channel, adjoint, Petz map, tabletop reverse, IsTTR and claim retain the formulas of #20652.
The literal environmental witness remains concrete data; its positivity and normalization
use the existing Fuchs qutrit-state owners.
Only the fixed qutrit instance is proved; no continuous-family assertion is included.
The imported Fuchs state owners have audit tracking at https://github.com/the-omega-institute/trureturing/issues/21365
Direct frozen dependencies:
  F1: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight;
      declaration statement_id: sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77.
  F2: D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation.sqrt_diagonal;
      declaration statement_id: sha256:7964566c3415a28c412eeca11cb928af14297a692bd33e53f741fa02c42ad908.
  F3: D5/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation.rho0_posDef;
      declaration statement_id: sha256:b1d78f3848a05a0bbebd5c6a7f504ff945e577692f88bc9bc2fd4d7fc00d089c.
  F4: D5/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation.rho0_trace;
      declaration statement_id: sha256:693125d6767e9f5632e5d7c9a24d9cc931dbae1924e86d9ac3b99fe0d69dce8e.
  F5: D5/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation.rho0;
      declaration statement_id: sha256:c767d13b06dd16dbab7dee89e809a4979907cd83be5061e462cbb0e23a30c8d9.
All declarations below have proof_shape: bind-only and escape_witness: none.
The dependency and consumer list expands same-module proof helpers:
  channel: dependencies: F1; consumers: petz, claim, stationary, petz_10, petz_21.
  channelAdjoint: dependencies: F1; consumers: petz, adjoint_10, adjoint_21, petz_10, petz_21.
  petz: dependencies: F1; consumers: IsTTR, petz_10, petz_21, not_ttr.
  tabletopReverse: dependencies: F1; consumers: IsTTR, tabletop_10, tabletop_21, not_ttr.
  IsTTR: dependencies: F1; consumers: claim, not_ttr.
  claim: dependencies: F1; consumers: result.
  sigma: dependencies: none; consumers: U, U_unitary, stationary, tabletop_10, tabletop_21, adjoint_10, adjoint_21.
  U: dependencies: none; consumers: U_unitary, stationary, tabletop_10, tabletop_21, adjoint_10, adjoint_21, petz_10, petz_21, not_ttr, result.
  xi: dependencies: none; consumers: xi_psd, xi_trace, stationary, adjoint_10, adjoint_21, petz_10, petz_21, not_ttr, result.
  gamma: dependencies: none; consumers: gamma_pd, gamma_trace, stationary, sqrt_gamma, inv_sqrt_gamma, petz_10, petz_21, not_ttr, result.
  U_unitary: dependencies: none; consumers: result.
  xi_psd: dependencies: F3, F5; consumers: result.
  gamma_pd: dependencies: none; consumers: g_pos, result.
  xi_trace: dependencies: F4; consumers: result.
  gamma_trace: dependencies: none; consumers: result.
  stationary: dependencies: F1; consumers: petz_10, petz_21, result.
  tabletop_10: dependencies: F1; consumers: not_ttr.
  tabletop_21: dependencies: F1; consumers: not_ttr.
  g: dependencies: none; consumers: root, g_pos, root_sq, root_ne, sqrt_gamma, scaled_basis, petz_10, petz_21.
  root: dependencies: none; consumers: root_sq, root_ne, sqrt_gamma, inv_sqrt_gamma, scaled_basis, petz_10, petz_21.
  g_pos: dependencies: none; consumers: root_sq, root_ne, sqrt_gamma.
  root_sq: dependencies: none; consumers: scaled_basis, petz_10, petz_21.
  root_ne: dependencies: none; consumers: inv_sqrt_gamma.
  sqrt_gamma: dependencies: F2; consumers: inv_sqrt_gamma, petz_10, petz_21.
  inv_sqrt_gamma: dependencies: F2; consumers: petz_10, petz_21.
  adjoint_10: dependencies: F1; consumers: petz_10.
  adjoint_21: dependencies: F1; consumers: petz_21.
  scaled_basis: dependencies: none; consumers: petz_10, petz_21.
  petz_10: dependencies: F1, F2; consumers: not_ttr.
  petz_21: dependencies: F1, F2; consumers: not_ttr.
  not_ttr: dependencies: F1, F2; consumers: result.
  result: dependencies: F1, F2, F3, F4, F5; consumers: external open-question settlement #20652.
-/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation
import D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation

/-! Binding conventions for M. Song, H. Kwon and V. Scarani, "Exact and approximate conditions of tabletop
reversibility: when is Petz recovery cost-free?", arXiv:2510.26895v1 (30 October 2025).

* (1): "N(•) = Tr_E[U_SE (• ⊗ ξ_E) U_SE†]". The partial trace over E is the frozen owner
  `PartialTraceMutualInformation.partialTraceRight`.
* Definition 1, (2): "N̂_γ^(P)(•) ≡ √γ N†( (1/√N(γ)) • (1/√N(γ)) ) √γ", with N† the Hilbert–Schmidt adjoint of N. For
  the dilation (1) it is N†(Y) = Tr_E[U†(Y ⊗ 1)U(1 ⊗ ξ)].
* Definition 2, (3)–(4): "N̂_ξ′^(T)(•) ≡ Tr_E[U_SE† (• ⊗ ξ′_E) U_SE]", and N is tabletop time-reversible (TTR) for a prior
  γ "if there exists ξ′ = ξ′_γ such that its Petz recovery map N̂_γ^(P) is given by N̂_γ^(P) = N̂_ξ′^(T)".
* Section V, open question 2: "In all of the examples we considered, a dynamics appears to be tabletop
  time-reversible whenever a prior state is a steady state. We do not have a proof that this is true in general,
  and leave it for a future investigation." -/

namespace D5.S3.Quantum.Information.SongKwonScaraniSteadyPriorReversibility

open Matrix D5.S3.Quantum.Information.PartialTraceMutualInformation
open scoped ComplexOrder MatrixOrder Kronecker

variable {S E : Type} [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E]

/-- (1): the channel `N(X) = Tr_E[U (X ⊗ ξ) U†]`. -/
noncomputable def channel (U : Matrix (S × E) (S × E) ℂ) (ξ : Matrix E E ℂ) (X : Matrix S S ℂ) : Matrix S S ℂ :=
  partialTraceRight (U * (X ⊗ₖ ξ) * Uᴴ)

/-- The Hilbert–Schmidt adjoint of (1): `N†(Y) = Tr_E[U†(Y ⊗ 1)U(1 ⊗ ξ)]`. -/
noncomputable def channelAdjoint (U : Matrix (S × E) (S × E) ℂ) (ξ : Matrix E E ℂ) (Y : Matrix S S ℂ) :
    Matrix S S ℂ :=
  partialTraceRight (Uᴴ * (Y ⊗ₖ (1 : Matrix E E ℂ)) * U * ((1 : Matrix S S ℂ) ⊗ₖ ξ))

/-- Definition 1, (2): the Petz recovery map `√γ N†(N(γ)^{−1/2} • N(γ)^{−1/2}) √γ`. -/
noncomputable def petz (U : Matrix (S × E) (S × E) ℂ) (ξ : Matrix E E ℂ) (γ X : Matrix S S ℂ) : Matrix S S ℂ :=
  CFC.sqrt γ * channelAdjoint U ξ ((CFC.sqrt (channel U ξ γ))⁻¹ * X * (CFC.sqrt (channel U ξ γ))⁻¹) * CFC.sqrt γ

/-- Definition 2, (3): the tabletop reverse map `Tr_E[U†(• ⊗ ξ′)U]`. -/
noncomputable def tabletopReverse (U : Matrix (S × E) (S × E) ℂ) (ξ' : Matrix E E ℂ) (X : Matrix S S ℂ) :
    Matrix S S ℂ :=
  partialTraceRight (Uᴴ * (X ⊗ₖ ξ') * U)

/-- Definition 2, (4): `(U, ξ)` is tabletop time-reversible for the prior `γ`. -/
def IsTTR (U : Matrix (S × E) (S × E) ℂ) (ξ : Matrix E E ℂ) (γ : Matrix S S ℂ) : Prop :=
  ∃ ξ' : Matrix E E ℂ, ξ'.PosSemidef ∧ ξ'.trace = 1 ∧ ∀ X, petz U ξ γ X = tabletopReverse U ξ' X

/-- Section V, open question 2: a dynamics `(U, ξ)` is tabletop time-reversible for every full-rank prior that is a
steady state. -/
def claim : Prop :=
  ∀ (S E : Type) [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E]
    (U : Matrix (S × E) (S × E) ℂ) (ξ : Matrix E E ℂ) (γ : Matrix S S ℂ),
    U ∈ Matrix.unitaryGroup (S × E) ℂ → ξ.PosSemidef → ξ.trace = 1 → γ.PosDef → γ.trace = 1 →
    channel U ξ γ = γ → IsTTR U ξ γ

end D5.S3.Quantum.Information.SongKwonScaraniSteadyPriorReversibility


namespace D5.S3.Quantum.Information.SongKwonScaraniSteadyPriorReversibility
open Matrix D5.S3.Quantum.Information.PartialTraceMutualInformation
open scoped ComplexOrder MatrixOrder Kronecker

private def sigma (x : (Fin 3) × (Fin 3)) : (Fin 3) × (Fin 3) :=
  ![![(1,1), (0,1), (2,0)], ![(2,2), (0,0), (1,2)], ![(0,2), (2,1), (1,0)]] x.1 x.2

private noncomputable def U : Matrix ((Fin 3) × (Fin 3)) ((Fin 3) × (Fin 3)) ℂ := fun r c =>
  if r = sigma c then
    if c = (0,1) ∨ c = (1,2) ∨ c = (2,1) then 1 else -Complex.I
  else 0

private noncomputable def xi : Matrix (Fin 3) (Fin 3) ℂ := diagonal ![1/2, 1/3, 1/6]
private noncomputable def gamma : Matrix (Fin 3) (Fin 3) ℂ := diagonal ![17/44, 13/44, 14/44]

set_option maxHeartbeats 2000000

private theorem U_unitary : U ∈ Matrix.unitaryGroup ((Fin 3) × (Fin 3)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three,
      Matrix.conjTranspose_apply, U, sigma, Matrix.one_apply, Complex.ext_iff]

private theorem xi_psd : xi.PosSemidef := by
  exact (D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation.rho0_posDef).posSemidef

private theorem gamma_pd : gamma.PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num [Complex.le_def]

private theorem xi_trace : xi.trace = 1 := by
  exact D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation.rho0_trace

private theorem gamma_trace : gamma.trace = 1 := by
  norm_num [gamma, Matrix.trace_diagonal, Fin.sum_univ_three]

private theorem stationary : channel U xi gamma = gamma := by
  ext a c
  fin_cases a <;> fin_cases c <;>
    norm_num [channel, partialTraceRight, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_three, Matrix.conjTranspose_apply, Matrix.kronecker_apply,
      U, sigma, xi, gamma, Matrix.diagonal_apply, Complex.ext_iff]

private theorem tabletop_10 (eta : Matrix (Fin 3) (Fin 3) ℂ) :
    tabletopReverse U eta (Matrix.single 0 0 1) 1 1 = eta 0 0 := by
  simp [tabletopReverse, partialTraceRight, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_three, Matrix.conjTranspose_apply,
    U, sigma, Matrix.single_apply, mul_assoc, mul_comm Complex.I]

private theorem tabletop_21 (eta : Matrix (Fin 3) (Fin 3) ℂ) :
    tabletopReverse U eta (Matrix.single 1 1 1) 2 2 = eta 0 0 := by
  simp [tabletopReverse, partialTraceRight, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_three, Matrix.conjTranspose_apply,
    U, sigma, Matrix.single_apply, mul_assoc, mul_comm Complex.I]



private noncomputable def g : (Fin 3) → ℝ := ![17/44, 13/44, 14/44]
private noncomputable def root (i : (Fin 3)) : ℂ := (Real.sqrt (g i) : ℂ)

private theorem g_pos (i : (Fin 3)) : 0 < g i := by
  apply Complex.zero_lt_real.mp
  convert gamma_pd.diag_pos (i := i) using 1
  fin_cases i <;> norm_num [g, gamma, Matrix.diagonal_apply]

private theorem root_sq (i : (Fin 3)) : root i * root i = (g i : ℂ) := by
  simpa only [root, ← Complex.ofReal_mul] using
    congrArg (fun x : ℝ => (x : ℂ)) (Real.mul_self_sqrt (g_pos i).le)

private theorem root_ne (i : (Fin 3)) : root i ≠ 0 := by
  unfold root
  exact_mod_cast (Real.sqrt_pos.mpr (g_pos i)).ne'

private theorem sqrt_gamma : CFC.sqrt gamma = diagonal root := by
  have he : gamma = diagonal (fun i => (g i : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [gamma, g, Matrix.diagonal_apply]
  rw [he]
  exact D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation.sqrt_diagonal
    g (fun i => (g_pos i).le)

private theorem inv_sqrt_gamma : (CFC.sqrt gamma)⁻¹ = diagonal (fun i => (root i)⁻¹) := by
  rw [sqrt_gamma]
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  simp [root_ne]

private theorem adjoint_10 (d : (Fin 3) → ℂ) :
    channelAdjoint U xi (diagonal d) 1 1 = d 0 / 3 + d 1 / 6 + d 2 / 2 := by
  norm_num [channelAdjoint, partialTraceRight, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_three, Matrix.conjTranspose_apply, Matrix.kronecker_apply,
    U, sigma, xi, Matrix.diagonal_apply, Matrix.one_apply, mul_assoc, mul_comm Complex.I]
  ring

private theorem adjoint_21 (d : (Fin 3) → ℂ) :
    channelAdjoint U xi (diagonal d) 2 2 = d 0 / 2 + d 1 / 6 + d 2 / 3 := by
  norm_num [channelAdjoint, partialTraceRight, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_three, Matrix.conjTranspose_apply, Matrix.kronecker_apply,
    U, sigma, xi, Matrix.diagonal_apply, Matrix.one_apply, mul_assoc, mul_comm Complex.I]
  ring

private theorem scaled_basis (k : (Fin 3)) :
    diagonal (fun i => (root i)⁻¹) * Matrix.single k k 1 *
      diagonal (fun i => (root i)⁻¹) =
      diagonal (fun i => if i = k then (g k : ℂ)⁻¹ else 0) := by
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply, Matrix.diagonal_apply]
  by_cases hik : k = i
  · subst i
    by_cases hjk : k = j
    · subst j
      simp only [and_self, ite_true, mul_one]
      rw [← _root_.mul_inv_rev, root_sq]
    · simp [hjk]
  · simp [hik, Ne.symm hik]

private theorem petz_10 : petz U xi gamma (Matrix.single 0 0 1) 1 1 = (13/51 : ℂ) := by
  unfold petz
  rw [stationary, inv_sqrt_gamma, sqrt_gamma, scaled_basis]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, adjoint_10]
  norm_num [g]
  have h := root_sq 1
  norm_num [g] at h
  linear_combination (44 / 51 : ℂ) * h

private theorem petz_21 : petz U xi gamma (Matrix.single 1 1 1) 2 2 = (7/39 : ℂ) := by
  unfold petz
  rw [stationary, inv_sqrt_gamma, sqrt_gamma, scaled_basis]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, adjoint_21]
  norm_num [g]
  have h := root_sq 2
  norm_num [g] at h
  linear_combination (22 / 39 : ℂ) * h

private theorem not_ttr : ¬ IsTTR U xi gamma := by
  rintro ⟨eta, _, _, h⟩
  have h1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 1 1) (h (Matrix.single 0 0 1))
  have h2 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 2 2) (h (Matrix.single 1 1 1))
  rw [petz_10, tabletop_10] at h1
  rw [petz_21, tabletop_21] at h2
  have hh : (13 / 51 : ℂ) = 7 / 39 := h1.trans h2.symm
  norm_num at hh

theorem result : ¬ claim := by
  intro h
  exact not_ttr (h (Fin 3) (Fin 3) U xi gamma U_unitary xi_psd xi_trace gamma_pd gamma_trace stationary)


end D5.S3.Quantum.Information.SongKwonScaraniSteadyPriorReversibility
