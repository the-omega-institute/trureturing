/- GID: D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/MixedStateInverseSumsetRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.claim; result=D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.result; claim=D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.claim
   digest: A two-level qudit state refutes the mixed-state inverse sumset bound. -/

import D5.S3.Observer.MatrixUnitCertificate
import D5.S3.Quantum.Divergence.GibbsVariationalIdentity
import D5.S3.Quantum.Subentropy.StrongSubadditivityRefutation
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity

/-! The single-qudit reading of Bu--Gu--Jaffe, arXiv:2401.14385v3,
Remark 45, equation (58), with its positive-denominator hypotheses.
The certified instance is the equal mixture of levels zero and one in dimension seven. -/

set_option autoImplicit false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix Finset
open scoped ComplexOrder MatrixOrder BigOperators Kronecker
open scoped Matrix.Norms.L2Operator
open D5.S3.Observer.WindowRegister
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.GibbsVariationalIdentity
open D5.S3.Quantum.Subentropy.StrongSubadditivityRefutation (diagonalState)
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics

namespace D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation

/-- The source's odd-dimensional Weyl operator, with the clock preceding the shift. -/
def weyl (d : ℕ) [NeZero d] (p q : ZMod d) : Matrix (ZMod d) (ZMod d) ℂ :=
  (windowRoot d ^ ((d + 1) / 2)) ^ (- (p * q)).val •
    (clockMatrix d ^ p.val * shiftMatrix d ^ q.val)

/-- The characteristic function uses the negative Weyl argument. -/
def charFun {d : ℕ} [NeZero d] (ρ : Matrix (ZMod d) (ZMod d) ℂ)
    (x : ZMod d × ZMod d) : ℂ := trace (ρ * weyl d (-x.1) (-x.2))

/-- Weyl orthogonality reconstructs the operator whose characteristic function retains
exactly the coefficients of modulus one, as in the source's mean state. -/
def meanState {d : ℕ} [NeZero d] (ρ : Matrix (ZMod d) (ZMod d) ℂ) :
    Matrix (ZMod d) (ZMod d) ℂ :=
  (d : ℂ)⁻¹ • ∑ x ∈ univ.filter (fun x => ‖charFun ρ x‖ = 1),
    charFun ρ x • weyl d x.1 x.2

/-- Rank of the mean state. -/
def meanRank {d : ℕ} [NeZero d] (ρ : Matrix (ZMod d) (ZMod d) ℂ) : ℕ :=
  (meanState ρ).rank

/-- The source's magic gap, including its empty-set convention. -/
def magicGap {d : ℕ} [NeZero d] (ρ : Matrix (ZMod d) (ZMod d) ℂ) : ℝ :=
  let a := univ.filter (fun x => charFun ρ x ≠ 0 ∧ ‖charFun ρ x‖ ≠ 1)
  if h : a.Nonempty then 1 - a.sup' h (fun x => ‖charFun ρ x‖) else 0

/-- The factor denoted lambda in equation (58). -/
def gapFactor {d : ℕ} [NeZero d] (ρ : Matrix (ZMod d) (ZMod d) ℂ) : ℝ :=
  (1 - magicGap ρ) ^ 2

/-- Purity is the real trace of the square. -/
def purity {d : ℕ} [NeZero d] (ρ : Matrix (ZMod d) (ZMod d) ℂ) : ℝ :=
  (trace (ρ * ρ)).re

/-- Conjugation by the source's linear permutation followed by the right partial trace.
For admissible parameters the matrix in this formula is the unitary U of the source. -/
def convolution {d : ℕ} [NeZero d] (s t : ZMod d)
    (ρ σ : Matrix (ZMod d) (ZMod d) ℂ) : Matrix (ZMod d) (ZMod d) ℂ :=
  let u : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ :=
    fun a b => if a = (s * b.1 + t * b.2, -t * b.1 + s * b.2) then 1 else 0
  partialTraceRight (u * (ρ ⊗ₖ σ) * uᴴ)

/-- The mixed-state expectation (58) on its stated positive-denominator domain. -/
def claim : Prop :=
  ∀ (d : ℕ) [NeZero d], d.Prime → ∀ (s t : ZMod d),
    s ≠ 0 → t ≠ 0 → s ^ 2 + t ^ 2 = 1 →
    ∀ (ρ σ τ : DensityState (ZMod d)) (c : ℝ),
      σ.1 = CStarMatrix.ofMatrix (meanState ρ.1) →
      τ.1 = CStarMatrix.ofMatrix (convolution s t ρ.1 ρ.1) →
      let δ := Real.exp (vonNeumannEntropy τ - vonNeumannEntropy ρ)
      let r := (meanRank ρ.1 : ℝ)
      let l := gapFactor ρ.1
      1 < δ → δ ≤ c → 0 < 1 + l * (r * purity ρ.1 - 1) →
      0 < Real.log r - Real.log (1 + l * (r * purity ρ.1 - 1)) →
      quantumRelativeEntropy ρ σ ≤
        Real.log r / (Real.log r - Real.log (1 + l * (r * purity ρ.1 - 1))) * Real.log c

private def rhoWeights (i : ZMod 7) : ℝ := if i = 0 ∨ i = 1 then 1 / 2 else 0
private def tauWeights (i : ZMod 7) : ℝ :=
  if i = 0 ∨ i = 4 then 1 / 4 else if i = 2 then 1 / 2 else 0

private def rho : DensityState (ZMod 7) :=
  diagonalState rhoWeights
    (fun i => by delta rhoWeights; split_ifs <;> norm_num)
    (by delta rhoWeights; simp -congrConsts +decide [ZMod, Fin.sum_univ_seven]; norm_num)
private def sigma : DensityState (ZMod 7) :=
  gibbsState 0 (IsSelfAdjoint.zero _)
private def tau : DensityState (ZMod 7) :=
  diagonalState tauWeights
    (fun i => by delta tauWeights; split_ifs <;> norm_num)
    (by delta tauWeights; simp -congrConsts +decide [ZMod, Fin.sum_univ_seven]; norm_num)

private lemma convolution_eq : convolution (2 : ZMod 7) 2 rho.1 rho.1 = tau.1 := by
  let u : Matrix (ZMod 7 × ZMod 7) (ZMod 7 × ZMod 7) ℂ := fun a b =>
    if a = (2 * b.1 + 2 * b.2, -2 * b.1 + 2 * b.2) then 1 else 0
  change partialTraceRight
    (u *
      ((diagonal fun i => (rhoWeights i : ℂ)) ⊗ₖ
        (diagonal fun i => (rhoWeights i : ℂ))) * uᴴ) =
    diagonal (fun i => (tauWeights i : ℂ))
  rw [diagonal_kronecker_diagonal]
  ext a c
  delta rhoWeights tauWeights
  simp -congrConsts +decide [partialTraceRight, Matrix.mul_apply,
    conjTranspose_apply, Fintype.sum_prod_type, ZMod, Fin.sum_univ_seven,
    diagonal_apply, u]
  fin_cases a <;> fin_cases c <;>
    norm_num [← (ZMod.val_injective 7).eq_iff, ZMod.val_add, ZMod.val_ofNat,
      ZMod.val_zero, ZMod.val_one_eq_one_mod, ZMod.val]

private lemma rho_entropy : vonNeumannEntropy rho = Real.log 2 := by
  convert (von_neumann_entropy_basisPinchingState rho) using 1
  · congr 1
    apply Subtype.ext
    change CStarMatrix.ofMatrix (diagonal fun i => (rhoWeights i : ℂ)) =
      CStarMatrix.ofMatrix (diagonal (Matrix.diag (diagonal fun i => (rhoWeights i : ℂ))))
    rw [Matrix.diag_diagonal]
  · change Real.log 2 = -(∑ i : ZMod 7, rhoWeights i * Real.log (rhoWeights i))
    delta rhoWeights
    simp -congrConsts +decide [ZMod, Fin.sum_univ_seven]
    ring

private lemma tau_entropy : vonNeumannEntropy tau = 3 / 2 * Real.log 2 := by
  convert (von_neumann_entropy_basisPinchingState tau) using 1
  · congr 1
    apply Subtype.ext
    change CStarMatrix.ofMatrix (diagonal fun i => (tauWeights i : ℂ)) =
      CStarMatrix.ofMatrix (diagonal (Matrix.diag (diagonal fun i => (tauWeights i : ℂ))))
    rw [Matrix.diag_diagonal]
  · change 3 / 2 * Real.log 2 = -(∑ i : ZMod 7, tauWeights i * Real.log (tauWeights i))
    delta tauWeights
    simp -congrConsts +decide [ZMod, Fin.sum_univ_seven]
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]
    ring

private lemma weyl_diagonal (p q i : ZMod 7) :
    weyl 7 p q i i = if q = 0 then windowRoot 7 ^ (i.val * p.val) else 0 := by
  delta weyl
  simp -congrConsts only [clockMatrix, diagonal_pow, Matrix.smul_apply, diagonal_mul,
    Pi.pow_apply, D5.S3.Observer.MatrixUnitCertificate.shift_matrix_pow_apply,
    ZMod.natCast_zmod_val, sub_self, smul_eq_mul]
  by_cases hq : q = 0
  · subst q
    simp -congrConsts [pow_mul]
  · simp -congrConsts [hq, Ne.symm hq]

private lemma characteristic_off_axis (p q : ZMod 7) (hq : q ≠ 0) :
    charFun rho.1 (p, q) = 0 := by
  change trace ((diagonal fun i => (rhoWeights i : ℂ)) * weyl 7 (-p) (-q)) = 0
  simp -congrConsts [trace, diagonal_mul, weyl_diagonal, hq]

private lemma characteristic_axis (p : ZMod 7) :
    charFun rho.1 (p, 0) = (1 + windowRoot 7 ^ (-p).val) / 2 := by
  change trace ((diagonal fun i => (rhoWeights i : ℂ)) * weyl 7 (-p) (-(0 : ZMod 7))) = _
  delta rhoWeights
  simp -congrConsts +decide [trace, diagonal_mul, weyl_diagonal, ZMod, Fin.sum_univ_seven,
    show (1 : ZMod 7).val = 1 from rfl]
  ring

private lemma characteristic_norm_one (x : ZMod 7 × ZMod 7) :
    ‖charFun rho.1 x‖ = 1 ↔ x = (0, 0) := by
  rcases x with ⟨p, q⟩
  by_cases hq : q = 0
  · subst q
    rw [characteristic_axis]
    have hz : ‖windowRoot 7 ^ (-p).val‖ = 1 := by
      rw [norm_pow, (windowRoot_isPrimitiveRoot 7).norm'_eq_one (by decide), one_pow]
    constructor
    · intro h
      have he : ‖(1 : ℂ) + windowRoot 7 ^ (-p).val‖ = 2 := by
        rw [norm_div] at h
        norm_num at h
        linarith
      have heq := norm_add_eq_iff_real.mp
        (show ‖(1 : ℂ) + windowRoot 7 ^ (-p).val‖ = ‖(1 : ℂ)‖ +
          ‖windowRoot 7 ^ (-p).val‖ by rw [norm_one, hz]; norm_num; exact he)
      have heqone : windowRoot 7 ^ (-p).val = 1 := by simpa -congrConsts [hz] using heq.symm
      have hval := (windowRoot_isPrimitiveRoot 7).pow_inj (ZMod.val_lt (-p))
        (by norm_num : 0 < 7) (by simpa -congrConsts using heqone)
      have hp : p = 0 := neg_eq_zero.mp ((ZMod.val_eq_zero (-p)).mp hval)
      simp -congrConsts [hp]
    · intro hp
      have hpzero : p = 0 := congrArg Prod.fst hp
      simp -congrConsts [hpzero]
  · simp -congrConsts [characteristic_off_axis p q hq, hq]

private lemma characteristic_bound (x : ZMod 7 × ZMod 7) :
    ‖charFun rho.1 x‖ ≤ 1 := by
  rcases x with ⟨p, q⟩
  by_cases hq : q = 0
  · subst q
    rw [characteristic_axis, norm_div]
    have hz : ‖windowRoot 7 ^ (-p).val‖ = 1 := by
      rw [norm_pow, (windowRoot_isPrimitiveRoot 7).norm'_eq_one (by decide), one_pow]
    have ht := norm_add_le (1 : ℂ) (windowRoot 7 ^ (-p).val)
    norm_num [hz] at ht ⊢
    linarith
  · simp -congrConsts [characteristic_off_axis p q hq]

private lemma mean_eq : meanState rho.1 = sigma.1 := by
  rw [sigma, gibbs_state_zero]
  norm_num -congrConsts only [ZMod.card, Nat.cast_ofNat]
  change meanState rho.1 = (1 / 7 : ℝ) • (1 : Matrix (ZMod 7) (ZMod 7) ℂ)
  delta meanState
  have hf : univ.filter (fun x => ‖charFun rho.1 x‖ = 1) = {(0, 0)} := by
    ext x
    simp -congrConsts only [mem_filter, mem_univ, true_and, characteristic_norm_one, mem_singleton]
  rw [hf, sum_singleton, characteristic_axis]
  delta weyl
  norm_num -congrConsts [Matrix.smul_apply, Complex.real_smul]
  ext i j
  norm_num -congrConsts [Matrix.smul_apply, Complex.real_smul]
private lemma rank_eq : meanRank rho.1 = 7 := by
  change (meanState rho.1).rank = 7
  rw [mean_eq, sigma, gibbs_state_zero]
  norm_num -congrConsts only [ZMod.card, Nat.cast_ofNat]
  change ((1 / 7 : ℝ) • (1 : Matrix (ZMod 7) (ZMod 7) ℂ)).rank = 7
  rw [← diagonal_one, ← diagonal_smul, rank_diagonal]
  simp -congrConsts

private lemma gap_bounds : 0 ≤ gapFactor rho.1 ∧ gapFactor rho.1 ≤ 1 := by
  classical
  delta gapFactor magicGap
  simp -congrConsts only
  by_cases h : (univ.filter (fun x : ZMod 7 × ZMod 7 =>
    charFun rho.1 x ≠ 0 ∧ ‖charFun rho.1 x‖ ≠ 1)).Nonempty
  · rw [dif_pos h]
    have hu := Finset.sup'_le h (fun x => ‖charFun rho.1 x‖)
      (fun x _ => characteristic_bound x)
    obtain ⟨x, hx⟩ := h
    have hl := (norm_nonneg (charFun rho.1 x)).trans
      (Finset.le_sup' (fun x => ‖charFun rho.1 x‖) hx)
    constructor
    · positivity
    · nlinarith
  · rw [dif_neg h]
    norm_num

private lemma purity_eq : purity rho.1 = 1 / 2 := by
  change (trace ((diagonal fun i => (rhoWeights i : ℂ)) *
    (diagonal fun i => (rhoWeights i : ℂ)))).re = _
  delta rhoWeights
  simp -congrConsts +decide [diagonal_mul_diagonal, trace_diagonal, ZMod, Fin.sum_univ_seven]
  norm_num
private lemma divergence_eq : quantumRelativeEntropy rho sigma = Real.log 7 - Real.log 2 := by
  have h := entropy_uniform_identity rho
  change vonNeumannEntropy rho + quantumRelativeEntropy rho sigma = Real.log 7 at h
  rw [rho_entropy] at h
  linarith

private lemma doubling_eq :
    Real.exp (vonNeumannEntropy tau - vonNeumannEntropy rho) =
      Real.exp (1 / 2 * Real.log 2) := by
  rw [rho_entropy, tau_entropy]
  congr 1
  ring

private lemma doubling_gt_one : 1 < Real.exp (1 / 2 * Real.log 2) := by
  apply Real.one_lt_exp_iff.mpr
  positivity

private lemma numerical_bound (l : ℝ) (hl : 0 ≤ l ∧ l ≤ 1) :
    0 < 1 + l * (7 * (1 / 2) - 1) ∧
    0 < Real.log 7 - Real.log (1 + l * (7 * (1 / 2) - 1)) ∧
    Real.log 7 / (Real.log 7 - Real.log (1 + l * (7 * (1 / 2) - 1))) *
      Real.log (Real.exp (1 / 2 * Real.log 2)) ≤ 1 / 2 * Real.log 7 := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hseven : 0 < Real.log 7 := Real.log_pos (by norm_num)
  have hlo : 1 ≤ 1 + l * (7 * (1 / 2) - 1) := by nlinarith [hl.1]
  have hhi : 1 + l * (7 * (1 / 2) - 1) ≤ 7 / 2 := by nlinarith [hl.2]
  have hpos : 0 < 1 + l * (7 * (1 / 2) - 1) := lt_of_lt_of_le zero_lt_one hlo
  have hlog := Real.log_le_log hpos hhi
  rw [Real.log_div (by norm_num : (7 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)] at hlog
  have hden : Real.log 2 ≤ Real.log 7 - Real.log (1 + l * (7 * (1 / 2) - 1)) := by
    linarith
  refine ⟨hpos, htwo.trans_le hden, ?_⟩
  rw [Real.log_exp]
  calc
    _ ≤ (Real.log 7 / Real.log 2) * (1 / 2 * Real.log 2) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hseven.le htwo hden)
        (by positivity)
    _ = 1 / 2 * Real.log 7 := by field_simp

private lemma strict_violation : 1 / 2 * Real.log 7 < Real.log 7 - Real.log 2 := by
  have h : Real.log ((2 : ℝ) ^ 2) < Real.log 7 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at h
  norm_num at h
  linarith

/-- The registered seven-dimensional mixed state violates equation (58). -/
theorem result : ¬ claim := by
  intro h
  have hb := numerical_bound (gapFactor rho.1) gap_bounds
  have hc := h 7 (by decide) 2 2 (by decide) (by decide) (by decide)
    rho sigma tau (Real.exp (1 / 2 * Real.log 2))
    (by exact congrArg CStarMatrix.ofMatrix mean_eq.symm)
    (by exact congrArg CStarMatrix.ofMatrix convolution_eq.symm)
  simp -congrConsts only at hc
  rw [doubling_eq, rank_eq, purity_eq, divergence_eq] at hc
  exact (not_le_of_gt strict_violation) ((hc doubling_gt_one le_rfl hb.1 hb.2.1).trans hb.2.2)

end D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation
