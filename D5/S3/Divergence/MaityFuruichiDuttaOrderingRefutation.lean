/- GID: D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation
   generality: I
   mirror-B: D5/B/S3/Divergence/MaityFuruichiDuttaOrderingRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.claim; result=D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.result; claim=D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.claim
   digest: A noncommuting qubit pair reverses the proposed Tsallis bound order. -/

/- admission_basis: open-problem-resolution (#18947; Refuted)
   escape_witness: none.
   Direct frozen dependencies: D5/S3/Quantum/Matrix/TwoPointFunctionalCalculus.two_point_cfc
     (declaration statement_id: sha256:e205c9df9843810ad13e051ec2a3191ca35fa088ca37e29ae941265284390be7).
   The public result is the designated refutation result (`basis=refutes`) and is exempt
   from four-slot escape registration (CLAUDE.md §3.9).
   B1 is the source's name for renyiRZ; the claim uses its identical defining body
   renyiRZ directly, without an additional forwarding definition.
   Per-declaration proof_shape and consumers (escape_witness: none throughout):
     lnr: bind-only (definition); consumers=renyiRZ,B2.
     renyiRZ: bind-only (definition); consumers=claim,B1_gt.
     tsallis: bind-only (definition); consumer=claim.
     B2: bind-only (definition); consumers=claim,B2_lt.
     claim: bind-only (definition); consumer=result.
     rho,sigma,H,K,A,a: bind-only (literal data); consumers=the matrix evaluations below.
     pair_involutions,pair_affine: bind-only; consumer=pair_cfc.
     pair_states: bind-only; consumers=eighth_square,A_nonneg,result.
     pair_cfc: bind-only; consumers=rho_quarter,sigma_quarter,rho_inverse_half.
     quarter_scalars: bind-only; consumers=rho_quarter,sigma_quarter,sandwich_trace.
     rho_quarter,sigma_quarter,eighth_square: bind-only; consumer=sandwich_trace.
     sandwich_trace: bind-only; consumer=B1_gt.
     B1_gt: bind-only; consumer=result.
     rho_inverse_half: bind-only; consumer=sandwich_A.
     sandwich_A: bind-only; consumers=A_nonneg,B2_lt.
     A_nonneg: bind-only; consumers=A_sqrt,B2_lt.
     A_sqrt: bind-only; consumer=B2_lt.
     B2_lt: bind-only; consumer=result.
     result: proof_shape: bind-only; external assertion refuted by exact matrix evaluation.
   After inlining same-module helpers, only pair_cfc and its consumers depend on
   the frozen two_point_cfc declaration; all other dependencies are pinned Mathlib. -/

import D5.S3.Quantum.Matrix.TwoPointFunctionalCalculus
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false

namespace D5.S3.Divergence.MaityFuruichiDuttaOrderingRefutation

open Matrix
open scoped ComplexOrder

/-- Definition 1 of Maity–Furuichi–Dutta, arXiv:2607.01805: the r-logarithm
`ln_r(x) = (x^r − 1)/r` (`r ≠ 0`, `x ≥ 0`). -/
noncomputable def lnr (r x : ℝ) : ℝ := (x ^ r - 1) / r

/-- Definition 2: the r-deformed α-z-Rényi relative entropy
`D^{(r)}_{α,z}(ρ‖σ) = (1/(α−1)) ln_r Tr[(σ^{(1−α)/(2z)} ρ^{α/z} σ^{(1−α)/(2z)})^z]`. -/
noncomputable def renyiRZ {n : ℕ} (α r z : ℝ) (ρ σ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  1 / (α - 1) * lnr r (Matrix.trace (cfc (fun x : ℝ => x ^ z)
    (cfc (fun x : ℝ => x ^ ((1 - α) / (2 * z))) σ * cfc (fun x : ℝ => x ^ (α / z)) ρ *
      cfc (fun x : ℝ => x ^ ((1 - α) / (2 * z))) σ))).re

/-- Eq. (6): the Tsallis relative entropy `D_α(ρ‖σ) = Tr[ρ − ρ^α σ^{1−α}]/(1 − α)`. -/
noncomputable def tsallis {n : ℕ} (α : ℝ) (ρ σ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (Matrix.trace (ρ - cfc (fun x : ℝ => x ^ α) ρ * cfc (fun x : ℝ => x ^ (1 - α)) σ)).re / (1 - α)

/-- Eq. (47): `B₂(ρ‖σ) = −Tr[ρ ln_{1−α}((ρ^{−q/2} σ^q ρ^{−q/2})^{1/q})]`. -/
noncomputable def B2 {n : ℕ} (α q : ℝ) (ρ σ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  -(Matrix.trace (ρ * cfc (fun x : ℝ => lnr (1 - α) x)
    (cfc (fun x : ℝ => x ^ (1 / q))
      (cfc (fun x : ℝ => x ^ (-(q / 2))) ρ * cfc (fun x : ℝ => x ^ q) σ *
        cfc (fun x : ℝ => x ^ (-(q / 2))) ρ)))).re

/-- Eq. (9) (with Section 4, Case 5): "For 0 ≤ α < 1 and q > (1 − α) … We observe that for
non-commutative density operators ρ and σ, D_α(ρ||σ) ≤ B₁(ρ||σ) ≤ B₂(ρ||σ)." Density operators are
taken positive definite (so that `ρ^{−q/2}` and Definition 2's support condition hold), and the
deformation parameters range over Definition 2's domain (`r ≠ 0`, `z > 0`). -/
def claim : Prop :=
  ∀ n : ℕ, ∀ ρ σ : Matrix (Fin n) (Fin n) ℂ,
    ρ.PosDef → ρ.trace = 1 → σ.PosDef → σ.trace = 1 → ρ * σ ≠ σ * ρ →
    ∀ α r z q : ℝ, 0 ≤ α → α < 1 → r ≠ 0 → 0 < z → 1 - α < q →
      tsallis α ρ σ ≤ renyiRZ α r z ρ σ ∧ renyiRZ α r z ρ σ ≤ B2 α q ρ σ

end D5.S3.Divergence.MaityFuruichiDuttaOrderingRefutation
namespace D5.S3.Divergence.MaityFuruichiDuttaOrderingRefutation
open Matrix
open scoped ComplexOrder MatrixOrder
noncomputable section
private def rho : Matrix (Fin 2) (Fin 2) ℂ := !![4/5, 0; 0, 1/5]
private def sigma : Matrix (Fin 2) (Fin 2) ℂ := !![28/125, (6 * Real.sqrt 6 : ℝ) / 125;
  (6 * Real.sqrt 6 : ℝ) / 125, 97/125]
private def H : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
private def K : Matrix (Fin 2) (Fin 2) ℂ := !![-23/25, (4 * Real.sqrt 6 : ℝ) / 25;
  (4 * Real.sqrt 6 : ℝ) / 25, 23/25]

private lemma pair_involutions :
    IsSelfAdjoint H ∧ H * H = 1 ∧ IsSelfAdjoint K ∧ K * K = 1 := by
  have hs : (Real.sqrt 6 : ℂ)^2 = 6 := by
    exact_mod_cast Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · change H.conjTranspose = H
    ext i j; fin_cases i <;> fin_cases j <;> simp [H, Matrix.conjTranspose_apply]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [H, Matrix.mul_apply, Fin.sum_univ_two]
  · change K.conjTranspose = K
    ext i j; fin_cases i <;> fin_cases j <;> simp [K, Matrix.conjTranspose_apply]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [K, Matrix.mul_apply, Fin.sum_univ_two] <;>
      push_cast <;> norm_num <;> ring_nf <;> norm_num [hs, map_ofNat] <;> ring

private lemma pair_affine :
    rho = (1/2 : ℝ) • (1:Matrix (Fin 2) (Fin 2) ℂ) + (3/10 : ℝ) • H ∧
    sigma = (1/2 : ℝ) • (1:Matrix (Fin 2) (Fin 2) ℂ) + (3/10 : ℝ) • K := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [rho, sigma, H, K, Matrix.one_apply, Complex.real_smul] <;> ring

private lemma pair_states : rho.PosDef ∧ rho.trace = 1 ∧
    sigma.PosDef ∧ sigma.trace = 1 ∧ rho * sigma ≠ sigma * rho := by
  have hs : (Real.sqrt 6 : ℂ)^2 = 6 := by
    exact_mod_cast Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  have hr : rho = diagonal ![(4/5:ℂ), 1/5] := by
    exact Matrix.ext_iff_trace_mul_left.mpr (congrFun rfl)
  have hsig : sigma = (1/5:ℝ) • (1:Matrix (Fin 2) (Fin 2) ℂ) + (3/5:ℝ) •
      vecMulVec (![((1/5:ℝ):ℂ), ((2 * Real.sqrt 6 / 5:ℝ):ℂ)] : Fin 2 → ℂ)
        (star (![((1/5:ℝ):ℂ), ((2 * Real.sqrt 6 / 5:ℝ):ℂ)] : Fin 2 → ℂ)) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [sigma, vecMulVec, Pi.star_apply, Matrix.one_apply, Complex.real_smul] <;>
      push_cast <;> norm_num <;> ring_nf <;> norm_num [hs, map_ofNat] <;> ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hr, Matrix.posDef_diagonal_iff]
    intro i; fin_cases i <;> norm_num [Complex.pos_iff]
  · norm_num [rho, Matrix.trace, Fin.sum_univ_two]
  · rw [hsig]
    exact (Matrix.PosDef.one.smul (show (0:ℝ)<1/5 by norm_num)).add_posSemidef
      ((Matrix.posSemidef_vecMulVec_self_star _).smul (show (0:ℝ)≤3/5 by norm_num))
  · norm_num [sigma, Matrix.trace, Fin.sum_univ_two]
  · intro heq
    have he := congrArg (fun A:Matrix (Fin 2) (Fin 2) ℂ => (A 0 1).re) heq
    norm_num [rho, sigma, Matrix.mul_apply, Fin.sum_univ_two] at he
    have hp := Real.sqrt_pos.mpr (show (0:ℝ)<6 by norm_num)
    linarith

private lemma pair_cfc (f : ℝ → ℝ) :
    cfc f rho = ((f (4/5) + f (1/5))/2) • (1:Matrix (Fin 2) (Fin 2) ℂ) +
      ((f (4/5) - f (1/5))/2) • H ∧
    cfc f sigma = ((f (4/5) + f (1/5))/2) • (1:Matrix (Fin 2) (Fin 2) ℂ) +
      ((f (4/5) - f (1/5))/2) • K := by
  constructor
  · rw [pair_affine.1]
    convert QuantumTwoPointFunctionalCalculus.two_point_cfc f (1/2) (3/10) H
      pair_involutions.1 pair_involutions.2.1 using 1 <;> norm_num
  · rw [pair_affine.2]
    convert QuantumTwoPointFunctionalCalculus.two_point_cfc f (1/2) (3/10) K
      pair_involutions.2.2.1 pair_involutions.2.2.2 using 1 <;> norm_num

private def a : ℝ := (1/5 : ℝ) ^ (1/4 : ℝ)
private lemma quarter_scalars :
    a ^ 4 = 1/5 ∧ (4/5:ℝ) ^ (1/4:ℝ) = a * Real.sqrt 2 := by
  constructor
  · simpa [a] using Real.rpow_inv_natCast_pow (show (0:ℝ) ≤ 1/5 by norm_num)
      (show (4:ℕ) ≠ 0 by decide)
  · have hs : Real.sqrt 2 ^ 4 = (4:ℝ) := by
      calc
        Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2)^2 := by ring
        _ = 4 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
    have h4 : (4:ℝ) ^ (1/4:ℝ) = Real.sqrt 2 := by
      nth_rewrite 1 [← hs]
      simpa only [Nat.cast_ofNat, one_div] using Real.pow_rpow_inv_natCast (Real.sqrt_nonneg 2) (show (4:ℕ) ≠ 0 by decide)
    rw [show (4/5:ℝ) = 4 * (1/5) by norm_num,
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (by norm_num : (0:ℝ) ≤ 1/5), h4]
    dsimp [a]
    ring

private lemma rho_quarter : cfc (fun x:ℝ => x^(1/4:ℝ)) rho =
    !![((a * Real.sqrt 2 : ℝ) : ℂ), 0; 0, (a:ℂ)] := by
  rw [(pair_cfc _).1, quarter_scalars.2]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [H, Matrix.one_apply, Complex.real_smul, a] <;> push_cast <;> ring

private lemma sigma_quarter : cfc (fun x:ℝ => x^(1/4:ℝ)) sigma =
    !![((a * (24 + Real.sqrt 2) / 25 : ℝ) : ℂ),
      ((2 * a * Real.sqrt 6 * (Real.sqrt 2 - 1) / 25 : ℝ) : ℂ);
      ((2 * a * Real.sqrt 6 * (Real.sqrt 2 - 1) / 25 : ℝ) : ℂ),
      ((a * (1 + 24 * Real.sqrt 2) / 25 : ℝ) : ℂ)] := by
  rw [(pair_cfc _).2, quarter_scalars.2]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [K, Matrix.one_apply, Complex.real_smul, a] <;> push_cast <;> ring

private lemma eighth_square :
    cfc (fun x:ℝ => x^(1/8:ℝ)) sigma * cfc (fun x:ℝ => x^(1/8:ℝ)) sigma =
      cfc (fun x:ℝ => x^(1/4:ℝ)) sigma := by
  rw [← cfc_mul _ _ sigma (sigma.finite_real_spectrum.continuousOn _)
    (sigma.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro x hx
  have hp : 0 < x := pair_states.2.2.1.isStrictlyPositive.spectrum_pos hx
  change x^(1/8:ℝ) * x^(1/8:ℝ) = x^(1/4:ℝ)
  rw [← Real.rpow_add hp]
  norm_num

private lemma sandwich_trace :
    (trace (cfc (fun x:ℝ => x^(2:ℝ))
      (cfc (fun x:ℝ => x^(1/8:ℝ)) sigma * cfc (fun x:ℝ => x^(1/4:ℝ)) rho *
        cfc (fun x:ℝ => x^(1/8:ℝ)) sigma))).re =
      (2117 + 288 * Real.sqrt 2) / 3125 := by
  let S := cfc (fun x:ℝ => x^(1/8:ℝ)) sigma
  let R := cfc (fun x:ℝ => x^(1/4:ℝ)) rho
  have hS : IsSelfAdjoint S := IsSelfAdjoint.cfc
  have hR : IsSelfAdjoint R := IsSelfAdjoint.cfc
  have hpow : cfc (fun x:ℝ => x^(2:ℝ)) (S*R*S) = (S*R*S)^2 := by
    simp only [Real.rpow_two]
    exact cfc_pow_id (S*R*S) 2 (hR.conjugate_self hS)
  change (trace (cfc (fun x:ℝ => x^(2:ℝ)) (S*R*S))).re = _
  rw [hpow]
  have ht : trace ((S*R*S)^2) = trace ((R*(S*S))^2) := by
    simp only [pow_two]
    calc
      trace (S*R*S*(S*R*S)) = trace (S*(R*(S*S)*R*S)) := by
        congr 1; noncomm_ring
      _ = trace ((R*(S*S)*R*S)*S) := trace_mul_comm _ _
      _ = trace (R*(S*S)*(R*(S*S))) := by congr 1; noncomm_ring
  rw [ht]
  change (trace ((cfc (fun x:ℝ => x^(1/4:ℝ)) rho * (S*S))^2)).re = _
  rw [show S*S = cfc (fun x:ℝ => x^(1/4:ℝ)) sigma from eighth_square,
    rho_quarter, sigma_quarter]
  have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have h6 := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  have h4 := quarter_scalars.1
  norm_num [pow_two, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf
  have h3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    rw [pow_succ, h2]
  have h22 : Real.sqrt 2 ^ 4 = 4 := by
    calc
      Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2)^2 := by ring
      _ = 4 := by rw [h2]; norm_num
  rw [h4, h3, h22, h2, h6]
  ring
private lemma B1_gt : (2/5:ℝ) < renyiRZ (1/2) (1/2) 2 rho sigma := by
  have hv : renyiRZ (1/2) (1/2) 2 rho sigma =
      4 * (1 - Real.sqrt ((2117 + 288 * Real.sqrt 2) / 3125)) := by
    unfold renyiRZ lnr
    norm_num only
    rw [sandwich_trace, ← Real.sqrt_eq_rpow]
    ring
  rw [hv]
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have h2p := Real.sqrt_nonneg 2
  have h2u : Real.sqrt 2 < 17/12 := by nlinarith
  have hf : (0:ℝ) ≤ (2117 + 288 * Real.sqrt 2)/3125 := by positivity
  have hsF := Real.sq_sqrt hf
  have hFp := Real.sqrt_nonneg ((2117 + 288 * Real.sqrt 2)/3125)
  nlinarith
private def A : Matrix (Fin 2) (Fin 2) ℂ := !![7/25, (3 * Real.sqrt 6:ℝ)/25;
  (3 * Real.sqrt 6:ℝ)/25, 97/25]

private lemma rho_inverse_half : cfc (fun x:ℝ => x^(-(1/2:ℝ))) rho =
    diagonal ![((Real.sqrt 5/2:ℝ):ℂ), ((Real.sqrt 5:ℝ):ℂ)] := by
  have hlow : (1/5:ℝ)^(-(1/2:ℝ)) = Real.sqrt 5 := by
    rw [Real.rpow_neg_eq_inv_rpow]
    norm_num
    rw [← Real.sqrt_eq_rpow]
  have hhigh : (4/5:ℝ)^(-(1/2:ℝ)) = Real.sqrt 5/2 := by
    rw [Real.rpow_neg_eq_inv_rpow]
    norm_num
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num)]
    norm_num
  rw [(pair_cfc _).1, hhigh, hlow]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [H, Matrix.diagonal, Matrix.one_apply, Complex.real_smul] <;> push_cast <;> ring

private lemma sandwich_A :
    cfc (fun x:ℝ => x^(-(1/2:ℝ))) rho * sigma *
      cfc (fun x:ℝ => x^(-(1/2:ℝ))) rho = A := by
  rw [rho_inverse_half]
  have hs : (Real.sqrt 5:ℂ)^2 = 5 := by
    exact_mod_cast Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [sigma, A, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] <;>
    push_cast <;> ring_nf <;> norm_num [hs] <;> ring

private lemma A_nonneg : (0:Matrix (Fin 2) (Fin 2) ℂ) ≤ A := by
  rw [← sandwich_A]
  let T := cfc (fun x:ℝ => x^(-(1/2:ℝ))) rho
  have hT : IsSelfAdjoint T := IsSelfAdjoint.cfc
  have hp := pair_states.2.2.1.posSemidef.mul_mul_conjTranspose_same T
  simpa only [← Matrix.star_eq_conjTranspose, hT.star_eq] using hp.nonneg

private lemma A_sqrt : cfc (fun x:ℝ => x^(1/2:ℝ)) A =
    (5 / Real.sqrt 154:ℝ) • (A + 1) := by
  rw [← CFC.rpow_eq_cfc_real A_nonneg, ← CFC.sqrt_eq_rpow]
  apply CFC.sqrt_unique
  · have h6 : (Real.sqrt 6:ℂ)^2 = 6 := by
      exact_mod_cast Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
    have h154 : (Real.sqrt 154:ℂ)^2 = 154 := by
      exact_mod_cast Real.sq_sqrt (show (0:ℝ) ≤ 154 by norm_num)
    have hn : (Real.sqrt 154:ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (show (0:ℝ)<154 by norm_num)))
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [A, Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul, Matrix.one_apply] <;>
      push_cast <;> field_simp <;> ring_nf <;> norm_num [h6, h154]
  · exact smul_nonneg (by positivity) (add_nonneg A_nonneg zero_le_one)

private lemma B2_lt : B2 (1/2) 1 rho sigma < (2/5:ℝ) := by
  have hv : B2 (1/2) 1 rho sigma = 2 - 20 / Real.sqrt 154 := by
    unfold B2
    norm_num only [Real.rpow_one]
    rw [cfc_id' (p := IsSelfAdjoint) ℝ sigma (show IsSelfAdjoint sigma from pair_states.2.2.1.1), sandwich_A,
      cfc_id' (p := IsSelfAdjoint) ℝ A A_nonneg.isSelfAdjoint]
    have hl : cfc (fun x:ℝ => lnr (1/2) x) A =
        (2:ℝ) • (cfc (fun x:ℝ => x^(1/2:ℝ)) A - 1) := by
      have he : (fun x:ℝ => lnr (1/2) x) = (fun x:ℝ => 2 * (x^(1/2:ℝ) - 1)) := by
        funext x
        unfold lnr
        ring
      rw [he, cfc_const_mul (2:ℝ) (fun x:ℝ => x^(1/2:ℝ) - 1) A
        (A.finite_real_spectrum.continuousOn _),
        cfc_sub (fun x:ℝ => x^(1/2:ℝ)) (fun _ : ℝ => 1) A
          (A.finite_real_spectrum.continuousOn _) (by fun_prop),
        cfc_const 1 A A_nonneg.isSelfAdjoint]
      simp [Algebra.algebraMap_eq_smul_one]
    rw [hl, A_sqrt]
    norm_num [rho, A, Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.one_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      Fin.sum_univ_two, Complex.real_smul]
    ring
  rw [hv]
  have hp : 0 < Real.sqrt 154 := Real.sqrt_pos.mpr (by norm_num)
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 154 by norm_num)
  have hu : Real.sqrt 154 < 25/2 := by nlinarith
  have hd : (8/5:ℝ) < 20 / Real.sqrt 154 := by
    apply (lt_div_iff₀ hp).2
    nlinarith
  linarith
theorem result : ¬ claim := by
  intro hc
  obtain ⟨hrp, hrt, hsp, hst, hnc⟩ := pair_states
  have hord := (hc 2 rho sigma hrp hrt hsp hst hnc (1/2) (1/2) 2 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
  exact (not_lt_of_ge hord) (B2_lt.trans B1_gt)

end
end D5.S3.Divergence.MaityFuruichiDuttaOrderingRefutation
