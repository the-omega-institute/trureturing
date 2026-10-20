/- GID: D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.claim; result=D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.result; claim=D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.claim
   digest: An explicit four-dimensional system refutes Fu-Luo decoherence convexity. -/

/-
proof_shape:
  J, EnvIdx, liftE, rhoE, omega, finalState, D, claim: definitions; consumers are the
    delivered theorem and its proof path as recorded by the public statements below.
  result: bind-only (the explicit witness evaluates the definitions and closes the Jensen
    inequality contradiction by pinned Mathlib normalization).
escape_witness: none
admission_basis: open-problem-resolution (#19026; Refuted)
Direct frozen dependencies: D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
  statement_id sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5;
  D5/S3/Quantum/Reduction/ProbeComponentRigidity.probe
  statement_id sha256:f5b3b039ec347372b8b6448078a180419ab9681a2991f506e66c5cd8ba39b684;
  all other proof steps use pinned Mathlib.
Per-declaration proof_shape and live consumers:
  Public definitions J, EnvIdx, liftE, rhoE, omega, finalState, D: definitions; consumers=claim/result.
  claim: definition; consumer=result.
  result: bind-only; consumer=external open-problem resolution.
  Private definitions q, r, v, ve, vo, w, e, R, M, B, BM, SM, S, SBM,
    z, tau0, tau, UX, UZ, detectors, tag, delta, state: definitions; consumers are
    the private proofs and result that use them.
  Private lemmas q_sq, r_sq, q_star, R_pos, SM_pos, S_pos, SBM_pos, R_trace, mixture,
    R_square, SM_square, S_square, SBM_square, sqrt_R, sqrt_M, sqrt_B, sqrt_BM,
    rhoE_eq, lift_column, omega_delta, omega_table, final_R, final_M, D_R, D_M:
    bind-only; each is consumed by a later private proof or result.
Claims keep the preregistered definitions literally; the frozen DensityState and probe owners
are used inside the witness construction without introducing duplicate definitions.
The public result is the designated refutation result (`basis=refutes`) and is exempt from
four-slot escape registration (CLAUDE.md §3.9).
-/
import D5.S3.Quantum.Reduction.ProbeComponentRigidity

/-! Binding conventions for S. Fu and S. Luo, "Quantifying Decoherence via Increases in Classicality",
Entropy 23 (2021) 1594, Section 3, Eqs. (17)-(22) and (27). The system is `d`-dimensional with pointer basis
`Π = {|i⟩⟨i|}` (the standard basis of `Fin d`); the environment has `d` parts, part `i` of dimension `k i`. -/

noncomputable section
namespace D5.S3.Quantum.Decoherence.FuLuoDecoherenceConvexityRefutation

open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open scoped ComplexOrder MatrixOrder

variable {d : ℕ}

/-- Eq. (17): `J(ρ, Π) = 1 + Σ_i ⟨i|√ρ|i⟩²`. -/
def J (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  1 + ∑ i, (((CFC.sqrt ρ) i i) ^ 2).re

/-- A basis label of the environment `H_E = H_{E_1} ⊗ ⋯ ⊗ H_{E_d}`. -/
abbrev EnvIdx (k : Fin d → ℕ) : Type := (l : Fin d) → Fin (k l)

/-- `U_{E_i}` acting only on `H_{E_i}`: the operator `1 ⊗ ⋯ ⊗ U_i ⊗ ⋯ ⊗ 1` on `H_E`. -/
def liftE {k : Fin d → ℕ} (i : Fin d) (Ui : Matrix (Fin (k i)) (Fin (k i)) ℂ) :
    Matrix (EnvIdx k) (EnvIdx k) ℂ :=
  fun x y => if ∀ l, l ≠ i → x l = y l then Ui (x i) (y i) else 0

/-- `ρ_E = ρ_{E_1} ⊗ ρ_{E_2} ⊗ ⋯ ⊗ ρ_{E_d}`. -/
def rhoE {k : Fin d → ℕ} (τ : (l : Fin d) → DensityState (Fin (k l))) :
    Matrix (EnvIdx k) (EnvIdx k) ℂ :=
  fun x y => ∏ l, (τ l).val (x l) (y l)

/-- Eq. (21): `ω_{ij} = tr(U_{E_i} ρ_E U_{E_j}†)`. -/
def omega {k : Fin d → ℕ} (τ : (l : Fin d) → DensityState (Fin (k l)))
    (U : (l : Fin d) → Matrix.unitaryGroup (Fin (k l)) ℂ) (i j : Fin d) : ℂ :=
  (liftE i (U i : Matrix (Fin (k i)) (Fin (k i)) ℂ) * rhoE τ *
    (liftE j (U j : Matrix (Fin (k j)) (Fin (k j)) ℂ)).conjTranspose).trace

/-- Eq. (22): the final system state `ρ'_S = ρ_S ∘ Ω`, with `Ω = (ω_{ij})`. -/
def finalState {k : Fin d → ℕ} (τ : (l : Fin d) → DensityState (Fin (k l)))
    (U : (l : Fin d) → Matrix.unitaryGroup (Fin (k l)) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun a b => ρ a b * omega τ U a b

/-- Eq. (27): `D(ρ_S | Π, U) = J(ρ'_S, Π) − J(ρ_S, Π)`. -/
def D {k : Fin d → ℕ} (τ : (l : Fin d) → DensityState (Fin (k l)))
    (U : (l : Fin d) → Matrix.unitaryGroup (Fin (k l)) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  J (finalState τ U ρ) - J ρ

/-- "We conjecture that `D(ρ_S | Π, U)` is convex in `ρ`" (Section 3, after Proposition 3), for every system
dimension, every product environment state and every family of local unitaries. -/
def claim : Prop :=
  ∀ (d : ℕ) (k : Fin d → ℕ) (τ : (l : Fin d) → DensityState (Fin (k l)))
    (U : (l : Fin d) → Matrix.unitaryGroup (Fin (k l)) ℂ) (ρ σ : DensityState (Fin d)) (t : ℝ),
    0 ≤ t → t ≤ 1 →
      D τ U (CStarMatrix.ofMatrix.symm (t • ρ.val + (1 - t) • σ.val)) ≤
        t * D τ U (CStarMatrix.ofMatrix.symm ρ.val) + (1 - t) * D τ U (CStarMatrix.ofMatrix.symm σ.val)

end D5.S3.Quantum.Decoherence.FuLuoDecoherenceConvexityRefutation

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace D5.S3.Quantum.Decoherence.FuLuoDecoherenceConvexityRefutation
open scoped MatrixOrder ComplexOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)

private def q : ℂ := (Real.sqrt 3 : ℝ)
private def r : ℂ := (Real.sqrt 2 : ℝ)
private lemma q_sq : q ^ 2 = 3 := by norm_num [q, ← Complex.ofReal_pow, Real.sq_sqrt]
private lemma r_sq : r ^ 2 = 2 := by norm_num [r, ← Complex.ofReal_pow, Real.sq_sqrt]
private lemma q_star : (starRingEnd ℂ) q = q := by
  exact Complex.conj_eq_iff_re.mpr rfl
private def v (b : Bool) : Fin 4 → ℂ := if b then ![1,-1,q,-q] else ![1,1,q,q]
private def ve : Fin 4 → ℂ := ![1,0,q,0]
private def vo : Fin 4 → ℂ := ![0,1,0,q]
private def w (b : Bool) : Fin 4 → ℂ := if b then ![0,0,1,-1] else ![0,0,1,1]
private def e (i : Fin 4) : Fin 4 → ℂ := Pi.single i 1
private def R (b : Bool) : Matrix (Fin 4) (Fin 4) ℂ := (1/8 : ℝ) • D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe (v b)
private def M : Matrix (Fin 4) (Fin 4) ℂ := (1/8 : ℝ) • (D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe ve + D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe vo)
private def B (b : Bool) : Matrix (Fin 4) (Fin 4) ℂ := (1/8 : ℝ) • (D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe (e 0) + D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe (e 1)) +
  (3/8 : ℝ) • D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe (w b)
private def BM : Matrix (Fin 4) (Fin 4) ℂ := (1/8 : ℝ) • (D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe (e 0) + D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe (e 1)) +
  (3/8 : ℝ) • (D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe (e 2) + D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe (e 3))
private def SM : Matrix (Fin 4) (Fin 4) ℂ := (Real.sqrt 2 / 8 : ℝ) • (D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe ve + D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe vo)
private def S (b : Bool) : Matrix (Fin 4) (Fin 4) ℂ := (Real.sqrt 2 / 4 : ℝ) • (D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe (e 0) + D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe (e 1)) +
  (Real.sqrt 3 / 4 : ℝ) • D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe (w b)
private def SBM : Matrix (Fin 4) (Fin 4) ℂ := (Real.sqrt 2 / 4 : ℝ) • (D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe (e 0) + D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe (e 1)) +
  (Real.sqrt 2 * Real.sqrt 3 / 4 : ℝ) • (D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe (e 2) + D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe (e 3))

private lemma R_pos (b : Bool) : (R b).PosSemidef := by
  exact (Matrix.posSemidef_vecMulVec_self_star (v b)).smul (by norm_num : (0:ℝ) ≤ 1/8)
private lemma SM_pos : SM.PosSemidef := by
  exact ((Matrix.posSemidef_vecMulVec_self_star ve).add
    (Matrix.posSemidef_vecMulVec_self_star vo)).smul (by positivity : (0:ℝ) ≤ Real.sqrt 2 / 8)
private lemma S_pos (b : Bool) : (S b).PosSemidef := by
  exact (((Matrix.posSemidef_vecMulVec_self_star (e 0)).add
    (Matrix.posSemidef_vecMulVec_self_star (e 1))).smul (by positivity : (0:ℝ) ≤ Real.sqrt 2 / 4)).add
    ((Matrix.posSemidef_vecMulVec_self_star (w b)).smul (by positivity : (0:ℝ) ≤ Real.sqrt 3 / 4))
private lemma SBM_pos : SBM.PosSemidef := by
  exact (((Matrix.posSemidef_vecMulVec_self_star (e 0)).add
    (Matrix.posSemidef_vecMulVec_self_star (e 1))).smul (by positivity : (0:ℝ) ≤ Real.sqrt 2 / 4)).add
    (((Matrix.posSemidef_vecMulVec_self_star (e 2)).add
    (Matrix.posSemidef_vecMulVec_self_star (e 3))).smul (by positivity : (0:ℝ) ≤ Real.sqrt 2 * Real.sqrt 3 / 4))

private lemma R_trace (b : Bool) : (R b).trace = 1 := by
  unfold R D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe
  rw [Matrix.trace_smul, Matrix.trace_vecMulVec]
  cases b <;> norm_num [v, dotProduct, Fin.sum_univ_succ, Pi.star_apply, q_star,
    ← pow_two, q_sq]
private def state (b : Bool) : DensityState (Fin 4) :=
  ⟨CStarMatrix.ofMatrix (R b), map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (R_pos b).nonneg, R_trace b⟩

private lemma mixture : (1/2 : ℝ) • R false + (1/2 : ℝ) • R true = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [R, M, D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe, v, ve, vo, Matrix.vecMulVec, Matrix.smul_apply,
      Matrix.add_apply, smul_eq_mul, Pi.star_apply, q_star] <;> ring

private lemma R_square (b : Bool) : R b * R b = R b := by
  unfold R D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec]
  cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [v, dotProduct, Matrix.vecMulVec, Matrix.smul_apply, smul_eq_mul,
      Fin.sum_univ_succ, Pi.star_apply, q_star, ← pow_two, q_sq] <;> ring_nf <;>
    simp only [show q ^ 3 = q ^ 2 * q by ring,
      show q ^ 4 = (q ^ 2) ^ 2 by ring, q_sq] <;> ring
private lemma SM_square : SM * SM = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [SM, M, D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe, ve, vo, Matrix.mul_apply, Matrix.vecMulVec, Matrix.smul_apply,
      Matrix.add_apply, smul_eq_mul, Fin.sum_univ_succ, Pi.star_apply, q_star,
      Complex.ofReal_div, show ((Real.sqrt 3 : ℝ) : ℂ) = q from rfl, show ((Real.sqrt 2 : ℝ) : ℂ) = r from rfl, q_star] <;> ring_nf <;> simp only [show q ^ 3 = q ^ 2 * q by ring,
        show q ^ 4 = (q ^ 2) ^ 2 by ring, q_sq, r_sq] <;> ring
private lemma S_square (b : Bool) : S b * S b = B b := by
  cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [S, B, D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe, e, w, Matrix.mul_apply, Matrix.vecMulVec, Matrix.smul_apply,
      Matrix.add_apply, smul_eq_mul, Fin.sum_univ_succ, Pi.star_apply, Pi.single_apply,
      Complex.ofReal_div, show ((Real.sqrt 3 : ℝ) : ℂ) = q from rfl, show ((Real.sqrt 2 : ℝ) : ℂ) = r from rfl, q_star] <;> ring_nf <;> simp only [show q ^ 3 = q ^ 2 * q by ring,
        show q ^ 4 = (q ^ 2) ^ 2 by ring, q_sq, r_sq] <;> ring
private lemma SBM_square : SBM * SBM = BM := by
  unfold SBM BM D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe
  simp only [Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, Matrix.vecMulVec_mul_vecMulVec]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [SBM, BM, D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe, e, Matrix.mul_apply, Matrix.vecMulVec, Matrix.smul_apply,
      Matrix.add_apply, smul_eq_mul, Fin.sum_univ_succ, Pi.star_apply, Pi.single_apply,
      Complex.ofReal_div, Complex.ofReal_mul, show ((Real.sqrt 3 : ℝ) : ℂ) = q from rfl, show ((Real.sqrt 2 : ℝ) : ℂ) = r from rfl, q_star] <;> ring_nf <;> simp only [show q ^ 3 = q ^ 2 * q by ring,
        show q ^ 4 = (q ^ 2) ^ 2 by ring, q_sq, r_sq] <;> ring

private lemma sqrt_R (b : Bool) : CFC.sqrt (R b) = R b :=
  CFC.sqrt_unique (R_square b) (R_pos b).nonneg
private lemma sqrt_M : CFC.sqrt M = SM := CFC.sqrt_unique SM_square SM_pos.nonneg
private lemma sqrt_B (b : Bool) : CFC.sqrt (B b) = S b := CFC.sqrt_unique (S_square b) (S_pos b).nonneg
private lemma sqrt_BM : CFC.sqrt BM = SBM := CFC.sqrt_unique SBM_square SBM_pos.nonneg

end D5.S3.Quantum.Decoherence.FuLuoDecoherenceConvexityRefutation

namespace D5.S3.Quantum.Decoherence.FuLuoDecoherenceConvexityRefutation
open scoped MatrixOrder ComplexOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
private def z : Fin 4 → Fin 2 := fun _ => 0
private def tau0 : DensityState (Fin 2) :=
  ⟨CStarMatrix.ofMatrix (Matrix.single 0 0 1),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (by
      apply Matrix.PosSemidef.nonneg
      rw [← Matrix.diagonal_single, Matrix.posSemidef_diagonal_iff]
      intro i
      fin_cases i <;> norm_num [Pi.single_apply]), by
    change Matrix.trace (Matrix.single (0:Fin 2) 0 (1:ℂ)) = 1
    simp⟩
private def tau : (l : Fin 4) → DensityState (Fin 2) := fun _ => tau0
private def UX : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨!![0,1;1,0], Matrix.mem_unitaryGroup_iff.mpr (by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_succ])⟩
private def UZ : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨!![1,0;0,-1], Matrix.mem_unitaryGroup_iff.mpr (by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_succ])⟩
private def detectors (i : Fin 4) : Matrix.unitaryGroup (Fin 2) ℂ :=
  if i < 2 then UX else UZ
private def tag (i : Fin 4) : Fin 4 → Fin 2 := if i < 2 then Function.update z i 1 else z
private def delta (i : Fin 4) (x : Fin 4 → Fin 2) : ℂ := if x = tag i then 1 else 0

private lemma rhoE_eq : rhoE tau = Matrix.single z z 1 := by
  ext x y
  change (∏ l : Fin 4, Matrix.single (0:Fin 2) 0 (1:ℂ) (x l) (y l)) = _
  simp only [Matrix.single, Matrix.of_apply]
  simp only [Fintype.prod_boole]
  congr 1
  simp only [funext_iff, z, forall_and]

private lemma lift_column (i : Fin 4) (x : Fin 4 → Fin 2) :
    liftE i (detectors i : Matrix (Fin 2) (Fin 2) ℂ) x z = delta i x := by
  fin_cases i
  · generalize h : x 0 = a
    fin_cases a <;> simp [liftE, detectors, UX, UZ, delta, tag, z, funext_iff,
      Fin.forall_fin_succ, Function.update_apply, h]
  · generalize h : x 1 = a
    fin_cases a <;> simp [liftE, detectors, UX, UZ, delta, tag, z, funext_iff,
      Fin.forall_fin_succ, Function.update_apply, h]
  · generalize h : x 2 = a
    fin_cases a <;> simp [liftE, detectors, UX, UZ, delta, tag, z, funext_iff,
      Fin.forall_fin_succ, Function.update_apply, h]
  · generalize h : x 3 = a
    fin_cases a <;> simp [liftE, detectors, UX, UZ, delta, tag, z, funext_iff,
      Fin.forall_fin_succ, Function.update_apply, h]

private lemma omega_delta (i j : Fin 4) : omega tau detectors i j = if tag i = tag j then 1 else 0 := by
  unfold omega
  rw [rhoE_eq, Matrix.trace_mul_cycle, Matrix.trace_mul_single]
  simp only [op_smul_eq_smul, one_smul, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [lift_column]
  simp [delta]

private lemma omega_table (i j : Fin 4) :
    omega tau detectors i j = if i = j ∨ (2 ≤ i ∧ 2 ≤ j) then 1 else 0 := by
  rw [omega_delta]
  fin_cases i <;> fin_cases j <;>
    norm_num [tag, z, funext_iff, Fin.forall_fin_succ, Function.update_apply]
end D5.S3.Quantum.Decoherence.FuLuoDecoherenceConvexityRefutation

namespace D5.S3.Quantum.Decoherence.FuLuoDecoherenceConvexityRefutation
open scoped MatrixOrder ComplexOrder
private lemma final_R (b : Bool) : finalState tau detectors (R b) = B b := by
  cases b <;> ext i j <;> rw [finalState, omega_table] <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [R, B, D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe, v, w, e, Matrix.vecMulVec, Matrix.smul_apply,
      Matrix.add_apply, smul_eq_mul, Pi.star_apply, Pi.single_apply, q_star] <;> ring_nf <;> norm_num [q_sq,pow_succ]
private lemma final_M : finalState tau detectors M = BM := by
  ext i j
  rw [finalState, omega_table]
  fin_cases i <;> fin_cases j <;>
    norm_num [M, BM, D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe, ve, vo, e, Matrix.vecMulVec, Matrix.smul_apply,
      Matrix.add_apply, smul_eq_mul, Pi.star_apply, Pi.single_apply, q_star] <;> ring_nf <;> norm_num [q_sq,pow_succ]
private lemma D_R (b : Bool) : D tau detectors (R b) = 5/16 := by
  unfold D
  rw [final_R]
  unfold J
  rw [sqrt_B, sqrt_R]
  cases b <;>
    norm_num [R, S, D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe, v, w, e, Matrix.vecMulVec, Matrix.smul_apply,
      Matrix.add_apply, smul_eq_mul, Pi.star_apply, Pi.single_apply, q, r,
      Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im, pow_two] <;>
    ring_nf <;> norm_num [Real.sq_sqrt]
private lemma D_M : D tau detectors M = 3/8 := by
  unfold D
  rw [final_M]
  unfold J
  rw [sqrt_BM, sqrt_M]
  norm_num [SM, SBM, D5.S3.Quantum.Reduction.ProbeComponentRigidity.probe, ve, vo, e, Matrix.vecMulVec, Matrix.smul_apply,
    Matrix.add_apply, smul_eq_mul, Pi.star_apply, Pi.single_apply, q, r,
    Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im, pow_two] <;>
    ring_nf <;> norm_num [Real.sq_sqrt]

theorem result : ¬ claim := by
  intro h
  have h' := h 4 (fun _ => 2) tau detectors (state false) (state true) (1/2) (by norm_num) (by norm_num)
  change D tau detectors ((1/2:ℝ) • R false + (1-1/2:ℝ) • R true) ≤
    (1/2:ℝ) * D tau detectors (R false) + (1-1/2:ℝ) * D tau detectors (R true) at h'
  norm_num only [show (1-1/2:ℝ) = 1/2 by norm_num] at h'
  rw [mixture, D_R, D_R, D_M] at h'
  norm_num at h'
end D5.S3.Quantum.Decoherence.FuLuoDecoherenceConvexityRefutation
