/- GID: D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.claim; result=D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.result; claim=D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.claim
   digest: The closed upper power interval fails at exponent one. -/

/-
admission_basis: open-problem-resolution (#18757; Refuted at a = 1).
endpoint_psd: proof_shape: bind-only; escape_witness: none; direct_frozen_dependencies: F1; consumers: result.
result: proof_shape: bind-only; escape_witness: none; direct_frozen_dependencies: F1; consumers: external settlement.
Direct frozen dependency:
F1: D5.S3.Quantum.Matrix.ZhangJingBlockNormalityRefutation.block.
The source block uses CFC.sqrt (Aᴴ * A) exactly. No absolute-value alias is introduced.
The designated result refutes the literal closed-interval claim and is exempt from
four-slot escape registration (CLAUDE.md §3.9). The complete strict-interval
application of existing results is expounded in this module's owning Blueprint Scribe.
The public canonical CFC supplier's unfinished audit remains under
https://github.com/the-omega-institute/trureturing/issues/19914.
-/
import D5.S3.Quantum.Matrix.ZhangJingBlockNormalityRefutation

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section

namespace D5.S3.Quantum.Matrix.ZhangJingPowerCaseSettlement

open _root_.Matrix
open D5.S3.Quantum.Matrix.ZhangJingBlockNormalityRefutation (block)
open scoped ComplexOrder MatrixOrder

/-- Zhang–Jing, ELA 41 (2025), after Remark 2.13: "we cannot solve the problem that Theorem 2.3 holds for
1/2 ≤ a ≤ 1", where Theorem 2.3 reads "[[|A|^{2a}, A*], [A, |A|^{2(1−a)}]] ≥ 0 … if and only if A is normal". -/
def claim : Prop :=
  ∀ a : ℝ, 1 / 2 ≤ a → a ≤ 1 → ∀ n : ℕ, ∀ A : Matrix (Fin n) (Fin n) ℂ,
    (block (fun x => x ^ (2 * a)) (fun x => x ^ (2 * (1 - a))) A).PosSemidef ↔ Aᴴ * A = A * Aᴴ

private lemma endpoint_psd {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (block (fun x => x ^ (2 * (1 : ℝ))) (fun x => x ^ (2 * (1 - (1 : ℝ)))) A).PosSemidef := by
  have hD : 0 ≤ (CFC.sqrt (Aᴴ * A)) := CFC.sqrt_nonneg _
  have hF : cfc (fun x : ℝ => x ^ (2 : ℝ)) ((CFC.sqrt (Aᴴ * A))) = Aᴴ * A := by
    simp_rw [Real.rpow_two]
    rw [cfc_pow_id (R := ℝ) ((CFC.sqrt (Aᴴ * A))) 2 hD.isSelfAdjoint]
    exact CFC.sq_sqrt (Aᴴ * A) (posSemidef_conjTranspose_mul_self A).nonneg
  have hG : cfc (fun _ : ℝ => (1 : ℝ)) ((CFC.sqrt (Aᴴ * A))) = 1 := by
    exact cfc_const_one ℝ _
  have hgram := posSemidef_conjTranspose_mul_self
    (fromBlocks A (1 : Matrix (Fin n) (Fin n) ℂ) (0 : Matrix (Fin n) (Fin n) ℂ) 0)
  simpa only [block, mul_one, sub_self, mul_zero, Real.rpow_zero, hG, hF,
    fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_one,
    conjTranspose_zero, zero_mul, mul_zero, add_zero, zero_add, one_mul] using hgram

theorem result : ¬ claim := by
  intro h
  let A : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 2, 0]
  have hn := (h 1 (by norm_num) le_rfl 2 A).mp (endpoint_psd A)
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hn
  norm_num [A, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, map_ofNat] at he

end D5.S3.Quantum.Matrix.ZhangJingPowerCaseSettlement
