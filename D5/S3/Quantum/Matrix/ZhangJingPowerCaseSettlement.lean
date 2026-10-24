/- GID: D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.claim; result=D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.result; claim=D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.claim
   digest: The power block detects normality below exponent one and fails at exponent one. -/

/-
admission_basis: open-problem-resolution (#18757; Refuted at a = 1; Proved below one).
cfc_unitary_diagonal: proof_shape: bind-only; escape_witness: none; direct_frozen_dependencies: F3; consumers: svd_abs, block_svd_coordinates.
rpow_factor: proof_shape: bind-only; escape_witness: none; direct_frozen_dependencies: none; consumers: diagonal_schur_forces_commute.
unitary_conjugate_trace: proof_shape: bind-only; escape_witness: none; direct_frozen_dependencies: none; consumers: diagonal_schur_forces_commute.
diag_commute_of_rpow_commute: proof_shape: bind-only; escape_witness: none; direct_frozen_dependencies: none; consumers: svd_normal_iff, diagonal_schur_forces_commute.
unitary_star_cancel: proof_shape: bind-only; escape_witness: none; direct_frozen_dependencies: none; consumers: svd_gram, svd_normal_iff, block_svd_coordinates.
unitary_cancel_star: proof_shape: bind-only; escape_witness: none; direct_frozen_dependencies: none; consumers: svd_normal_iff.
svd_abs: proof_shape: bind-only; escape_witness: none; direct_frozen_dependencies: F1, F3; consumers: below_one.
svd_gram: proof_shape: bind-only; escape_witness: none; direct_frozen_dependencies: none; consumers: svd_abs, svd_normal_iff.
svd_normal_iff: proof_shape: bind-only; escape_witness: none; direct_frozen_dependencies: none; consumers: below_one.
balanced_block_psd: proof_shape: bind-only; escape_witness: none; direct_frozen_dependencies: none; consumers: diagonal_block_iff_commute.
diagonal_schur_forces_commute: proof_shape: bind-only; escape_witness: none; direct_frozen_dependencies: none; consumers: diagonal_block_iff_commute.
block_unitary_mem: proof_shape: bind-only; escape_witness: none; direct_frozen_dependencies: none; consumers: block_svd_coordinates.
block_svd_coordinates: proof_shape: bind-only; escape_witness: none; direct_frozen_dependencies: F3, F4; consumers: below_one.
diagonal_block_iff_commute: proof_shape: bind-only; escape_witness: none; direct_frozen_dependencies: F2; consumers: below_one.
endpoint_psd: proof_shape: bind-only; escape_witness: none; direct_frozen_dependencies: F4; consumers: result.
result: proof_shape: bind-only; escape_witness: none; direct_frozen_dependencies: F4; consumers: external settlement.
below_one: proof_shape: bind-only; escape_witness: none; direct_frozen_dependencies: F1, F2, F3, F4; consumers: external settlement.
Direct frozen dependencies:
F1: D5.S3.Quantum.Foundation.FiniteTraceDistance.exists_svd_sqrt_eigenvalues
  statement_id: sha256:e079c550fa808a0eb9281e4fd4662a1ea12091a4328d1330c268597ffc16be91.
F2: D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal
  statement_id: sha256:873e4955783786d99a250879f3da4640dab6550433b567150988ca3aaede9fe0.
F3: D5.S3.Quantum.Information.RenyiInformationCombiningOrderThree.cfc_unitary_diagonal.
F4: D5.S3.Quantum.Matrix.ZhangJingBlockNormalityRefutation.block.
The block contains CFC.sqrt (Aᴴ * A) exactly. No absM alias is introduced: CFC.abs
already defines that expression. The frozen ZhangJingBlockNormalityRefutation.block owner is used directly.
The public result is the designated refutation result (basis=refutes), exempt from
four-slot escape registration (CLAUDE.md §3.9). Escape audit unfinished for below_one:
https://github.com/the-omega-institute/trureturing/issues/19914.
-/
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.Information.RenyiInformationCombiningOrderThree
import D5.S3.Quantum.Matrix.ZhangJingBlockNormalityRefutation

set_option autoImplicit false

namespace D5.S3.Quantum.Matrix.ZhangJingPowerCaseSettlement

open _root_.Matrix
open D5.S3.Quantum.Matrix.ZhangJingBlockNormalityRefutation (block)
open scoped ComplexOrder MatrixOrder


/-- Zhang–Jing, ELA 41 (2025), after Remark 2.13: "we cannot solve the problem that Theorem 2.3 holds for
1/2 ≤ a ≤ 1", where Theorem 2.3 reads "[[|A|^{2a}, A*], [A, |A|^{2(1−a)}]] ≥ 0 … if and only if A is normal". -/
def claim : Prop :=
  ∀ a : ℝ, 1 / 2 ≤ a → a ≤ 1 → ∀ n : ℕ, ∀ A : Matrix (Fin n) (Fin n) ℂ,
    (block (fun x => x ^ (2 * a)) (fun x => x ^ (2 * (1 - a))) A).PosSemidef ↔ Aᴴ * A = A * Aᴴ

/-- The equivalence of Theorem 2.3 for every `1/2 ≤ a < 1`, the range on which it holds. -/
def claimBelowOne : Prop :=
  ∀ a : ℝ, 1 / 2 ≤ a → a < 1 → ∀ n : ℕ, ∀ A : Matrix (Fin n) (Fin n) ℂ,
    (block (fun x => x ^ (2 * a)) (fun x => x ^ (2 * (1 - a))) A).PosSemidef ↔ Aᴴ * A = A * Aᴴ

end D5.S3.Quantum.Matrix.ZhangJingPowerCaseSettlement

set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
open _root_.Matrix
open D5.S3.Quantum.Matrix.ZhangJingBlockNormalityRefutation (block)
open scoped ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Matrix.ZhangJingPowerCaseSettlement
variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma cfc_unitary_diagonal (U : Matrix.unitaryGroup n ℂ) (d : n → ℝ) (f : ℝ → ℝ) :
    cfc f ((U : Matrix n n ℂ) * diagonal (fun i => (d i : ℂ)) * star (U : Matrix n n ℂ)) =
      (U : Matrix n n ℂ) * diagonal (fun i => (f (d i) : ℂ)) * star (U : Matrix n n ℂ) := by
  exact D5.S3.Quantum.Information.RenyiInformationCombiningOrderThree.cfc_unitary_diagonal U d f

private lemma rpow_factor (x a : ℝ) (hx : 0 ≤ x) (ha : 1 / 2 ≤ a) (ha1 : a < 1) :
    x ^ (2*a) * x ^ (1-2*a) = x ∧
      x ^ (1-2*a) * x = x ^ (2*(1-a)) := by
  by_cases hx0 : x = 0
  · subst x
    have h2a : 2*a ≠ 0 := by linarith
    have h2b : 2*(1-a) ≠ 0 := by linarith
    simp [Real.zero_rpow h2a, Real.zero_rpow h2b]
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    constructor
    · rw [← Real.rpow_add hxp, show 2*a+(1-2*a) = 1 by ring, Real.rpow_one]
    · conv_lhs => rhs; rw [← Real.rpow_one x]
      rw [← Real.rpow_add hxp]
      congr 1
      ring

private lemma unitary_conjugate_trace (U : Matrix.unitaryGroup n ℂ) (G : Matrix n n ℂ) :
    (star (U : Matrix n n ℂ) * G * (U : Matrix n n ℂ)).trace = G.trace := by
  exact trace_units_conj' (Unitary.toUnits U) G

private lemma diag_commute_of_rpow_commute (U : Matrix n n ℂ) (d : n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (r : ℝ) (hr : r ≠ 0)
    (h : U * diagonal (fun i => ((d i ^ r : ℝ) : ℂ)) =
      diagonal (fun i => ((d i ^ r : ℝ) : ℂ)) * U) :
    U * diagonal (fun i => (d i : ℂ)) = diagonal (fun i => (d i : ℂ)) * U := by
  ext i j
  have hij := congrArg (fun M : Matrix n n ℂ => M i j) h
  simp only [mul_diagonal, diagonal_mul] at hij ⊢
  by_cases hz : U i j = 0
  · simp [hz]
  · have he : ((d j ^ r : ℝ) : ℂ) = ((d i ^ r : ℝ) : ℂ) := by
      apply mul_left_cancel₀ hz
      simpa only [mul_comm (U i j)] using hij
    have he' : d j = d i := (Real.rpow_left_inj (hd j) (hd i) hr).mp
      (Complex.ofReal_injective he)
    rw [he', mul_comm]

end D5.S3.Quantum.Matrix.ZhangJingPowerCaseSettlement

namespace D5.S3.Quantum.Matrix.ZhangJingPowerCaseSettlement
variable {n : Type*} [Fintype n] [DecidableEq n]

@[simp]
private lemma unitary_star_cancel (U : Matrix.unitaryGroup n ℂ) (X : Matrix n n ℂ) :
    star (U : Matrix n n ℂ) * ((U : Matrix n n ℂ) * X) = X := by
  exact Units.inv_mul_cancel_left (Unitary.toUnits U) X

@[simp]
private lemma unitary_cancel_star (U : Matrix.unitaryGroup n ℂ) (X : Matrix n n ℂ) :
    (U : Matrix n n ℂ) * (star (U : Matrix n n ℂ) * X) = X := by
  exact Units.mul_inv_cancel_left (Unitary.toUnits U) X

private lemma svd_gram (V W : Matrix.unitaryGroup n ℂ) (d : n → ℝ)
    (A : Matrix n n ℂ)
    (hA : A = (V : Matrix n n ℂ) * diagonal (fun i => (d i : ℂ)) * star (W : Matrix n n ℂ)) :
    Aᴴ * A = (W : Matrix n n ℂ) * diagonal (fun i => ((d i ^ 2 : ℝ) : ℂ)) * star (W : Matrix n n ℂ) ∧
    A * Aᴴ = (V : Matrix n n ℂ) * diagonal (fun i => ((d i ^ 2 : ℝ) : ℂ)) * star (V : Matrix n n ℂ) := by
  have hD : star (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (d i : ℂ)) := by
    simp [star_eq_conjTranspose, diagonal_conjTranspose]
  rw [hA]
  simp only [← star_eq_conjTranspose, star_mul, star_star, hD]
  constructor <;> simp [mul_assoc, ← diagonal_mul_diagonal, pow_two]

private lemma svd_abs {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ∃ (V W : Matrix.unitaryGroup (Fin k) ℂ) (d : Fin k → ℝ),
      (∀ i, 0 ≤ d i) ∧
      A = (V : Matrix (Fin k) (Fin k) ℂ) * diagonal (fun i => (d i : ℂ)) *
        star (W : Matrix (Fin k) (Fin k) ℂ) ∧
      (CFC.sqrt (Aᴴ * A)) = (W : Matrix (Fin k) (Fin k) ℂ) * diagonal (fun i => (d i : ℂ)) *
        star (W : Matrix (Fin k) (Fin k) ℂ) := by
  let hH : (Aᴴ * A).IsHermitian := isHermitian_conjTranspose_mul_self A
  obtain ⟨V, W, hA⟩ := D5.S3.Quantum.Foundation.FiniteTraceDistance.exists_svd_sqrt_eigenvalues A
  let d : Fin k → ℝ := fun i => Real.sqrt (hH.eigenvalues i)
  have hd : ∀ i, 0 ≤ d i := fun i => Real.sqrt_nonneg _
  change A = (V : Matrix (Fin k) (Fin k) ℂ) * diagonal (fun i => (d i : ℂ)) *
      star (W : Matrix (Fin k) (Fin k) ℂ) at hA
  refine ⟨V, W, d, hd, hA, ?_⟩
  have hGram := (svd_gram V W d A hA).1
  rw [CFC.sqrt_eq_real_sqrt _ (posSemidef_conjTranspose_mul_self A).nonneg,
    cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), hGram, cfc_unitary_diagonal]
  simp only [Real.sqrt_sq (hd _)]

private lemma svd_normal_iff (V W : Matrix.unitaryGroup n ℂ) (d : n → ℝ) (hd : ∀ i, 0 ≤ d i)
    (A : Matrix n n ℂ)
    (hA : A = (V : Matrix n n ℂ) * diagonal (fun i => (d i : ℂ)) * star (W : Matrix n n ℂ)) :
    Aᴴ * A = A * Aᴴ ↔
      ((star W * V : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) * diagonal (fun i => (d i : ℂ)) =
        diagonal (fun i => (d i : ℂ)) * ((star W * V : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) := by
  let D : Matrix n n ℂ := diagonal (fun i => (d i : ℂ))
  let E : Matrix n n ℂ := diagonal (fun i => ((d i ^ 2 : ℝ) : ℂ))
  let U : Matrix.unitaryGroup n ℂ := star W * V
  obtain ⟨h1, h2⟩ := svd_gram V W d A hA
  constructor
  · intro hn
    have hEq := congrArg (fun X : Matrix n n ℂ => star (W : Matrix n n ℂ) * X * (V : Matrix n n ℂ)) hn
    rw [h1, h2] at hEq
    have hc : (U : Matrix n n ℂ) * E = E * (U : Matrix n n ℂ) := by
      simpa [U, E, mul_assoc] using hEq.symm
    apply diag_commute_of_rpow_commute _ d hd 2 (by norm_num)
    simpa only [Real.rpow_two] using hc
  · intro hc
    change (U : Matrix n n ℂ) * D = D * (U : Matrix n n ℂ) at hc
    have hE : E = D * D := by
      simp [E, D, diagonal_mul_diagonal, pow_two]
    have hcE : (U : Matrix n n ℂ) * E = E * (U : Matrix n n ℂ) := by
      rw [hE]
      calc (U : Matrix n n ℂ) * (D*D) = ((U : Matrix n n ℂ)*D)*D := by rw [mul_assoc]
           _ = (D*(U : Matrix n n ℂ))*D := by rw [hc]
           _ = D*((U : Matrix n n ℂ)*D) := by rw [mul_assoc]
           _ = D*(D*(U : Matrix n n ℂ)) := by rw [hc]
           _ = (D*D)*(U : Matrix n n ℂ) := by rw [mul_assoc]
    rw [h1, h2]
    have he := congrArg (fun X : Matrix n n ℂ => (W : Matrix n n ℂ) * X * star (V : Matrix n n ℂ)) hcE
    simpa [U, E, mul_assoc] using he.symm

end D5.S3.Quantum.Matrix.ZhangJingPowerCaseSettlement

namespace D5.S3.Quantum.Matrix.ZhangJingPowerCaseSettlement
variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma balanced_block_psd (d : n → ℝ) (hd : ∀ i, 0 ≤ d i) (a : ℝ)
    (ha : 1/2 ≤ a) (ha1 : a < 1) :
    (fromBlocks (diagonal (fun i => ((d i ^ (2*a) : ℝ) : ℂ)))
      (diagonal (fun i => (d i : ℂ))) (diagonal (fun i => (d i : ℂ)))
      (diagonal (fun i => ((d i ^ (2*(1-a)) : ℝ) : ℂ)))).PosSemidef := by
  let X : Matrix n n ℂ := diagonal (fun i => ((d i ^ a : ℝ) : ℂ))
  let Y : Matrix n n ℂ := diagonal (fun i => ((d i ^ (1-a) : ℝ) : ℂ))
  have hX : Xᴴ = X := by simp [X, diagonal_conjTranspose]
  have hY : Yᴴ = Y := by simp [Y, diagonal_conjTranspose]
  have hXX : X * X = diagonal (fun i => ((d i ^ (2*a) : ℝ) : ℂ)) := by
    rw [show X * X = diagonal (fun i => ((d i ^ a : ℝ) : ℂ) * ((d i ^ a : ℝ) : ℂ)) by
      exact diagonal_mul_diagonal _ _]
    congr 1; funext i
    rw [← Complex.ofReal_mul, ← Real.rpow_add' (hd i) (by linarith : a+a ≠ 0)]
    congr 2; ring
  have hYY : Y * Y = diagonal (fun i => ((d i ^ (2*(1-a)) : ℝ) : ℂ)) := by
    rw [show Y * Y = diagonal (fun i => ((d i ^ (1-a) : ℝ) : ℂ) * ((d i ^ (1-a) : ℝ) : ℂ)) by
      exact diagonal_mul_diagonal _ _]
    congr 1; funext i
    rw [← Complex.ofReal_mul, ← Real.rpow_add' (hd i) (by linarith : (1-a)+(1-a) ≠ 0)]
    congr 2; ring
  have hXY : X * Y = diagonal (fun i => (d i : ℂ)) := by
    change diagonal _ * diagonal _ = _
    rw [diagonal_mul_diagonal]
    congr 1; funext i
    rw [← Complex.ofReal_mul, ← Real.rpow_add' (hd i) (by ring_nf; norm_num : a+(1-a) ≠ 0)]
    simp
  have hYX : Y * X = diagonal (fun i => (d i : ℂ)) := by
    simpa [X, Y, diagonal_mul_diagonal, mul_comm] using hXY
  have h := posSemidef_conjTranspose_mul_self (fromBlocks X Y (0 : Matrix n n ℂ) 0)
  simpa only [fromBlocks_conjTranspose, fromBlocks_multiply, hX, hY,
    conjTranspose_zero, zero_mul, mul_zero, add_zero, hXX, hYY, hXY, hYX] using h

private lemma diagonal_schur_forces_commute (U : Matrix.unitaryGroup n ℂ) (d : n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (a : ℝ) (ha : 1/2 ≤ a) (ha1 : a < 1)
    (h : (fromBlocks (diagonal (fun i => ((d i ^ (2*a) : ℝ) : ℂ)))
      (diagonal (fun i => (d i : ℂ))) (diagonal (fun i => (d i : ℂ)))
      (star (U : Matrix n n ℂ) * diagonal (fun i => ((d i ^ (2*(1-a)) : ℝ) : ℂ)) *
        (U : Matrix n n ℂ))).PosSemidef) :
    (U : Matrix n n ℂ) * diagonal (fun i => (d i : ℂ)) =
      diagonal (fun i => (d i : ℂ)) * (U : Matrix n n ℂ) := by
  let F : Matrix n n ℂ := diagonal (fun i => ((d i ^ (2*a) : ℝ) : ℂ))
  let D : Matrix n n ℂ := diagonal (fun i => (d i : ℂ))
  let G : Matrix n n ℂ := diagonal (fun i => ((d i ^ (2*(1-a)) : ℝ) : ℂ))
  let P : Matrix n n ℂ := diagonal (fun i => ((d i ^ (1-2*a) : ℝ) : ℂ))
  let H : Matrix n n ℂ := star (U : Matrix n n ℂ) * G * (U : Matrix n n ℂ)
  have hP : Pᴴ = P := by simp [P, diagonal_conjTranspose]
  have hPF : P * F = D := by
    change diagonal _ * diagonal _ = _
    rw [diagonal_mul_diagonal]
    congr 1; funext i
    exact_mod_cast (by simpa [mul_comm] using (rpow_factor (d i) a (hd i) ha ha1).1)
  have hPD : P * D = G := by
    change diagonal _ * diagonal _ = _
    rw [diagonal_mul_diagonal]
    congr 1; funext i
    exact_mod_cast (rpow_factor (d i) a (hd i) ha ha1).2
  let L : Matrix (n ⊕ n) (n ⊕ n) ℂ := fromBlocks (-P) 0 1 0
  have hschur := h.conjTranspose_mul_mul_same L
  have hcompute : Lᴴ * fromBlocks F D D H * L = fromBlocks (H-G) 0 0 0 := by
    simp [L, fromBlocks_conjTranspose, fromBlocks_multiply, hP, hPF, hPD,
      sub_eq_add_neg, add_comm]
  change (Lᴴ * fromBlocks F D D H * L).PosSemidef at hschur
  rw [hcompute] at hschur
  have hdiff : (H-G).PosSemidef := by
    convert hschur.submatrix (Sum.inl : n → n ⊕ n) using 1
    ext i j
    rfl
  have ht : (H-G).trace = 0 := by
    dsimp [H]
    rw [trace_sub, unitary_conjugate_trace, sub_self]
  have he : H = G := sub_eq_zero.mp (hdiff.trace_eq_zero_iff.mp ht)
  have hcomm : (U : Matrix n n ℂ) * G = G * (U : Matrix n n ℂ) :=
    (commute_unitary_iff_star_left_conjugate U.prop).mpr he
  exact diag_commute_of_rpow_commute _ d hd (2*(1-a)) (by linarith) hcomm

end D5.S3.Quantum.Matrix.ZhangJingPowerCaseSettlement

namespace D5.S3.Quantum.Matrix.ZhangJingPowerCaseSettlement
variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma block_unitary_mem (V W : Matrix.unitaryGroup n ℂ) :
    fromBlocks (W : Matrix n n ℂ) (0 : Matrix n n ℂ) 0 (V : Matrix n n ℂ) ∈
      Matrix.unitaryGroup (n ⊕ n) ℂ := by
  rw [mem_unitaryGroup_iff']
  simp [star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply,
    ← fromBlocks_one]
  exact ⟨W.prop.1, V.prop.1⟩

private lemma block_svd_coordinates {k : ℕ} (V W : Matrix.unitaryGroup (Fin k) ℂ)
    (d : Fin k → ℝ) (A : Matrix (Fin k) (Fin k) ℂ)
    (hA : A = (V : Matrix (Fin k) (Fin k) ℂ) * diagonal (fun i => (d i : ℂ)) *
      star (W : Matrix (Fin k) (Fin k) ℂ))
    (hD : (CFC.sqrt (Aᴴ * A)) = (W : Matrix (Fin k) (Fin k) ℂ) * diagonal (fun i => (d i : ℂ)) *
      star (W : Matrix (Fin k) (Fin k) ℂ)) (f g : ℝ → ℝ) :
    (block f g A).PosSemidef ↔
      (fromBlocks (diagonal (fun i => (f (d i) : ℂ))) (diagonal (fun i => (d i : ℂ)))
        (diagonal (fun i => (d i : ℂ)))
        (star (((star W * V : Matrix.unitaryGroup (Fin k) ℂ)) : Matrix (Fin k) (Fin k) ℂ) *
          diagonal (fun i => (g (d i) : ℂ)) *
          (((star W * V : Matrix.unitaryGroup (Fin k) ℂ)) : Matrix (Fin k) (Fin k) ℂ))).PosSemidef := by
  let T : Matrix.unitaryGroup (Fin k ⊕ Fin k) ℂ :=
    ⟨fromBlocks (W : Matrix (Fin k) (Fin k) ℂ) 0 0 (V : Matrix (Fin k) (Fin k) ℂ),
      block_unitary_mem V W⟩
  have hW : (W : Matrix (Fin k) (Fin k) ℂ)ᴴ * (W : Matrix (Fin k) (Fin k) ℂ) = 1 := W.prop.1
  have hV : (V : Matrix (Fin k) (Fin k) ℂ)ᴴ * (V : Matrix (Fin k) (Fin k) ℂ) = 1 := V.prop.1
  have hcW (X : Matrix (Fin k) (Fin k) ℂ) :
      (W : Matrix (Fin k) (Fin k) ℂ)ᴴ * ((W : Matrix (Fin k) (Fin k) ℂ) * X) = X :=
    unitary_star_cancel W X
  have hcV (X : Matrix (Fin k) (Fin k) ℂ) :
      (V : Matrix (Fin k) (Fin k) ℂ)ᴴ * ((V : Matrix (Fin k) (Fin k) ℂ) * X) = X :=
    unitary_star_cancel V X
  have hcompute : star (T : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℂ) * block f g A *
      (T : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℂ) =
      fromBlocks (diagonal (fun i => (f (d i) : ℂ))) (diagonal (fun i => (d i : ℂ)))
        (diagonal (fun i => (d i : ℂ)))
        (star (((star W * V : Matrix.unitaryGroup (Fin k) ℂ)) : Matrix (Fin k) (Fin k) ℂ) *
          diagonal (fun i => (g (d i) : ℂ)) *
          (((star W * V : Matrix.unitaryGroup (Fin k) ℂ)) : Matrix (Fin k) (Fin k) ℂ)) := by
    rw [block, hD, cfc_unitary_diagonal, cfc_unitary_diagonal, hA]
    simp [T, star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply,
      conjTranspose_mul, diagonal_conjTranspose, mul_assoc, Pi.star_def, hW, hV, hcW, hcV]
  have hi := (Unitary.isUnit_coe (U := T)).posSemidef_star_left_conjugate_iff
    (x := block f g A)
  rw [hcompute] at hi
  exact hi.symm

private lemma diagonal_block_iff_commute (U : Matrix.unitaryGroup n ℂ) (d : n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (a : ℝ) (ha : 1/2 ≤ a) (ha1 : a < 1) :
    (fromBlocks (diagonal (fun i => ((d i ^ (2*a) : ℝ) : ℂ)))
      (diagonal (fun i => (d i : ℂ))) (diagonal (fun i => (d i : ℂ)))
      (star (U : Matrix n n ℂ) * diagonal (fun i => ((d i ^ (2*(1-a)) : ℝ) : ℂ)) *
        (U : Matrix n n ℂ))).PosSemidef ↔
      (U : Matrix n n ℂ) * diagonal (fun i => (d i : ℂ)) =
        diagonal (fun i => (d i : ℂ)) * (U : Matrix n n ℂ) := by
  constructor
  · exact diagonal_schur_forces_commute U d hd a ha ha1
  · intro hc
    have hc' : Commute (diagonal (fun i => (d i : ℂ))) (U : Matrix n n ℂ) := hc.symm
    have hcg := hc'.cfc_real (fun x : ℝ => x ^ (2*(1-a)))
    rw [D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal] at hcg
    have he := (commute_unitary_iff_star_left_conjugate U.prop).mp hcg.symm
    rw [he]
    exact balanced_block_psd d hd a ha ha1

end D5.S3.Quantum.Matrix.ZhangJingPowerCaseSettlement


namespace D5.S3.Quantum.Matrix.ZhangJingPowerCaseSettlement
open _root_.Matrix
open D5.S3.Quantum.Matrix.ZhangJingBlockNormalityRefutation (block)
open scoped ComplexOrder MatrixOrder

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

theorem below_one : claimBelowOne := by
  intro a ha ha1 n A
  obtain ⟨V, W, d, hd, hA, hD⟩ := svd_abs A
  rw [block_svd_coordinates V W d A hA hD]
  exact (diagonal_block_iff_commute (star W * V) d hd a ha ha1).trans
    (svd_normal_iff V W d hd A hA).symm

end D5.S3.Quantum.Matrix.ZhangJingPowerCaseSettlement
