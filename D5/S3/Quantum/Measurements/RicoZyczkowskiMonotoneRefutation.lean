/- GID: D5/S3/Quantum/Measurements/RicoZyczkowskiMonotoneRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/RicoZyczkowskiMonotoneRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurements/RicoZyczkowskiMonotoneRefutation.claim; result=D5/S3/Quantum/Measurements/RicoZyczkowskiMonotoneRefutation.result; claim=D5/S3/Quantum/Measurements/RicoZyczkowskiMonotoneRefutation.claim
   digest: Commuting blockwise bistochastic dynamics violate the 2-norm prefix bound. -/

/-
proof_shape: result: bind-only
escape_witness: none (pinned positivity and square-root facts plus finite normalization)
admission_basis: open-problem-resolution (#14670; Refuted)
Direct frozen dependencies:
  gid:D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM
  statement_id: sha256:218e2b42c4dc29468db56af33ad277eb32b8ed575533012439ed233131c5efa1
  gid:D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.diagonal_povm
  statement_id: sha256:de0639eb7d2cc0e2744e5c02a6801acaa920144435fb7dd8831281ad678d7430
  gid:D5/S3/Quantum/Matrix/CartesianVariance.frobSq_eq_sum
  statement_id: sha256:41486c053d8cde79073cf7fd478d3eec15c60ab40b220c770f2f8b9d2ae6c459
  gid:D5/S3/Weil/ZetaLinear/PosIndex.frobSq
  statement_id: sha256:a1114d4731d26d6c5ef81acb0a254cdc6e0ed6e629ccb2dcf75d7faa00f4ccce
proof_shape: p_nonneg: bind-only; consumers: P_prob, S_square
proof_shape: b_nonneg: bind-only; consumer: B_bistoch
proof_shape: P_prob: bind-only; consumer: result
proof_shape: Q_prob: bind-only; consumer: result
proof_shape: B_bistoch: bind-only; consumer: result
proof_shape: S_psd: bind-only; consumer: block_product_explicit
proof_shape: S_square: bind-only; consumers: S_sandwich, block_product_explicit
proof_shape: B_S_commute: bind-only; consumer: S_sandwich
proof_shape: S_sandwich: bind-only; consumer: block_product_explicit
proof_shape: IsExplicitBlockProduct: bind-only proposition-valued private def; consumer: block_product
proof_shape: block_product_explicit: bind-only; consumer: block_product
proof_shape: block_product: bind-only; consumer: result
proof_shape: trace_eq_sum: bind-only; consumer: hs_eq_sqrt_sum
proof_shape: hs_eq_sqrt_sum: bind-only; consumer: result
proof_shape: P_hs_sq: bind-only; consumer: result
proof_shape: Q_hs_sq: bind-only; consumer: result
proof_shape: prefix_one: bind-only; consumer: result
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import D5.S3.Quantum.Matrix.CartesianVariance

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
namespace D5.S3.Quantum.Measurements.RicoZyczkowskiMonotoneRefutation

def BlockBistoch {n d : ℕ} (B : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  2 ≤ d ∧ (∀ i j, (B i j).PosSemidef) ∧
  (∀ i, ∑ j, B i j = 1) ∧ (∀ j, ∑ i, B i j = 1)

def IsBlockProduct {n d : ℕ} (B : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ)
    (P Q : Fin n → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ i, Q i = ∑ j, CFC.sqrt (P j) * B i j * CFC.sqrt (P j)

def hs {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  Real.sqrt (RHLinalg.frobSq A)

def claim : Prop :=
  ∀ (n d : ℕ) (P Q : Fin n → Matrix (Fin d) (Fin d) ℂ) (B : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ),
    IsPOVM P → IsPOVM Q → BlockBistoch B → IsBlockProduct B P Q →
    ∀ σ : Equiv.Perm (Fin n), ∃ π : Equiv.Perm (Fin n),
      ∀ k : ℕ, 1 ≤ k → k ≤ n →
        hs (∑ i with i.val < k, (P (π i) - (1 / n : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ))) ≥
        hs (∑ i with i.val < k, (Q (σ i) - (1 / n : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)))

private def IsExplicitBlockProduct {n d : ℕ}
    (B : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ)
    (P Q : Fin n → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ roots : Fin n → Matrix (Fin d) (Fin d) ℂ,
    (∀ j, (roots j).PosSemidef ∧ roots j * roots j = P j) ∧
    ∀ i, Q i = ∑ j, roots j * B i j * roots j

private def p : Fin 3 → Fin 2 → ℝ := ![![5/12, 1/6], ![1/6, 5/12], ![5/12, 5/12]]

private def coordPerm (a : Fin 2) : Equiv.Perm (Fin 3) :=
  if a = 0 then Equiv.swap 0 1 else Equiv.refl _

private def b (i j : Fin 3) (a : Fin 2) : ℝ :=
  (9/10) * (if j = coordPerm a i then 1 else 0) + (1 - 9/10) / 3

private def q (i : Fin 3) (_a : Fin 2) : ℝ := if i = 0 then 11/60 else 49/120

private def P (j : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (fun a => (p j a : ℂ))
private def B (i j : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (fun a => (b i j a : ℂ))
private def Q (i : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (fun a => (q i a : ℂ))
private def S (j : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (fun a => (Real.sqrt (p j a) : ℂ))

private theorem p_nonneg (j : Fin 3) (a : Fin 2) : 0 ≤ p j a := by
  fin_cases j <;> fin_cases a <;> norm_num [p]

private theorem b_nonneg (i j : Fin 3) (a : Fin 2) : 0 ≤ b i j a := by
  fin_cases i <;> fin_cases j <;> fin_cases a <;>
    norm_num [b, coordPerm, Equiv.swap_apply_def, Fin.reduceEq, Fin.reduceFinMk, Fin.reduceSucc]

private theorem P_prob : IsPOVM P := by
  refine D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.diagonal_povm
    (d := 2) (Ω := Fin 3) p p_nonneg ?_
  intro a
  fin_cases a <;> norm_num [p, Fin.sum_univ_succ]

private theorem Q_prob : IsPOVM Q := by
  refine D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.diagonal_povm
    (d := 2) (Ω := Fin 3) q ?_ ?_
  · intro i a
    fin_cases i <;> norm_num [q]
  · intro a
    norm_num [q, Fin.sum_univ_succ]

private theorem B_bistoch : BlockBistoch B := by
  have row (i : Fin 3) : IsPOVM (B i) := by
    refine D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.diagonal_povm
      (d := 2) (Ω := Fin 3) (b i) (b_nonneg i) ?_
    intro a
    fin_cases i <;> fin_cases a <;>
      norm_num [b, coordPerm, Equiv.swap_apply_def, Fin.reduceEq, Fin.reduceFinMk,
        Fin.reduceSucc, Fin.sum_univ_succ] <;>
      simp only [Fin.ext_iff] <;> norm_num
  have column (j : Fin 3) : IsPOVM (fun i => B i j) := by
    refine D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.diagonal_povm
      (d := 2) (Ω := Fin 3) (fun i a => b i j a) (fun i a => b_nonneg i j a) ?_
    intro a
    fin_cases j <;> fin_cases a <;>
      norm_num [b, coordPerm, Equiv.swap_apply_def, Fin.reduceEq, Fin.reduceFinMk,
        Fin.reduceSucc, Fin.sum_univ_succ] <;>
      simp only [Fin.ext_iff] <;> norm_num
  exact ⟨by norm_num, fun i j => (row i).1 j, fun i => (row i).2, fun j => (column j).2⟩

private theorem S_psd (j : Fin 3) : (S j).PosSemidef :=
  Matrix.PosSemidef.diagonal (fun _a => Complex.zero_le_real.mpr (Real.sqrt_nonneg _))

private theorem S_square (j : Fin 3) : S j * S j = P j := by
  unfold S P
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (p_nonneg j a)]

private theorem B_S_commute (i j : Fin 3) : Commute (B i j) (S j) :=
  Matrix.commute_diagonal _ _

private theorem S_sandwich (i j : Fin 3) :
    S j * B i j * S j = Matrix.diagonal (fun a => ((p j a * b i j a : ℝ) : ℂ)) := by
  calc
    S j * B i j * S j = S j * (B i j * S j) := Matrix.mul_assoc _ _ _
    _ = S j * (S j * B i j) := by rw [(B_S_commute i j).eq]
    _ = P j * B i j := by rw [← Matrix.mul_assoc, S_square]
    _ = Matrix.diagonal (fun a => ((p j a * b i j a : ℝ) : ℂ)) := by
      unfold P B
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext a
      exact (Complex.ofReal_mul _ _).symm

private theorem block_product_explicit : IsExplicitBlockProduct B P Q := by
  refine ⟨S, fun j => ⟨S_psd j, S_square j⟩, ?_⟩
  intro i
  simp_rw [S_sandwich]
  ext a c
  simp only [Matrix.sum_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  fin_cases i <;> fin_cases a <;> fin_cases c <;>
    norm_num [Q, q, p, b, coordPerm, Equiv.swap_apply_def, Fin.reduceEq, Fin.reduceFinMk, Fin.reduceSucc,
      Fin.sum_univ_succ, Matrix.diagonal_apply, Matrix.cons_val_two] <;>
      simp only [Fin.ext_iff] <;> norm_num

private theorem block_product : IsBlockProduct B P Q := by
  obtain ⟨roots, hroots, hQ⟩ := block_product_explicit
  have principal_root (j : Fin 3) : CFC.sqrt (P j) = roots j :=
    CFC.sqrt_unique (hroots j).2 (hroots j).1.nonneg
  intro i
  simp_rw [principal_root]
  exact hQ i

private theorem trace_eq_sum {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    Complex.re (Matrix.trace (Aᴴ * A)) = ∑ a, ∑ b, ‖A a b‖ ^ 2 := by
  have h := D5.S3.Quantum.Matrix.CartesianVariance.frobSq_eq_sum A
  rw [Finset.sum_comm] at h
  simpa only [RHLinalg.frobSq, RCLike.re_eq_complex_re,
    Complex.normSq_eq_norm_sq] using h

private theorem hs_eq_sqrt_sum {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    hs A = Real.sqrt (∑ a, ∑ b, ‖A a b‖ ^ 2) := by
  change Real.sqrt (Complex.re (Matrix.trace (Aᴴ * A))) = _
  rw [trace_eq_sum]

private theorem P_hs_sq (j : Fin 3) :
    (∑ a, ∑ b, ‖(P j - (1/3 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) a b‖ ^ 2) ≤ 5/144 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp only [Complex.sq_norm, Complex.normSq_apply]
  fin_cases j <;>
    norm_num [P, p, Matrix.diagonal_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]

private theorem Q_hs_sq :
    (∑ a, ∑ b, ‖(Q 0 - (1/3 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) a b‖ ^ 2) = 9/200 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp only [Complex.sq_norm, Complex.normSq_apply]
  norm_num [Q, q, Matrix.diagonal_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]

private theorem prefix_one (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ i with i.val < 1, V i) = V 0 := by
  rw [show (Finset.univ.filter fun i : Fin 3 => i.val < 1) = {0} by decide]
  simp

theorem result : ¬ claim := by
  intro h
  obtain ⟨π, hπ⟩ := h 3 2 P Q B P_prob Q_prob B_bistoch
    block_product (Equiv.refl _)
  have h1 := hπ 1 (by norm_num) (by norm_num)
  simp only [prefix_one, Equiv.refl_apply] at h1
  norm_num only [Nat.cast_ofNat] at h1
  simp_rw [hs_eq_sqrt_sum] at h1
  rw [Q_hs_sq] at h1
  have hp := Real.sqrt_le_sqrt (P_hs_sq (π 0))
  have hgap : Real.sqrt (5/144) < Real.sqrt (9/200) :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

end D5.S3.Quantum.Measurements.RicoZyczkowskiMonotoneRefutation
