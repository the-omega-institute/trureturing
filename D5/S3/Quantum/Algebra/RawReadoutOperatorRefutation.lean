/- GID: D5/S3/Quantum/Algebra/RawReadoutOperatorRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/RawReadoutOperatorRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/RawReadoutOperatorRefutation.claim; result=D5/S3/Quantum/Algebra/RawReadoutOperatorRefutation.result; claim=D5/S3/Quantum/Algebra/RawReadoutOperatorRefutation.claim
   digest: The six seminorm conditions do not lift quotient operator identities to the raw algebra. -/

import Mathlib.Analysis.Quaternion
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Prod
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

/-! A seminorm can hide both operator defects on an associative product algebra. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Quantum.Algebra.RawReadoutOperatorRefutation

/-- The original bracketed synthesis operator for a real bilinear multiplication. -/
def synthesis {V : Type} [AddCommGroup V] [Module ℝ V]
    (m : V →ₗ[ℝ] V →ₗ[ℝ] V) (a b c : V) : V :=
  m (m a b - m b a) c + m a (m b c) - m b (m a c)

/-- The original projection expression, using the square of the same seminorm. -/
def projection {V : Type} [AddCommGroup V] [Module ℝ V]
    (m : V →ₗ[ℝ] V →ₗ[ℝ] V) (p : V → ℝ) (a b c : V) : V :=
  (-(1 / (2 * p (m a b - m b a) ^ 2))) •
    m (m a b - m b a) (synthesis m a b c)

/-- B1 is the bilinear type of m; B2, E, N, U_p and F use the same raw variables. -/
def Candidate {V : Type} [AddCommGroup V] [Module ℝ V]
    (m : V →ₗ[ℝ] V →ₗ[ℝ] V) (p : V → ℝ) (e a b : V) : Prop :=
  (∀ x, 0 ≤ p x) ∧
  (∀ (t : ℝ) x, p (t • x) = |t| * p x) ∧
  (∀ x y, p (x + y) ≤ p x + p y) ∧
  (∃ x, 0 < p x) ∧
  (∀ x y, p (m x y) = p x * p y) ∧
  (∀ x, p (m e x - x) + p (m x e - x) = 0) ∧
  (∀ c, p (synthesis m a b c) = 0 → p c = 0)

/-- The raw lifting inference denied by the raw-versus-quotient counterexample. -/
def claim : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V]
    (m : V →ₗ[ℝ] V →ₗ[ℝ] V) (p : V → ℝ) (e a b : V),
    Candidate m p e a b →
      (∀ c, synthesis m a b (synthesis m a b (synthesis m a b c)) =
        (-(4 * p (m a b - m b a) ^ 2)) • synthesis m a b c) ∧
      (∀ c, projection m p a b (projection m p a b c) = projection m p a b c)

private abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
private abbrev Raw := Quaternion ℝ × Mat
private def A : Mat := !![0, 1, 0; 0, 0, 1; 0, 0, 0]
private def B : Mat := !![0, 0, 0; 1, 0, 0; 0, 2, 0]
private def K : Mat := Matrix.diagonal ![1, 1, -2]
private def qi : Quaternion ℝ := ⟨0, 1, 0, 0⟩
private def qj : Quaternion ℝ := ⟨0, 0, 1, 0⟩
private def qk : Quaternion ℝ := ⟨0, 0, 0, 1⟩
private def a : Raw := (qi, A)
private def b : Raw := (qj, B)
private def p (c : Raw) : ℝ := ‖c.1‖
private def m : Raw →ₗ[ℝ] Raw →ₗ[ℝ] Raw := LinearMap.mul ℝ Raw
private def k : Raw := a * b - b * a
private def T (c : Raw) : Raw := synthesis m a b c
private def P (c : Raw) : Raw := projection m p a b c
private def readout : Raw →ₐ[ℝ] Quaternion ℝ := AlgHom.fst ℝ _ _
private abbrev N : Ideal Raw := RingHom.ker readout
private abbrev Readable := Raw ⧸ N

private def quotientEquiv : Readable ≃ₐ[ℝ] Quaternion ℝ :=
  Ideal.quotientKerAlgEquivOfSurjective (fun h => ⟨(h, 0), rfl⟩)
private def quotientT (x : Readable) : Readable :=
  quotientEquiv.symm ((4 : ℝ) • (qk * quotientEquiv x))
private def quotientP (x : Readable) : Readable := x

private lemma k_value : k = ((2 : ℝ) • qk, K) := by
  apply Prod.ext
  · ext <;> norm_num [k, a, b, qi, qj, qk]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [k, a, b, A, B, K, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma qk_square : qk * qk = -1 := by
  ext <;> norm_num [qk]

private lemma norm_qk : ‖qk‖ = 1 := by
  have h : ‖qk‖ * ‖qk‖ = 1 := by
    rw [← Quaternion.normSq_eq_norm_mul_self]
    norm_num [Quaternion.normSq_def', qk]
  nlinarith [norm_nonneg qk]

private lemma q_k : p k ^ 2 = 4 := by
  rw [k_value]
  norm_num [p, norm_smul, norm_qk]

private lemma t_action (c : Raw) : T c = ((4 : ℝ) • (qk * c.1), (2 : ℝ) • (K * c.2)) := by
  have ht : T c = (2 : ℝ) • (k * c) := by
    dsimp [T, synthesis, m, k]
    simp only [sub_mul, mul_assoc, two_smul]
    abel
  rw [ht, k_value]
  apply Prod.ext <;> norm_num [smul_smul]

private lemma p_action (c : Raw) : P c = (c.1, (-(1 / 4) : ℝ) • (K * (K * c.2))) := by
  change (-(1 / (2 * p k ^ 2))) • (k * T c) = _
  rw [q_k, k_value, t_action]
  apply Prod.ext
  · norm_num [smul_smul, ← mul_assoc, qk_square]
  · simp [smul_smul]

private lemma p_t (c : Raw) : p (T c) = 4 * p c := by
  rw [t_action]
  simp [p, norm_smul, norm_mul, norm_qk]

private lemma candidates : Candidate m p (1 : Raw) a b := by
  refine ⟨fun x => norm_nonneg _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t x
    exact norm_smul t x.1
  · intro x y
    exact norm_add_le x.1 y.1
  · exact ⟨1, by norm_num [p]⟩
  · intro x y
    exact norm_mul x.1 y.1
  · intro x
    simp [m, p]
  · intro c hc
    change p (T c) = 0 at hc
    rw [p_t] at hc
    linarith

private lemma kernel_iff (c : Raw) : c ∈ N ↔ p c = 0 := by
  change readout c = 0 ↔ ‖c.1‖ = 0
  simp [readout]

private lemma cubic_fst (c : Raw) :
    (T (T (T c)) + (16 : ℝ) • T c).1 = 0 := by
  simp only [t_action, Prod.fst_add, mul_smul_comm,
    smul_smul, ← mul_assoc, qk_square]
  simp
  <;> module

private lemma projector_fst (c : Raw) : (P (P c) - P c).1 = 0 := by
  simp only [p_action, Prod.fst_sub, sub_self]

private lemma defects_in_kernel (c : Raw) :
    T (T (T c)) + (16 : ℝ) • T c ∈ N ∧ P (P c) - P c ∈ N := by
  constructor
  · change (T (T (T c)) + (16 : ℝ) • T c).1 = 0
    exact cubic_fst c
  · change (P (P c) - P c).1 = 0
    exact projector_fst c

private lemma cubic_failure :
    T (T (T (0, 1))) + (16 : ℝ) • T (0, 1) =
      (0, Matrix.diagonal ![40, 40, -128]) := by
  apply Prod.ext
  · exact cubic_fst (0, 1)
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [t_action, K, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma projector_failure :
    P (P (0, 1)) - P (0, 1) = (0, Matrix.diagonal ![5/16, 5/16, 2]) := by
  apply Prod.ext
  · exact projector_fst (0, 1)
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [p_action, K, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma quotient_map_T (c : Raw) :
    Ideal.Quotient.mk N (T c) = quotientT (Ideal.Quotient.mk N c) := by
  apply quotientEquiv.injective
  change (T c).1 = quotientEquiv (quotientEquiv.symm
    ((4 : ℝ) • (qk * quotientEquiv (Ideal.Quotient.mk N c))))
  rw [AlgEquiv.apply_symm_apply]
  change (T c).1 = (4 : ℝ) • (qk * c.1)
  exact congrArg Prod.fst (t_action c)

private lemma quotient_map_P (c : Raw) :
    Ideal.Quotient.mk N (P c) = quotientP (Ideal.Quotient.mk N c) := by
  apply quotientEquiv.injective
  change (P c).1 = c.1
  exact congrArg Prod.fst (p_action c)

private lemma quotient_cubic (x : Readable) :
    quotientT (quotientT (quotientT x)) = (-16 : ℝ) • quotientT x := by
  apply quotientEquiv.injective
  simp [quotientT, smul_smul, ← mul_assoc, qk_square]
  <;> module

/-- All clauses concern the same product algebra, witnesses, seminorm and quotient kernel. -/
def Certificate : Prop :=
  Candidate m p (1 : Raw) a b ∧
  (∀ c : Raw, p c ^ 2 = Quaternion.normSq c.1) ∧
  (∀ c : Raw, c ∈ N ↔ c.1 = 0) ∧
  (∀ c : Raw, c ∈ N ↔ p c = 0) ∧
  k = ((2 : ℝ) • qk, K) ∧ p k ^ 2 = 4 ∧
  (∀ c, T c = ((4 : ℝ) • (qk * c.1), (2 : ℝ) • (K * c.2))) ∧
  (∀ c, P c = (c.1, (-(1 / 4) : ℝ) • (K * (K * c.2)))) ∧
  (∀ c, T (T (T c)) + (16 : ℝ) • T c ∈ N ∧ P (P c) - P c ∈ N) ∧
  T (T (T (0, 1))) + (16 : ℝ) • T (0, 1) =
    (0, Matrix.diagonal ![40, 40, -128]) ∧
  P (P (0, 1)) - P (0, 1) = (0, Matrix.diagonal ![5/16, 5/16, 2]) ∧
  T (T (T (0, 1))) + (16 : ℝ) • T (0, 1) ≠ 0 ∧
  P (P (0, 1)) - P (0, 1) ≠ 0 ∧
  (∀ c : Raw, quotientEquiv (Ideal.Quotient.mk N c) = c.1) ∧
  (∀ c, Ideal.Quotient.mk N (T c) = quotientT (Ideal.Quotient.mk N c)) ∧
  (∀ c, Ideal.Quotient.mk N (P c) = quotientP (Ideal.Quotient.mk N c)) ∧
  (∀ x, quotientT (quotientT (quotientT x)) = (-16 : ℝ) • quotientT x) ∧
  (∀ x, quotientP (quotientP x) = quotientP x)

/-- The simultaneous original-domain countermodel and its exact same-kernel quotient. -/
theorem raw_counterexample_certificate : Certificate := by
  refine ⟨candidates, ?_, ?_, kernel_iff, k_value, q_k, t_action, p_action,
    defects_in_kernel, cubic_failure, projector_failure, ?_, ?_, ?_,
    quotient_map_T, quotient_map_P, quotient_cubic, fun _ => rfl⟩
  · intro c
    rw [Quaternion.normSq_eq_norm_mul_self, pow_two]
    rfl
  · intro c
    rfl
  · rw [cubic_failure]
    intro h
    have hentry := congrArg (fun c : Raw => c.2 0 0) h
    norm_num [Matrix.diagonal] at hentry
  · rw [projector_failure]
    intro h
    have hentry := congrArg (fun c : Raw => c.2 0 0) h
    norm_num [Matrix.diagonal] at hentry
  · intro c
    rfl

/-- Six conditions suffice only for quotient identities, not their exact raw lifts. -/
theorem result : ¬ claim := by
  intro h
  rcases raw_counterexample_certificate with
    ⟨hcand, _, _, _, _, hq, _, _, _, _, _, bad, _, _, _, _, _, _⟩
  have hraw := h Raw m p 1 a b hcand
  apply bad
  change T (T (T (0, 1))) + (16 : ℝ) • T (0, 1) = 0
  have hc := hraw.1 (0, 1)
  change T (T (T (0, 1))) = (-(4 * p k ^ 2)) • T (0, 1) at hc
  rw [q_k] at hc
  rw [hc]
  norm_num

end D5.S3.Quantum.Algebra.RawReadoutOperatorRefutation
