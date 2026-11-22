/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformHardCoreBaseLocus
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformHardCoreBaseLocus
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Zero locus of periodic bond-two trace words. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformZeroCorner
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! The degree-`n` base locus of the binary bond-two trace map on realized cores. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreBaseLocus

open PeriodicMPSParentIntersection (Bond Word)
open PeriodicMPSUniformZeroCorner
  (listTrace listTrace_eq_of_invariants listTrace_eq_zero_of_odd_of_traceless)
open UniformMPSExpectedDimensionRefutation (traceWord)
open D5.S0.Observation.MatrixTracePowerSum (trace_pow_add_two)
open Polynomial
open scoped Matrix

noncomputable section

/-- The power-sum polynomial in the determinant with trace fixed to `t`. -/
def tracePowerPolynomial (t : ℂ) : ℕ → ℂ[X]
  | 0 => C 2
  | 1 => C t
  | n + 2 => C t * tracePowerPolynomial t (n + 1) - X * tracePowerPolynomial t n

theorem trace_pow_eq_eval (A : Bond) (n : ℕ) :
    (A ^ n).trace = (tracePowerPolynomial A.trace n).eval A.det := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [tracePowerPolynomial, Matrix.trace_one, Fintype.card_fin]
  | one => simp [tracePowerPolynomial]
  | more n ih₀ ih₁ =>
    rw [trace_pow_add_two, ih₀, ih₁, tracePowerPolynomial]
    simp

private theorem tracePowerPolynomial_one_eval_zero (n : ℕ) :
    (tracePowerPolynomial 1 (n + 1)).eval 0 = 1 := by
  induction n with
  | zero => simp [tracePowerPolynomial]
  | succ n ih => simp [tracePowerPolynomial, ih]

private theorem tracePowerPolynomial_one_ne_zero {n : ℕ} (hn : 0 < n) :
    tracePowerPolynomial 1 n ≠ 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  intro h
  have he := tracePowerPolynomial_one_eval_zero k
  simp [h] at he

/-- The homogeneous determinant pencil in the five trace invariants. -/
theorem det_pencil (A B : Bond) (x y : ℂ) :
    (x • A + y • B).det =
      A.det * x ^ 2 + (A.trace * B.trace - (A * B).trace) * x * y + B.det * y ^ 2 := by
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private def detPencilPolynomial (A B : Bond) : ℂ[X] :=
  C A.det + C (A.trace * B.trace - (A * B).trace) * X + C B.det * X ^ 2

private theorem eval_detPencilPolynomial (A B : Bond) (z : ℂ) :
    (detPencilPolynomial A B).eval z = (A + z • B).det := by
  simpa [detPencilPolynomial] using (det_pencil A B 1 z).symm

private theorem detPencilPolynomial_coeff_one (A B : Bond) :
    (detPencilPolynomial A B).coeff 1 = A.trace * B.trace - (A * B).trace := by
  simp [detPencilPolynomial, coeff_add, coeff_C]

private theorem detPencilPolynomial_coeff_two (A B : Bond) :
    (detPencilPolynomial A B).coeff 2 = B.det := by
  simp [detPencilPolynomial, coeff_add]

private theorem coefficients_of_constant_detPencil (A B : Bond) {d : ℂ}
    (h : detPencilPolynomial A B = C d) :
    A.trace * B.trace - (A * B).trace = 0 ∧ B.det = 0 := by
  constructor
  · simpa [detPencilPolynomial_coeff_one] using congrArg (fun p : ℂ[X] => p.coeff 1) h
  · simpa [detPencilPolynomial_coeff_two] using congrArg (fun p : ℂ[X] => p.coeff 2) h

/-- In the normalized trace chart, pure-power vanishing forces the determinant
pencil to be constant. Its two nonconstant coefficients are the mixed trace
up to sign and the determinant of the traceless generator. -/
theorem trace_one_base_of_pure_pencil (A B : Bond) {n : ℕ} (hn : 0 < n)
    (hA : A.trace = 1) (hB : B.trace = 0)
    (h : ∀ z : ℂ, ((A + z • B) ^ n).trace = 0) :
    (tracePowerPolynomial 1 n).eval A.det = 0 ∧ B.det = 0 ∧ (A * B).trace = 0 := by
  have hcomp : (tracePowerPolynomial 1 n).comp (detPencilPolynomial A B) = 0 := by
    apply Polynomial.funext
    intro z
    have ht : (A + z • B).trace = 1 := by simp [Matrix.trace_add, Matrix.trace_smul, hA, hB]
    rw [eval_comp, eval_detPencilPolynomial, eval_zero, ← ht, ← trace_pow_eq_eval, h z]
  obtain ⟨_, hconst⟩ := (comp_eq_zero_iff.mp hcomp).resolve_left
    (tracePowerPolynomial_one_ne_zero hn)
  obtain ⟨hm, hd⟩ := coefficients_of_constant_detPencil A B hconst
  refine ⟨?_, hd, ?_⟩
  · simpa [trace_pow_eq_eval, hA] using h 0
  · simpa [hB] using hm

/-- The even power trace of a traceless matrix is a nonzero scalar times
a power of its determinant. -/
theorem trace_even_pow_of_traceless (A : Bond) (hA : A.trace = 0) (m : ℕ) :
    (A ^ (2 * m)).trace = 2 * (-A.det) ^ m := by
  induction m with
  | zero => norm_num [Matrix.trace_one, Fintype.card_fin]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, trace_pow_add_two, hA, zero_mul, zero_sub,
      ih, pow_succ]
    ring

private theorem trace_mul_pow_eq_zero_of_word_traces (P : Fin 2 → Bond) (x y : ℂ)
    (n : ℕ) (M : Bond)
    (h : ∀ w : List (Fin 2), w.length = n → (M * (w.map P).prod).trace = 0) :
    (M * (x • P 0 + y • P 1) ^ n).trace = 0 := by
  induction n generalizing M with
  | zero => simpa using h [] rfl
  | succ n ih =>
    let N := (x • P 0 + y • P 1) ^ n
    have step (i : Fin 2) : (M * P i * N).trace = 0 := by
      apply ih (M * P i)
      intro w hw
      simpa only [List.map_cons, List.prod_cons, mul_assoc] using
        h (i :: w) (by simp [hw])
    rw [pow_succ', ← mul_assoc, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.add_mul, smul_mul_assoc, smul_mul_assoc, Matrix.trace_add, Matrix.trace_smul,
      Matrix.trace_smul, step 0, step 1]
    simp

private theorem traceWord_eq_listTrace (P : Fin 2 → Bond) {n : ℕ} (w : Word n) :
    traceWord 2 2 n P w = listTrace P (List.ofFn w) := by
  simp only [traceWord, listTrace, List.map_ofFn, Function.comp_def]

/-- Every pure pencil power is a linear combination of the ordered binary
word traces of the same length. -/
theorem pure_pencil_zero_of_traceWord_zero (P : Fin 2 → Bond) {n : ℕ}
    (h : traceWord 2 2 n P = 0) (x y : ℂ) :
    ((x • P 0 + y • P 1) ^ n).trace = 0 := by
  have hlists (w : List (Fin 2)) (hw : w.length = n) : listTrace P w = 0 := by
    subst n
    simpa [traceWord_eq_listTrace] using congrFun h w.get
  simpa only [one_mul] using trace_mul_pow_eq_zero_of_word_traces P x y n 1
    (by simpa only [one_mul, listTrace] using hlists)

/-- The invariant equations defining the degree-`n` base locus. With a nonzero
trace covector the determinant pencil is a constant times its square. With
zero trace covector odd lengths impose no further equations, and even positive
lengths require the zero determinant pencil. -/
def BaseInvariants (n : ℕ) (t s d e k : ℂ) : Prop :=
  ((t ≠ 0 ∨ s ≠ 0) ∧ ∃ δ : ℂ, (tracePowerPolynomial 1 n).eval δ = 0 ∧
    d = δ * t ^ 2 ∧ e = δ * s ^ 2 ∧ k = (1 - 2 * δ) * t * s) ∨
  (t = 0 ∧ s = 0 ∧ (Odd n ∨ d = 0 ∧ e = 0 ∧ k = 0))

private theorem exists_normalized_det_of_pure_pencil (A B : Bond)
    {n : ℕ} (hn : 0 < n) (hA : A.trace ≠ 0)
    (h : ∀ x y : ℂ, ((x • A + y • B) ^ n).trace = 0) :
    ∃ δ : ℂ, (tracePowerPolynomial 1 n).eval δ = 0 ∧
      A.det = δ * A.trace ^ 2 ∧ B.det = δ * B.trace ^ 2 ∧
      (A * B).trace = (1 - 2 * δ) * A.trace * B.trace := by
  let U : Bond := A.trace⁻¹ • A
  let V : Bond := B - B.trace • U
  have hU : U.trace = 1 := by simp [U, Matrix.trace_smul, smul_eq_mul, hA]
  have hV : V.trace = 0 := by simp [V, Matrix.trace_sub, Matrix.trace_smul, hU]
  have hp (z : ℂ) : ((U + z • V) ^ n).trace = 0 := by
    have he : U + z • V = ((1 - z * B.trace) * A.trace⁻¹) • A + z • B := by
      dsimp only [U, V]
      module
    rw [he]
    exact h _ _
  obtain ⟨hroot, hdV, hm⟩ := trace_one_base_of_pure_pencil U V hn hU hV hp
  have hA' : A.trace • U = A := by simp [U, smul_smul, hA]
  have hB' : B.trace • U + (1 : ℂ) • V = B := by
    rw [one_smul]
    dsimp only [V]
    abel
  have hdet (x y : ℂ) : (x • U + y • V).det = U.det * x ^ 2 := by
    rw [det_pencil]
    simp [hV, hdV, hm]
  have hdA : A.det = U.det * A.trace ^ 2 := by simpa [hA'] using hdet A.trace 0
  have hdB : B.det = U.det * B.trace ^ 2 := by
    calc
      B.det = (B.trace • U + (1 : ℂ) • V).det := congrArg Matrix.det hB'.symm
      _ = U.det * B.trace ^ 2 := hdet B.trace 1
  have hdSum : (A + B).det = U.det * (A.trace + B.trace) ^ 2 := by
    rw [← hdet (A.trace + B.trace) 1, add_smul, add_assoc, hA', hB']
  have hdSum' : (A + B).det = A.det + (A.trace * B.trace - (A * B).trace) + B.det := by
    simpa using det_pencil A B 1 1
  refine ⟨U.det, hroot, hdA, hdB, ?_⟩
  linear_combination hdSum' - hdSum + hdA + hdB

private theorem baseInvariants_of_pure_pencil (P : Fin 2 → Bond) {n : ℕ} (hn : 0 < n)
    (h : ∀ x y : ℂ, ((x • P 0 + y • P 1) ^ n).trace = 0) :
    BaseInvariants n (P 0).trace (P 1).trace (P 0).det (P 1).det (P 0 * P 1).trace := by
  by_cases ht : (P 0).trace = 0
  · by_cases hs : (P 1).trace = 0
    · refine Or.inr ⟨ht, hs, ?_⟩
      rcases Nat.even_or_odd n with he | ho
      · obtain ⟨m, hm⟩ := he
        rw [← two_mul] at hm
        have hdet (x y : ℂ) : (x • P 0 + y • P 1).det = 0 := by
          let M := x • P 0 + y • P 1
          have htM : M.trace = 0 := by simp [M, Matrix.trace_add, Matrix.trace_smul, ht, hs]
          have hz : (M ^ n).trace = 0 := h x y
          rw [hm, trace_even_pow_of_traceless M htM] at hz
          by_contra hd
          exact (pow_ne_zero m (neg_ne_zero.mpr hd))
            ((mul_eq_zero.mp hz).resolve_left (by norm_num))
        have heval : detPencilPolynomial (P 0) (P 1) = C 0 := by
          apply Polynomial.funext
          intro z
          rw [eval_detPencilPolynomial, eval_C]
          simpa using hdet 1 z
        obtain ⟨hmix, hdB⟩ := coefficients_of_constant_detPencil (P 0) (P 1) heval
        exact Or.inr ⟨by simpa using hdet 1 0, hdB, by simpa [ht] using hmix⟩
      · exact Or.inl ho
    · obtain ⟨δ, hr, hd₁, hd₀, hmix⟩ :=
        exists_normalized_det_of_pure_pencil (P 1) (P 0) hn hs
          (fun x y => by rw [add_comm]; exact h y x)
      refine Or.inl ⟨Or.inr hs, δ, hr, hd₀, hd₁, ?_⟩
      rw [Matrix.trace_mul_comm, hmix]
      ring
  · exact Or.inl ⟨Or.inl ht, exists_normalized_det_of_pure_pencil (P 0) (P 1) hn ht h⟩

private theorem listTrace_scaled_core (A : Bond) (t : Fin 2 → ℂ) (w : List (Fin 2)) :
    listTrace (fun i => t i • A) w = (w.map t).prod * (A ^ w.length).trace := by
  have hprod : (w.map (fun i => t i • A)).prod = (w.map t).prod • A ^ w.length := by
    induction w with
    | nil => simp
    | cons i w ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, ih, pow_succ' A]
      rw [smul_mul_assoc, Matrix.mul_smul, smul_smul]
  rw [listTrace, hprod, Matrix.trace_smul, smul_eq_mul]

private theorem traceWord_zero_of_baseInvariants (P : Fin 2 → Bond) {n : ℕ} (hn : 0 < n)
    (h : BaseInvariants n (P 0).trace (P 1).trace (P 0).det (P 1).det (P 0 * P 1).trace) :
    traceWord 2 2 n P = 0 := by
  funext w
  rw [traceWord_eq_listTrace, Pi.zero_apply]
  rcases h with ⟨_, δ, hr, hdA, hdB, hmix⟩ | ⟨ht, hs, ho | ⟨hdA, hdB, hmix⟩⟩
  · let A : Bond := !![1, -δ; 1, 0]
    have hA : A.trace = 1 := by simp [A, Matrix.trace_fin_two]
    have hd : A.det = δ := by simp [A, Matrix.det_fin_two]
    let Q : Fin 2 → Bond := fun i => (P i).trace • A
    have ht (i : Fin 2) : (Q i).trace = (P i).trace := by
      simp [Q, Matrix.trace_smul, hA]
    have hdet (i : Fin 2) : (Q i).det = δ * (P i).trace ^ 2 := by
      change ((P i).trace • A).det = _
      rw [Matrix.det_smul, Fintype.card_fin, hd, mul_comm]
    have hsq : (A * A).trace = 1 - 2 * δ := by
      have hrec := trace_pow_add_two A 0
      norm_num [pow_two, hA, hd, Matrix.trace_one, Fintype.card_fin] at hrec
      linear_combination hrec
    have hm : (Q 0 * Q 1).trace = (1 - 2 * δ) * (P 0).trace * (P 1).trace := by
      simp only [Q, smul_mul_assoc, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, hsq]
      ring
    rw [listTrace_eq_of_invariants P Q (ht 0).symm (ht 1).symm (hdA.trans (hdet 0).symm)
      (hdB.trans (hdet 1).symm) (hmix.trans hm.symm)]
    rw [show Q = (fun i => (P i).trace • A) from rfl, listTrace_scaled_core,
      List.length_ofFn, trace_pow_eq_eval, hA, hd, hr, mul_zero]
  · exact listTrace_eq_zero_of_odd_of_traceless P ht hs _ (by simpa using ho)
  · let Q : Fin 2 → Bond := fun i => (0 : ℂ) • (0 : Bond)
    rw [listTrace_eq_of_invariants P Q (by simpa [Q] using ht) (by simpa [Q] using hs)
      (by simpa [Q] using hdA) (by simpa [Q] using hdB) (by simpa [Q] using hmix)]
    rw [show Q = (fun _ : Fin 2 => (0 : ℂ) • (0 : Bond)) from rfl, listTrace_scaled_core,
      List.length_ofFn, zero_pow hn.ne', Matrix.trace_zero, mul_zero]

/-- Pure traces of the full pencil detect the entire trace base locus of a
realized pair at every positive length. -/
theorem pure_pencil_zero_iff_baseInvariants (P : Fin 2 → Bond) {n : ℕ} (hn : 0 < n) :
    (∀ x y : ℂ, ((x • P 0 + y • P 1) ^ n).trace = 0) ↔
      BaseInvariants n (P 0).trace (P 1).trace (P 0).det (P 1).det (P 0 * P 1).trace :=
  ⟨baseInvariants_of_pure_pencil P hn,
    fun h => pure_pencil_zero_of_traceWord_zero P (traceWord_zero_of_baseInvariants P hn h)⟩

/-- Classification of the base locus in the five trace invariants of the
actual matrix pair `P`. At a nonzero weighted invariant point, the all-zero
invariant vertex in the even, traceless case is excluded. -/
theorem traceWord_zero_iff_baseInvariants (P : Fin 2 → Bond) {n : ℕ} (hn : 0 < n) :
    traceWord 2 2 n P = 0 ↔
      BaseInvariants n (P 0).trace (P 1).trace (P 0).det (P 1).det (P 0 * P 1).trace :=
  ⟨fun h => baseInvariants_of_pure_pencil P hn (pure_pencil_zero_of_traceWord_zero P h),
    traceWord_zero_of_baseInvariants P hn⟩

/-- Vanishing on all pure pencil powers is equivalent to vanishing of the
complete degree-`n` binary trace tensor. -/
theorem traceWord_zero_iff_pure_pencil_zero (P : Fin 2 → Bond) {n : ℕ} (hn : 0 < n) :
    traceWord 2 2 n P = 0 ↔ ∀ x y : ℂ, ((x • P 0 + y • P 1) ^ n).trace = 0 :=
  (traceWord_zero_iff_baseInvariants P hn).trans (pure_pencil_zero_iff_baseInvariants P hn).symm

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreBaseLocus
