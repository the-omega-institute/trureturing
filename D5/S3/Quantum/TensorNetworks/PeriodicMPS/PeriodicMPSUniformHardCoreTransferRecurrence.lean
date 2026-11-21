/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreTransferRecurrence
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreTransferRecurrence
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteAmbiguity]
   utility: none
   digest: The order-r raw two-site coefficient is determined from 2(r+1) consecutive lengths by a power of the Fibonacci characteristic polynomial. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteAmbiguity
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite comparison of periodic two-site transfer coefficients

The polynomial variable in the transfer matrices is the jet parameter. The
polynomial used as the characteristic polynomial is evaluated at a shift in
chain length. A raw two-site entry at length n has transfer exponent n - 2.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreTransferRecurrence

open Polynomial
open scoped Matrix Kronecker

noncomputable section

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The polynomial for the Fibonacci shift recurrence. -/
def fibonacciPolynomial (R : Type*) [CommRing R] : Polynomial R :=
  X ^ 2 - X - 1

private lemma fibonacciPolynomial_monic [Nontrivial R] :
    (fibonacciPolynomial R).Monic := by
  unfold fibonacciPolynomial
  rw [sub_sub, ← C_1]
  apply monic_X_pow_sub
  rw [degree_X_add_C]
  decide

private lemma fibonacciPolynomial_natDegree [Nontrivial R] :
    (fibonacciPolynomial R).natDegree = 2 := by
  unfold fibonacciPolynomial
  rw [sub_sub, ← C_1]
  rw [natDegree_sub_eq_left_of_natDegree_lt]
  · simp
  · rw [natDegree_X_add_C, natDegree_X_pow]
    decide

/-- The recurrence with monic shift polynomial (X² - X - 1)^(r + 1). -/
def fibonacciJetRecurrence (R : Type*) [CommRing R] (r : ℕ) : LinearRecurrence R :=
  ⟨2 * (r + 1), fun i => -((fibonacciPolynomial R) ^ (r + 1)).coeff i⟩

private lemma solution_of_aeval_eq_zero {A : Type*} [Ring A] [Algebra R A]
    (P : Polynomial R) (d : ℕ) (hd : P.natDegree = d) (hP : P.Monic)
    (T : A) (readout : A →ₗ[R] R) (h : ∀ k : ℕ, readout (T ^ k * aeval T P) = 0) :
    (LinearRecurrence.mk d (fun i => -P.coeff i)).IsSolution
      (fun k => readout (T ^ k)) := by
  intro k
  have heval := h k
  rw [aeval_eq_sum_range, hd, Finset.sum_range_succ] at heval
  simp only [mul_add, Finset.mul_sum, Algebra.mul_smul_comm, ← pow_add, map_add,
    map_sum, map_smul, smul_eq_mul] at heval
  rw [← hd, hP.coeff_natDegree, one_mul, hd] at heval
  change readout (T ^ (k + d)) = ∑ i : Fin d, -P.coeff i * readout (T ^ (k + i))
  rw [Fin.sum_univ_eq_sum_range (fun i => -P.coeff i * readout (T ^ (k + i))) d]
  simpa only [neg_mul, ← Finset.sum_neg_distrib] using
    eq_neg_of_add_eq_zero_right heval

private lemma exists_X_smul_of_eval_zero (S : Matrix ι ι (Polynomial R))
    (hS : (Polynomial.evalRingHom (0 : R)).mapMatrix S = 0) :
    ∃ U : Matrix ι ι (Polynomial R), S = (X : Polynomial R) • U := by
  have hentry (i j : ι) : (X : Polynomial R) ∣ S i j := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    exact congrArg (fun M : Matrix ι ι R => M i j) hS
  choose U hU using hentry
  exact ⟨U, Matrix.ext hU⟩

/-- At jet degree r, the first admissible transfer exponent is r + 1. -/
theorem transferPower_isSolution (T L : Matrix ι ι (Polynomial R)) (r m : ℕ)
    (hm : r + 1 ≤ m)
    (hbase : let T₀ := (Polynomial.evalRingHom (0 : R)).mapMatrix T
             T₀ * (T₀ ^ 2 - T₀ - 1) = 0) :
    (fibonacciJetRecurrence R r).IsSolution
      (fun k => (L * T ^ (m + k)).trace.coeff r) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · intro k
    exact Subsingleton.elim _ _
  let P := (fibonacciPolynomial R) ^ (r + 1)
  have hP : P.Monic := fibonacciPolynomial_monic.pow _
  have hd : P.natDegree = 2 * (r + 1) := by
    rw [fibonacciPolynomial_monic.natDegree_pow, fibonacciPolynomial_natDegree, Nat.mul_comm]
  let Q := T ^ 2 - T - 1
  have hQ : Commute T Q :=
    (((Commute.self_pow T 2).sub_right (Commute.refl T)).sub_right (Commute.one_right T))
  have hzero : (Polynomial.evalRingHom (0 : R)).mapMatrix (T * Q) = 0 := by
    simpa only [Q, map_mul, map_sub, map_pow, map_one] using hbase
  obtain ⟨U, hU⟩ := exists_X_smul_of_eval_zero (T * Q) hzero
  let readout : Matrix ι ι (Polynomial R) →ₗ[R] R :=
    (Polynomial.lcoeff R r).comp
      ((Matrix.traceLinearMap ι R (Polynomial R)).comp (LinearMap.mulLeft R (L * T ^ m)))
  have hread (k : ℕ) : readout (T ^ k) = (L * T ^ (m + k)).trace.coeff r := by
    change ((L * T ^ m) * T ^ k).trace.coeff r = _
    rw [mul_assoc, ← pow_add]
  have hz (k : ℕ) : readout (T ^ k * aeval T P) = 0 := by
    have heval : aeval T P = Q ^ (r + 1) := by
      simp [P, Q, fibonacciPolynomial]
    have hsplit : m + k = (m + k - (r + 1)) + (r + 1) := by omega
    have hfactor : T ^ (m + k) * Q ^ (r + 1) =
        T ^ (m + k - (r + 1)) * (T * Q) ^ (r + 1) := by
      conv_lhs => rw [hsplit, pow_add, mul_assoc, ← hQ.mul_pow]
    change ((L * T ^ m) * (T ^ k * aeval T P)).trace.coeff r = 0
    rw [heval, ← mul_assoc, mul_assoc L, ← pow_add, mul_assoc, hfactor, hU, _root_.smul_pow,
      Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      Polynomial.coeff_X_pow_mul', ite_eq_right (by omega)]
  have hs : (fibonacciJetRecurrence R r).IsSolution (fun k => readout (T ^ k)) := by
    apply solution_of_aeval_eq_zero P _ hd hP T readout
    exact hz
  simpa only [hread] using hs

/-- The raw coefficient of a transfer entry at chain length n. -/
def transferCoefficient (T L : Matrix ι ι (Polynomial R)) (r n : ℕ) : R :=
  (L * T ^ (n - 2)).trace.coeff r

/-- At lengths 7 + k the coefficient sequence has order 2(r + 1) for r ≤ 4. -/
theorem transferCoefficient_isSolution (T L : Matrix ι ι (Polynomial R))
    (r : ℕ) (hr : r ≤ 4)
    (hbase : let T₀ := (Polynomial.evalRingHom (0 : R)).mapMatrix T
             T₀ * (T₀ ^ 2 - T₀ - 1) = 0) :
    (fibonacciJetRecurrence R r).IsSolution
      (fun k => transferCoefficient T L r (7 + k)) := by
  have h (k : ℕ) : 7 + k - 2 = 5 + k := by omega
  simpa only [transferCoefficient, h] using transferPower_isSolution T L r 5 (by omega) hbase

/-- A candidate sequence satisfying the same shifted recurrence is determined
by its agreement at lengths 7 through 7 + 2(r + 1) - 1. -/
theorem transferCoefficient_eq_of_initial (T L : Matrix ι ι (Polynomial R))
    (r : ℕ) (hr : r ≤ 4)
    (hbase : let T₀ := (Polynomial.evalRingHom (0 : R)).mapMatrix T
             T₀ * (T₀ ^ 2 - T₀ - 1) = 0)
    (candidate : ℕ → R)
    (hsolution : (fibonacciJetRecurrence R r).IsSolution (fun k => candidate (7 + k)))
    (hinitial : ∀ k < 2 * (r + 1), transferCoefficient T L r (7 + k) = candidate (7 + k))
    (n : ℕ) (hn : 7 ≤ n) :
    transferCoefficient T L r n = candidate n := by
  have heq := ((fibonacciJetRecurrence R r).eq_iff_eqOn_range_order _ _
    (transferCoefficient_isSolution T L r hr hbase) hsolution).mpr
      (fun k hk => hinitial k (Finset.mem_range.mp hk))
  simpa only [Nat.add_sub_of_le hn] using congrFun heq (n - 7)

private def sequenceShift (R : Type*) [CommRing R] : Module.End R (ℕ → R) where
  toFun u k := u (k + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma sequenceShift_pow_apply (u : ℕ → R) (k n : ℕ) :
    (sequenceShift R ^ k) u n = u (n + k) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    change (sequenceShift R ^ k) u (n + 1) = u (n + (k + 1))
    rw [ih, show n + 1 + k = n + (k + 1) by omega]

private def fibonacciOperator (R : Type*) [CommRing R] : Module.End R (ℕ → R) :=
  sequenceShift R ^ 2 - sequenceShift R - 1

private lemma fibonacciOperator_apply (u : ℕ → R) (k : ℕ) :
    fibonacciOperator R u k = u (k + 2) - u (k + 1) - u k := by
  change (sequenceShift R ^ 2) u k - u (k + 1) - u k = _
  rw [sequenceShift_pow_apply]

private lemma degree_translate_sub_lt [IsDomain R] (P : Polynomial R) (hP : P ≠ 0) (t : R) :
    (P.comp (X + C t) - P).degree < P.degree := by
  have hdegree : (P.comp (X + C t)).degree = P.degree := by
    rw [degree_comp (by simp : 0 < (X + C t : Polynomial R).degree), degree_X_add_C, mul_one]
  have hleading : (P.comp (X + C t)).leadingCoeff = P.leadingCoeff := by
    rw [leadingCoeff_comp (by simp : (X + C t : Polynomial R).natDegree ≠ 0),
      (monic_X_add_C t).leadingCoeff, one_pow, mul_one]
  exact degree_sub_lt_right hdegree hP hleading

private lemma fibonacciOperator_pow_weighted [IsDomain R] (b m : ℕ) (P : Polynomial R)
    (hP : P.degree < (m : WithBot ℕ)) (u : ℕ → R)
    (hu : ∀ k, u (k + 2) = u (k + 1) + u k) :
    (fibonacciOperator R ^ m) (fun k => P.eval (↑(b + k)) * u k) = 0 := by
  induction m generalizing P u with
  | zero =>
    have hz : P = 0 := by
      by_contra h
      simp [degree_eq_natDegree h] at hP
    simp [hz, ← Pi.zero_def]
  | succ m ih =>
    by_cases hz : P = 0
    · simp [hz, ← Pi.zero_def]
    have hnat : P.natDegree < m + 1 := by
      rw [degree_eq_natDegree hz] at hP
      exact WithBot.coe_lt_coe.mp hP
    have lower (t : R) : (P.comp (X + C t) - P).degree < (m : WithBot ℕ) :=
      (degree_translate_sub_lt P hz t).trans_le (by
        rw [degree_eq_natDegree hz]
        exact WithBot.coe_le_coe.mpr (Nat.le_of_lt_succ hnat))
    have hstep : fibonacciOperator R (fun k => P.eval (↑(b + k)) * u k) =
        (fun k => (P.comp (X + C 2) - P).eval (↑(b + k)) * u (k + 2)) -
        (fun k => (P.comp (X + C 1) - P).eval (↑(b + k)) * u (k + 1)) := by
      funext k
      rw [fibonacciOperator_apply]
      simp only [Pi.sub_apply, eval_sub, eval_comp, eval_add, eval_X, eval_C,
        ← Nat.add_assoc, Nat.cast_add, Nat.cast_ofNat]
      rw [hu k]
      ring
    have huShift (j k : ℕ) : u (k + 2 + j) = u (k + 1 + j) + u (k + j) := by
      rw [Nat.add_right_comm k 2 j, Nat.add_right_comm k 1 j, hu]
    rw [pow_succ, Module.End.mul_apply, hstep, map_sub,
      ih _ (lower 2) _ (huShift 2), ih _ (lower 1) _ (huShift 1), sub_self]

private lemma weightedFibonacci_isSolution [IsDomain R] (b r : ℕ) (P : Polynomial R)
    (hP : P.degree ≤ (r : WithBot ℕ)) (u : ℕ → R)
    (hu : ∀ k, u (k + 2) = u (k + 1) + u k) :
    (fibonacciJetRecurrence R r).IsSolution (fun k => P.eval (↑(b + k)) * u k) := by
  let v : ℕ → R := fun k => P.eval (↑(b + k)) * u k
  let readout : Module.End R (ℕ → R) →ₗ[R] R :=
    (LinearMap.proj 0).comp (LinearMap.applyₗ v)
  let F := fibonacciPolynomial R ^ (r + 1)
  have hdeg : F.natDegree = 2 * (r + 1) := by
    rw [fibonacciPolynomial_monic.natDegree_pow, fibonacciPolynomial_natDegree, Nat.mul_comm]
  have hf : aeval (sequenceShift R) F v = 0 := by
    rw [show aeval (sequenceShift R) F = fibonacciOperator R ^ (r + 1) by
      simp [F, fibonacciPolynomial, fibonacciOperator]]
    exact fibonacciOperator_pow_weighted b (r + 1) P
      (hP.trans_lt (by exact_mod_cast Nat.lt_succ_self r)) u hu
  have hz (k : ℕ) : readout (sequenceShift R ^ k * aeval (sequenceShift R) F) = 0 := by
    change ((sequenceShift R ^ k) (aeval (sequenceShift R) F v)) 0 = 0
    rw [hf, map_zero, Pi.zero_apply]
  have h := solution_of_aeval_eq_zero F _ hdeg (fibonacciPolynomial_monic.pow _)
    (sequenceShift R) readout hz
  have hread (k : ℕ) : readout (sequenceShift R ^ k) = v k := by
    change (sequenceShift R ^ k) v 0 = v k
    rw [sequenceShift_pow_apply, zero_add]
  simpa only [hread, fibonacciJetRecurrence, F, v] using h

/-- A candidate of the form P(n) F_n + Q(n) F_(n-1). -/
def fibonacciCandidate (P Q : Polynomial R) (n : ℕ) : R :=
  P.eval (n : R) * (Nat.fib n : R) + Q.eval (n : R) * (Nat.fib (n - 1) : R)

/-- Polynomial weights of degree at most r times the two Fibonacci sequences
in the certificate solve the length recurrence for the r-th jet coefficient. -/
theorem fibonacciCandidate_isSolution [IsDomain R] (P Q : Polynomial R) (r : ℕ)
    (hP : P.degree ≤ (r : WithBot ℕ)) (hQ : Q.degree ≤ (r : WithBot ℕ)) :
    (fibonacciJetRecurrence R r).IsSolution (fun k => fibonacciCandidate P Q (7 + k)) := by
  let E := fibonacciJetRecurrence R r
  have hshift (j k : ℕ) :
      (Nat.fib (j + (k + 2)) : R) = (Nat.fib (j + (k + 1)) : R) + (Nat.fib (j + k) : R) := by
    simp only [← Nat.add_assoc, Nat.fib_add_two, Nat.cast_add, add_comm]
  have hp := weightedFibonacci_isSolution 7 r P hP (fun k => (Nat.fib (7 + k) : R)) (hshift 7)
  have hq := weightedFibonacci_isSolution 7 r Q hQ (fun k => (Nat.fib (6 + k) : R)) (hshift 6)
  have h := E.solSpace.add_mem ((E.is_sol_iff_mem_solSpace _).mp hp)
    ((E.is_sol_iff_mem_solSpace _).mp hq)
  have hlen (k : ℕ) : 7 + k - 1 = 6 + k := by omega
  have hc :
      (fun k => fibonacciCandidate P Q (7 + k)) =
        (fun k => P.eval ((7 + k : ℕ) : R) * (Nat.fib (7 + k) : R)) +
          (fun k => Q.eval ((7 + k : ℕ) : R) * (Nat.fib (6 + k) : R)) := by
    funext k
    simp only [fibonacciCandidate, hlen, Pi.add_apply]
  rw [hc]
  exact (E.is_sol_iff_mem_solSpace _).mpr h

abbrev TwoBits := Fin 2 × Fin 2

/-- Transfer matrix of two binary matrix families. -/
def binaryTransfer {S : Type*} [Add S] [Mul S]
    (A B : Fin 2 → Matrix (Fin 2) (Fin 2) S) : Matrix TwoBits TwoBits S :=
  A 0 ⊗ₖ B 0 + A 1 ⊗ₖ B 1

/-- Insertion of the two words selecting a raw marginal entry. -/
def binaryInsertion {S : Type*} [CommSemiring S]
    (A B : Fin 2 → Matrix (Fin 2) (Fin 2) S) (p q : TwoBits) :
    Matrix TwoBits TwoBits S :=
  (A p.1 * A p.2) ⊗ₖ (B q.1 * B q.2)

/-- The polynomial chart of the hard-core transfer certificate. -/
def hardCoreChart {S : Type*} [Zero S] [One S] (a b c d : S) :
    Fin 2 → Matrix (Fin 2) (Fin 2) S :=
  ![!![1, 0; 1, a], !![0, b; c, d]]

/-- Coefficientwise conjugation preserves the real jet variable. -/
def conjugateJet (A : Fin 2 → Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) :
    Fin 2 → Matrix (Fin 2) (Fin 2) (Polynomial ℂ) :=
  fun i => (A i).map (Polynomial.map (starRingEnd ℂ))

/-- The two-site raw transfer entry before coefficient extraction. -/
def binaryRawTransfer (A : Fin 2 → Matrix (Fin 2) (Fin 2) (Polynomial ℂ))
    (p q : TwoBits) (n : ℕ) : Polynomial ℂ :=
  (binaryInsertion A (conjugateJet A) p q * binaryTransfer A (conjugateJet A) ^ (n - 2)).trace

private lemma map_kronecker {S V : Type*} [CommSemiring S] [CommSemiring V] (f : S →+* V)
    (A B : Matrix (Fin 2) (Fin 2) S) :
    f.mapMatrix (A ⊗ₖ B) = f.mapMatrix A ⊗ₖ f.mapMatrix B := by
  ext i j
  exact f.map_mul _ _

private lemma map_binaryTransfer {S V : Type*} [CommSemiring S] [CommSemiring V] (f : S →+* V)
    (A B : Fin 2 → Matrix (Fin 2) (Fin 2) S) :
    f.mapMatrix (binaryTransfer A B) =
      binaryTransfer (fun i => f.mapMatrix (A i)) (fun i => f.mapMatrix (B i)) := by
  simp only [binaryTransfer, map_add, map_kronecker]

private lemma map_binaryInsertion {S V : Type*} [CommSemiring S] [CommSemiring V]
    (f : S →+* V) (A B : Fin 2 → Matrix (Fin 2) (Fin 2) S) (p q : TwoBits) :
    f.mapMatrix (binaryInsertion A B p q) =
      binaryInsertion (fun i => f.mapMatrix (A i)) (fun i => f.mapMatrix (B i)) p q := by
  simp only [binaryInsertion, map_kronecker, map_mul]

private lemma eval_conjugateJet
    (A : Fin 2 → Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) (t : ℝ) (i : Fin 2) :
    (Polynomial.evalRingHom (t : ℂ)).mapMatrix (conjugateJet A i) =
      ((Polynomial.evalRingHom (t : ℂ)).mapMatrix (A i)).map (starRingEnd ℂ) := by
  ext u v
  change ((A i u v).map (starRingEnd ℂ)).eval (t : ℂ) = starRingEnd ℂ ((A i u v).eval (t : ℂ))
  simpa using Polynomial.eval_map_apply (f := starRingEnd ℂ) (p := A i u v) (t : ℂ)

private lemma eval_hardCoreChart (a b c d : Polynomial ℂ) (t : ℂ) (i : Fin 2) :
    (Polynomial.evalRingHom t).mapMatrix (hardCoreChart a b c d i) =
      hardCoreChart (a.eval t) (b.eval t) (c.eval t) (d.eval t) i := by
  ext u v
  fin_cases i <;> fin_cases u <;> fin_cases v <;> simp [hardCoreChart, RingHom.mapMatrix_apply]

private lemma hardCoreBase_annihilation :
    let A := hardCoreChart (0 : ℂ) 1 0 0
    let T := binaryTransfer A A
    T * (T ^ 2 - T - 1) = 0 := by
  dsimp only
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    norm_num [pow_two, binaryTransfer, hardCoreChart, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- The constant transfer of the hard-core chart is annihilated by T(T² - T - I). -/
theorem hardCoreTransfer_eval_zero (a b c d : Polynomial ℂ)
    (ha : a.eval 0 = 0) (hb : b.eval 0 = 1) (hc : c.eval 0 = 0) (hd : d.eval 0 = 0) :
    let A := hardCoreChart a b c d
    let T₀ := (Polynomial.evalRingHom (0 : ℂ)).mapMatrix (binaryTransfer A (conjugateJet A))
    T₀ * (T₀ ^ 2 - T₀ - 1) = 0 := by
  dsimp only
  rw [map_binaryTransfer]
  have hA (i : Fin 2) : (Polynomial.evalRingHom (0 : ℂ)).mapMatrix (hardCoreChart a b c d i) =
      hardCoreChart (0 : ℂ) 1 0 0 i := by
    rw [eval_hardCoreChart, ha, hb, hc, hd]
  have hB (i : Fin 2) :
      (Polynomial.evalRingHom (0 : ℂ)).mapMatrix (conjugateJet (hardCoreChart a b c d) i) =
        hardCoreChart (0 : ℂ) 1 0 0 i := by
    have h := eval_conjugateJet (hardCoreChart a b c d) 0 i
    rw [Complex.ofReal_zero, hA] at h
    rw [h]
    ext u v
    fin_cases i <;> fin_cases u <;> fin_cases v <;> simp [hardCoreChart]
  simp only [hA, hB]
  exact hardCoreBase_annihilation

/-- Finite comparison for each raw entry in the complex hard-core chart. -/
theorem hardCoreRaw_coeff_eq_of_initial (a b c d : Polynomial ℂ)
    (ha : a.eval 0 = 0) (hb : b.eval 0 = 1) (hc : c.eval 0 = 0) (hd : d.eval 0 = 0)
    (p q : TwoBits) (r : ℕ) (hr : r ≤ 4) (candidate : ℕ → ℂ)
    (hsolution : (fibonacciJetRecurrence ℂ r).IsSolution (fun k => candidate (7 + k)))
    (hinitial : ∀ k < 2 * (r + 1),
      (binaryRawTransfer (hardCoreChart a b c d) p q (7 + k)).coeff r = candidate (7 + k))
    (n : ℕ) (hn : 7 ≤ n) :
    (binaryRawTransfer (hardCoreChart a b c d) p q n).coeff r = candidate n :=
  transferCoefficient_eq_of_initial _ _ r hr (hardCoreTransfer_eval_zero a b c d ha hb hc hd)
    candidate hsolution hinitial n hn

/-- The certificate's polynomially weighted Fibonacci formula agrees at every
length from 7 onward exactly when it agrees at the first 2(r + 1) lengths. -/
theorem hardCoreRaw_fibonacci_iff_initial (a b c d : Polynomial ℂ)
    (ha : a.eval 0 = 0) (hb : b.eval 0 = 1) (hc : c.eval 0 = 0) (hd : d.eval 0 = 0)
    (p q : TwoBits) (r : ℕ) (hr : r ≤ 4) (P Q : Polynomial ℂ)
    (hP : P.degree ≤ (r : WithBot ℕ)) (hQ : Q.degree ≤ (r : WithBot ℕ)) :
    (∀ n ≥ 7, (binaryRawTransfer (hardCoreChart a b c d) p q n).coeff r =
      fibonacciCandidate P Q n) ↔
    (∀ k < 2 * (r + 1), (binaryRawTransfer (hardCoreChart a b c d) p q (7 + k)).coeff r =
      fibonacciCandidate P Q (7 + k)) := by
  constructor
  · intro h k _
    exact h (7 + k) (by omega)
  · exact hardCoreRaw_coeff_eq_of_initial a b c d ha hb hc hd p q r hr _
      (fibonacciCandidate_isSolution P Q r hP hQ)

open PeriodicMPSParentIntersection (Bond Word wordMatrix)
open PeriodicMPSTwoSiteAmbiguity (rawTwo flattening_entry)

private lemma binaryTransfer_pow {S : Type*} [CommSemiring S]
    (A B : Fin 2 → Matrix (Fin 2) (Fin 2) S) (m : ℕ) :
    binaryTransfer A B ^ m =
      ∑ w : Word m,
        (List.ofFn (fun i => A (w i))).prod ⊗ₖ (List.ofFn (fun i => B (w i))).prod := by
  induction m with
  | zero => simp [Finset.univ_unique]
  | succ m ih =>
    rw [pow_succ', ih, ← (Fin.consEquiv (fun _ : Fin (m+1) => Fin 2)).sum_comp,
      Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons,
      Fin.sum_univ_two]
    unfold binaryTransfer
    simp_rw [Matrix.mul_kronecker_mul, ← Finset.mul_sum, ← add_mul]

private lemma rawTwo_eq_trace (A : Fin 2 → Bond) (s : ℕ) (p q : TwoBits) :
    rawTwo A s p q =
      (binaryInsertion A (fun i => (A i).map (starRingEnd ℂ)) p q *
        binaryTransfer A (fun i => (A i).map (starRingEnd ℂ)) ^ (s + 2)).trace := by
  classical
  rw [binaryTransfer_pow, Matrix.mul_sum, Matrix.trace_sum]
  simp only [rawTwo, Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro w _
  rw [flattening_entry, flattening_entry]
  simp only [binaryInsertion, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]
  congr 1
  let f : Bond →+* Bond := RingHom.mapMatrix (starRingEnd ℂ)
  change starRingEnd ℂ (A q.1 * A q.2 * wordMatrix A w).trace =
    (f (A q.1) * f (A q.2) * (List.ofFn fun i => f (A (w i))).prod).trace
  have hw : (List.ofFn fun i => f (A (w i))) =
      (List.ofFn fun i => A (w i)).map f := List.map_ofFn.symm
  rw [hw, ← map_list_prod, ← map_mul, ← map_mul]
  exact AddMonoidHom.map_trace (starRingEnd ℂ) _

/-- On the real parameter line, the polynomial evaluates to the actual raw
two-site entry. The repository index s describes chain length s + 4. -/
theorem eval_binaryRawTransfer
    (A : Fin 2 → Matrix (Fin 2) (Fin 2) (Polynomial ℂ))
    (t : ℝ) (s : ℕ) (p q : TwoBits) :
    (binaryRawTransfer A p q (s + 4)).eval (t : ℂ) =
      rawTwo (fun i => (Polynomial.evalRingHom (t : ℂ)).mapMatrix (A i)) s p q := by
  rw [rawTwo_eq_trace, binaryRawTransfer]
  change (Polynomial.evalRingHom (t : ℂ)) (Matrix.trace _) = _
  rw [AddMonoidHom.map_trace (Polynomial.evalRingHom (t : ℂ))]
  change ((Polynomial.evalRingHom (t : ℂ)).mapMatrix (_ * _ ^ (s + 4 - 2))).trace = _
  have h : s + 4 - 2 = s + 2 := by omega
  simp only [h, map_mul, map_pow, map_binaryTransfer, map_binaryInsertion, eval_conjugateJet]

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreTransferRecurrence
