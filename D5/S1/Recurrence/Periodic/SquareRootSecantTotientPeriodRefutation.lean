/- GID: D5/S1/Recurrence/Periodic/SquareRootSecantTotientPeriodRefutation
   generality: I
   mirror-B: D5/B/S1/Recurrence/Periodic/SquareRootSecantTotientPeriodRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Recurrence/Periodic/SquareRootSecantTotientPeriodRefutation.claim; result=D5/S1/Recurrence/Periodic/SquareRootSecantTotientPeriodRefutation.result; claim=D5/S1/Recurrence/Periodic/SquareRootSecantTotientPeriodRefutation.claim
   digest: Two-step differences refute the eventual totient-period bound. -/

/-
Source: OEIS A126156, COMMENTS, Peter Bala; issue #22077.
The source's factorial coefficient expression is inlined in claim; proofs use
IntegralEGFComposition.eCoeff, so no duplicate coefficient definition is introduced.
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
admission_basis: open-problem-resolution (#22077; Refuted)
escape_witness: none (the module is admitted by its settling result).
Direct frozen dependencies (declaration identities, not module pins):
F1: D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff
    statement_id: sha256:4352a2872dd069de3ca054aab1c4950930a811b324435173c0e64781d46fc330
F2: D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_derivative
    statement_id: sha256:d8c528ef732aa837c3d79d7314200e072b40f5bcdc873683da352f1acf37c5c8
F3: D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_zero
    statement_id: sha256:69e1d2e22802c66151c2c3239fdceab9ab8a796d9f10d82c7366e4d57e790054
F4: D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.eCoeff_ext
    statement_id: sha256:be297942dba1d71d921d56e5059d2544375954e34dd6e505146ebcbbed2baaff
F5: D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.eCoeff_encode
    statement_id: sha256:352e6f7d24ca45dedb1bc8138765409965b1fb7a21903187a52a0d3fbd0a3bf7
F6: D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.encode
    statement_id: sha256:bb200c57b57d3db01e9c5a71120a010d1a0509f29a9046ca82c6726744329840

Declaration judgement (same-delivery helpers expanded; F labels resolve above):
cosSqrtTwo: proof_shape: not-applicable; escape_witness: none;
  Direct frozen dependencies: none; consumers: IsSourceEGF, cos_ecoeff, cos_second, source_intA, source_system.
IsSourceEGF: proof_shape: not-applicable; escape_witness: none;
  Direct frozen dependencies: none; consumers: claim, persistent_obstruction, result, source_intA, source_system.
claim: proof_shape: not-applicable; escape_witness: none;
  Direct frozen dependencies: none; consumers: result.
cos_ecoeff: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F5, F6; consumers: cos_second, source_system.
cos_second: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F4, F5, F6; consumers: source_system.
source_system: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F4, F5, F6; consumers: source_intA.
step: proof_shape: not-applicable; escape_witness: none;
  Direct frozen dependencies: none; consumers: coeff_intA, deriv_eval, deriv_iter, intA_anti, intA_escape, intA_odd, persistent_obstruction, source_intA, step_four, step_one, step_three, step_two, step_zero.
step_zero: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: step_four.
step_one: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: step_four.
step_two: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: step_four.
step_three: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: step_four.
step_four: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: intA_anti.
intA_anti: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: intA_escape.
intA_odd: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: intA_escape.
intA_escape: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: persistent_obstruction.
deriv_eval: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: deriv_iter.
deriv_iter: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: coeff_intA.
constant_aeval: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: coeff_intA.
coeff_intA: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: source_intA.
source_intA: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F4, F5, F6; consumers: persistent_obstruction.
persistent_obstruction: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F4, F5, F6; consumers: result.
result: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F4, F5, F6; consumers: none.
-/


import D5.S1.Recurrence.Residue.IntegralEGFComposition
import D5.S1.Recurrence.Residue.QuarticEGFFixedPoint

/-! The even EGF coefficients have an all-index obstruction to totient periods. -/

namespace D5.S1.Recurrence.Periodic.SquareRootSecantTotientPeriodRefutation

open PowerSeries

/-- cos(√2 x) as a rational power series: Σ_m (-2)^m x^(2m)/(2m)!. -/
noncomputable def cosSqrtTwo : PowerSeries ℚ :=
  PowerSeries.mk fun j =>
    if Even j then ((-2 : ℚ) ^ (j / 2)) / (Nat.factorial j : ℚ) else 0

/-- OEIS A126156 NAME: the e.g.f. sqrt(sec(sqrt(2) x)), encoded by its
constant term 1 and the equation A^2 * cos(sqrt(2) x) = 1 over ℚ. -/
def IsSourceEGF (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 1 ∧ A ^ 2 * cosSqrtTwo = 1

/-- Bala's A126156 COMMENTS conjecture: modulo every positive k the sequence is
eventually periodic with a period dividing phi(k). Congruence is stated as an
integer multiple of k. The existence clause prevents a vacuous assertion.
The refutation target is `Not claim`. -/
def claim : Prop :=
  (∃ A : PowerSeries ℚ, IsSourceEGF A) ∧
  ∀ A : PowerSeries ℚ, IsSourceEGF A →
    ∀ k : ℕ, 0 < k →
      ∃ N : ℕ, ∃ p : ℕ, 0 < p ∧ p ∣ Nat.totient k ∧
        ∀ n : ℕ, N ≤ n → ∃ z : ℤ, (Nat.factorial (2 * (n + p)) : ℚ) * coeff (2 * (n + p)) A -
          (Nat.factorial (2 * n) : ℚ) * coeff (2 * n) A = (k : ℚ) * (z : ℚ)

open D5.S1.Recurrence.Residue.IntegralEGFComposition
open D5.S1.Recurrence.Residue.QuarticEGFFixedPoint (eCoeff_ext)

local notation "D" => PowerSeries.derivative (R := ℚ)

private theorem cos_ecoeff (n : ℕ) :
    eCoeff cosSqrtTwo n = if Even n then (-2 : ℚ) ^ (n / 2) else 0 := by
  simpa only [cosSqrtTwo, D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.encode,
    ite_div, zero_div] using
    (D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.eCoeff_encode
      (fun j => if Even j then (-2 : ℚ) ^ (j / 2) else 0) n)

private theorem cos_second : D (D cosSqrtTwo) = -2 * cosSqrtTwo := by
  apply eCoeff_ext
  intro n
  rw [eCoeff_derivative, eCoeff_derivative]
  have he : Even (n + 1 + 1) ↔ Even n := by
    simpa only [even_two, iff_true] using (Nat.even_add (m := n) (n := 2))
  have hn : (n + 1 + 1) / 2 = n / 2 + 1 := Nat.add_div_right n (z := 2) (by decide)
  have hc : eCoeff (-2 * cosSqrtTwo) n = (-2 : ℚ) * eCoeff cosSqrtTwo n := by
    simp only [eCoeff, neg_mul, map_neg, PowerSeries.coeff_ofNat_mul]
    ring
  rw [hc, cos_ecoeff, cos_ecoeff]
  simp only [he, hn]
  split_ifs <;> simp [pow_succ, mul_comm]

private theorem source_system (A : PowerSeries ℚ) (hA : IsSourceEGF A) :
    ∃ U : PowerSeries ℚ, constantCoeff U = 0 ∧ D A = A * U ∧ D U = 1 + 2 * U ^ 2 := by
  let c : PowerSeries ℚ := C (1 / 2 : ℚ)
  have hc : 2 * c = 1 := by
    change C (2 : ℚ) * C (1 / 2 : ℚ) = 1
    rw [← map_mul]
    norm_num
  let U := -c * A ^ 2 * D cosSqrtTwo
  refine ⟨U, ?_, ?_, ?_⟩
  · have hz : constantCoeff (D cosSqrtTwo) = 0 := by
      rw [← eCoeff_zero, eCoeff_derivative, cos_ecoeff]
      norm_num
    simp [U, hz]
  · have hd := congrArg D hA.2
    simp only [Derivation.leibniz, PowerSeries.derivative_pow,
      smul_eq_mul, PowerSeries.derivative_one] at hd
    have hl : 2 * D A + A ^ 3 * D cosSqrtTwo = 0 := by
      linear_combination A * hd - 2 * D A * hA.2
    dsimp [U]
    linear_combination c * hl - D A * hc
  · have hd := congrArg D hA.2
    simp only [Derivation.leibniz, PowerSeries.derivative_pow,
      smul_eq_mul, PowerSeries.derivative_one] at hd
    have hl : 2 * D A + A ^ 3 * D cosSqrtTwo = 0 := by
      linear_combination A * hd - 2 * D A * hA.2
    have hAU : D A = A * U := by
      dsimp [U]
      linear_combination c * hl - D A * hc
    have hdc : D c = 0 := PowerSeries.derivative_C
    dsimp [U]
    simp only [Derivation.leibniz, map_neg, hdc, neg_zero, smul_eq_mul,
      PowerSeries.derivative_pow, cos_second]
    rw [hAU]
    dsimp [U]
    linear_combination hc * (A ^ 2 * cosSqrtTwo) + hA.2

private noncomputable def step (p : Polynomial ℤ) : Polynomial ℤ :=
  Polynomial.X * p + (1 + 2 * Polynomial.X ^ 2) * p.derivative

private theorem step_zero (p : Polynomial ℤ) : (step p).coeff 0 = p.coeff 1 := by
  simp [step, Polynomial.coeff_derivative, add_mul, mul_assoc]

private theorem step_one (p : Polynomial ℤ) :
    (step p).coeff 1 = p.coeff 0 + 2 * p.coeff 2 := by
  simp [step, Polynomial.coeff_derivative, add_mul,
    Polynomial.coeff_X_pow_mul', mul_assoc]
  ring

private theorem step_two (p : Polynomial ℤ) :
    (step p).coeff 2 = 3 * p.coeff 1 + 3 * p.coeff 3 := by
  simp [step, Polynomial.coeff_derivative, add_mul,
    Polynomial.coeff_X_pow_mul', mul_assoc]
  ring

private theorem step_three (p : Polynomial ℤ) :
    (step p).coeff 3 = 5 * p.coeff 2 + 4 * p.coeff 4 := by
  simp [step, Polynomial.coeff_derivative, add_mul,
    Polynomial.coeff_X_pow_mul', mul_assoc]
  ring

private theorem step_four (p : Polynomial ℤ) :
    (step (step (step (step p)))).coeff 0 + p.coeff 0 =
      4 * (2 * p.coeff 0 + 11 * p.coeff 2 + 6 * p.coeff 4) := by
  simp only [step_zero, step_one, step_two, step_three]
  ring

private theorem intA_anti (n : ℕ) :
    ∃ z : ℤ, (step^[2 * (n + 2)] (1 : Polynomial ℤ)).coeff 0 +
      (step^[2 * n] (1 : Polynomial ℤ)).coeff 0 = 4 * z := by
  refine ⟨2 * (step^[2*n] (1 : Polynomial ℤ)).coeff 0 +
    11 * (step^[2*n] (1 : Polynomial ℤ)).coeff 2 +
    6 * (step^[2*n] (1 : Polynomial ℤ)).coeff 4, ?_⟩
  rw [show 2 * (n+2) = 4 + 2*n by omega, Function.iterate_add_apply]
  exact step_four (step^[2*n] (1 : Polynomial ℤ))

private theorem intA_odd (n : ℕ) : (step^[2 * n] (1 : Polynomial ℤ)).coeff 0 % 2 = 1 := by
  let observe : Polynomial ℤ → ℤ := fun p => p.coeff 0 % 2
  have hinv : observe ∘ (step^[2]) = observe := by
    funext p
    change (step (step p)).coeff 0 % 2 = p.coeff 0 % 2
    simp [step, Polynomial.coeff_derivative, add_mul,
      mul_assoc, Int.add_emod]
  have h := congrFun (Function.iterate_invariant hinv n) (1 : Polynomial ℤ)
  rw [Function.iterate_mul step 2 n]
  simpa [observe, Function.comp_apply] using h

private theorem intA_escape (n : ℕ) :
    ∃ z : ℤ, (step^[2 * (n + 2)] (1 : Polynomial ℤ)).coeff 0 -
      (step^[2 * n] (1 : Polynomial ℤ)).coeff 0 = 4 * z + 2 := by
  obtain ⟨z, hz⟩ := intA_anti n
  have ho := intA_odd n
  refine ⟨z - (step^[2 * n] (1 : Polynomial ℤ)).coeff 0 / 2 - 1, ?_⟩
  omega


private theorem deriv_eval (A U : PowerSeries ℚ)
    (hA : D A = A * U) (hU : D U = 1 + 2 * U ^ 2) (p : Polynomial ℤ) :
    D (A * Polynomial.aeval U p) = A * Polynomial.aeval U (step p) := by
  have hd := ((PowerSeries.derivative (R := ℚ)).restrictScalars ℤ).map_aeval p U
  change D (Polynomial.aeval U p) = Polynomial.aeval U p.derivative * D U at hd
  rw [Derivation.leibniz, hd, hA, hU]
  simp only [step, map_add, map_mul, map_one, map_ofNat, map_pow, Polynomial.aeval_X,
    smul_eq_mul]
  ring

private theorem deriv_iter (A U : PowerSeries ℚ)
    (hA : D A = A * U) (hU : D U = 1 + 2 * U ^ 2) (n : ℕ) :
    D^[n] A = A * Polynomial.aeval U (step^[n] (1 : Polynomial ℤ)) := by
  have hs : Function.Semiconj (fun p : Polynomial ℤ => A * Polynomial.aeval U p) step D :=
    fun p => (deriv_eval A U hA hU p).symm
  simpa only [map_one, mul_one] using (hs.iterate_right n 1).symm

private theorem constant_aeval (U : PowerSeries ℚ) (hU : PowerSeries.constantCoeff U = 0)
    (p : Polynomial ℤ) :
    PowerSeries.constantCoeff (Polynomial.aeval U p) = (p.coeff 0 : ℚ) := by
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hU, Polynomial.eval₂_at_zero]
  simp

private theorem coeff_intA (A U : PowerSeries ℚ)
    (hc : PowerSeries.constantCoeff A = 1) (hz : PowerSeries.constantCoeff U = 0)
    (hA : D A = A * U) (hU : D U = 1 + 2 * U ^ 2) (n : ℕ) :
    (Nat.factorial (2 * n) : ℚ) * PowerSeries.coeff (2 * n) A =
      ((step^[2 * n] (1 : Polynomial ℤ)).coeff 0 : ℚ) := by
  rw [← PowerSeries.constantCoeff_iterate_derivative, deriv_iter A U hA hU,
    map_mul, hc, one_mul, constant_aeval U hz]

private theorem source_intA (A : PowerSeries ℚ) (hA : IsSourceEGF A) (n : ℕ) :
    eCoeff A (2 * n) = ((step^[2 * n] (1 : Polynomial ℤ)).coeff 0 : ℚ) := by
  obtain ⟨U, hz, hdA, hdU⟩ := source_system A hA
  exact coeff_intA A U hA.1 hz hdA hdU n

private theorem persistent_obstruction (A : PowerSeries ℚ) (hA : IsSourceEGF A) (n : ℕ) :
    ∃ z : ℤ, eCoeff A (2 * (n + 2)) - eCoeff A (2 * n) = 4 * (z : ℚ) + 2 := by
  obtain ⟨z, hz⟩ := intA_escape n
  refine ⟨z, ?_⟩
  rw [source_intA A hA, source_intA A hA]
  exact_mod_cast hz

theorem result : ¬ claim := by
  intro hc
  obtain ⟨A, hA⟩ := hc.1
  obtain ⟨N, p, hp, hd, hper⟩ := hc.2 A hA 4 (by decide)
  have hphi : Nat.totient 4 = 2 := by exact Nat.two_eq_digitChar.mp rfl
  rw [hphi] at hd
  have hp2 : p ≤ 2 := Nat.le_of_dvd (by decide) hd
  have hcases : p = 1 ∨ p = 2 := by omega
  have he : ∃ z : ℤ, eCoeff A (2 * (N + 2)) - eCoeff A (2 * N) = 4 * (z : ℚ) := by
    rcases hcases with rfl | rfl
    · obtain ⟨z, hz⟩ := hper N (by omega)
      obtain ⟨w, hw⟩ := hper (N+1) (by omega)
      refine ⟨z+w, ?_⟩
      push_cast
      norm_num at hz hw
      have hn : N + 1 + 1 = N + 2 := by exact Nat.add_left_inj.mpr rfl
      rw [hn] at hw
      dsimp only [eCoeff]
      linarith
    · exact hper N (by omega)
  obtain ⟨z, hz⟩ := he
  obtain ⟨w, hw⟩ := persistent_obstruction A hA N
  have hzw : 4 * z = 4 * w + 2 := by exact_mod_cast hz.symm.trans hw
  omega

end D5.S1.Recurrence.Periodic.SquareRootSecantTotientPeriodRefutation
