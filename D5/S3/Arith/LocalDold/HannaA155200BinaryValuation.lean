/- GID: D5/S3/Arith/LocalDold/HannaA155200BinaryValuation
   generality: I
   mirror-B: D5/B/S3/Arith/LocalDold/HannaA155200BinaryValuation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna A155200 has an odd integer quotient by its binary digit-sum power of two. -/

/-
admission_basis: open-problem-resolution (#21398; Proved)
The source exponential and coefficient expressions are inlined in claim; proofs
use HannaDiagonalGhostPowerIntegrality.exponentialSum and logarithmicInput.
The correspondence is definitional, with the same zero constant coefficient.
No separate escape witness is claimed for admission.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23611
Direct frozen dependencies:
F1: D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.result; sha256:6b344bafbd49c7b59b833d33c153b4324735e331a16dd7bf23b58579419ea848.
F2: D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.exponentialSum; sha256:011c3ffffaa4e8d1dcbdeb263ad502ee54def47d35b5b4b833b360f4360f996e.
F3: D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.logarithmicInput; sha256:b5bd1729420ea137fa187a9a0e1d88b1b77aaf96af596fd62dcfe2f59419635b.
F6: D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.exponential_sum_constant; sha256:43f4b699454a38a2a658b16394a082c492a5ac5290c19cdaccb92f0e3eb8a9e4.
F7: D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.exponential_sum_equation; sha256:255ec220c1840896af96b59ba7e1decd1b861f2d4a1741042206a0997fe6fd8a.
F4: D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure.IntegralSeries;
    sha256:63e70f464749e368856bfaa91133b0adfeda478327572310319dbf6077b632cb.
F5: D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.geometric_inverse;
    sha256:9525f01e017fb1c9a0b2ce2b637f99278274ce4571130d1c72eb8cbcb336a1c8.
F8: D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity.step;
    sha256:238f94e20168898d8702329a0fe0a77fe7f11f4c04adccbfbdf480c38fc14838.
F9: D5/S3/Arith/FactorialRatio/BalaA361034Parity.binary_factorial_balance;
    sha256:a2d52eecb76d024216158ebe2ea9e5bee489a1347b063d27a9854c1f1f486dff.
claim: proof_shape: definition; escape_witness: none; consumers: result;
  Direct frozen dependencies: none.
geometric_exponential_integral: proof_shape: bind-only; escape_witness: none;
  consumers: result; Direct frozen dependencies: F2, F3, F4, F5.
normalized_integral_mod_four: proof_shape: content; escape_witness: none;
  consumers: result; Direct frozen dependencies: none.
odd_quotient_of_integral_normalization: proof_shape: bind-only;
  escape_witness: none; consumers: result; Direct frozen dependencies: F9.
result: proof_shape: content; escape_witness: none;
  consumers: external settlement; Direct frozen dependencies: F1, F2, F3, F4, F5, F6, F7, F8, F9.
-/

import D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality
import D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure
import D5.S1.Recurrence.Invariants.CompositionalIterateCongruence
import D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity
import D5.S3.Arith.FactorialRatio.BalaA361034Parity

/-! Exact odd quotients for the ordinary coefficients of Hanna's formal exponential. -/

namespace D5.S3.Arith.LocalDold.HannaA155200BinaryValuation

open PowerSeries Finset
open D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality (exponentialSum logarithmicInput)
open D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure (IntegralSeries)

/-- OEIS A155200, Hanna's binary-valuation assertion, including index zero. -/
def claim : Prop :=
  ∀ n : ℕ, ∃ z : ℤ, Odd z ∧
    PowerSeries.coeff n ((PowerSeries.exp ℚ).subst
      (PowerSeries.mk fun k => if k = 0 then 0 else (2 : ℚ) ^ (k ^ 2) / (k : ℚ))) =
        (2 : ℚ) ^ (Nat.digits 2 n).sum * (z : ℚ)

set_option maxHeartbeats 1000000 in
private theorem geometric_exponential_integral :
    IntegralSeries (exponentialSum (fun n => (2 : ℚ) ^ n)) := by
  let H : PowerSeries ℚ := rescale (-2) (log ℚ)
  have hH : HasSubst H := HasSubst.of_constantCoeff_zero'
    (by simp [H, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale])
  have harg : logarithmicInput (fun n => (2 : ℚ) ^ n) = -H := by
    ext n
    simp only [logarithmicInput, coeff_mk, map_neg, H, coeff_rescale, coeff_log,
      Algebra.algebraMap_self, RingHom.id_apply]
    by_cases hn : n = 0
    · simp [hn]
    · simp only [ite_eq_right hn]
      rw [neg_pow, pow_succ]
      have hsign : (-1 : ℚ)^n * (-1)^n = 1 := by
        rw [← mul_pow]; norm_num
      calc
        (2 : ℚ)^n / n = ((-1 : ℚ)^n * (-1)^n) * (2^n / n) := by rw [hsign]; ring
        _ = _ := by ring
  have hplus : (exp ℚ).subst H = 1 - C (2 : ℚ) * X := by
    have h := congrArg (fun f : PowerSeries ℚ => f.subst ((-2 : ℚ) • (X : PowerSeries ℚ)))
      (PowerSeries.subst_exp_log (A := ℚ))
    rw [subst_comp_subst_apply HasSubst.log (HasSubst.smul_X' (-2 : ℚ))] at h
    rw [← rescale_eq_subst] at h
    rw [← coe_substAlgHom (HasSubst.smul_X' (-2 : ℚ)), map_add, map_one, substAlgHom_X] at h
    simpa [H, smul_eq_C_mul, sub_eq_add_neg] using h
  have hinv : (exponentialSum (fun n => (2 : ℚ)^n)) * (1 - C (2 : ℚ)*X) = 1 := by
    have h := congrArg (fun f : PowerSeries ℚ => f.subst H)
      (exp_mul_exp_neg_eq_one (A := ℚ))
    rw [subst_mul hH] at h
    have hneg : (evalNegHom (exp ℚ)).subst H = (exp ℚ).subst (-H) := by
      change (rescale (-1 : ℚ) (exp ℚ)).subst H = _
      rw [rescale_eq_subst, subst_comp_subst_apply (HasSubst.smul_X' (-1 : ℚ)) hH]
      congr 1
      simp [← coe_substAlgHom hH, substAlgHom_X]
    rw [hneg, hplus] at h
    simpa [exponentialSum, harg, mul_comm, ← coe_substAlgHom hH] using h
  have hg : (rescale (2 : ℚ) (mk 1)) * (1 - C (2 : ℚ) * X) = 1 := by
    exact D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.geometric_inverse (2 : ℚ)
  have heq : exponentialSum (fun n => (2 : ℚ)^n) = rescale (2 : ℚ) (mk 1) := by
    apply mul_right_cancel₀ (b := 1 - C (2 : ℚ) * X)
    · intro h
      have hc := congrArg constantCoeff h
      simp at hc
    · exact hinv.trans hg.symm
  intro n
  refine ⟨(2 : ℤ)^n, ?_⟩
  simp [heq, coeff_rescale]

set_option maxHeartbeats 1000000 in
private theorem normalized_integral_mod_four (f : ℕ → ℚ) (hzero : f 0 = 1)
    (hrec : ∀ n : ℕ, f (n + 1) * (n + 1 : ℚ) =
      ∑ k ∈ range (n + 1), f (n - k) * (2 : ℚ) ^ ((k + 1) ^ 2)) :
    ∀ n : ℕ, ∃ z : ℤ, z % 4 = 1 ∧
      (n.factorial : ℚ) * f n = (2 : ℚ) ^ n * (z : ℚ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact ⟨1, by norm_num, by simp [hzero]⟩
    | succ n =>
      let b (k : ℕ) : ℤ := if hk : k < n + 1 then Classical.choose (ih k hk) else 0
      have hb (k : ℕ) (hk : k < n + 1) :
          b k % 4 = 1 ∧ (k.factorial : ℚ) * f k = (2 : ℚ)^k * (b k : ℚ) := by
        simpa only [b, dite_eq_left hk] using Classical.choose_spec (ih k hk)
      let z : ℤ := ∑ k ∈ range (n + 1),
        (n.descFactorial k : ℤ) * (2 : ℤ) ^ (k * (k + 1)) * b (n - k)
      refine ⟨z, ?_, ?_⟩
      · have hs : ∀ k ∈ range (n + 1), 1 ≤ k →
            ((n.descFactorial k : ℤ) * 2 ^ (k * (k + 1)) * b (n - k)) % 4 = 0 := by
          intro k hk hk1
          have he : 2 ≤ k * (k + 1) := by nlinarith
          have hd : (4 : ℤ) ∣ (2 : ℤ) ^ (k * (k + 1)) := by
            convert pow_dvd_pow (2 : ℤ) he using 1; norm_num
          exact Int.emod_eq_zero_of_dvd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _)
        rw [show z = b n + ∑ k ∈ (range (n + 1)).erase 0,
          (n.descFactorial k : ℤ) * 2 ^ (k * (k + 1)) * b (n - k) by
          dsimp [z]
          rw [← sum_erase_add _ _ (mem_range.mpr (by omega : 0 < n + 1))]
          simp only [Nat.descFactorial_zero, Nat.cast_one, zero_mul, pow_zero, one_mul,
            Nat.sub_zero]
          exact add_comm _ _]
        rw [Int.add_emod, Finset.sum_int_mod]
        have hsum : (∑ k ∈ (range (n + 1)).erase 0,
            ((n.descFactorial k : ℤ) * 2 ^ (k * (k + 1)) * b (n - k)) % 4) = 0 := by
          apply sum_eq_zero
          intro k hk
          exact hs k (mem_of_mem_erase hk) (by have := ne_of_mem_erase hk; omega)
        rw [hsum]
        simpa only [Int.zero_emod, add_zero, Int.emod_emod] using (hb n (by omega)).1
      · have hr := congrArg (fun q : ℚ => (n.factorial : ℚ) * q) (hrec n)
        rw [mul_sum] at hr
        have ht (k : ℕ) (hk : k ∈ range (n + 1)) :
            (n.factorial : ℚ) * (f (n - k) * 2 ^ ((k + 1) ^ 2)) =
              (2 : ℚ) ^ (n + 1) *
              ((n.descFactorial k : ℤ) * 2 ^ (k * (k + 1)) * b (n - k) : ℤ) := by
          have hk' : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
          have hf : (n.factorial : ℚ) =
              ((n - k).factorial : ℚ) * (n.descFactorial k : ℚ) := by
            exact_mod_cast (Nat.factorial_mul_descFactorial hk').symm
          rw [hf]
          have hi := (hb (n - k) (by omega)).2
          rw [show ((n - k).factorial : ℚ) * (n.descFactorial k : ℚ) *
              (f (n - k) * 2 ^ ((k + 1) ^ 2)) =
              (n.descFactorial k : ℚ) * (((n - k).factorial : ℚ) * f (n - k)) *
                2 ^ ((k + 1) ^ 2) by ring, hi]
          push_cast
          have he : n - k + (k + 1) ^ 2 = n + 1 + k * (k + 1) := by
            have := Nat.sub_add_cancel hk'
            nlinarith
          have hp : (2 : ℚ)^(n-k) * 2^((k+1)^2) = 2^(n+1) * 2^(k*(k+1)) := by
            rw [← pow_add, he, pow_add]
          calc
            _ = (n.descFactorial k : ℚ) * (b (n-k) : ℚ) *
                (2^(n-k) * 2^((k+1)^2)) := by ring
            _ = _ := by rw [hp]; ring
        rw [sum_congr rfl ht, ← mul_sum] at hr
        simpa only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
          Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast,
          mul_assoc, mul_comm, mul_left_comm, z] using hr


set_option maxHeartbeats 1000000 in
private theorem odd_quotient_of_integral_normalization
    (n : ℕ) (x b : ℤ) (hb : b % 4 = 1)
    (h : (n.factorial : ℤ) * x = (2 : ℤ) ^ n * b) :
    ∃ z : ℤ, Odd z ∧ x = (2 : ℤ) ^ (Nat.digits 2 n).sum * z := by
  let s := (Nat.digits 2 n).sum
  let e := n.factorial.factorization 2
  let d := n.factorial / 2 ^ e
  have hes : e + s = n := by
    simpa only [e, s] using
      D5.S3.Arith.FactorialRatio.BalaA361034Parity.binary_factorial_balance n
  have hf : (2 : ℤ) ^ e * (d : ℤ) = n.factorial := by
    exact_mod_cast Nat.ordProj_mul_ordCompl_eq_self n.factorial 2
  have hcancel : (d : ℤ) * x = (2 : ℤ)^s * b := by
    apply mul_left_cancel₀ (pow_ne_zero e (two_ne_zero : (2 : ℤ) ≠ 0))
    calc
      2^e * ((d : ℤ) * x) = (n.factorial : ℤ) * x := by rw [← mul_assoc, hf]
      _ = 2^n * b := h
      _ = 2^e * (2^s * b) := by rw [← hes, pow_add, mul_assoc]
  have hc : Nat.Coprime 2 d := Nat.coprime_ordCompl Nat.prime_two n.factorial_ne_zero
  have hcz : IsCoprime ((2 : ℤ)^s) (d : ℤ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (hc.pow_left s).isCoprime
  obtain ⟨z, hz⟩ := hcz.dvd_of_dvd_mul_left (show (2 : ℤ)^s ∣ (d : ℤ) * x from
    hcancel.symm ▸ dvd_mul_right _ _)
  refine ⟨z, ?_, hz⟩
  have hdz : (d : ℤ) * z = b := by
    apply mul_left_cancel₀ (pow_ne_zero s (two_ne_zero : (2 : ℤ) ≠ 0))
    calc
      2^s * ((d : ℤ) * z) = (d : ℤ) * x := by rw [hz]; ring
      _ = 2^s * b := hcancel
  apply Int.Odd.of_mul_right (m := (d : ℤ))
  rw [hdz, Int.odd_iff]
  omega

set_option maxHeartbeats 1000000 in
theorem result : claim := by
  let f : ℕ → ℚ := fun n => coeff n (exponentialSum (fun k => (2 : ℚ) ^ (k ^ 2)))
  have hzero : f 0 = 1 := by
    simpa only [f, coeff_zero_eq_constantCoeff] using
      D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality.exponential_sum_constant
        (fun k : ℕ => (2 : ℚ) ^ (k ^ 2))
  have hrec : ∀ n : ℕ, f (n + 1) * (n + 1 : ℚ) =
      ∑ k ∈ range (n + 1), f (n - k) * (2 : ℚ) ^ ((k + 1) ^ 2) := by
    intro n
    let a : ℕ → ℚ := fun k => (2 : ℚ) ^ (k ^ 2)
    have heq :=
      D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality.exponential_sum_equation a
    change X * derivative (exponentialSum a) =
      (mk (fun k => if k = 0 then 0 else a k -
        coeff k ((X * derivative (R := ℚ) 0) * 0 * invOfUnit (1 - C (k : ℚ) * 0) 1))) *
          exponentialSum a at heq
    simp only [mul_zero, zero_mul, map_zero, sub_zero] at heq
    have h := congrArg (coeff (n + 1)) heq
    rw [coeff_succ_X_mul, coeff_derivative, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => coeff i (mk (fun k => if k = 0 then 0 else a k)) *
          coeff j (exponentialSum a)) (n + 1)] at h
    rw [Finset.sum_range_succ'] at h
    simp only [coeff_mk, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      ite_false, ite_true, zero_mul, add_zero] at h
    simpa only [Nat.add_sub_add_right, Nat.cast_add, Nat.cast_one, a, f, mul_comm] using h
  have hi := D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality.result
    ℚ inferInstance inferInstance (fun n => (2 : ℚ) ^ n) geometric_exponential_integral
  have hpow : (fun n : ℕ => ((2 : ℚ)^n)^n) = (fun n => (2 : ℚ)^(n^2)) := by
    funext n
    rw [← pow_mul, pow_two]
  rw [hpow] at hi
  change ∀ n, ∃ z : ℤ, Odd z ∧ f n = (2 : ℚ) ^ (Nat.digits 2 n).sum * (z : ℚ)
  intro n
  obtain ⟨x, hx⟩ := hi n
  obtain ⟨b, hb, heq⟩ := normalized_integral_mod_four f hzero hrec n
  change f n = (x : ℚ) at hx
  rw [hx] at heq
  have heZ : (n.factorial : ℤ)*x = (2:ℤ)^n*b := by exact_mod_cast heq
  obtain ⟨z, hz, hez⟩ := odd_quotient_of_integral_normalization n x b hb heZ
  refine ⟨z, hz, ?_⟩
  rw [hx]
  exact_mod_cast hez

end D5.S3.Arith.LocalDold.HannaA155200BinaryValuation
