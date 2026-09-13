/- GID: D5/S1/Recurrence/GoldenTrinomialTraceObstruction
   generality: G
   mirror-B: none(waiver:existing-golden-carrier-adapter)
   mirror-E: none(waiver:all-odd-indices-and-all-moduli)
   anchors: []
   digest: The evaluated power-compositional trinomial has exactly the scalar divisibility of the original Lucas trace excess; no number-field index theorem is assumed. -/

import D5.S1.Scale.Lucas
import D5.S3.Arith.GoldenApparition
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S1.Recurrence.GoldenTrinomialTraceObstruction

open D5.S0.Carrier D5.S1.Scale D5.S3.Arith.GoldenApparition
open Polynomial

noncomputable section

/-- The actual polynomial used in the golden specialization of Jones's theorem. -/
def compositionalTrinomial (n : ℕ) : Polynomial ℤ := X ^ (2 * n) - X ^ n - 1

/-- Evaluation in the original golden-integer ring, not a newly postulated root. -/
def evaluatedDefect (n : ℕ) : GoldenInt :=
  Polynomial.eval₂ (Int.castRingHom GoldenInt) phi (compositionalTrinomial n)

def traceExcess (n : ℕ) : ℤ := goldenLucas n - 1

lemma evaluatedDefect_eq (n : ℕ) :
    evaluatedDefect n = phi ^ (2 * n) - phi ^ n - 1 := by
  simp [evaluatedDefect, compositionalTrinomial]

/-- Cayley-Hamilton in the existing integral coordinates. -/
private lemma golden_characteristic_identity (x : GoldenInt) :
    x ^ 2 - (trace x : GoldenInt) * x + (norm x : GoldenInt) = 0 := by
  apply GoldenInt.ext <;>
    simp [pow_two, a_mul, b_mul, trace, norm] <;> ring

private lemma negative_norm_inverse (x : GoldenInt) (hx : norm x = -1) :
    x * (-conj x) = 1 := by
  rw [mul_neg, ← norm_eq_mul_conj, hx]
  norm_num

private lemma negative_norm_factor (x : GoldenInt) (hx : norm x = -1) :
    x ^ 2 - x - 1 = ((trace x - 1 : ℤ) : GoldenInt) * x := by
  have h := golden_characteristic_identity x
  rw [hx] at h
  push_cast at h ⊢
  linear_combination h

/-- Exact all-odd-index factorization. Prime indices are a specialization. -/
theorem evaluatedDefect_factor (n : ℕ) (hn : Odd n) :
    evaluatedDefect n = (traceExcess n : GoldenInt) * phi ^ n := by
  rw [evaluatedDefect_eq, show 2 * n = n * 2 by omega, pow_mul]
  apply negative_norm_factor
  rw [norm_phi_pow, hn.neg_one_pow]

/-- Scalar divisibility is identical on the two sides, including composite and zero scalars.
Cancellation uses an explicit inverse in GoldenInt; no residue-ring cancellation is assumed. -/
theorem scalar_divisibility_iff (q : ℤ) (n : ℕ) (hn : Odd n) :
    (q : GoldenInt) ∣ evaluatedDefect n ↔ q ∣ traceExcess n := by
  have hinv : phi ^ n * (-conj (phi ^ n)) = 1 :=
    negative_norm_inverse _ (by rw [norm_phi_pow, hn.neg_one_pow])
  constructor
  · rintro ⟨z, hz⟩
    have hc : (traceExcess n : GoldenInt) =
        (q : GoldenInt) * (z * (-conj (phi ^ n))) := by
      calc
        _ = ((traceExcess n : GoldenInt) * phi ^ n) * (-conj (phi ^ n)) := by
          rw [mul_assoc, hinv, mul_one]
        _ = evaluatedDefect n * (-conj (phi ^ n)) := by rw [evaluatedDefect_factor n hn]
        _ = _ := by rw [hz, mul_assoc]
    refine ⟨(z * (-conj (phi ^ n))).a, ?_⟩
    simpa using congrArg GoldenInt.a hc
  · rintro ⟨k, hk⟩
    refine ⟨(k : GoldenInt) * phi ^ n, ?_⟩
    rw [evaluatedDefect_factor n hn, hk, Int.cast_mul, mul_assoc]

/-- The obstruction seen at every modular precision uses the already existing GoldenMod. -/
theorem reduced_defect_zero_iff (q n : ℕ) (hn : Odd n) :
    GoldenMod.reduce q (evaluatedDefect n) = 0 ↔ (traceExcess n : ZMod q) = 0 := by
  have hinv : phi ^ n * (-conj (phi ^ n)) = 1 :=
    negative_norm_inverse _ (by rw [norm_phi_pow, hn.neg_one_pow])
  have hinvMod : GoldenMod.reduce q (phi ^ n) * GoldenMod.reduce q (-conj (phi ^ n)) = 1 := by
    rw [← map_mul, hinv, map_one]
  rw [evaluatedDefect_factor n hn, map_mul, map_intCast]
  constructor
  · intro h
    have he := congrArg (fun z : GoldenMod q => z * GoldenMod.reduce q (-conj (phi ^ n))) h
    rw [mul_assoc, hinvMod, mul_one, zero_mul] at he
    simpa using congrArg GoldenMod.a he
  · intro h
    have hs : (traceExcess n : GoldenMod q) = 0 := by
      apply GoldenMod.ext
      · simpa using h
      · simp
    rw [hs, zero_mul]

/-- Both real embeddings have an exact common scalar defect; the norm records its square. -/
theorem defect_norm (n : ℕ) (hn : Odd n) :
    norm (evaluatedDefect n) = -(traceExcess n) ^ 2 := by
  rw [evaluatedDefect_factor n hn, norm_mul, norm_phi_pow, hn.neg_one_pow]
  simp [norm, pow_two]

/-- The golden specialization of the polynomial's local p^2 test is a prime-index trace test.
This does not identify the index of a number-field order or assert WSS existence. -/
theorem prime_square_test (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    GoldenMod.reduce (p ^ 2) (evaluatedDefect p) = 0 ↔
      ((p : ℤ) ^ 2) ∣ goldenLucas p - 1 := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  rw [reduced_defect_zero_iff _ _ hodd, ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [traceExcess, Nat.cast_pow]

end
end D5.S1.Recurrence.GoldenTrinomialTraceObstruction
