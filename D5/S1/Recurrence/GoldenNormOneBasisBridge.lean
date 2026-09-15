/- GID: D5/S1/Recurrence/GoldenNormOneBasisBridge
   generality: I
   mirror-B: none(waiver:actual-golden-basis-transfer)
   mirror-E: none(waiver:all-norm-one-elements-and-moduli)
   anchors: []
   utility: none
   digest: The norm-one companion intertwines with actual golden multiplication, with determinant minus the golden coefficient. Return equivalence requires that coefficient to be a unit; bad basis primes cannot be treated as WSS witnesses. -/

import D5.S1.Recurrence.NormOneCriticalPrimes

set_option autoImplicit false

namespace D5.S1.Recurrence.GoldenNormOneBasisBridge

open Matrix LucasEvenDescent D5.S0.Carrier D5.S1.Scale
open scoped Matrix

section Ring

variable {R : Type*} [CommRing R]

def actionMatrix (a b : R) : Matrix (Fin 2) (Fin 2) R := !![a + b, b; b, a]
def basisMatrix (a b : R) : Matrix (Fin 2) (Fin 2) R := !![b, 0; a, -1]
def traceCompanion (a b : R) : Matrix (Fin 2) (Fin 2) R := !![2 * a + b, -1; 1, 0]

theorem basis_determinant (a b : R) : (basisMatrix a b).det = -b := by
  simp [basisMatrix, Matrix.det_fin_two]

/-- The original quadratic relation gives the exact intertwining, even at bad primes. -/
theorem norm_one_intertwining (a b : R) (hn : a ^ 2 + a * b - b ^ 2 = 1) :
    actionMatrix a b * basisMatrix a b = basisMatrix a b * traceCompanion a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [actionMatrix, basisMatrix, traceCompanion, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination -hn

theorem power_intertwining (a b : R) (hn : a ^ 2 + a * b - b ^ 2 = 1) (t : ℕ) :
    actionMatrix a b ^ t * basisMatrix a b = basisMatrix a b * traceCompanion a b ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [pow_succ, mul_assoc, norm_one_intertwining a b hn, ← mul_assoc, ih,
        mul_assoc, ← pow_succ]

/-- Return equivalence requires a genuine inverse to the basis determinant. -/
theorem returns_iff_of_unit_coefficient (a b : R)
    (hn : a ^ 2 + a * b - b ^ 2 = 1) (hb : IsUnit b) (t : ℕ) :
    actionMatrix a b ^ t = 1 ↔ traceCompanion a b ^ t = 1 := by
  obtain ⟨u, hu⟩ := hb
  let c : R := ↑u⁻¹
  have hc : b * c = 1 := by rw [← hu]; simp [c]
  let S : Matrix (Fin 2) (Fin 2) R := !![c, 0; a * c, -1]
  have hPS : basisMatrix a b * S = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [basisMatrix, S, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hc | linear_combination a * hc
  have hSP : S * basisMatrix a b = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [basisMatrix, S, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hc | linear_combination a * hc
  have h := power_intertwining a b hn t
  constructor
  · intro hA
    calc
      traceCompanion a b ^ t = (S * basisMatrix a b) * traceCompanion a b ^ t := by
        rw [hSP, one_mul]
      _ = S * (actionMatrix a b ^ t * basisMatrix a b) := by rw [mul_assoc, h]
      _ = 1 := by rw [hA, one_mul, hSP]
  · intro hC
    calc
      actionMatrix a b ^ t = actionMatrix a b ^ t * (basisMatrix a b * S) := by
        rw [hPS, mul_one]
      _ = (basisMatrix a b * traceCompanion a b ^ t) * S := by rw [← mul_assoc, h]
      _ = 1 := by rw [hC, mul_one, hPS]

end Ring

/-- Action of the ORIGINAL golden integer on coordinates ordered as (b,a). -/
def goldenAction (m : ℕ) (x : GoldenInt) : Matrix (Fin 2) (Fin 2) (ZMod m) :=
  actionMatrix (x.a : ZMod m) (x.b : ZMod m)

theorem goldenAction_mulVec (m : ℕ) (x y : GoldenInt) :
    goldenAction m x *ᵥ ![(y.b : ZMod m), (y.a : ZMod m)] =
      ![((x * y).b : ZMod m), ((x * y).a : ZMod m)] := by
  ext i
  fin_cases i <;>
    simp [goldenAction, actionMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      a_mul, b_mul] <;> ring

/-- Every even golden power has a norm-one companion; its return times agree wherever
its actual golden coefficient is invertible. No universal basis invertibility is assumed. -/
theorem even_golden_returns_iff (k m t : ℕ)
    (hb : IsUnit (((phi ^ (2 * k)).b : ℤ) : ZMod m)) :
    goldenAction m (phi ^ (2 * k)) ^ t = 1 ↔
      companion (goldenLucas (2 * k) : ZMod m) (1 : (ZMod m)ˣ) ^ t = 1 := by
  have hnZ := norm_phi_pow (2 * k)
  have he : Even (2 * k) := ⟨k, by omega⟩
  rw [he.neg_one_pow] at hnZ
  have hn : (((phi ^ (2 * k)).a : ℤ) : ZMod m) ^ 2 +
      (((phi ^ (2 * k)).a : ℤ) : ZMod m) * (((phi ^ (2 * k)).b : ℤ) : ZMod m) -
      (((phi ^ (2 * k)).b : ℤ) : ZMod m) ^ 2 = 1 := by
    dsimp [D5.S0.Carrier.norm] at hnZ
    have hcast := congrArg (fun z : ℤ => (z : ZMod m)) hnZ
    simpa only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_one, pow_two] using hcast
  have hc : traceCompanion (((phi ^ (2 * k)).a : ℤ) : ZMod m)
      (((phi ^ (2 * k)).b : ℤ) : ZMod m) =
      (↑(companion (goldenLucas (2 * k) : ZMod m) (1 : (ZMod m)ˣ)) :
        Matrix (Fin 2) (Fin 2) (ZMod m)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [traceCompanion, companion, goldenLucas, D5.S0.Carrier.trace]
  change actionMatrix _ _ ^ t = 1 ↔ _
  rw [returns_iff_of_unit_coefficient _ _ hn hb t, hc]
  constructor
  · intro h
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h
  · intro h
    have hv := congrArg Units.val h
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using hv

/-- The basis obstruction is the actual Fibonacci coefficient, including depth zero. -/
theorem even_golden_basis_determinant (k m : ℕ) :
    (basisMatrix (((phi ^ (2 * k)).a : ℤ) : ZMod m)
      (((phi ^ (2 * k)).b : ℤ) : ZMod m)).det = -(Nat.fib (2 * k) : ZMod m) := by
  rw [basis_determinant, golden_phi_pow_b_eq_fib_index]
  simp

#print axioms basis_determinant
#print axioms norm_one_intertwining
#print axioms power_intertwining
#print axioms returns_iff_of_unit_coefficient
#print axioms goldenAction_mulVec
#print axioms even_golden_returns_iff
#print axioms even_golden_basis_determinant

end D5.S1.Recurrence.GoldenNormOneBasisBridge
