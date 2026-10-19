/- GID: D5/S1/Recurrence/Invariants/HannaBilateralThetaModFour
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaBilateralThetaModFour
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna A380060 has integral coefficients and the square residue pattern modulo four. -/

/-
Public theorem result:
proof_shape: content (coefficient-prefix induction constructs the integer solution).
escape_witness: none.
admission_basis: open-problem-resolution (#18872; Proved).
Direct frozen dependencies: original declarations from
UnitReversionSquareParity, QuotientThetaCompositionModFour and
BilateralQuarterShiftThetaModFour; their base declaration identities follow.
D5/S1/Recurrence/Invariants/UnitReversionSquareParity.agree_pow: sha256:e945155d0fd4037744bdfa3b501a69322686a328c9f2a97407086578f1d884e2
D5/S1/Recurrence/Invariants/UnitReversionSquareParity.agree_mul: sha256:585faad9db8267f33e8a75fd9f2c24f1c1f52db44340a96fd0994e4f1ee77283
D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.inverse_agreement: sha256:d1379c38e0f8cbcd0bdb5f7cf15b769e6f62621f650163840608c4c7690dcd03
D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.map_inverse: sha256:abefeeb8f16faff8a0ea797ffdbd624e7161dd16717338880296e1818a2be34b
D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.square_approximation: sha256:7d7be03003fe434a364d3134620842c49008bd6ecc874ece4f397d9302fff4b1
D5/S1/Recurrence/Invariants/UnitReversionSquareParity.Agree: sha256:eb82dc176dba692d1a4fdabe8e1432cde2ea59af844e13b4f551e71d85d5d1ed
D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.squareSupport: sha256:f3df41faa5c8bd252767c001de1a94c557d8e0077e29c85923e7a76aa31c2aec
These are declaration statement_ids before publication, not module pins.
The source equations are the literal IsGF and claim bodies; proofs use the original
coefficient-agreement, unit-inverse and square-support declarations.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19022

Per-declaration proof shapes (all escape_witness values are none):
denominator_constant: proof_shape: bind-only; consumers: reciprocal_mul, summand_agree, map_reciprocal, rational_summand.
reciprocal_mul: proof_shape: bind-only; consumers: summand_one.
summand_agree: proof_shape: bind-only; consumers: step_agree.
step_agree: proof_shape: bind-only; consumers: approximation_stable, solution_fixed, fixed_unique.
approximation_stable: proof_shape: content; consumers: solution_agree.
solution_agree: proof_shape: content; consumers: solution_fixed.
solution_fixed: proof_shape: content; consumers: rational_solution, solution_mod_two, solution_coefficient.
fixed_unique: proof_shape: content; consumers: rational_unique.
map_denominator: proof_shape: bind-only; consumers: map_reciprocal.
map_reciprocal: proof_shape: bind-only; consumers: map_summand.
map_summand: proof_shape: bind-only; consumers: map_step, summand_mod_two.
map_step: proof_shape: bind-only; consumers: rational_solution, solution_mod_two.
rational_summand: proof_shape: bind-only; consumers: isGF_iff.
isGF_iff: proof_shape: bind-only; consumers: rational_solution, rational_unique.
rational_solution: proof_shape: content; consumers: rational_unique, result.
rational_unique: proof_shape: content; consumers: result.
step_char_two: proof_shape: bind-only; consumers: solution_mod_two.
solution_mod_two: proof_shape: content; consumers: summand_mod_two.
summand_one: proof_shape: bind-only; consumers: summand_mod_two.
summand_mod_two: proof_shape: content; consumers: halfCoeff_mod_two.
theta_coefficient: proof_shape: bind-only; consumers: halfCoeff_mod_two.
halfCoeff_mod_two: proof_shape: content; consumers: result.
solution_coefficient: proof_shape: content; consumers: result.
residue_arithmetic: proof_shape: bind-only; consumers: result.
result: proof_shape: content; consumers: settlement #18872.
Utility none: all assertions are unbounded symbolic statements, with no bounded
certificate, enumeration, checker or numeric reduction.
-/

import D5.S1.Recurrence.Residue.QuotientThetaCompositionModFour
import D5.S1.Recurrence.Bilateral.BilateralQuarterShiftThetaModFour
import D5.S1.Recurrence.Invariants.UnitReversionSquareParity

set_option autoImplicit false

namespace D5.S1.Recurrence.Invariants.HannaBilateralThetaModFour

open PowerSeries

/-- OEIS A380060: "G.f. A(x) satisfies A(x) = Sum_{n=-oo..+oo} x^(n^2) * (A(x) - x^n)^n/(1 - x^n*A(x))^n".
The term `n = 0` is `1` and the term `-n` equals the term `n` (the entry's comment "The term ... is invariant
under sign reversal of n" and its formula (2)), so the equation reads
`A(x) = 1 + 2 * Sum_{n>=1} x^(n^2) * (A(x) - x^n)^n/(1 - x^n*A(x))^n`; the summand `n` has order `n^2`, so only
`n ≤ m` contribute to `x^m`. -/
def IsGF (A : PowerSeries ℚ) : Prop :=
  A = mk fun m => coeff m (1 + 2 * ∑ n ∈ Finset.Icc 1 m,
    (X : PowerSeries ℚ) ^ (n ^ 2) * (A - X ^ n) ^ n * ((1 - X ^ n * A) ^ n)⁻¹)

/-- OEIS A380060 (P. D. Hanna), conjecture: "for n > 0, a(n) == 2 (mod 4) iff n is a square, and a(n) is
divisible by 4 when n is nonsquare". The terms are integers. -/
def claim : Prop :=
  (∃ A, IsGF A) ∧
    ∀ A, IsGF A → ∀ n : ℕ, 0 < n → ∃ z : ℤ, coeff n A = z ∧
      (z ≡ 2 [ZMOD 4] ↔ IsSquare n) ∧ (¬ IsSquare n → (4 : ℤ) ∣ z)

end D5.S1.Recurrence.Invariants.HannaBilateralThetaModFour

open PowerSeries
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity (Agree agree_pow agree_mul)
open D5.S1.Recurrence.Bilateral.BilateralQuarterShiftThetaModFour (squareSupport square_approximation)
open D5.S1.Recurrence.Residue.QuotientThetaCompositionModFour (inverse_agreement map_inverse)

namespace D5.S1.Recurrence.Invariants.HannaBilateralThetaModFour
section Integral
variable {R : Type*} [CommRing R]

private noncomputable def denominator (m : ℕ) (A : PowerSeries R) : PowerSeries R :=
  (1 - X ^ m * A) ^ m
private noncomputable def reciprocal (m : ℕ) (A : PowerSeries R) : PowerSeries R :=
  invOfUnit (denominator m A) 1
private noncomputable def summand (m : ℕ) (A : PowerSeries R) : PowerSeries R :=
  X ^ (m ^ 2) * ((A - X ^ m) ^ m * reciprocal m A)
private noncomputable def step (A : PowerSeries R) : PowerSeries R :=
  mk fun k => coeff k (1 + 2 * ∑ m ∈ Finset.Icc 1 k, summand m A)

private theorem denominator_constant (m : ℕ) (hm : 0 < m) (A : PowerSeries R) :
    constantCoeff (denominator m A) = 1 := by
  simp [denominator, hm.ne']

private theorem reciprocal_mul (m : ℕ) (hm : 0 < m) (A : PowerSeries R) :
    reciprocal m A * denominator m A = 1 :=
  invOfUnit_mul _ _ (by simpa using denominator_constant m hm A)

private theorem summand_agree {d m : ℕ} (hm : 0 < m) {A B : PowerSeries R}
    (h : Agree d A B) : Agree (d + m ^ 2) (summand m A) (summand m B) := by
  have hn : Agree d ((A - X ^ m) ^ m) ((B - X ^ m) ^ m) := by
    apply agree_pow
    intro k hk
    simp only [map_sub, h k hk]
  have hd : Agree d (denominator m A) (denominator m B) := by
    apply agree_pow
    have hx := agree_mul (show Agree d (X ^ m) (X ^ m) from fun _ _ => rfl) h
    intro k hk
    simpa only [map_sub] using congrArg (fun x => coeff k (1 : PowerSeries R) - x) (hx k hk)
  have hi := inverse_agreement (denominator_constant m hm A) (denominator_constant m hm B) hd
  have hp := agree_mul hn hi
  intro k hk
  simp only [summand, coeff_X_pow_mul']
  split_ifs with hm'
  · exact hp (k - m ^ 2) (by omega)
  · rfl

private theorem step_agree {d : ℕ} {A B : PowerSeries R} (h : Agree d A B) :
    Agree (d + 1) (step A) (step B) := by
  intro k hk
  simp only [step, coeff_mk, map_add, coeff_ofNat_mul, map_sum]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  have hm' : 0 < m := (Finset.mem_Icc.mp hm).1
  exact summand_agree hm' h k (by nlinarith [Nat.one_le_pow 2 m hm'])

private noncomputable def approximation : ℕ → PowerSeries R
  | 0 => 1
  | n + 1 => step (approximation n)

private theorem approximation_stable {d k : ℕ} (h : d ≤ k) :
    Agree d (approximation (R := R) d) (approximation k) := by
  induction d generalizing k with
  | zero => intro n hn; omega
  | succ d ih =>
    cases k with
    | zero => omega
    | succ k => exact step_agree (ih (by omega))

private noncomputable def solution : PowerSeries R :=
  mk fun n => coeff n (approximation (R := R) (n + 1))

private theorem solution_agree (d : ℕ) : Agree d (solution (R := R)) (approximation d) := by
  intro n hn
  simpa only [solution, coeff_mk] using
    approximation_stable (R := R) (by omega : n + 1 ≤ d) n (by omega)

private theorem solution_fixed : solution (R := R) = step solution := by
  ext n
  have h1 := solution_agree (R := R) (n + 2) n (by omega)
  have h2 := step_agree (solution_agree (R := R) (n + 1)) n (by omega)
  exact h1.trans h2.symm

private theorem fixed_unique {A B : PowerSeries R} (ha : A = step A) (hb : B = step B) : A = B := by
  have h : ∀ d, Agree d A B := by
    intro d
    induction d with
    | zero => intro n hn; omega
    | succ d ih => simpa only [← ha, ← hb] using step_agree ih
  ext n
  exact h (n + 1) n (by omega)

end Integral
section Maps
variable {R S : Type*} [CommRing R] [CommRing S]

private theorem map_denominator (f : R →+* S) (m : ℕ) (A : PowerSeries R) :
    (denominator m A).map f = denominator m (A.map f) := by
  simp [denominator]

private theorem map_reciprocal (f : R →+* S) (m : ℕ) (hm : 0 < m) (A : PowerSeries R) :
    (reciprocal m A).map f = reciprocal m (A.map f) := by
  unfold reciprocal
  rw [map_inverse f _ (denominator_constant m hm A), map_denominator]

private theorem map_summand (f : R →+* S) (m : ℕ) (hm : 0 < m) (A : PowerSeries R) :
    (summand m A).map f = summand m (A.map f) := by
  simp [summand, map_reciprocal f m hm]

private theorem map_step (f : R →+* S) (A : PowerSeries R) :
    (step A).map f = step (A.map f) := by
  classical
  ext k
  simp only [coeff_map, step, coeff_mk]
  rw [← coeff_map]
  congr 1
  simp only [map_add, map_mul, map_ofNat, map_one, map_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro m hm
  exact map_summand f m (Finset.mem_Icc.mp hm).1 A

end Maps

private theorem rational_summand (m : ℕ) (hm : 0 < m) (A : PowerSeries ℚ) :
    summand m A = X ^ (m ^ 2) * (A - X ^ m) ^ m * ((1 - X ^ m * A) ^ m)⁻¹ := by
  rw [summand, reciprocal, invOfUnit_eq' _ 1 (by simpa using denominator_constant m hm A)]
  exact (mul_assoc _ _ _).symm

private theorem isGF_iff (A : PowerSeries ℚ) : IsGF A ↔ A = step A := by
  classical
  have he : step A = mk (fun k => coeff k (1 + 2 * ∑ m ∈ Finset.Icc 1 k,
      X ^ (m ^ 2) * (A - X ^ m) ^ m * ((1 - X ^ m * A) ^ m)⁻¹)) := by
    ext k
    simp only [step, coeff_mk]
    congr 3
    apply Finset.sum_congr rfl
    intro m hm
    exact rational_summand m (Finset.mem_Icc.mp hm).1 A
  unfold IsGF
  rw [he]

private theorem rational_solution : IsGF ((solution (R := ℤ)).map (Int.castRingHom ℚ)) := by
  apply (isGF_iff _).mpr
  rw [← map_step, ← solution_fixed]

private theorem rational_unique (A : PowerSeries ℚ) (ha : IsGF A) :
    A = (solution (R := ℤ)).map (Int.castRingHom ℚ) :=
  fixed_unique ((isGF_iff _).mp ha) ((isGF_iff _).mp rational_solution)



private theorem step_char_two (B : PowerSeries (ZMod 2)) : step B = 1 := by
  ext k
  simp [step, CharP.ofNat_eq_zero (ZMod 2) 2]

private theorem solution_mod_two : (solution (R := ℤ)).map (Int.castRingHom (ZMod 2)) = 1 := by
  rw [solution_fixed, map_step, step_char_two]

private theorem summand_one {R : Type*} [CommRing R] (m : ℕ) (hm : 0 < m) :
    summand m (1 : PowerSeries R) = X ^ (m ^ 2) := by
  rw [summand, show (1 - X ^ m) ^ m = denominator m (1 : PowerSeries R) by simp [denominator]]
  rw [mul_comm (denominator m 1), reciprocal_mul m hm 1, mul_one]

private theorem summand_mod_two (m : ℕ) (hm : 0 < m) :
    (summand m (solution (R := ℤ))).map (Int.castRingHom (ZMod 2)) = X ^ (m ^ 2) := by
  rw [map_summand _ m hm, solution_mod_two, summand_one m hm]

private theorem theta_coefficient (n : ℕ) (hn : 0 < n) :
    (∑ m ∈ Finset.Icc 1 n, coeff n ((X : PowerSeries (ZMod 2)) ^ (m ^ 2))) =
      if IsSquare n then 1 else 0 := by
  classical
  have h := square_approximation (R := ZMod 2) n n (by omega)
  simp only [squareSupport, coeff_mk] at h
  rw [ite_eq_right hn.ne', map_sum, Finset.sum_range_succ] at h
  have hz : coeff n ((X : PowerSeries (ZMod 2)) ^ ((n + 1) ^ 2)) = 0 := by
    rw [coeff_X_pow, ite_eq_right (by nlinarith)]
  rw [hz, add_zero] at h
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simpa only [Nat.add_sub_cancel, Nat.add_comm] using h.symm

private noncomputable def halfCoeff (n : ℕ) : ℤ :=
  ∑ m ∈ Finset.Icc 1 n, coeff n (summand m (solution (R := ℤ)))

private theorem halfCoeff_mod_two (n : ℕ) (hn : 0 < n) :
    (halfCoeff n : ZMod 2) = if IsSquare n then 1 else 0 := by
  classical
  rw [halfCoeff, Int.cast_sum]
  have he : (∑ m ∈ Finset.Icc 1 n, ((coeff n (summand m (solution (R := ℤ))) : ℤ) : ZMod 2)) =
      ∑ m ∈ Finset.Icc 1 n, coeff n ((X : PowerSeries (ZMod 2)) ^ (m ^ 2)) := by
    apply Finset.sum_congr rfl
    intro m hm
    have h := congrArg (coeff n) (summand_mod_two m (Finset.mem_Icc.mp hm).1)
    exact h
  rw [he, theta_coefficient n hn]

private theorem solution_coefficient (n : ℕ) (hn : 0 < n) :
    coeff n (solution (R := ℤ)) = 2 * halfCoeff n := by
  have h := congrArg (coeff n) (solution_fixed (R := ℤ))
  simpa [step, halfCoeff, coeff_one, hn.ne'] using h

private theorem residue_arithmetic (c : ℤ) (s : Prop) [Decidable s] (hs : (c : ZMod 2) = if s then 1 else 0) :
    ((2 * c) ≡ 2 [ZMOD 4] ↔ s) ∧ (¬ s → (4 : ℤ) ∣ 2 * c) := by
  classical
  by_cases h : s
  · have hc : Odd c := (ZMod.intCast_eq_one_iff_odd).mp (by simpa [h] using hs)
    obtain ⟨k, hk⟩ := hc
    constructor
    · constructor
      · intro _; exact h
      · intro _
        show (2 * c) % 4 = 2 % 4
        omega
    · intro hnot
      exact (hnot h).elim
  · have hc : (2 : ℤ) ∣ c := (ZMod.intCast_zmod_eq_zero_iff_dvd c 2).mp (by simpa [h] using hs)
    obtain ⟨k, hk⟩ := hc
    constructor
    · constructor
      · intro he
        change (2 * c) % 4 = 2 % 4 at he
        omega
      · intro hyes; exact (h hyes).elim
    · intro _
      exact ⟨k, by omega⟩

theorem result : claim := by
  classical
  constructor
  · exact ⟨_, rational_solution⟩
  · intro A ha n hn
    refine ⟨coeff n (solution (R := ℤ)), ?_, ?_⟩
    · rw [rational_unique A ha, coeff_map]
      rfl
    · rw [solution_coefficient n hn]
      exact residue_arithmetic (halfCoeff n) (IsSquare n) (halfCoeff_mod_two n hn)

end D5.S1.Recurrence.Invariants.HannaBilateralThetaModFour
