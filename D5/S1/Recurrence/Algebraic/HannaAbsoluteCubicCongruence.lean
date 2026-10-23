/- GID: D5/S1/Recurrence/Algebraic/HannaAbsoluteCubicCongruence
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaAbsoluteCubicCongruence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Coefficient contraction and reduction modulo two prove Hanna's cubic congruence. -/

/-
result:
  proof_shape: bind-only (normalized contraction and the frozen cubic comparison)
  escape_witness: none
  admission_basis: open-problem-resolution (#18828; Proved)
Direct frozen dependencies:
  D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity.absSeries
    declaration statement_id: sha256:6750066fc3735d8621ea55155bd271360f67ff82305365101d87299272caa26d
  D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.generatingSeries
    declaration statement_id: sha256:3612e062cfa99d038b5b902d3512bf6f0f212e3705c25f87402c925ac567bb92
  D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.generating_equation
    declaration statement_id: sha256:abe819e1cf6d17e6e49384a7c17ca626e00f33db0fbb80469f3ef9e34ac5dbba
  D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity.map_abs
    declaration statement_id: sha256:4a6db6498012db5aa8de263506b6718badd8e80d119caf89ee01d1b939793082
  D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.reduced_cubic
    declaration statement_id: sha256:1428deb5e31a2d451eca6972436727e6793a6b872637e8c2927e3d78f39d89ba
  D5/S1/Recurrence/Invariants/UnitReversionSquareParity.Agree
    declaration statement_id: sha256:76d7ce5ef0f66968d4516f93f05e27e9125f8f29944ffacca0d95b580f786d34
  D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.Agree
    declaration statement_id: sha256:2ee8ed98da278ffd1ebd198b2092408351dcd0b50f49fa7c4d1de3e9724691b9
  D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.agree_inv
    declaration statement_id: sha256:08ca54a1ff0f6dac6300f134bbfa5bd27fd9e2c7f64d37b46218787d9b012d97
  D5/S1/Recurrence/Invariants/UnitReversionSquareParity.agree_pow
    declaration statement_id: sha256:0c9456bb3300b1f38308df2b3a2abc2d51d68b3b05356990e7bc5cfc4bfb0dbb
  D5/S1/Recurrence/Invariants/UnitReversionSquareParity.agree_X
    declaration statement_id: sha256:cb4bbeb74f9bb4de6a237dc609532d94ac61147a4a3cd321ca192132b9b26215
  D5/S1/Recurrence/Invariants/UnitReversionSquareParity.agree_mul
    declaration statement_id: sha256:b4802ea85bb0964fd0f4727040613a738a00c26e68db4c758612d114939c9e3a
  D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime.map_inverse
    declaration statement_id: sha256:21cbe0dfb305cf778a51d75a983f9d36050deb93ea8585db1a35cd90665dcbf0
  D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.exists_unique_fixed
    declaration statement_id: sha256:bd62df5aa141eaff1ceec9e8af00309b4a8e194b4354ad180a51862599cef981
  D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.ternary_dvd
    declaration statement_id: sha256:78a174ace729c4c2fd41b5ecaaa9cc6f36fd2402e035602258bda1ddab9ccf23
  D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.a
    declaration statement_id: sha256:9cc430508fc99edb56bf536e1c45bf83436e5dafd75c8ebc731d629eec69e84b
  D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.hanna_conjecture
    declaration statement_id: sha256:854dbff18fbb33906678b21c826c522d8f9f36122e6f46a731c25d30e5fb25fe
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19951.
The source predicates and generalized-binomial quotient retain their defining expressions.
The existence and uniqueness arguments use PowerSeriesNormalizedContraction.exists_unique_fixed.
The statement is unbounded; no finite enumeration or computational certificate is used.
Declaration classifications (same-delivery helpers inlined; escape_witness: none):
  IsGF: proof_shape: bind-only; consumers: isGF_iff, solution_unique, claim, result.
  absSeries: proof_shape: bind-only; consumers: stepQ, map_stepZ, isGF_iff, solution_unique, IsGF, stepQ_contract, map_absZ.
  claim: proof_shape: bind-only; consumers: result.
  integer_exists: proof_shape: bind-only; consumers: result.
  integral_reduction: proof_shape: bind-only; consumers: result.
  isGF_iff: proof_shape: bind-only; consumers: solution_unique, result.
  map_absZ: proof_shape: bind-only; consumers: map_stepZ.
  map_stepZ: proof_shape: bind-only; consumers: result.
  quotient: proof_shape: bind-only; consumers: quotient_integer, claim, result.
  quotient_integer: proof_shape: bind-only; consumers: result.
  result: proof_shape: bind-only; consumers: settling result.
  solution_unique: proof_shape: bind-only; consumers: result.
  stepQ: proof_shape: bind-only; consumers: map_stepZ, isGF_iff, solution_unique, stepQ_contract, result.
  stepQ_contract: proof_shape: bind-only; consumers: solution_unique.
  stepZ: proof_shape: bind-only; consumers: integral_reduction, stepZ_contract, map_stepZ, integer_exists, result.
  stepZ_contract: proof_shape: bind-only; consumers: integer_exists.
-/

import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
import D5.S1.Recurrence.Invariants.AbsoluteReciprocalSquareParity
import D5.S1.Recurrence.Invariants.UnitReversionSquareParity
import D5.S1.Recurrence.Parity.AbsoluteReciprocalSquareShiftParity
import D5.S1.Recurrence.Invariants.AbsoluteReciprocalGeometricParity
import D5.S1.Recurrence.Residue.NegativePowerDiagonalModPrime
import Mathlib.RingTheory.Binomial

set_option autoImplicit false

namespace D5.S1.Recurrence.Algebraic.HannaAbsoluteCubicCongruence

open PowerSeries

/-- `abs(F)`: the series with the absolute values of the coefficients of F. -/
noncomputable def absSeries (F : PowerSeries ℚ) : PowerSeries ℚ := mk fun n => |coeff n F|

/-- OEIS A380711: "G.f. A(x) satisfies A(x) = 1 + x*A(x)*abs( 1/A(x)^3 )", offset 0. -/
def IsGF (A : PowerSeries ℚ) : Prop :=
  A = 1 + X * A * absSeries ((A ^ 3)⁻¹)

/-- `binomial(3n-1, n)/(3n-1)` with the generalized binomial coefficient (so n = 0 gives 1/(-1)). -/
noncomputable def quotient (n : ℕ) : ℚ :=
  (Ring.choose (3 * (n : ℤ) - 1) n : ℚ) / (3 * (n : ℚ) - 1)

/-- OEIS A380711 (P. D. Hanna), conjecture: "a(n) == binomial(3n-1,n)/(3n-1) (mod 2) for n >= 0." -/
def claim : Prop :=
  (∃ A, IsGF A) ∧
    ∀ A, IsGF A → ∀ n : ℕ, ∃ m z : ℤ, coeff n A = m ∧ quotient n = z ∧ m ≡ z [ZMOD 2]

end D5.S1.Recurrence.Algebraic.HannaAbsoluteCubicCongruence

set_option maxHeartbeats 800000


namespace D5.S1.Recurrence.Algebraic.HannaAbsoluteCubicCongruence
open PowerSeries
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity (Agree agree_iff agree_pow agree_mul agree_X)
open D5.S1.Recurrence.Invariants.AbsoluteReciprocalSquareParity (absSeries) in
private noncomputable def stepZ (f : PowerSeries ℤ) : PowerSeries ℤ :=
  1 + X * f * D5.S1.Recurrence.Invariants.AbsoluteReciprocalSquareParity.absSeries
    (invOfUnit (f ^ 3) 1)

open D5.S1.Recurrence.Invariants.AbsoluteReciprocalGeometricParity (agree_inv)
open D5.S1.Recurrence.Residue.NegativePowerDiagonalModPrime (map_inverse)

private theorem stepZ_contract (d : ℕ) (f g : PowerSeries ℤ)
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) (h : Agree d f g) :
    Agree (d + 1) (stepZ f) (stepZ g) := by
  have hi := agree_inv (by simp [hf]) (by simp [hg]) (agree_pow h 3)
  have habs : Agree d
      (D5.S1.Recurrence.Invariants.AbsoluteReciprocalSquareParity.absSeries (invOfUnit (f ^ 3) 1))
      (D5.S1.Recurrence.Invariants.AbsoluteReciprocalSquareParity.absSeries (invOfUnit (g ^ 3) 1)) := by
    intro n hn
    simp only [D5.S1.Recurrence.Invariants.AbsoluteReciprocalSquareParity.absSeries, coeff_mk,
      hi n hn]
  have hm := agree_X (agree_mul h habs)
  intro n hn
  simpa only [stepZ, mul_assoc, map_add] using
    congrArg (fun t => coeff n (1 : PowerSeries ℤ) + t) (hm n hn)

private theorem integer_exists : ∃ s : PowerSeries ℤ, constantCoeff s = 1 ∧ s = stepZ s :=
  by
    obtain ⟨s, hs, he, _⟩ :=
      D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction.exists_unique_fixed
        stepZ (by intro f _; simp [stepZ]) (fun _ hf hg h => stepZ_contract _ _ _ hf hg h)
    exact ⟨s, hs, he⟩


private noncomputable def stepQ (f : PowerSeries ℚ) : PowerSeries ℚ :=
  1 + X * f * absSeries (invOfUnit (f ^ 3) 1)

private theorem stepQ_contract (d : ℕ) (f g : PowerSeries ℚ)
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) (h : Agree d f g) :
    Agree (d + 1) (stepQ f) (stepQ g) := by
  have hi := agree_inv (by simp [hf]) (by simp [hg]) (agree_pow h 3)
  have habs : Agree d (absSeries (invOfUnit (f ^ 3) 1))
      (absSeries (invOfUnit (g ^ 3) 1)) := by
    intro n hn
    simp only [absSeries, coeff_mk, hi n hn]
  have hm := agree_X (agree_mul h habs)
  intro n hn
  simpa only [stepQ, mul_assoc, map_add] using
    congrArg (fun t => coeff n (1 : PowerSeries ℚ) + t) (hm n hn)

private theorem isGF_iff (f : PowerSeries ℚ) : IsGF f ↔ constantCoeff f = 1 ∧ f = stepQ f := by
  have hnormalize (hf : constantCoeff f = 1) :
      invOfUnit (f ^ 3) 1 = (f ^ 3)⁻¹ :=
    invOfUnit_eq' _ _ (by simp [hf])
  constructor
  · intro hf
    have h0 : constantCoeff f = 1 := by rw [hf]; simp
    exact ⟨h0, by simpa only [IsGF, stepQ, hnormalize h0] using hf⟩
  · rintro ⟨hf, he⟩
    simpa only [IsGF, stepQ, hnormalize hf] using he

private theorem map_absZ (f : PowerSeries ℤ) :
    (D5.S1.Recurrence.Invariants.AbsoluteReciprocalSquareParity.absSeries f).map
      (Int.castRingHom ℚ) = absSeries (f.map (Int.castRingHom ℚ)) := by
  ext n
  simp [absSeries, D5.S1.Recurrence.Invariants.AbsoluteReciprocalSquareParity.absSeries]

private theorem map_stepZ (f : PowerSeries ℤ) (hf : constantCoeff f = 1) :
    (stepZ f).map (Int.castRingHom ℚ) = stepQ (f.map (Int.castRingHom ℚ)) := by
  have hi := map_inverse (Int.castRingHom ℚ) (f ^ 3) (by simp [hf])
  simp only [map_pow] at hi
  simp only [stepZ, stepQ, map_add, map_one, map_mul, map_X, map_absZ, hi]

private theorem solution_unique (f g : PowerSeries ℚ) (hf : IsGF f) (hg : IsGF g) : f = g :=
  by
    obtain ⟨s, _, _, hu⟩ :=
      D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction.exists_unique_fixed
        stepQ (by intro f _; simp [stepQ]) (fun _ hf hg h => stepQ_contract _ _ _ hf hg h)
    exact (hu f ((isGF_iff f).mp hf).1 ((isGF_iff f).mp hf).2).trans
      (hu g ((isGF_iff g).mp hg).1 ((isGF_iff g).mp hg).2).symm

open D5.S1.Recurrence.Invariants.AbsoluteReciprocalSquareParity (map_abs)
open D5.S1.Recurrence.Parity.AbsoluteReciprocalSquareShiftParity (reduced_cubic)

private theorem integral_reduction (s : PowerSeries ℤ) (hs : constantCoeff s = 1)
    (he : s = stepZ s) :
    s.map (Int.castRingHom (ZMod 2)) =
      D5.S1.Recurrence.Parity.AbsoluteReciprocalSquareShiftParity.generatingSeries.map
        (Int.castRingHom (ZMod 2)) := by
  let hom := Int.castRingHom (ZMod 2)
  let F := s.map hom
  let I := (invOfUnit (s ^ 3) 1).map hom
  let G := D5.S1.Recurrence.Parity.AbsoluteReciprocalSquareShiftParity.generatingSeries.map hom
  have h0 : constantCoeff F = 1 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, hs, map_one]
  have hG0 : constantCoeff G = 1 := by
    dsimp [G]
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      D5.S1.Recurrence.Parity.AbsoluteReciprocalSquareShiftParity.generating_equation.1, map_one]
  have hF : F = 1 + X * F * I := by
    simpa only [F, I, stepZ, map_add, map_one, map_mul, map_X, hom, map_abs] using
      congrArg (PowerSeries.map hom) he
  have hI : F ^ 3 * I = 1 := by
    have hi := congrArg (PowerSeries.map hom) (mul_invOfUnit (s ^ 3) 1 (by simp [hs]))
    rw [_root_.map_mul, _root_.map_pow, _root_.map_one] at hi
    exact hi
  have hc : F ^ 3 = F ^ 2 + X := by linear_combination F ^ 2 * hF + X * hI
  have hg : G ^ 3 = G ^ 2 + X := reduced_cubic
  have hu : IsUnit (F ^ 2 + F * G + G ^ 2 - F - G) := by
    rw [isUnit_iff_constantCoeff]
    simp [h0, hG0]
  apply sub_eq_zero.mp
  apply hu.mul_left_cancel
  change (F ^ 2 + F * G + G ^ 2 - F - G) * (F - G) =
    (F ^ 2 + F * G + G ^ 2 - F - G) * 0
  linear_combination hc - hg

private theorem quotient_integer (n : ℕ) (hn : 0 < n) :
    quotient n = ((Nat.choose (3 * n - 1) n / (3 * n - 1) : ℕ) : ℤ) := by
  have hQ : 3 * (n : ℚ) - 1 = ((3 * n - 1 : ℕ) : ℚ) := by
    have hnat : 3 * n - 1 + 1 = 3 * n := by omega
    have h := congrArg (Nat.cast : ℕ → ℚ) hnat
    push_cast at h
    linarith
  unfold quotient
  simp only [Int.cast_natCast]
  rw [hQ, Ring.choose_natCast]
  apply (div_eq_iff (by exact_mod_cast (by omega : 3 * n - 1 ≠ 0))).mpr
  exact_mod_cast (Nat.div_mul_cancel
    (D5.S1.Recurrence.Parity.AbsoluteReciprocalSquareShiftParity.ternary_dvd n hn)).symm

theorem result : claim := by
  obtain ⟨s, hs, he⟩ := integer_exists
  let f := s.map (Int.castRingHom ℚ)
  have hf : IsGF f := by
    apply (isGF_iff f).mpr
    refine ⟨?_, ?_⟩
    · dsimp [f]
      rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, hs, map_one]
    · exact (congrArg (PowerSeries.map (Int.castRingHom ℚ)) he).trans (map_stepZ s hs)
  refine ⟨⟨f, hf⟩, ?_⟩
  intro A hA n
  have hAf : A = f := solution_unique A f hA hf
  refine ⟨coeff n s, if n = 0 then -1 else
      ((Nat.choose (3 * n - 1) n / (3 * n - 1) : ℕ) : ℤ), ?_, ?_, ?_⟩
  · rw [hAf]
    simp [f, coeff_map]
  · by_cases hn : n = 0
    · subst n
      norm_num [quotient, Ring.choose_zero_right]
    · rw [ite_eq_right hn]
      exact quotient_integer n (by omega)
  · by_cases hn : n = 0
    · subst n
      rw [ite_eq_left rfl, coeff_zero_eq_constantCoeff, hs]
      norm_num [Int.ModEq]
    · rw [ite_eq_right hn]
      apply (ZMod.intCast_eq_intCast_iff _ _ 2).mp
      have hc := congrArg (coeff n) (integral_reduction s hs he)
      simp only [coeff_map, Int.coe_castRingHom] at hc
      have hq := D5.S1.Recurrence.Parity.AbsoluteReciprocalSquareShiftParity.hanna_conjecture
        n (by omega)
      have hb := (ZMod.intCast_eq_intCast_iff' _ _ 2).mpr hq
      change ((coeff n s : ℤ) : ZMod 2) =
        ((Nat.choose (3 * n - 1) n / (3 * n - 1) : ℕ) : ZMod 2)
      change (D5.S1.Recurrence.Parity.AbsoluteReciprocalSquareShiftParity.a n : ZMod 2) =
        ((Nat.choose (3 * n - 1) n / (3 * n - 1) : ℕ) : ZMod 2) at hb
      simp only [D5.S1.Recurrence.Parity.AbsoluteReciprocalSquareShiftParity.generatingSeries,
        coeff_mk] at hc
      exact hc.trans hb


end D5.S1.Recurrence.Algebraic.HannaAbsoluteCubicCongruence
