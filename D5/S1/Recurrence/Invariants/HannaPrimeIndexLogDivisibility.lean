/- GID: D5/S1/Recurrence/Invariants/HannaPrimeIndexLogDivisibility
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaPrimeIndexLogDivisibility
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Integral source construction and rational uniqueness prove Hanna A381355 divisibility. -/

/-
admission_basis: open-problem-resolution (#23982; Proved)
proof_shape: result: content (integral coefficient construction and rational uniqueness).
proof_shape: low_prime_coeff: bind-only; consumers: correction_mul, source_divisibility.
proof_shape: advance_agree: bind-only; consumers: advance_equation, approximation_stable.
proof_shape: advance_zero: bind-only; consumer: advance_equation.
proof_shape: correction_mul: bind-only; consumer: advance_equation.
proof_shape: advance_equation: bind-only; consumer: generating_equation_zero.
proof_shape: approximation_stable: content (coefficient-stability induction);
consumers: approximation_zero, generating_agree.
proof_shape: approximation_zero: bind-only; consumer: generating_equation_zero.
proof_shape: generating_agree: content (coefficientwise limit of stable approximations);
consumers: generating_equation_zero, castSeries_source.
proof_shape: generating_equation_zero: content (integral lifting);
consumers: log_mul, source_divisibility, castSeries_source, map_invOfUnit.
proof_shape: log_mul: bind-only; consumer: derivative_identity.
proof_shape: derivative_identity: bind-only; consumer: source_divisibility.
proof_shape: source_divisibility: content (the integral lifting supplies the zero diagonal);
consumer: result. Its local coefficient and divisibility algebra is bind-only.
proof_shape: castSeries_source: content (transport of the constructed source);
consumers: generating_uniqueQ, map_invOfUnit, result.
proof_shape: generating_uniqueQ: content (strong induction on rational coefficients);
consumer: result.
proof_shape: map_invOfUnit: bind-only; consumer: sourceTerm_cast.
proof_shape: sourceTerm_cast: bind-only; consumer: result.
escape_witness: none; admission uses the external named settling result.
Direct frozen dependencies (declaration statement_id):
D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.prime:
sha256:0a736efbf5ea49c36d6d348f1d3d21b17714ff433baaef1d2acb118a193af86b
D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.prime_is_prime:
sha256:c69cad3dd0e0f731e6d72c5a23e478ab050bc04ff36315a285e62f03cdee35a9
D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.lt_prime:
sha256:6d1e9781ad95c0927e40e35b903401eb5faf74d76a655668f525adba8d384c59
D5/S1/Recurrence/Invariants/UnitReversionSquareParity.Agree:
sha256:76d7ce5ef0f66968d4516f93f05e27e9125f8f29944ffacca0d95b580f786d34
D5/S1/Recurrence/Invariants/UnitReversionSquareParity.agree_pow:
sha256:0c9456bb3300b1f38308df2b3a2abc2d51d68b3b05356990e7bc5cfc4bfb0dbb
D5/S1/Recurrence/Invariants/UnitReversionSquareParity.agree_mul:
sha256:b4802ea85bb0964fd0f4727040613a738a00c26e68db4c758612d114939c9e3a
D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.prime_power_subst:
sha256:4b665513911f58443c7679757dc619d66730344174351ea1f23cedc92766f795
D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.map_inverse:
sha256:514cac370bcaca2ab772ee68d2f70f9768dcdff53acb4e2a4df3e5420df06e90
D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport.pow_change and derivative_map:
declaration identities pending the scoped report; cached source fingerprint differs.
The source predicates and coefficient extraction use the preregistered expressions.
The proofs use the public coefficient-agreement, power-change and Frobenius owners.
All implementation definitions and auxiliary theorems are private and used by result.
Unbounded symbolic statements only; no certified finite-instance computation is delivered.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24211
-/

import D5.S1.Recurrence.Parity.PrimePowerShiftLogDerivative
import D5.S1.Recurrence.Invariants.UnitReversionSquareParity
import D5.S1.Recurrence.LinearRows.LinearExponentDyadicSupport
import D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity
import D5.S1.Recurrence.Residue.ContinuedFractionOddSquare

/-! Hanna's source series is constructed over the integers and identified uniquely over the rationals. -/

namespace D5.S1.Recurrence.Invariants.HannaPrimeIndexLogDivisibility
open PowerSeries
open D5.S1.Recurrence.Parity.PrimePowerShiftLogDerivative (prime)
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity (Agree agree_pow agree_mul)

def IsSourceSeries (F : PowerSeries ℚ) : Prop :=
  coeff 0 F = 1 ∧ coeff 1 F = 1 ∧
    ∀ n : ℕ, 1 < n → coeff n (F ^ prime n) = 0

noncomputable def sourceTerm (F : PowerSeries ℚ) (n : ℕ) : ℚ :=
  coeff (n - 1) (derivative F * F⁻¹)

def claim : Prop :=
  (∃ F : PowerSeries ℚ, IsSourceSeries F) ∧
    ∀ F : PowerSeries ℚ, IsSourceSeries F →
      ∀ n : ℕ, 1 < n →
        ∃ z : ℤ, sourceTerm F n = (prime n : ℚ) * (z : ℚ)

private theorem low_prime_coeff (B : PowerSeries ℤ) {p j : ℕ}
    (hp : Nat.Prime p) (hj : 1 ≤ j) (hjp : j < p) :
    (p : ℤ) ∣ coeff j (B ^ p) := by
  letI : Fact p.Prime := ⟨hp⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  change (Int.castRingHom (ZMod p)) (coeff j (B ^ p)) = 0
  rw [← PowerSeries.coeff_map, map_pow,
    D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.prime_power_subst,
    coeff_subst_X_pow hp.ne_zero, if_neg (Nat.not_dvd_of_pos_of_lt (by omega) hjp)]

private noncomputable def correction (n : ℕ) (B : PowerSeries ℤ) : ℤ :=
  if n = 1 then 1 else -coeff n (B ^ prime n) / (prime n : ℤ)

private noncomputable def advance (n : ℕ) (B : PowerSeries ℤ) : PowerSeries ℤ :=
  B + C (correction n B) * X ^ n

private theorem advance_agree (n : ℕ) (B : PowerSeries ℤ) : Agree n (advance n B) B := by
  intro j hj
  simp only [advance, map_add, coeff_C_mul_X_pow, if_neg (by omega : j ≠ n), add_zero]

private theorem advance_zero {n : ℕ} (hn : 1 ≤ n) (B : PowerSeries ℤ)
    (h0 : constantCoeff B = 1) : constantCoeff (advance n B) = 1 := by
  simp [advance, h0, show n ≠ 0 by omega]

private theorem correction_mul (n : ℕ) (hn : 1 < n) (B : PowerSeries ℤ) :
    (prime n : ℤ) * correction n B = - coeff n (B ^ prime n) := by
  have hp := D5.S1.Recurrence.Parity.PrimePowerShiftLogDerivative.prime_is_prime n
  have hd : (prime n : ℤ) ∣ coeff n (B ^ prime n) :=
    low_prime_coeff B hp (by omega) (by have := D5.S1.Recurrence.Parity.PrimePowerShiftLogDerivative.lt_prime n (by omega); omega)
  rw [correction, if_neg (by omega)]
  exact Int.mul_ediv_cancel' (dvd_neg.mpr hd)

private theorem advance_equation {n : ℕ} (hn : 1 < n) (B : PowerSeries ℤ)
    (h0 : constantCoeff B = 1) :
    coeff n ((advance n B) ^ prime n) = 0 := by
  have he := D5.S1.Recurrence.LinearRows.LinearExponentDyadicSupport.pow_change (advance_zero (by omega) B h0) h0 (advance_agree n B) (prime n)
  have hadd : coeff n (advance n B) - coeff n B = correction n B := by
    simp only [advance, map_add, coeff_C_mul_X_pow, ↓reduceIte, add_sub_cancel_left]
  rw [hadd] at he
  rw [correction_mul n hn B] at he
  linear_combination he

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => 1
  | n + 1 => advance (n + 1) (approximation n)

private theorem approximation_stable {s t : ℕ} (h : s ≤ t) :
    Agree (s + 1) (approximation s) (approximation t) := by
  induction t, h using Nat.le_induction with
  | base => intro j hj; rfl
  | succ t hst ih =>
    intro j hj
    exact (ih j hj).trans ((advance_agree (t + 1) (approximation t)) j (by omega)).symm

private theorem approximation_zero (n : ℕ) : constantCoeff (approximation n) = 1 := by
  simpa only [coeff_zero_eq_constantCoeff, approximation, map_one] using
    (approximation_stable (s := 0) (t := n) (Nat.zero_le n) 0 (by omega)).symm

private noncomputable def generatingSeries : PowerSeries ℤ :=
  mk fun n => coeff n (approximation n)

private theorem generating_agree (s : ℕ) : Agree (s + 1) generatingSeries (approximation s) := by
  intro j hj
  simpa only [generatingSeries, coeff_mk] using
    approximation_stable (s := j) (t := s) (by omega) j (by omega)

private theorem generating_equation_zero : constantCoeff generatingSeries = 1 ∧
    ∀ n, 1 < n → coeff n (generatingSeries ^ prime n) = 0 := by
  constructor
  · simpa only [coeff_zero_eq_constantCoeff, approximation, map_one] using
      generating_agree 0 0 (by omega)
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [agree_pow (generating_agree (k + 1)) _ (k + 1) (by omega)]
    exact advance_equation (by omega) _ (approximation_zero k)

private noncomputable def logDerivative : PowerSeries ℤ :=
  PowerSeries.derivative (R := ℤ) generatingSeries * invOfUnit generatingSeries 1

private theorem log_mul : logDerivative * generatingSeries = PowerSeries.derivative (R := ℤ) generatingSeries := by
  rw [logDerivative, mul_assoc, invOfUnit_mul _ 1 generating_equation_zero.1, mul_one]

private theorem derivative_identity (n : ℕ) :
    PowerSeries.derivative (R := ℤ) (generatingSeries ^ n) =
      C (n : ℤ) * logDerivative * generatingSeries ^ n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [derivative_pow, Nat.add_sub_cancel, pow_succ, ← log_mul]
    have hc : (↑(n + 1) : PowerSeries ℤ) = C ((n + 1 : ℕ) : ℤ) := by simp
    rw [hc]
    ring

private theorem source_divisibility (n : ℕ) (hn : 1 < n) :
    (prime n : ℤ) ∣ coeff (n - 1) logDerivative := by
  have hn1 : 1 ≤ n := by omega
  have hp : (prime n : ℤ) ≠ 0 := by
    exact_mod_cast (D5.S1.Recurrence.Parity.PrimePowerShiftLogDerivative.prime_is_prime n).ne_zero
  have he := congrArg (coeff (n - 1)) (derivative_identity (prime n))
  rw [coeff_derivative, Nat.sub_add_cancel hn1, mul_assoc, coeff_C_mul] at he
  rw [show ((n - 1 : ℕ) : ℤ) + 1 = (n : ℤ) by omega] at he
  rw [generating_equation_zero.2 n hn] at he
  have he' : (prime n : ℤ) * coeff (n - 1) (logDerivative * generatingSeries ^ prime n) = 0 := by
    simpa using he.symm
  have hz : coeff (n - 1) (logDerivative * generatingSeries ^ prime n) = 0 := by
    exact (mul_eq_zero.mp he').resolve_left hp
  let f := Int.castRingHom (ZMod (prime n))
  have ha : Agree n (PowerSeries.map f (generatingSeries ^ prime n)) 1 := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      rw [PowerSeries.coeff_map]
      simp [coeff_zero_eq_constantCoeff, generating_equation_zero.1]
    · rw [PowerSeries.coeff_map, coeff_one, if_neg hj0]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
        (low_prime_coeff generatingSeries
          (D5.S1.Recurrence.Parity.PrimePowerShiftLogDerivative.prime_is_prime n)
          (by omega) (by have := D5.S1.Recurrence.Parity.PrimePowerShiftLogDerivative.lt_prime n hn1; omega))
  have heq := agree_mul (f := PowerSeries.map f logDerivative)
    (g := PowerSeries.map f logDerivative) (fun _ _ => rfl) ha (n - 1) (by omega)
  rw [← map_mul, PowerSeries.coeff_map, hz, map_zero, mul_one] at heq
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by
    simpa [f, PowerSeries.coeff_map] using heq.symm)

private noncomputable def castSeries : PowerSeries ℚ :=
  PowerSeries.map (Int.castRingHom ℚ) generatingSeries

private theorem castSeries_source : IsSourceSeries castSeries := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [castSeries, coeff_zero_eq_constantCoeff] using
      congrArg (Int.castRingHom ℚ) generating_equation_zero.1
  · have hgen : coeff 1 generatingSeries = 1 := by
      calc
        coeff 1 generatingSeries = coeff 1 (approximation 1) := generating_agree 1 1 (by omega)
        _ = 1 := by simp [approximation, advance, correction]
    simpa [castSeries] using congrArg (Int.castRingHom ℚ) hgen
  · intro n hn
    change coeff n ((PowerSeries.map (Int.castRingHom ℚ) generatingSeries) ^ prime n) = 0
    rw [← map_pow, PowerSeries.coeff_map]
    exact congrArg (Int.castRingHom ℚ) (generating_equation_zero.2 n hn)

private theorem generating_uniqueQ (B : PowerSeries ℚ) (h0 : constantCoeff B = 1)
    (h1 : coeff 1 B = 1)
    (hB : ∀ n, 1 < n → coeff n (B ^ prime n) = 0) : B = castSeries := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      simpa only [coeff_zero_eq_constantCoeff, castSeries_source.1] using h0
    by_cases hn1 : n = 1
    · subst n
      simpa only [castSeries_source.2.1] using h1
    have hag : Agree n B castSeries := by
      intro j hj
      exact ih j (by omega)
    have hp : (prime n : ℚ) ≠ 0 := by
      exact_mod_cast (D5.S1.Recurrence.Parity.PrimePowerShiftLogDerivative.prime_is_prime n).ne_zero
    have h0' : constantCoeff castSeries = 1 := by simpa [coeff_zero_eq_constantCoeff] using castSeries_source.1
    have he := D5.S1.Recurrence.LinearRows.LinearExponentDyadicSupport.pow_change h0 h0' hag (prime n)
    rw [hB n (by omega), castSeries_source.2.2 n (by omega), sub_self] at he
    exact sub_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_left hp)

private theorem map_invOfUnit :
    PowerSeries.map (Int.castRingHom ℚ) (invOfUnit generatingSeries 1) =
      (PowerSeries.map (Int.castRingHom ℚ) generatingSeries)⁻¹ := by
  rw [D5.S1.Recurrence.Residue.ContinuedFractionOddSquare.map_inverse
    (Int.castRingHom ℚ) generatingSeries generating_equation_zero.1]
  apply invOfUnit_eq'
  simpa only [castSeries, coeff_zero_eq_constantCoeff, Units.val_one] using castSeries_source.1

private theorem sourceTerm_cast (n : ℕ) :
    sourceTerm castSeries n =
      (Int.castRingHom ℚ) (coeff (n - 1) logDerivative) := by
  rw [sourceTerm, castSeries,
    ← D5.S1.Recurrence.LinearRows.LinearExponentDyadicSupport.derivative_map,
    ← map_invOfUnit, ← map_mul]
  rfl

theorem result : claim := by
  constructor
  · exact ⟨castSeries, castSeries_source⟩
  · intro F hF n hn
    have h0F : constantCoeff F = 1 := by simpa [coeff_zero_eq_constantCoeff] using hF.1
    have huniq := generating_uniqueQ F h0F hF.2.1 hF.2.2
    obtain ⟨z, hz⟩ := source_divisibility n hn
    refine ⟨z, ?_⟩
    rw [huniq, sourceTerm_cast]
    simpa using congrArg (Int.castRingHom ℚ) hz

end D5.S1.Recurrence.Invariants.HannaPrimeIndexLogDivisibility
