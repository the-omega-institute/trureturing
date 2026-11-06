/- GID: D5/S1/Recurrence/Residue/BalaQuarticEGFEventualDivisibility
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/BalaQuarticEGFEventualDivisibility
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Eventual divisibility for the quartic hyperbolic EGF of OEIS A281428. -/

/-
admission_basis: open-problem-resolution (#22065; Proved)
escape_witness: none; result is the settling theorem.
The source hyperbolic cosine expression is literal; the proof uses the existing eCoeff owner for (2*n)! * coeff (2*n) C.
The source integral expression is inlined literally in IsSourceSeries; primitive_literal connects it to the existing SchroderIntegralEGF.primitive owner.
Hyperbolic cosine and sine expressions are inlined; no forwarding series definition is introduced.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25663
proof_shape and consumers (names relative to this module):
IsSourceSeries: proof_shape: bind-only; escape_witness: none; consumers: claim, source_exists_unique, source_system, source_invariant, source_integral, sourceU_identities, source_cubic, sourceU_coeff_mem, source_coeff_mem, source_den_coprime, result; Direct frozen dependencies: none.
claim: proof_shape: bind-only; escape_witness: none; consumers: result (statement); Direct frozen dependencies: none.
primitive_literal: proof_shape: bind-only; escape_witness: none; consumers: source_exists_unique, source_system, source_invariant, source_integral, sourceU_identities, source_cubic, sourceU_coeff_mem, source_coeff_mem, source_den_coprime, result; Direct frozen dependencies: F8.
integral_succ: proof_shape: bind-only; escape_witness: none; consumers: integral_agree, source_exists_unique, result; Direct frozen dependencies: F8, F7.
integral_agree: proof_shape: bind-only; escape_witness: none; consumers: source_exists_unique, result; Direct frozen dependencies: F9, F8, F7, F11.
cosh_constant: proof_shape: bind-only; escape_witness: none; consumers: source_exists_unique, result; Direct frozen dependencies: F19.
cosh_agree: proof_shape: bind-only; escape_witness: none; consumers: source_exists_unique, result; Direct frozen dependencies: F13, F11.
source_exists_unique: proof_shape: bind-only; escape_witness: none; consumers: result; Direct frozen dependencies: F9, F8, F19, F7, F10, F12, F13, F11.
sourceSinh_constant: proof_shape: bind-only; escape_witness: none; consumers: source_invariant, source_integral, sourceU_constant, sourceU_identities, source_cubic, sourceU_coeff_mem, source_coeff_mem, source_den_coprime, result; Direct frozen dependencies: F9, F8, F19.
source_system: proof_shape: bind-only; escape_witness: none; consumers: source_invariant, source_integral, sourceU_identities, source_cubic, sourceU_coeff_mem, source_coeff_mem, source_den_coprime, result; Direct frozen dependencies: F9, F8, F7, F6.
source_invariant: proof_shape: bind-only; escape_witness: none; consumers: sourceU_identities, source_cubic, sourceU_coeff_mem, source_coeff_mem, source_den_coprime, result; Direct frozen dependencies: F9, F8, F19, F7, F6.
eCoeff_mul_mem: proof_shape: bind-only; escape_witness: none; consumers: eCoeff_pow_mem, source_integral, result; Direct frozen dependencies: F15, F17.
eCoeff_pow_mem: proof_shape: bind-only; escape_witness: none; consumers: source_integral, result; Direct frozen dependencies: F18, F15, F17.
source_integral: proof_shape: content; escape_witness: none; consumers: result; Direct frozen dependencies: F18, F15, F17, F9, F16, F8, F19, F7, F6.
sourceU: proof_shape: bind-only; escape_witness: none; consumers: sourceU_constant, sourceU_identities, source_cubic, sourceU_coeff_mem, source_coeff_mem, source_den_coprime, result; Direct frozen dependencies: F8.
sourceU_constant: proof_shape: bind-only; escape_witness: none; consumers: source_cubic, sourceU_coeff_mem, source_coeff_mem, source_den_coprime, result; Direct frozen dependencies: F9, F8, F19.
sourceU_identities: proof_shape: bind-only; escape_witness: none; consumers: source_cubic, sourceU_coeff_mem, source_coeff_mem, source_den_coprime, result; Direct frozen dependencies: F9, F8, F19, F7, F6.
source_cubic: proof_shape: bind-only; escape_witness: none; consumers: sourceU_coeff_mem, source_coeff_mem, source_den_coprime, result; Direct frozen dependencies: F9, F8, F19, F7, F6.
coeff_mul_mem: proof_shape: bind-only; escape_witness: none; consumers: coeff_pow_mem, sourceU_coeff_mem, source_coeff_mem, source_den_coprime, result; Direct frozen dependencies: none.
coeff_pow_mem: proof_shape: bind-only; escape_witness: none; consumers: sourceU_coeff_mem, source_coeff_mem, source_den_coprime, result; Direct frozen dependencies: none.
coeff_mul_mem_low: proof_shape: bind-only; escape_witness: none; consumers: sourceU_coeff_mem, source_coeff_mem, source_den_coprime, result; Direct frozen dependencies: none.
sourceU_coeff_mem: proof_shape: content; escape_witness: none; consumers: source_coeff_mem, source_den_coprime, result; Direct frozen dependencies: F9, F8, F19, F7, F6.
source_coeff_mem: proof_shape: content; escape_witness: none; consumers: source_den_coprime, result; Direct frozen dependencies: F9, F8, F19, F7, F6, F14.
localRing: proof_shape: bind-only; escape_witness: none; consumers: source_den_coprime, result; Direct frozen dependencies: F4, F3, F5, F1, F2, F0.
source_den_coprime: proof_shape: content; escape_witness: none; consumers: result; Direct frozen dependencies: F4, F3, F9, F5, F8, F19, F7, F1, F6, F14, F2, F0.
result: proof_shape: content; escape_witness: none; consumers: settlement of #22065; Direct frozen dependencies: F4, F18, F15, F17, F3, F9, F5, F16, F8, F19, F7, F10, F1, F6, F14, F12, F13, F2, F0, F11.
Direct frozen dependencies (declaration identities):
F0: D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.IsRIntegralRat @ ASSUMED-UNVERIFIED (declaration identity unavailable in the cached report; scoped report deferred to Stage B).
F1: D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.add @ ASSUMED-UNVERIFIED (declaration identity unavailable in the cached report; scoped report deferred to Stage B).
F2: D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.mul_coprime @ ASSUMED-UNVERIFIED (declaration identity unavailable in the cached report; scoped report deferred to Stage B).
F3: D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.neg @ ASSUMED-UNVERIFIED (declaration identity unavailable in the cached report; scoped report deferred to Stage B).
F4: D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.one_coprime @ ASSUMED-UNVERIFIED (declaration identity unavailable in the cached report; scoped report deferred to Stage B).
F5: D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.zero @ ASSUMED-UNVERIFIED (declaration identity unavailable in the cached report; scoped report deferred to Stage B).
F6: D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.expSeries_derivative @ ASSUMED-UNVERIFIED (declaration identity unavailable in the cached report; scoped report deferred to Stage B).
F7: D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.derivative_primitive @ ASSUMED-UNVERIFIED (declaration identity unavailable in the cached report; scoped report deferred to Stage B).
F8: D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.primitive @ ASSUMED-UNVERIFIED (declaration identity unavailable in the cached report; scoped report deferred to Stage B).
F9: D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.primitive_zero @ ASSUMED-UNVERIFIED (declaration identity unavailable in the cached report; scoped report deferred to Stage B).
F10: D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.exists_unique_fixed @ sha256:bd62df5aa141eaff1ceec9e8af00309b4a8e194b4354ad180a51862599cef981.
F11: D5/S1/Recurrence/Invariants/UnitReversionSquareParity.Agree @ sha256:76d7ce5ef0f66968d4516f93f05e27e9125f8f29944ffacca0d95b580f786d34.
F12: D5/S1/Recurrence/Invariants/UnitReversionSquareParity.agree_pow @ sha256:0c9456bb3300b1f38308df2b3a2abc2d51d68b3b05356990e7bc5cfc4bfb0dbb.
F13: D5/S1/Recurrence/Invariants/UnitReversionSquareParity.subst_inner_agree @ sha256:70b2ee35c9f37a83ac3c7fafdd24ab8c9a71bd427dd766a52b2641e8e37ecfa5.
F14: D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd.diagonal_multiplier @ sha256:baf4e278ec0ae3cd41a542f3cda3194f7876530c2576ffba51be13a9b08a55ac.
F15: D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff @ sha256:4352a2872dd069de3ca054aab1c4950930a811b324435173c0e64781d46fc330.
F16: D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_derivative @ sha256:d8c528ef732aa837c3d79d7314200e072b40f5bcdc873683da352f1acf37c5c8.
F17: D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_mul @ sha256:d77958a970452d82e689ee9878ff79fda28b9bc1537bf45041f667d5e694a1f5.
F18: D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_zero @ sha256:69e1d2e22802c66151c2c3239fdceab9ab8a796d9f10d82c7366e4d57e790054.
F19: D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.exp_subst_zero @ ASSUMED-UNVERIFIED (declaration identity unavailable in the cached report; scoped report deferred to Stage B).
The new degree inductions prove joint integer EGF coefficients and subring membership for the inverse cubic and C.
Definitions and the remaining coefficient, differentiation and divisibility adapters are bind-only.
-/

import D5.S1.Recurrence.Algebraic.SchroderIntegralEGF
import D5.S1.Recurrence.Residue.IntegralEGFComposition
import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
import D5.S1.Recurrence.Residue.ParametricExponentialSquareCongruence

import D5.S1.Recurrence.Residue.DiagonalPowerRatioAllOdd
import D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality
import D5.S1.Recurrence.Invariants.UnitReversionSquareParity

open D5.S1.Recurrence.Algebraic.SchroderIntegralEGF (primitive primitive_zero derivative_primitive)

namespace D5.S1.Recurrence.Residue.BalaQuarticEGFEventualDivisibility

open PowerSeries
open D5.S1.Recurrence.Residue.IntegralEGFComposition (eCoeff)

/-- OEIS A281428 NAME, with the zero-constant integral and C(0)=1 from EXAMPLE. -/
def IsSourceSeries (C : PowerSeries ℚ) : Prop :=
  PowerSeries.constantCoeff C = 1 ∧ C = (fun F : PowerSeries ℚ => PowerSeries.C (1 / 2 : ℚ) * ((PowerSeries.exp ℚ).subst F + (PowerSeries.exp ℚ).subst (-F))) (PowerSeries.mk fun j => match j with | 0 => 0 | k + 1 => PowerSeries.coeff k (C ^ 4) / (k + 1 : ℚ))

/-- Bala's first conjecture. Integer divisibility is encoded by an integer multiple,
rather than divisibility in the field of rationals. No integrality premise is added; the existence clause prevents a vacuous assertion. -/
def claim : Prop :=
  (∃ C : PowerSeries ℚ, IsSourceSeries C) ∧
  ∀ (C : PowerSeries ℚ), IsSourceSeries C →
    ∀ (N : ℕ), 0 < N → Nat.Coprime N 6 →
      ∃ (n₀ : ℕ), ∀ (n : ℕ), n₀ ≤ n →
        ∃ (k : ℤ), ((2 * n).factorial : ℚ) * coeff (2 * n) C = (N : ℚ) * (k : ℚ)

end D5.S1.Recurrence.Residue.BalaQuarticEGFEventualDivisibility

namespace D5.S1.Recurrence.Residue.BalaQuarticEGFEventualDivisibility
open PowerSeries Finset
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity
open D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
open D5.S1.Recurrence.Residue.IntegralEGFComposition

open D5.S1.Recurrence.Residue.ParametricExponentialSquareCongruence (exp_subst_zero)
open D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality (expSeries_derivative)


private theorem primitive_literal (F : PowerSeries ℚ) :
    (PowerSeries.mk fun j => match j with
      | 0 => 0
      | k + 1 => PowerSeries.coeff k F / (k + 1 : ℚ)) = primitive F := by
  ext n
  cases n <;> simp [primitive]

@[simp] private theorem integral_succ (F : PowerSeries ℚ) (n : ℕ) :
    coeff (n+1) (primitive F) = coeff n F / (n+1 : ℚ) := by
  apply (eq_div_iff (by positivity : (n+1 : ℚ) ≠ 0)).mpr
  simpa only [coeff_derivative] using congrArg (coeff n) (derivative_primitive F)

private theorem integral_agree {d : ℕ} {F G : PowerSeries ℚ} (h : Agree d F G) :
    Agree (d+1) (primitive F) (primitive G) := by
  intro n hn
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff, primitive_zero]
  | succ n => simp only [integral_succ, h n (by omega)]

@[simp] private theorem cosh_constant {F : PowerSeries ℚ} (h : constantCoeff F = 0) :
    constantCoeff ((fun F : PowerSeries ℚ => PowerSeries.C (1 / 2 : ℚ) * ((PowerSeries.exp ℚ).subst F + (PowerSeries.exp ℚ).subst (-F))) F) = 1 := by
  simp only [map_mul, map_add, constantCoeff_C, exp_subst_zero F h,
    exp_subst_zero (-F) (by simp [h])]
  norm_num

private theorem cosh_agree {d : ℕ} {F G : PowerSeries ℚ}
    (hF : constantCoeff F = 0) (hG : constantCoeff G = 0) (h : Agree d F G) :
    Agree d ((fun F : PowerSeries ℚ => PowerSeries.C (1 / 2 : ℚ) * ((PowerSeries.exp ℚ).subst F + (PowerSeries.exp ℚ).subst (-F))) F) ((fun F : PowerSeries ℚ => PowerSeries.C (1 / 2 : ℚ) * ((PowerSeries.exp ℚ).subst F + (PowerSeries.exp ℚ).subst (-F))) G) := by
  have hp := subst_inner_agree h (exp ℚ) hF hG
  have hm : Agree d (-F) (-G) := by
    intro n hn
    simpa only [map_neg] using congrArg Neg.neg (h n hn)
  have hn := subst_inner_agree hm (exp ℚ) (by simp [hF]) (by simp [hG])
  intro n hnd
  simp only [coeff_C_mul, map_add, hp n hnd, hn n hnd]

private theorem source_exists_unique : ∃! C : PowerSeries ℚ, IsSourceSeries C := by
  let step : PowerSeries ℚ → PowerSeries ℚ := fun F => (fun F : PowerSeries ℚ => PowerSeries.C (1 / 2 : ℚ) * ((PowerSeries.exp ℚ).subst F + (PowerSeries.exp ℚ).subst (-F))) (primitive (F^4))
  obtain ⟨F, h0, hF, huniq⟩ := exists_unique_fixed step
    (by intro G _; exact cosh_constant (primitive_zero _))
    (by intro d G H _ _ _ h; exact cosh_agree (primitive_zero _) (primitive_zero _)
          (integral_agree (agree_pow h 4)))
  simp only [IsSourceSeries, primitive_literal]
  refine ⟨F, ⟨h0, hF⟩, ?_⟩
  intro G hG
  exact huniq G hG.1 hG.2

@[simp] private theorem sourceSinh_constant (C : PowerSeries ℚ) : constantCoeff ((PowerSeries.C (1/2 : ℚ) * ((exp ℚ).subst (primitive (C^4)) - (exp ℚ).subst (-(primitive (C^4)))))) = 0 := by
  have hneg : constantCoeff (-(primitive (C^4))) = 0 := by
    simp only [map_neg, primitive_zero, neg_zero]
  rw [map_mul, map_sub, constantCoeff_C,
    exp_subst_zero _ (primitive_zero _), exp_subst_zero _ hneg]
  norm_num

private theorem source_system (C : PowerSeries ℚ) (hC : IsSourceSeries C) :
    PowerSeries.derivative (R := ℚ) C = (PowerSeries.C (1/2 : ℚ) * ((exp ℚ).subst (primitive (C^4)) - (exp ℚ).subst (-(primitive (C^4))))) * C^4 ∧ PowerSeries.derivative (R := ℚ) ((PowerSeries.C (1/2 : ℚ) * ((exp ℚ).subst (primitive (C^4)) - (exp ℚ).subst (-(primitive (C^4)))))) = C^5 := by
  have hp : PowerSeries.derivative (R := ℚ) ((exp ℚ).subst (primitive (C^4))) =
      (exp ℚ).subst (primitive (C^4)) * C^4 := by
    simpa only [derivative_primitive] using expSeries_derivative (primitive_zero (C^4))
  have hm : PowerSeries.derivative (R := ℚ) ((exp ℚ).subst (-(primitive (C^4)))) =
      (exp ℚ).subst (-(primitive (C^4))) * (-C^4) := by
    simpa only [map_neg, derivative_primitive] using
      expSeries_derivative (h := -(primitive (C^4)))
        (by simp [primitive_zero])
  have hs : C = PowerSeries.C (1/2 : ℚ) *
      ((exp ℚ).subst (primitive (C^4)) + (exp ℚ).subst (-(primitive (C^4)))) := by
    simpa only [primitive_literal] using hC.2
  constructor
  · conv_lhs => rw [hs]
    rw [Derivation.leibniz, derivative_C, smul_zero, add_zero, map_add, hp, hm]
    simp only [smul_eq_mul]
    ring
  · rw [Derivation.leibniz, derivative_C, smul_zero, add_zero, map_sub, hp, hm]
    simp only [smul_eq_mul]
    calc
      _ = (PowerSeries.C (1/2 : ℚ) *
          ((exp ℚ).subst (primitive (C^4)) +
            (exp ℚ).subst (-(primitive (C^4))))) * C^4 := by ring
      _ = C^5 := by rw [← hs]; ring

private theorem source_invariant (C : PowerSeries ℚ) (hC : IsSourceSeries C) :
    C^2 - (PowerSeries.C (1/2 : ℚ) * ((exp ℚ).subst (primitive (C^4)) - (exp ℚ).subst (-(primitive (C^4))))) ^ 2 = 1 := by
  apply PowerSeries.derivative.ext
  · rw [map_sub, derivative_pow, derivative_pow, (source_system C hC).1,
      (source_system C hC).2, derivative_one]
    ring
  · rw [map_sub, map_pow, map_pow, hC.1, sourceSinh_constant, map_one]
    norm_num

end D5.S1.Recurrence.Residue.BalaQuarticEGFEventualDivisibility

namespace D5.S1.Recurrence.Residue.BalaQuarticEGFEventualDivisibility
open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition

private theorem eCoeff_mul_mem (T : Subring ℚ) (F G : PowerSeries ℚ) (n : ℕ)
    (hF : ∀ i ≤ n, eCoeff F i ∈ T) (hG : ∀ i ≤ n, eCoeff G i ∈ T) :
    eCoeff (F*G) n ∈ T := by
  rw [eCoeff_mul]
  exact T.sum_mem fun i hi => T.mul_mem (T.mul_mem (natCast_mem T _)
    (hF i (by simpa using Finset.mem_range.mp hi))) (hG (n-i) (by omega))

private theorem eCoeff_pow_mem (T : Subring ℚ) (F : PowerSeries ℚ) (n k : ℕ)
    (hF : ∀ i ≤ n, eCoeff F i ∈ T) : eCoeff (F^k) n ∈ T := by
  induction k generalizing n with
  | zero =>
    by_cases h : n = 0
    · subst n; simp
    · simp [eCoeff, coeff_one, h]
  | succ k ih =>
    rw [pow_succ]
    exact eCoeff_mul_mem T _ _ n (fun i hi => ih i (fun j hj => hF j (by omega))) hF

private theorem source_integral (C : PowerSeries ℚ) (hC : IsSourceSeries C) :
    ∀ n, (∃ z : ℤ, eCoeff C n = z) ∧ (∃ z : ℤ, eCoeff ((PowerSeries.C (1/2 : ℚ) * ((exp ℚ).subst (primitive (C^4)) - (exp ℚ).subst (-(primitive (C^4)))))) n = z) := by
  let T : Subring ℚ := (Int.castRingHom ℚ).range
  have hm : ∀ n, eCoeff C n ∈ T ∧ eCoeff ((PowerSeries.C (1/2 : ℚ) * ((exp ℚ).subst (primitive (C^4)) - (exp ℚ).subst (-(primitive (C^4)))))) n ∈ T := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero =>
        rw [eCoeff_zero, eCoeff_zero, hC.1, sourceSinh_constant]
        exact ⟨T.one_mem, T.zero_mem⟩
      | succ n =>
        constructor
        · rw [← eCoeff_derivative, (source_system C hC).1]
          exact eCoeff_mul_mem T _ _ n (fun i hi => (ih i (by omega)).2)
            (fun i hi => eCoeff_pow_mem T C i 4 (fun j hj => (ih j (by omega)).1))
        · rw [← eCoeff_derivative, (source_system C hC).2]
          exact eCoeff_pow_mem T C n 5 (fun i hi => (ih i (by omega)).1)
  intro n
  exact ⟨by obtain ⟨z,hz⟩ := (hm n).1; exact ⟨z,hz.symm⟩,
    by obtain ⟨z,hz⟩ := (hm n).2; exact ⟨z,hz.symm⟩⟩

private noncomputable def sourceU (C : PowerSeries ℚ) : PowerSeries ℚ := (PowerSeries.C (1/2 : ℚ) * ((exp ℚ).subst (primitive (C^4)) - (exp ℚ).subst (-(primitive (C^4))))) * C⁻¹

@[simp] private theorem sourceU_constant (C : PowerSeries ℚ) : constantCoeff (sourceU C) = 0 := by
  rw [sourceU, map_mul, sourceSinh_constant, zero_mul]

private theorem sourceU_identities (C : PowerSeries ℚ) (hC : IsSourceSeries C) :
    PowerSeries.derivative (R := ℚ) (sourceU C) = C^2 ∧ (1 - sourceU C^2)*C^2 = 1 := by
  have hunit : C * C⁻¹ = 1 := PowerSeries.mul_inv_cancel C (by simp [hC.1])
  constructor
  · rw [sourceU, Derivation.leibniz, (source_system C hC).2, derivative_inv',
      (source_system C hC).1]
    simp only [smul_eq_mul]
    calc
      _ = C^4*(C*C⁻¹) - (PowerSeries.C (1/2 : ℚ) * ((exp ℚ).subst (primitive (C^4)) - (exp ℚ).subst (-(primitive (C^4)))))^2*C^2*(C*C⁻¹)^2 := by ring
      _ = (C^2 - (PowerSeries.C (1/2 : ℚ) * ((exp ℚ).subst (primitive (C^4)) - (exp ℚ).subst (-(primitive (C^4)))))^2)*C^2 := by rw [hunit]; ring
      _ = C^2 := by rw [source_invariant C hC]; ring
  · calc
      _ = C^2 - (PowerSeries.C (1/2 : ℚ) * ((exp ℚ).subst (primitive (C^4)) - (exp ℚ).subst (-(primitive (C^4)))))^2*(C*C⁻¹)^2 := by dsimp [sourceU]; ring
      _ = 1 := by rw [hunit]; simpa using source_invariant C hC

private theorem source_cubic (C : PowerSeries ℚ) (hC : IsSourceSeries C) :
    sourceU C - PowerSeries.C (1/3 : ℚ) * sourceU C^3 = X := by
  have h3 : (3 : PowerSeries ℚ) * PowerSeries.C (1/3 : ℚ) = 1 := by
    rw [← map_ofNat (PowerSeries.C (R := ℚ)) 3, ← map_mul]
    norm_num
  apply PowerSeries.derivative.ext
  · rw [map_sub, Derivation.leibniz, derivative_C, smul_zero, add_zero,
      derivative_pow, (sourceU_identities C hC).1, derivative_X]
    simp only [smul_eq_mul]
    calc
      _ = (1 - ((3 : PowerSeries ℚ)*PowerSeries.C (1/3 : ℚ))*sourceU C^2)*C^2 := by ring
      _ = 1 := by rw [h3]; simpa using (sourceU_identities C hC).2
  · simp

end D5.S1.Recurrence.Residue.BalaQuarticEGFEventualDivisibility

namespace D5.S1.Recurrence.Residue.BalaQuarticEGFEventualDivisibility
open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition
open D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality
  (IsRIntegralRat)

private theorem coeff_mul_mem (T : Subring ℚ) (F G : PowerSeries ℚ) (n : ℕ)
    (hF : ∀ i ≤ n, coeff i F ∈ T) (hG : ∀ i ≤ n, coeff i G ∈ T) :
    coeff n (F*G) ∈ T := by
  rw [PowerSeries.coeff_mul]
  exact T.sum_mem fun ij hij => T.mul_mem
    (hF ij.1 (by have := Finset.mem_antidiagonal.mp hij; omega))
    (hG ij.2 (by have := Finset.mem_antidiagonal.mp hij; omega))

private theorem coeff_pow_mem (T : Subring ℚ) (F : PowerSeries ℚ) (n k : ℕ)
    (hF : ∀ i ≤ n, coeff i F ∈ T) : coeff n (F^k) ∈ T := by
  induction k generalizing n with
  | zero =>
    by_cases h : n=0 <;> simp [h, coeff_one]
  | succ k ih =>
    rw [pow_succ]
    exact coeff_mul_mem T _ _ n (fun i hi => ih i (fun j hj => hF j (by omega))) hF

private theorem coeff_mul_mem_low (T : Subring ℚ) (F G : PowerSeries ℚ) (n : ℕ)
    (hF0 : constantCoeff F = 0) (hG0 : constantCoeff G = 0)
    (hF : ∀ i < n, coeff i F ∈ T) (hG : ∀ i < n, coeff i G ∈ T) :
    coeff n (F*G) ∈ T := by
  rw [PowerSeries.coeff_mul]
  apply T.sum_mem
  intro ij hij
  have hh := Finset.mem_antidiagonal.mp hij
  by_cases hi : ij.1 = 0
  · simp [hi, coeff_zero_eq_constantCoeff, hF0]
  by_cases hj : ij.2 = 0
  · simp [hj, coeff_zero_eq_constantCoeff, hG0]
  exact T.mul_mem (hF ij.1 (by omega)) (hG ij.2 (by omega))

private theorem sourceU_coeff_mem (T : Subring ℚ) (h3 : (1/3 : ℚ) ∈ T)
    (C : PowerSeries ℚ) (hC : IsSourceSeries C) : ∀ n, coeff n (sourceU C) ∈ T := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [coeff_zero_eq_constantCoeff]
    | succ n =>
      have hc := congrArg (coeff (n+1)) (source_cubic C hC)
      simp only [map_sub, coeff_C_mul] at hc
      have hm : coeff (n+1) (sourceU C^3) ∈ T := by
        rw [show sourceU C^3 = sourceU C * (sourceU C^2) by ring]
        exact coeff_mul_mem_low T _ _ _ (sourceU_constant C) (by simp)
          (fun i hi => ih i hi)
          (fun i hi => coeff_pow_mem T _ i 2 (fun j hj => ih j (by omega)))
      have hx : coeff (n+1) (X : PowerSeries ℚ) ∈ T := by
        simp only [coeff_X]
        split <;> simp
      have he : coeff (n+1) (sourceU C) =
          coeff (n+1) (X : PowerSeries ℚ) + (1/3 : ℚ)*coeff (n+1) (sourceU C^3) := by
        exact Eq.symm (add_eq_of_eq_sub (id (Eq.symm hc)))
      rw [he]
      exact T.add_mem hx (T.mul_mem h3 hm)

private theorem source_coeff_mem (T : Subring ℚ) (h2 : (1/2 : ℚ) ∈ T) (h3 : (1/3 : ℚ) ∈ T)
    (C : PowerSeries ℚ) (hC : IsSourceSeries C) : ∀ n, coeff n C ∈ T := by
  have hu := sourceU_coeff_mem T h3 C hC
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n; simp [coeff_zero_eq_constantCoeff, hC.1]
    let B : PowerSeries ℚ := mk fun j => if j<n then coeff j C else 0
    have hB0 : constantCoeff B = 1 := by
      rw [← coeff_zero_eq_constantCoeff]
      simp [B, Nat.pos_of_ne_zero hn, coeff_zero_eq_constantCoeff, hC.1]
    have hB : ∀ j, coeff j B ∈ T := by
      intro j
      simp only [B, coeff_mk]
      split
      · exact ih j (by assumption)
      · exact T.zero_mem
    have hd := D5.S1.Recurrence.Residue.DiagonalPowerRatioAllOdd.diagonal_multiplier (n := n)
      hC.1 hB0 (fun j hj => by simp [B, hj]) 2
    have hb : coeff n B = 0 := by simp [B]
    rw [hb, sub_zero, Nat.cast_ofNat] at hd
    have hr := congrArg (coeff n) (sourceU_identities C hC).2
    have hs : coeff n (C^2) = coeff n (sourceU C^2 * C^2) := by
      rw [sub_mul, one_mul, map_sub] at hr
      have hone : coeff n (1 : PowerSeries ℚ) = 0 := by simp [coeff_one, hn]
      rw [hone] at hr
      linear_combination hr
    have hm : coeff n (sourceU C^2 * C^2) ∈ T := by
      rw [PowerSeries.coeff_mul]
      apply T.sum_mem
      intro ij hij
      have hh := Finset.mem_antidiagonal.mp hij
      by_cases hi : ij.1=0
      · simp [hi, coeff_zero_eq_constantCoeff]
      exact T.mul_mem (coeff_pow_mem T _ _ 2 (fun j _ => hu j))
        (coeff_pow_mem T _ _ 2 (fun j hj => ih j (by omega)))
    have he : coeff n C = (1/2 : ℚ) *
        (coeff n (sourceU C^2*C^2) - coeff n (B^2)) := by
      linear_combination -hd / 2 + hs / 2
    rw [he]
    exact T.mul_mem h2 (T.sub_mem hm (coeff_pow_mem T B n 2 (fun j _ => hB j)))

private def localRing (N : ℕ) : Subring ℚ where
  carrier := {q | IsRIntegralRat N q}
  zero_mem' := IsRIntegralRat.zero N
  one_mem' := IsRIntegralRat.one_coprime N
  add_mem' := IsRIntegralRat.add
  neg_mem' := IsRIntegralRat.neg
  mul_mem' := IsRIntegralRat.mul_coprime

private theorem source_den_coprime (C : PowerSeries ℚ) (hC : IsSourceSeries C)
    (N : ℕ) (hN : Nat.Coprime N 6) (j : ℕ) : Nat.Coprime N (coeff j C).den := by
  have h2 : (1/2 : ℚ) ∈ localRing N := by
    change Nat.Coprime (1/2 : ℚ).den N
    norm_num
    exact (hN.symm.of_dvd_left (by decide : 2 ∣ 6)).odd_of_left
  have h3 : (1/3 : ℚ) ∈ localRing N := by
    change Nat.Coprime (1/3 : ℚ).den N
    norm_num
    exact hN.symm.of_dvd_left (by decide : 3 ∣ 6)
  exact (source_coeff_mem (localRing N) h2 h3 C hC j).symm

end D5.S1.Recurrence.Residue.BalaQuarticEGFEventualDivisibility

namespace D5.S1.Recurrence.Residue.BalaQuarticEGFEventualDivisibility
open PowerSeries
open D5.S1.Recurrence.Residue.IntegralEGFComposition

theorem result : claim := by
  refine ⟨source_exists_unique.exists, ?_⟩
  intro C hC N hNpos hN
  refine ⟨(N+1)/2, ?_⟩
  intro n hn
  obtain ⟨z,hz⟩ := (source_integral C hC (2*n)).1
  let b : ℚ := coeff (2*n) C
  have hb : (b.num : ℚ) = b*(b.den : ℚ) :=
    (div_eq_iff (by exact_mod_cast b.den_nz)).mp (Rat.num_div_den b)
  have hzq : (z : ℚ)*(b.den : ℚ) = ((2*n).factorial : ℚ)*(b.num : ℚ) := by
    rw [hb, ← hz]
    change (((2*n).factorial : ℚ)*b)*(b.den : ℚ) = _
    ring
  have hzi : z*(b.den : ℤ) = ((2*n).factorial : ℤ)*b.num := by exact_mod_cast hzq
  have hfact : N ∣ (2*n).factorial := Nat.dvd_factorial hNpos (by omega)
  have hmult : (N : ℤ) ∣ z*(b.den : ℤ) := by
    rw [hzi]
    exact dvd_mul_of_dvd_left (by exact_mod_cast hfact) _
  have hcop : Int.gcd (N : ℤ) (b.den : ℤ) = 1 := by
    simpa only [Int.gcd_natCast_natCast] using (source_den_coprime C hC N hN (2*n)).gcd_eq_one
  obtain ⟨k,hk⟩ := Int.dvd_of_dvd_mul_left_of_gcd_one hmult hcop
  refine ⟨k, ?_⟩
  change eCoeff C (2*n) = _
  rw [hz, hk]
  push_cast
  rfl

end D5.S1.Recurrence.Residue.BalaQuarticEGFEventualDivisibility
