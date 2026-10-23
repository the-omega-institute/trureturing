/- GID: D5/S1/Recurrence/Invariants/SomosPrimeIntegrality
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/SomosPrimeIntegrality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Frobenius lifting and a least-prime-factor obstruction characterize integrality. -/

/-
admission_basis: open-problem-resolution (#18793; Proved)
escape_witness: D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted; D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.prime_of_integral; D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.unique
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19794.
Published-owner audit targets: D5.S1.Recurrence.Invariants.AbsoluteReciprocalGeometricParity.agree_mul; D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.agree_iff; D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.agree_pow; D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.agree_subst_order; D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.power_two_one; https://github.com/the-omega-institute/trureturing/issues/19794.
The source predicates retain the recorded coefficient rings and normalizations.
The claim states the geometric coefficient series literally; proofs use CompositionalIterateCongruence.mobius through the consumed correspondence isGF_iff.
utility: none; no finite-instance refutation, enumeration, checker or numeric reduction.
Dependency identities are declaration statement_id values from the compiled Lean report.

F1: D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity
  declaration: D5.S1.Recurrence.Invariants.AbsoluteReciprocalGeometricParity.agree_mul
  statement_id: sha256:0b071f927d0c7116ae10fa21ec0d53961d2d6257d7126ef2321b75ceda92cb08
F2: D5/S1/Recurrence/Invariants/CompositionalIterateCongruence
  declaration: D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.Agree
  statement_id: sha256:18e60d106d70a7c2b4a1f20df01a2a3b5de4f15b8b0e181c4e59849d2e97d39e
F3: D5/S1/Recurrence/Invariants/CompositionalIterateCongruence
  declaration: D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius
  statement_id: sha256:c14027d96353cb11d580e4a417ec6f198feb0c6381ea739f21378160778c8d16
F4: D5/S1/Recurrence/Invariants/CompositionalIterateCongruence
  declaration: D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius_denominator
  statement_id: sha256:ea2185ba8a7b4378f0ccbba219bd7077c7c6c148eee12eb3493d263b4dddccd1
F5: D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity
  declaration: _private.D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.0.D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.Agree
  statement_id: sha256:e3cd9c09ab9c066077e3362c2145b9293441e263c1e4e0df7614ff40a3b1cb53
F6: D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity
  declaration: D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.agree_iff
  statement_id: sha256:340430849ca0ad913c0aa0863bcccb92d33bd21aa50c3b412a8b3cef397f35ad
F7: D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity
  declaration: D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.agree_pow
  statement_id: sha256:b3bb90d55d8ba37cc611a4805c85710ec861d7ff65a81fdff131082c6e94ac01
F8: D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity
  declaration: D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.agree_subst_order
  statement_id: sha256:ead6f2eaafaae036370ac4584734f53ff96d7447845331c6fff0a1d1fe01facd
F9: D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity
  declaration: D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.prime_power_subst
  statement_id: sha256:4b665513911f58443c7679757dc619d66730344174351ea1f23cedc92766f795

proof_shape: IsGF: bind-only
  consumers: claim, isGF_iff, result
  direct_frozen_dependencies: none
proof_shape: claim: bind-only
  consumers: result
  direct_frozen_dependencies: none
proof_shape: subst_one_series: bind-only
  consumers: General.residual_base, isGF_iff, General.low_order
  direct_frozen_dependencies: none
proof_shape: General.residual: bind-only
  consumers: General.residual_agree, General.residual_top, General.residual_base,
  General.exists_solution_of_correction, General.unique, General.residual_divisible,
  General.exists_integral, General.exists_rational, isGF_iff, General.map_residual,
  General.low_order, General.low_recurrence, General.prime_of_integral, result
  direct_frozen_dependencies: none
proof_shape: General.twist_agree: bind-only
  consumers: General.residual_agree, General.residual_top
  direct_frozen_dependencies: F2, F8
proof_shape: General.unit_power_top: bind-only
  consumers: General.residual_top
  direct_frozen_dependencies: F2, F5, F6
proof_shape: General.residual_agree: bind-only
  consumers: General.exists_solution_of_correction
  direct_frozen_dependencies: F1, F2, F7, F8
proof_shape: General.residual_top: bind-only
  consumers: General.exists_solution_of_correction, General.unique
  direct_frozen_dependencies: F1, F2, F5, F6, F7, F8
proof_shape: General.residual_base: bind-only
  consumers: General.exists_solution_of_correction
  direct_frozen_dependencies: F2
proof_shape: General.exists_solution_of_correction: content
  escape_witness: D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted
  consumers: General.exists_integral, General.exists_rational
  direct_frozen_dependencies: F1, F2, F5, F6, F7, F8
proof_shape: General.unique: content
  escape_witness: D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.unique
  consumers: result
  direct_frozen_dependencies: F1, F2, F5, F6, F7, F8
proof_shape: General.residual_divisible: bind-only
  consumers: General.exists_integral
  direct_frozen_dependencies: F9
proof_shape: General.exists_integral: content
  escape_witness: D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted
  consumers: result
  direct_frozen_dependencies: F1, F2, F5, F6, F7, F8, F9
proof_shape: General.exists_rational: content
  escape_witness: D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted
  consumers: result
  direct_frozen_dependencies: F1, F2, F5, F6, F7, F8
proof_shape: B_equation: bind-only
  consumers: isGF_iff
  direct_frozen_dependencies: F3, F4
proof_shape: isGF_iff: bind-only
  consumers: result
  direct_frozen_dependencies: F3, F4
proof_shape: General.map_residual: bind-only
  consumers: result
  direct_frozen_dependencies: none
proof_shape: General.low_order: bind-only
  consumers: General.low_recurrence
  direct_frozen_dependencies: F2, F5, F6, F8
proof_shape: General.low_recurrence: bind-only
  consumers: General.prime_of_integral
  direct_frozen_dependencies: F2, F5, F6, F8
proof_shape: General.prime_of_integral: content
  escape_witness: D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.prime_of_integral
  consumers: result
  direct_frozen_dependencies: F2, F5, F6, F8
proof_shape: result: content
  escape_witness: D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.prime_of_integral
  consumers: settling conclusion
  direct_frozen_dependencies: F1, F2, F3, F4, F5, F6, F7, F8, F9
-/

import D5.S1.Recurrence.Invariants.CompositionalIterateCongruence
import D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity
import D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality
import Mathlib.RingTheory.PowerSeries.Derivative
import D5.S1.Recurrence.Invariants.AbsoluteReciprocalGeometricParity

/-! Prime exponents characterize integrality in the normalized Somos family. -/

set_option autoImplicit false

namespace D5.S1.Recurrence.Invariants.SomosPrimeIntegrality

open PowerSeries



/-- OEIS A091190 (p = 3), A091200 (p = 5): "G.f. A(x) satisfies x*A(x)^p = B(x*A(x^p)) where
B(x) = x/(1-p*x)", with a(0) = 1 (offset 0). -/
def IsGF (p : ℕ) (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 1 ∧
    X * A ^ p = PowerSeries.subst (X * PowerSeries.subst ((X : PowerSeries ℚ) ^ p) A) (mk fun n => if n = 0 then 0 else (p : ℚ) ^ (n - 1))

/-- OEIS A091190, A091200 (comment): "More generally, given A(x) satisfies x*A(x)^p = B(x*A(x^p)) where
B(x) = x/(1-p*x), then it appears that A(x) is an integer series only when p is prime." -/
def claim : Prop :=
  ∀ p : ℕ, 2 ≤ p →
    (∃ A, IsGF p A) ∧
      ∀ A, IsGF p A → ((∀ n, ∃ m : ℤ, coeff n A = m) ↔ p.Prime)

end D5.S1.Recurrence.Invariants.SomosPrimeIntegrality


open PowerSeries
open D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity
open D5.S1.Recurrence.Invariants.CompositionalIterateCongruence (Agree)
open D5.S1.Recurrence.Invariants.AbsoluteReciprocalGeometricParity (agree_mul)

namespace D5.S1.Recurrence.Invariants.SomosPrimeIntegrality

@[simp] private theorem subst_one_series {R : Type*} [CommRing R] (a : PowerSeries R) :
    (1 : PowerSeries R).subst a = 1 := by
  simpa only [map_one] using (subst_C (a := a) (1 : R))

end D5.S1.Recurrence.Invariants.SomosPrimeIntegrality

namespace D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General
section Ring
variable {R : Type*} [CommRing R]

private noncomputable def residual (p : ℕ) (f : PowerSeries R) : PowerSeries R :=
  f ^ p * (1 - C (p : R) * X * (f.subst ((X : PowerSeries R) ^ p))) - (f.subst ((X : PowerSeries R) ^ p))

private theorem twist_agree {p n : ℕ} (hp : 2 ≤ p) (hn : 1 ≤ n) {f g : PowerSeries R}
    (h : Agree n f g) : Agree (n + 1) ((f.subst ((X : PowerSeries R) ^ p))) ((g.subst ((X : PowerSeries R) ^ p))) := by
  apply agree_subst_order (by simp [show p ≠ 0 by omega]) (by simp [show p ≠ 0 by omega])
    (dvd_refl (X ^ p)) (dvd_refl (X ^ p)) (by nlinarith) h
  intro k hk; rfl

private theorem unit_power_top {n : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) (h : Agree n f g) (p : ℕ) :
    coeff n (f ^ p) - coeff n (g ^ p) = (p : R) * (coeff n f - coeff n g) := by
  classical
  obtain ⟨w, hw⟩ := (agree_iff _ _ _).mp h
  have he : f ^ p - g ^ p = X ^ n *
      (w * ∑ i ∈ Finset.range p, f ^ i * g ^ (p - 1 - i)) := by
    rw [← geom_sum₂_mul, hw]
    ring
  have hc := congrArg (coeff n) he
  have hd := congrArg (coeff n) hw
  simp only [map_sub, coeff_X_pow_mul', le_refl, ↓reduceIte, Nat.sub_self,
    coeff_zero_eq_constantCoeff, map_mul, map_sum, map_pow, hf, hg,
    one_pow, one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hc hd
  rw [hd]
  simpa [mul_comm] using hc

private theorem residual_agree {p n : ℕ} (hp : 2 ≤ p) (hn : 1 ≤ n) {f g : PowerSeries R}
    (h : Agree n f g) : Agree n (residual p f) (residual p g) := by
  have ht := twist_agree hp hn h
  have hden : Agree n (1 - C (p : R) * X * (f.subst ((X : PowerSeries R) ^ p)))
      (1 - C (p : R) * X * (g.subst ((X : PowerSeries R) ^ p))) := by
    intro k hk
    simp only [map_sub]
    congr 1
    exact agree_mul (fun _ _ => rfl) (fun i hi => ht i (by omega)) k hk
  intro k hk
  simp only [residual, map_sub]
  rw [agree_mul (agree_pow h p) hden k hk, ht k (by omega)]

private theorem residual_top {p n : ℕ} (hp : 2 ≤ p) (hn : 1 ≤ n) {f g : PowerSeries R}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) (h : Agree n f g) :
    coeff n (residual p f) - coeff n (residual p g) = (p : R) * (coeff n f - coeff n g) := by
  have ht := twist_agree hp hn h
  have hprod : Agree n (f ^ p * (f.subst ((X : PowerSeries R) ^ p))) (g ^ p * (g.subst ((X : PowerSeries R) ^ p))) :=
    agree_mul (agree_pow h p) (fun k hk => ht k (by omega))
  have hc : coeff n (C (p : R) * X * (f ^ p * (f.subst ((X : PowerSeries R) ^ p)))) =
      coeff n (C (p : R) * X * (g ^ p * (g.subst ((X : PowerSeries R) ^ p)))) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp only [mul_assoc, coeff_C_mul, coeff_succ_X_mul]
    rw [hprod j (by omega)]
  have he (a : PowerSeries R) : residual p a =
      a ^ p - C (p : R) * X * (a ^ p * (a.subst (X ^ p))) - (a.subst (X ^ p)) := by dsimp [residual]; ring
  rw [he, he]
  simp only [map_sub]
  rw [hc, ht n (by omega)]
  linear_combination unit_power_top hf hg h p

private theorem residual_base (p : ℕ) : Agree 1 (residual p (1 : PowerSeries R)) 0 := by
  intro k hk
  have : k = 0 := Nat.lt_one_iff.mp hk
  subst k
  simp [residual]

private theorem exists_solution_of_correction (p : ℕ) (hp : 2 ≤ p) (q : R → R)
    (hq : ∀ f : PowerSeries R, Agree 1 f 1 → ∀ n,
      (p : R) * q (coeff n (residual p f)) = -coeff n (residual p f)) :
    ∃ f : PowerSeries R, constantCoeff f = 1 ∧ residual p f = 0 := by
  obtain ⟨f, hf, he⟩ := D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted (residual p) 1 1 0 (p : R) q
    (by intro n hn f g hf hg h; simpa using residual_agree hp hn h)
    (by
      intro n hn f g hf hg h
      have hf0 : constantCoeff f = 1 := by simpa using hf 0 (by decide)
      have hg0 : constantCoeff g = 1 := by simpa using hg 0 (by decide)
      simpa using residual_top hp hn hf0 hg0 h)
    hq (by simpa using residual_base (R := R) p)
  exact ⟨f, by simpa using hf 0 (by decide), he⟩

private theorem unique {p : ℕ} (hp : 2 ≤ p) [NoZeroDivisors R] (hp0 : (p : R) ≠ 0)
    {f g : PowerSeries R} (hf : constantCoeff f = 1) (hg : constantCoeff g = 1)
    (he : residual p f = 0) (he' : residual p g = 0) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; simpa [hf] using hg.symm
    have ht := residual_top hp (by omega : 1 ≤ n) hf hg ih
    rw [he, he', map_zero, sub_self] at ht
    exact sub_eq_zero.mp ((mul_eq_zero.mp ht.symm).resolve_left hp0)
end Ring

private theorem residual_divisible (p : ℕ) (hp : p.Prime) (f : PowerSeries ℤ) (n : ℕ) :
    (p : ℤ) ∣ coeff n (residual p f) := by
  let : Fact p.Prime := ⟨hp⟩
  let hom := Int.castRingHom (ZMod p)
  have ht : PowerSeries.map hom (f.subst ((X : PowerSeries ℤ) ^ p)) = (f.map hom).subst ((X : PowerSeries (ZMod p)) ^ p) := by
    rw [show PowerSeries.map hom (f.subst ((X : PowerSeries ℤ) ^ p)) =
        (f.map hom).subst ((X ^ p).map hom) from map_subst (.X_pow hp.ne_zero) f]
    simp
  have hp0 : hom (p : ℤ) = 0 := by simp [hom]
  have he : (residual p f).map hom = 0 := by
    simp only [residual, map_sub, map_mul, map_pow, map_one, map_C, map_X, ht, hp0, map_zero,
      zero_mul, sub_zero, mul_one]
    rw [prime_power_subst, sub_self]
  have h := congrArg (coeff n) he
  simp only [coeff_map, map_zero, hom, Int.coe_castRingHom] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

private theorem exists_integral (p : ℕ) (hp : p.Prime) :
    ∃ f : PowerSeries ℤ, constantCoeff f = 1 ∧ residual p f = 0 := by
  apply exists_solution_of_correction p hp.two_le (fun t => -(t / (p : ℤ)))
  intro f hf n
  rw [mul_neg, Int.mul_ediv_cancel' (residual_divisible p hp f n)]

private theorem exists_rational (p : ℕ) (hp : 2 ≤ p) :
    ∃ f : PowerSeries ℚ, constantCoeff f = 1 ∧ residual p f = 0 := by
  apply exists_solution_of_correction p hp (fun t => -t / (p : ℚ))
  intro f hf n
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

end D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General

namespace D5.S1.Recurrence.Invariants.SomosPrimeIntegrality
private theorem B_equation (p : ℕ) :
    (mk fun n => if n = 0 then 0 else (p : ℚ) ^ (n - 1)) * (1 - C (p : ℚ) * X) = X := by
  have hb : (mk fun n => if n = 0 then 0 else (p : ℚ) ^ (n - 1)) =
      D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius (p : ℚ) := by
    ext n
    cases n with
    | zero => simp [D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius]
    | succ n => simp [D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius]
  rw [hb]
  exact D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius_denominator (p : ℚ)

private theorem isGF_iff (p : ℕ) (f : PowerSeries ℚ) :
    IsGF p f ↔ constantCoeff f = 1 ∧ D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.residual p f = 0 := by
  let t : PowerSeries ℚ := X * (f.subst ((X : PowerSeries ℚ) ^ p))
  have ht0 : constantCoeff t = 0 := by simp [t]
  have ht : HasSubst t := .of_constantCoeff_zero ht0
  have hB := congrArg (subst t) (B_equation p)
  rw [subst_mul ht, subst_sub ht, subst_one_series, subst_mul ht, subst_C, subst_X ht] at hB
  change (mk fun n => if n = 0 then 0 else (p : ℚ) ^ (n - 1)).subst t * (1 - C (p : ℚ) * t) = t at hB
  constructor
  · rintro ⟨hf0, hf⟩
    refine ⟨hf0, ?_⟩
    have he : X * D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.residual p f = 0 := by
      change X * f ^ p = (mk fun n => if n = 0 then 0 else (p : ℚ) ^ (n - 1)).subst t at hf
      dsimp [D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.residual]
      change X * (f ^ p * (1 - C (p : ℚ) * X * (f.subst ((X : PowerSeries ℚ) ^ p))) - (f.subst ((X : PowerSeries ℚ) ^ p))) = 0
      dsimp [t] at hB
      linear_combination (1 - C (p : ℚ) * X * (f.subst ((X : PowerSeries ℚ) ^ p))) * hf + hB
    exact (mul_eq_zero.mp he).resolve_left X_ne_zero
  · rintro ⟨hf0, hf⟩
    refine ⟨hf0, ?_⟩
    change X * f ^ p = (mk fun n => if n = 0 then 0 else (p : ℚ) ^ (n - 1)).subst t
    have hd : (1 - C (p : ℚ) * t : PowerSeries ℚ) ≠ 0 := by
      intro h
      have hc := congrArg constantCoeff h
      simp [ht0] at hc
    apply mul_right_cancel₀ hd
    dsimp [D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.residual] at hf
    dsimp [t] at hB ⊢
    linear_combination X * hf - hB
end D5.S1.Recurrence.Invariants.SomosPrimeIntegrality

namespace D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General
private theorem map_residual {R S : Type*} [CommRing R] [CommRing S]
    (p : ℕ) (hp : 0 < p) (hom : R →+* S) (f : PowerSeries R) :
    (residual p f).map hom = residual p (f.map hom) := by
  have ht : PowerSeries.map hom (f.subst ((X : PowerSeries R) ^ p)) = ((f.map hom).subst ((X : PowerSeries S) ^ p)) := by
    rw [show PowerSeries.map hom (f.subst ((X : PowerSeries R) ^ p)) =
        (f.map hom).subst ((X ^ p).map hom) from map_subst (.X_pow hp.ne') f]
    simp
  simp only [residual, map_sub, map_mul, map_pow, map_one, map_natCast, map_X, ht]

private theorem low_order (p : ℕ) (hp : 2 ≤ p) (f : PowerSeries ℚ) (hf : constantCoeff f = 1)
    (he : residual p f = 0) :
    (X : PowerSeries ℚ) ^ p ∣ f ^ p * (1 - C (p : ℚ) * X) - 1 := by
  have hu : Agree p ((f.subst ((X : PowerSeries ℚ) ^ p))) 1 := by
    have h : Agree 1 f 1 := by
      intro k hk
      have hk0 : k = 0 := Nat.lt_one_iff.mp hk
      subst k
      simpa using hf
    have ht := agree_subst_order (by simp [show p ≠ 0 by omega])
      (by simp [show p ≠ 0 by omega]) (dvd_refl (X ^ p)) (dvd_refl (X ^ p))
      (le_refl (p * 1)) h (show Agree (p * 1) (X ^ p) (X ^ p) from fun _ _ => rfl)
    intro k hk
    simpa only [mul_one, subst_one_series] using ht k (by simpa using hk)
  have hd := dvd_mul_of_dvd_left ((agree_iff _ _ _).mp hu) (1 + C (p : ℚ) * X * f ^ p)
  convert hd using 1
  dsimp [residual] at he
  linear_combination he

private theorem low_recurrence (p : ℕ) (hp : 2 ≤ p) (f : PowerSeries ℚ) (hf : constantCoeff f = 1)
    (he : residual p f = 0) {n : ℕ} (hn : n + 1 < p) :
    (n + 1 : ℚ) * coeff (n + 1) f = (1 + (p : ℚ) * n) * coeff n f := by
  let H : PowerSeries ℚ := f ^ p * (1 - C (p : ℚ) * X) - 1
  have hH : (X : PowerSeries ℚ) ^ p ∣ H := low_order p hp f hf he
  have hD : (X : PowerSeries ℚ) ^ (p - 1) ∣ derivative H := by
    apply X_pow_dvd_iff.mpr
    intro k hk
    rw [coeff_derivative, X_pow_dvd_iff.mp hH (k + 1) (by omega), zero_mul]
  have hformula : derivative H = C (p : ℚ) * f ^ (p - 1) *
      ((1 - C (p : ℚ) * X) * derivative f - f) := by
    dsimp [H]
    simp only [map_sub, derivative_one, sub_zero, Derivation.leibniz, derivative_pow,
      derivative_C, derivative_X]
    rw [show f ^ p = f ^ (p - 1) * f from by rw [← pow_succ]; congr 1; omega]
    simp only [map_natCast]
    ring
  rw [hformula] at hD
  have hunit : IsUnit (C (p : ℚ) * f ^ (p - 1)) := by
    apply isUnit_iff_constantCoeff.mpr
    simp only [map_mul, constantCoeff_C, map_pow, hf, one_pow, mul_one]
    exact isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))
  have hE : (X : PowerSeries ℚ) ^ (p - 1) ∣
      ((1 - C (p : ℚ) * X) * derivative f - f) :=
    (IsUnit.dvd_mul_left hunit).mp hD
  have hc := X_pow_dvd_iff.mp hE n (by omega)
  have hexpand : (1 - C (p : ℚ) * X) * derivative f - f =
      derivative f - C (p : ℚ) * (X * derivative f) - f := by ring
  rw [hexpand] at hc
  simp only [map_sub, coeff_C_mul, coeff_derivative] at hc
  have hX : coeff n (X * derivative f) = (n : ℚ) * coeff n f := by
    cases n with
    | zero => simp
    | succ n => rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring
  rw [hX] at hc
  linear_combination hc
end D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General

namespace D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General
private theorem prime_of_integral (p : ℕ) (hp : 2 ≤ p) (f : PowerSeries ℚ)
    (hf : constantCoeff f = 1) (he : residual p f = 0)
    (hint : ∀ n, ∃ m : ℤ, coeff n f = m) : p.Prime := by
  classical
  by_contra hnp
  let q := p.minFac
  have hq : q.Prime := Nat.minFac_prime (by omega)
  have hqp : q < p := (Nat.not_prime_iff_minFac_lt hp).mp hnp
  have hqd : q ∣ p := Nat.minFac_dvd p
  let : Fact q.Prime := ⟨hq⟩
  let z : ℕ → ℤ := fun n => Classical.choose (hint n)
  have hz (n : ℕ) : coeff n f = (z n : ℚ) := Classical.choose_spec (hint n)
  have hz0 : z 0 = 1 := by
    apply Int.cast_injective (α := ℚ)
    rw [← hz]
    simpa using hf
  have hpz : (p : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff p q).mpr hqd
  have hrec (n : ℕ) (hn : n + 1 ≤ q) :
      (n + 1 : ZMod q) * (z (n + 1) : ZMod q) = (z n : ZMod q) := by
    have hr := low_recurrence p hp f hf he (show n + 1 < p by omega)
    rw [hz (n + 1), hz n] at hr
    have hi : (n + 1 : ℤ) * z (n + 1) = (1 + (p : ℤ) * n) * z n := by
      exact_mod_cast hr
    have hm := congrArg (Int.castRingHom (ZMod q)) hi
    simpa [hpz] using hm
  have hfac : ∀ n, n ≤ q → (n.factorial : ZMod q) * (z n : ZMod q) = 1 := by
    intro n
    induction n with
    | zero => intro hn; simp [hz0]
    | succ n ih =>
      intro hn
      rw [Nat.factorial_succ, Nat.cast_mul]
      calc
        _ = (n.factorial : ZMod q) * ((n + 1 : ZMod q) * (z (n + 1) : ZMod q)) := by push_cast; ring
        _ = (n.factorial : ZMod q) * (z n : ZMod q) := by rw [hrec n hn]
        _ = 1 := ih (by omega)
  have hzero : (q.factorial : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff q.factorial q).mpr (Nat.dvd_factorial hq.pos le_rfl)
  have hbad := hfac q le_rfl
  rw [hzero, zero_mul] at hbad
  exact zero_ne_one hbad
end D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General

namespace D5.S1.Recurrence.Invariants.SomosPrimeIntegrality
theorem result : claim := by
  classical
  intro p hp
  obtain ⟨f, hf, he⟩ := D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.exists_rational p hp
  refine ⟨⟨f, (isGF_iff p f).mpr ⟨hf, he⟩⟩, ?_⟩
  intro A hA
  have hAr := (isGF_iff p A).mp hA
  constructor
  · exact D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.prime_of_integral p hp A hAr.1 hAr.2
  · intro hprime
    obtain ⟨G, hG0, hG⟩ := D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.exists_integral p hprime
    let hom := Int.castRingHom ℚ
    have hmap0 : constantCoeff (G.map hom) = 1 := by
      exact Eq.symm (Rat.ext (id (Eq.symm hG0)) rfl)
    have hmape : D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.residual p (G.map hom) = 0 := by
      rw [← D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.map_residual p (by omega) hom G, hG, map_zero]
    have hEq : A = G.map hom :=
      D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.unique hp (Nat.cast_ne_zero.mpr (by omega)) hAr.1 hmap0 hAr.2 hmape
    intro n
    refine ⟨coeff n G, ?_⟩
    rw [hEq]
    rfl
end D5.S1.Recurrence.Invariants.SomosPrimeIntegrality
