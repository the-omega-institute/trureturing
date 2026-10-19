/- GID: D5/S1/Recurrence/Invariants/HannaGeometricSquareSubstitutionModThree
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaGeometricSquareSubstitutionModThree
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Integral construction and geometric reduction prove Hanna mod-three coefficients. -/

/-
proof_shape: denominator_zero: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.argument_mul, D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.map_argument, D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.isGF_iff, D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.geometric_equation.
proof_shape: argument_zero: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.inverse_bridge, D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.normalized_iff, D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.map_equation, D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.geometric_equation.
proof_shape: argument_order: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.equation_unique.
proof_shape: argument_mul: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.inverse_bridge, D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.map_argument, D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.geometric_equation.
proof_shape: reversion_rhs_agree: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.step_agree.
proof_shape: residual_even: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.step_coeff.
proof_shape: step_coeff: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.step_agree, D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.integralT_spec.
proof_shape: step_zero: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.integralT, D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.integralT_spec.
proof_shape: step_agree: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.integralT, D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.integralT_spec.
proof_shape: integralT_spec: content; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.integralR_spec.
proof_shape: integralR_spec: content; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.exists_integral.
proof_shape: inverse_bridge: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.exists_integral.
proof_shape: exists_integral: content; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.integralA, D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.integral_equation.
proof_shape: integral_equation: content; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.integral_mod_three, D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.rational_isGF.
proof_shape: normalized_iff: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.equation_unique.
proof_shape: equation_unique: content; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.integral_mod_three, D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.result.
proof_shape: map_argument: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.map_equation.
proof_shape: map_equation: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.integral_mod_three, D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.rational_isGF.
proof_shape: geometric_equation: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.integral_mod_three.
proof_shape: integral_mod_three: content; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.result.
proof_shape: isGF_iff: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.rational_isGF, D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.result.
proof_shape: rational_isGF: content; consumers: D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree.result.
proof_shape: result: content; consumers: settling result.
escape_witness: none
admission_basis: open-problem-resolution (#18850; Proved)
Direct frozen dependencies: existing power-series suppliers at their original declaration addresses;
declaration identities and the elaborated dependency closure are reported in the handover.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19089.
Unbounded existence, uniqueness, and coefficient identities; no finite-instance computation.
The source predicates IsGF and claim retain their literal expressions.
-/

import D5.S1.Recurrence.Invariants.SignedCatalanCubicSubstitutionModThree
import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction

set_option autoImplicit false

namespace D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree

open PowerSeries

/-- OEIS A274479: "G.f. satisfies: A(x)^2 = A( x^2/(1 - 2*x - 4*x^2) )", with A(x) = x + x^2 + ... (offset 1). -/
def IsGF (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 0 ∧ coeff 1 A = 1 ∧
    A ^ 2 = PowerSeries.subst (X ^ 2 * (1 - 2 * X - 4 * X ^ 2 : PowerSeries ℚ)⁻¹) A

/-- OEIS A274479 (P. D. Hanna), conjecture: "a(n) = 1 (mod 3) for n>=1", where a(n) = [x^n] A(x).
The terms are integers. -/
def claim : Prop :=
  (∃ A, IsGF A) ∧
    ∀ A, IsGF A → ∀ n : ℕ, 1 ≤ n → ∃ m : ℤ, coeff n A = m ∧ m ≡ 1 [ZMOD 3]

end D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree

namespace D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree
open PowerSeries D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction D5.S1.Recurrence.Invariants.UnitReversionSquareParity D5.S1.Recurrence.Invariants.ScaledReversionCongruence
variable {R : Type*} [CommRing R]

private noncomputable def denominator : PowerSeries R := 1 - 2 * X - 4 * X ^ 2
private noncomputable def argument : PowerSeries R := X ^ 2 * invOfUnit denominator 1

private theorem denominator_zero : constantCoeff (denominator : PowerSeries R) = 1 := by
  simp [denominator]
private theorem argument_zero : constantCoeff (argument : PowerSeries R) = 0 := by
  simp [argument]
private theorem argument_order : (X : PowerSeries R) ^ 2 ∣ argument := by
  exact ⟨invOfUnit denominator 1, rfl⟩
private theorem argument_mul : (argument : PowerSeries R) * denominator = X ^ 2 := by
  rw [argument, mul_assoc, invOfUnit_mul _ _ denominator_zero, mul_one]

private def Equation (f : PowerSeries R) : Prop := f ^ 2 = f.subst argument

private noncomputable def reversion_rhs (t : PowerSeries R) : PowerSeries R :=
  t.subst (X ^ 2) * (1 - 2 * X * t - 4 * X ^ 2 * t ^ 2)
private noncomputable def residual (t : PowerSeries ℤ) : PowerSeries ℤ := reversion_rhs t - t ^ 2
private noncomputable def step (t : PowerSeries ℤ) : PowerSeries ℤ :=
  t + mk (fun n => coeff n (residual t) / 2)

private theorem reversion_rhs_agree {d : ℕ} (hd : 1 ≤ d) {f g : PowerSeries R}
    (h : Agree d f g) : Agree (d + 1) (reversion_rhs f) (reversion_rhs g) := by
  have hs := D5.S1.Recurrence.Invariants.SignedCatalanCubicSubstitutionModThree.subst_two_agree hd h
  have hx := agree_X h
  have hx2 := agree_X (agree_X (agree_pow h 2))
  have ha : Agree (d + 1) (2 * X * f) (2 * X * g) := by
    simpa only [mul_assoc] using agree_mul (show Agree (d + 1) (2 : PowerSeries R) 2 from fun _ _ => rfl) hx
  have hb : Agree (d + 1) (4 * X ^ 2 * f ^ 2) (4 * X ^ 2 * g ^ 2) := by
    have hh := agree_mul (show Agree (d + 1) (4 : PowerSeries R) 4 from fun _ _ => rfl)
      (agree_mono hx2 (by omega : d + 1 ≤ d + 1 + 1))
    simpa only [pow_two, mul_assoc] using hh
  apply agree_mul hs
  intro n hn
  simp only [map_sub, ha n hn, hb n hn]

private theorem residual_even (t : PowerSeries ℤ) (n : ℕ) : (2 : ℤ) ∣ coeff n (residual t) := by
  let hom := Int.castRingHom (ZMod 2)
  have h2 : (2 : PowerSeries (ZMod 2)) = 0 := by
    rw [← map_ofNat C 2, show (2 : ZMod 2) = 0 by decide, map_zero]
  have h4 : (4 : PowerSeries (ZMod 2)) = 0 := by
    exact h2
  have he : PowerSeries.map hom (residual t) = 0 := by
    simp only [residual, reversion_rhs, map_sub, map_mul, map_pow, map_one,
      map_ofNat, map_X, map_subst_pow hom t 2 (by decide), h2, h4,
      zero_mul, sub_zero, mul_one, ← D5.S1.Recurrence.Invariants.SignedCatalanCubicSubstitutionModThree.prime_power_subst 2, sub_self]
  have hc := congrArg (coeff n) he
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc

private theorem step_coeff (t : PowerSeries ℤ) (n : ℕ) :
    2 * coeff n (step t) = 2 * coeff n t + coeff n (residual t) := by
  simp only [step, map_add, coeff_mk, mul_add]
  rw [Int.mul_ediv_cancel' (residual_even t n)]

private theorem step_zero {t : PowerSeries ℤ} (ht : constantCoeff t = 1) :
    constantCoeff (step t) = 1 := by
  simp [step, residual, reversion_rhs, coeff_zero_eq_constantCoeff,
    ht]

private theorem step_agree {d : ℕ} (hd : 1 ≤ d) {f g : PowerSeries ℤ}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) (h : Agree d f g) :
    Agree (d + 1) (step f) (step g) := by
  intro n hn
  have hs := reversion_rhs_agree hd h n hn
  have hl := D5.S1.Recurrence.Invariants.SignedCatalanCubicSubstitutionModThree.square_linear hf hg h n hn
  have hc := step_coeff f n
  have hc' := step_coeff g n
  simp only [residual, map_sub] at hc hc'
  omega

private noncomputable def integralT : PowerSeries ℤ :=
  Classical.choose (exists_unique_fixed step (fun _ h => step_zero h)
    (fun hd hb hc h => step_agree hd hb hc h))

private theorem integralT_spec : constantCoeff integralT = 1 ∧ reversion_rhs integralT = integralT ^ 2 := by
  have hs := Classical.choose_spec (exists_unique_fixed step (fun _ h => step_zero h)
    (fun hd hb hc h => step_agree hd hb hc h))
  refine ⟨hs.1, ?_⟩
  ext n
  have hc := step_coeff integralT n
  have hf : integralT = step integralT := hs.2.1
  rw [← hf] at hc
  simp only [residual, map_sub] at hc
  omega

private noncomputable def integralR : PowerSeries ℤ := X * integralT

private theorem integralR_spec : constantCoeff integralR = 0 ∧ coeff 1 integralR = 1 ∧
    integralR.subst (X ^ 2) * (1 - 2 * integralR - 4 * integralR ^ 2) = integralR ^ 2 := by
  refine ⟨by simp [integralR], by simpa [integralR] using integralT_spec.1, ?_⟩
  have sx : HasSubst ((X : PowerSeries ℤ) ^ 2) := .X_pow (by decide)
  simp only [integralR, subst_mul sx, subst_X sx]
  have he := integralT_spec.2
  dsimp [reversion_rhs] at he
  linear_combination X ^ 2 * he

end D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree
namespace D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree
open PowerSeries D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction D5.S1.Recurrence.Invariants.UnitReversionSquareParity D5.S1.Recurrence.Invariants.ScaledReversionCongruence
variable {R : Type*} [CommRing R]

private theorem inverse_bridge {a r : PowerSeries R}
    (ha : constantCoeff a = 0) (hr : constantCoeff r = 0)
    (har : a.subst r = X) (hra : r.subst a = X)
    (he : r.subst (X ^ 2) * (1 - 2 * r - 4 * r ^ 2) = r ^ 2) : Equation a := by
  have sa : HasSubst a := .of_constantCoeff_zero ha
  have sr : HasSubst r := .of_constantCoeff_zero hr
  have sx : HasSubst ((X : PowerSeries R) ^ 2) := .X_pow (by decide)
  have si : HasSubst (argument : PowerSeries R) := .of_constantCoeff_zero argument_zero
  have ha2 : HasSubst (a ^ 2) := .of_constantCoeff_zero
    (show PowerSeries.constantCoeff (a ^ 2) = 0 by simp [ha])
  have hone : (1 : PowerSeries R).subst r = 1 := by
    simpa only [map_one] using (subst_C (a := r) (1 : R))
  have htwo : (2 : PowerSeries R).subst r = 2 := by
    simpa only [map_ofNat] using (subst_C (a := r) (2 : R))
  have hfour : (4 : PowerSeries R).subst r = 4 := by
    simpa only [map_ofNat] using (subst_C (a := r) (4 : R))
  have hden : (denominator : PowerSeries R).subst r = 1 - 2 * r - 4 * r ^ 2 := by
    simp only [denominator, subst_sub sr, subst_mul sr, subst_pow sr, subst_X sr, hone, htwo, hfour]
  have hi : (argument : PowerSeries R).subst r * (1 - 2 * r - 4 * r ^ 2) = r ^ 2 := by
    have h := congrArg (subst r) (argument_mul (R := R))
    rw [subst_mul sr, hden, subst_pow sr, subst_X sr] at h
    exact h
  have hu : IsUnit (1 - 2 * r - 4 * r ^ 2) := isUnit_iff_constantCoeff.mpr (by simp [hr])
  have hir : (argument : PowerSeries R).subst r = r.subst (X ^ 2) :=
    hu.mul_right_cancel (hi.trans he.symm)
  have hh := congrArg (fun t : PowerSeries R => t.subst a) hir
  rw [subst_comp_subst_apply sr sa, hra, X_subst,
    subst_comp_subst_apply sx sa, subst_pow sa, subst_X sa] at hh
  have hh' := congrArg (fun t : PowerSeries R => a.subst t) hh
  rw [← subst_comp_subst_apply sr ha2, har, subst_X ha2] at hh'
  exact hh'.symm

private theorem exists_integral : ∃ f : PowerSeries ℤ,
    constantCoeff f = 0 ∧ coeff 1 f = 1 ∧ Equation f := by
  obtain ⟨f, hf, hf1, hrf, hfr⟩ := D5.S1.Recurrence.Invariants.SignedCatalanCubicSubstitutionModThree.inverse_exists integralR integralR_spec.1 integralR_spec.2.1
  exact ⟨f, hf, hf1, inverse_bridge hf integralR_spec.1 hfr hrf integralR_spec.2.2⟩

private noncomputable def integralA : PowerSeries ℤ := Classical.choose exists_integral

private theorem integral_equation : constantCoeff integralA = 0 ∧ coeff 1 integralA = 1 ∧ Equation integralA := by
  exact Classical.choose_spec exists_integral

private theorem normalized_iff (b : PowerSeries R) : Equation (X * b) ↔
    b ^ 2 = invOfUnit denominator 1 * b.subst argument := by
  have si : HasSubst (argument : PowerSeries R) := .of_constantCoeff_zero argument_zero
  change (X * b) ^ 2 = (X * b).subst argument ↔ _
  rw [subst_mul si, subst_X si]
  constructor
  · intro he
    apply X_pow_mul_injective (k := 2)
    dsimp only [argument] at he ⊢
    linear_combination he
  · intro he
    dsimp only [argument] at he ⊢
    linear_combination X ^ 2 * he

private theorem equation_unique [NoZeroDivisors R] (h2 : (2 : R) ≠ 0)
    {f g : PowerSeries R} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1)
    (he : Equation f) (he' : Equation g) : f = g := by
  obtain ⟨b, rfl⟩ := X_dvd_iff.mpr hf
  obtain ⟨c, rfl⟩ := X_dvd_iff.mpr hg
  have hb : constantCoeff b = 1 := by simpa using hf1
  have hc : constantCoeff c = 1 := by simpa using hg1
  have hbe := (normalized_iff b).mp he
  have hce := (normalized_iff c).mp he'
  suffices b = c by rw [this]
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa only [coeff_zero_eq_constantCoeff] using hb.trans hc.symm
    have hs := subst_outer_agree ih (argument_order (R := R))
    have hm := agree_mul (show Agree (2 * n) (invOfUnit (denominator : PowerSeries R) 1)
      (invOfUnit denominator 1) from fun _ _ => rfl) hs
    have hl := D5.S1.Recurrence.Invariants.SignedCatalanCubicSubstitutionModThree.square_linear hb hc ih n (by omega)
    have htop := hm n (by omega)
    rw [← hbe, ← hce] at htop
    have hz : 2 * (coeff n b - coeff n c) = 0 := by linear_combination -hl + htop
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left h2)

private theorem map_argument {S : Type*} [CommRing S] (hom : R →+* S) :
    (argument : PowerSeries R).map hom = (argument : PowerSeries S) := by
  have hd : IsUnit (denominator : PowerSeries S) := by
    rw [isUnit_iff_constantCoeff, denominator_zero]
    exact isUnit_one
  apply hd.mul_right_cancel
  have he := congrArg (PowerSeries.map hom) (argument_mul (R := R))
  have hm : (denominator : PowerSeries R).map hom = (denominator : PowerSeries S) := by
    simp only [denominator, map_sub, map_mul, map_pow, map_X, map_one, map_ofNat]
  rw [map_mul, hm, map_pow, map_X] at he
  exact he.trans argument_mul.symm

private theorem map_equation {S : Type*} [CommRing S] (hom : R →+* S)
    {f : PowerSeries R} (hf : Equation f) : Equation (f.map hom) := by
  have he := congrArg (PowerSeries.map hom) hf
  have hm : PowerSeries.map hom (f.subst (argument : PowerSeries R)) =
      (PowerSeries.map hom f).subst (PowerSeries.map hom (argument : PowerSeries R)) :=
    map_subst (.of_constantCoeff_zero (argument_zero (R := R))) f
  rw [map_argument] at hm
  simpa only [Equation, map_pow, hm] using he

private theorem geometric_equation : Equation (geometric : PowerSeries (ZMod 3)) := by
  let f : PowerSeries (ZMod 3) := geometric
  let u : PowerSeries (ZMod 3) := argument
  let d : PowerSeries (ZMod 3) := denominator
  have hu0 : constantCoeff u = 0 := argument_zero
  have su : HasSubst u := .of_constantCoeff_zero hu0
  have h3 : (3 : PowerSeries (ZMod 3)) = 0 := by
    rw [← map_ofNat C 3, show (3 : ZMod 3) = 0 by decide, map_zero]
  have hud : u * d = X ^ 2 := argument_mul
  have hden : (1 - u) * d = (1 - X) ^ 2 := by
    dsimp only [d, denominator] at hud ⊢
    linear_combination -hud - 2 * X ^ 2 * h3
  have hgeom : f.subst u * (1 - u) = u := by
    have hone : (1 : PowerSeries (ZMod 3)).subst u = 1 := by
      simpa only [map_one] using (subst_C (a := u) (1 : ZMod 3))
    have hh := congrArg (subst u) (geometric_mul (R := ZMod 3))
    rw [subst_mul su, subst_sub su, subst_X su, hone] at hh
    exact hh
  have hdunit : IsUnit d := by
    change IsUnit (denominator : PowerSeries (ZMod 3))
    rw [isUnit_iff_constantCoeff, denominator_zero]
    exact isUnit_one
  have huunit : IsUnit (1 - u) := isUnit_iff_constantCoeff.mpr (by simp [hu0])
  change f ^ 2 = f.subst u
  apply huunit.mul_right_cancel
  apply hdunit.mul_right_cancel
  calc
    (f ^ 2 * (1 - u)) * d = f ^ 2 * ((1 - u) * d) := by ring
    _ = f ^ 2 * (1 - X) ^ 2 := by rw [hden]
    _ = (f * (1 - X)) ^ 2 := by ring
    _ = X ^ 2 := by rw [show f * (1 - X) = X from geometric_mul]
    _ = (f.subst u * (1 - u)) * d := by rw [hgeom, hud]

private theorem integral_mod_three : integralA.map (Int.castRingHom (ZMod 3)) = geometric := by
  have h0 : constantCoeff (integralA.map (Int.castRingHom (ZMod 3))) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, integral_equation.1, map_zero]
  have h1 : coeff 1 (integralA.map (Int.castRingHom (ZMod 3))) = 1 := by simp [integral_equation.2.1]
  exact equation_unique (by decide : (2 : ZMod 3) ≠ 0) h0 geometric_zero h1 geometric_one
    (map_equation _ integral_equation.2.2) geometric_equation

private theorem isGF_iff (f : PowerSeries ℚ) : IsGF f ↔
    constantCoeff f = 0 ∧ coeff 1 f = 1 ∧ Equation f := by
  have hi : invOfUnit (denominator : PowerSeries ℚ) (1 : ℚˣ) =
      (denominator : PowerSeries ℚ)⁻¹ := invOfUnit_eq' _ _ (by simpa using (denominator_zero (R := ℚ)))
  unfold IsGF Equation argument
  rw [hi]
  rfl


private theorem rational_isGF : IsGF (integralA.map (Int.castRingHom ℚ)) := by
  apply (isGF_iff _).mpr
  refine ⟨?_, ?_, map_equation _ integral_equation.2.2⟩
  · rw [← coeff_zero_eq_constantCoeff]
    simp [coeff_zero_eq_constantCoeff, integral_equation.1]
  · simp [integral_equation.2.1]

theorem result : claim := by
  refine ⟨⟨(integralA.map (Int.castRingHom ℚ)), rational_isGF⟩, ?_⟩
  intro f hf n hn
  have heq : f = (integralA.map (Int.castRingHom ℚ)) := equation_unique (by norm_num : (2 : ℚ) ≠ 0)
    hf.1 rational_isGF.1 hf.2.1 rational_isGF.2.1
    ((isGF_iff f).mp hf).2.2 ((isGF_iff _).mp rational_isGF).2.2
  refine ⟨coeff n integralA, ?_, ?_⟩
  · rw [heq]
    simp
  · apply (ZMod.intCast_eq_intCast_iff _ _ 3).mp
    have h := congrArg (coeff n) integral_mod_three
    simpa only [coeff_map, Int.coe_castRingHom, Int.cast_one, geometric_coeff n hn] using h

end D5.S1.Recurrence.Invariants.HannaGeometricSquareSubstitutionModThree
