/- GID: D5/S1/Recurrence/Invariants/HannaA378258SquareRootParity
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaA378258SquareRootParity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Integral compositional square roots prove Hanna's dyadic parity conjecture. -/

/-
result: proof_shape: content; escape_witness: none.
admission_basis: open-problem-resolution (#18825; Proved).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19870.
Direct frozen dependencies: declarations of CatalanCompositionSquareParity,
CompositionalSquareDyadicDenominators and HannaHalfIterateCubicModThree;
declaration statement identities are supplied in the handover.
Utility is none: the construction is symbolic and unbounded, with no finite certificate.
Declaration classifications (same-delivery proofs inlined):
IsGF: proof_shape: bind-only; escape_witness: none; consumers: claim, rational_series_spec, solution_unique.
claim: proof_shape: bind-only; escape_witness: none; consumers: result.
IntegralSquareRoot.residual: proof_shape: bind-only; escape_witness: none; consumers: IntegralSquareRoot.correction, IntegralSquareRoot.residual_agree, IntegralSquareRoot.residual_four, IntegralSquareRoot.correction_even, IntegralSquareRoot.extend_residual, IntegralSquareRoot.approximation_spec, IntegralSquareRoot.root_spec.
IntegralSquareRoot.correction: proof_shape: bind-only; escape_witness: none; consumers: IntegralSquareRoot.extend, IntegralSquareRoot.correction_even, IntegralSquareRoot.extend_even, IntegralSquareRoot.extend_residual.
IntegralSquareRoot.extend: proof_shape: bind-only; escape_witness: none; consumers: IntegralSquareRoot.extend_agree, IntegralSquareRoot.extend_zero, IntegralSquareRoot.extend_one, IntegralSquareRoot.extend_even, IntegralSquareRoot.extend_residual, IntegralSquareRoot.approximation.
IntegralSquareRoot.residual_agree: proof_shape: bind-only; escape_witness: none; consumers: IntegralSquareRoot.extend_residual, IntegralSquareRoot.root_spec.
IntegralSquareRoot.residual_four: proof_shape: bind-only; escape_witness: none; consumers: IntegralSquareRoot.correction_even.
IntegralSquareRoot.correction_even: proof_shape: bind-only; escape_witness: none; consumers: IntegralSquareRoot.extend_even, IntegralSquareRoot.extend_residual.
IntegralSquareRoot.extend_agree: proof_shape: bind-only; escape_witness: none; consumers: IntegralSquareRoot.extend_zero, IntegralSquareRoot.extend_one, IntegralSquareRoot.extend_residual, IntegralSquareRoot.approximation_stable.
IntegralSquareRoot.extend_zero: proof_shape: bind-only; escape_witness: none; consumers: IntegralSquareRoot.extend_residual, IntegralSquareRoot.approximation_spec.
IntegralSquareRoot.extend_one: proof_shape: bind-only; escape_witness: none; consumers: IntegralSquareRoot.extend_residual, IntegralSquareRoot.approximation_spec.
IntegralSquareRoot.extend_even: proof_shape: bind-only; escape_witness: none; consumers: IntegralSquareRoot.approximation_spec.
IntegralSquareRoot.extend_residual: proof_shape: bind-only; escape_witness: none; consumers: IntegralSquareRoot.approximation_spec.
IntegralSquareRoot.approximation: proof_shape: bind-only; escape_witness: none; consumers: IntegralSquareRoot.approximation_spec, IntegralSquareRoot.approximation_stable, IntegralSquareRoot.root, IntegralSquareRoot.root_agree, IntegralSquareRoot.root_spec.
IntegralSquareRoot.approximation_spec: proof_shape: content; escape_witness: none; consumers: IntegralSquareRoot.root_spec.
IntegralSquareRoot.approximation_stable: proof_shape: content; escape_witness: none; consumers: IntegralSquareRoot.root_agree.
IntegralSquareRoot.root: proof_shape: bind-only; escape_witness: none; consumers: IntegralSquareRoot.root_agree, IntegralSquareRoot.root_spec, squareRoot, square_root_spec.
IntegralSquareRoot.root_agree: proof_shape: content; escape_witness: none; consumers: IntegralSquareRoot.root_spec.
IntegralSquareRoot.root_spec: proof_shape: content; escape_witness: none; consumers: square_root_spec.
subst_one: proof_shape: bind-only; escape_witness: none; consumers: integral_series_spec.
map_comp: proof_shape: bind-only; escape_witness: none; consumers: rational_series_spec, integral_mod_two, rational_square_root_spec, solution_unique.
h_order: proof_shape: bind-only; escape_witness: none; consumers: square_root_spec.
squareRoot: proof_shape: bind-only; escape_witness: none; consumers: square_root_spec, square_root_unit, inverseRoot, inverse_root_spec, integral_series_spec, rational_series_spec, square_root_mod_two, rational_square_root_spec, solution_unique.
square_root_spec: proof_shape: content; escape_witness: none; consumers: square_root_unit, inverse_root_spec, integral_series_spec, square_root_mod_two, integral_mod_two, rational_square_root_spec.
square_root_unit: proof_shape: bind-only; escape_witness: none; consumers: inverseRoot, inverse_root_spec.
inverseRoot: proof_shape: bind-only; escape_witness: none; consumers: integralSeries, inverse_root_spec, integral_series_spec, solution_unique.
integralSeries: proof_shape: bind-only; escape_witness: none; consumers: integral_series_spec, rationalSeries, rational_series_spec, integral_mod_two, result.
inverse_root_spec: proof_shape: bind-only; escape_witness: none; consumers: integral_series_spec, solution_unique.
integral_series_spec: proof_shape: content; escape_witness: none; consumers: rational_series_spec, integral_mod_two.
rationalSeries: proof_shape: bind-only; escape_witness: none; consumers: rational_series_spec, solution_unique, result.
rational_series_spec: proof_shape: content; escape_witness: none; consumers: result.
square_root_mod_two: proof_shape: content; escape_witness: none; consumers: integral_mod_two.
integral_mod_two: proof_shape: content; escape_witness: none; consumers: result.
rational_catalan_spec: proof_shape: bind-only; escape_witness: none; consumers: solution_unique.
rational_square_root_spec: proof_shape: content; escape_witness: none; consumers: solution_unique.
solution_unique: proof_shape: content; escape_witness: none; consumers: result.
result: proof_shape: content; escape_witness: none; consumers: settling result.
The normalized source equations are unchanged. Coefficient agreement and square-root
uniqueness use their existing owners. The Catalan identification uses Mathlib's
uniqueness of the compositional inverse of X-X^2.
-/

import D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators
import D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity
import D5.S1.Recurrence.Invariants.HannaHalfIterateCubicModThree

/-! # Integral compositional square roots and the parity of OEIS A378258 -/

set_option autoImplicit false

namespace D5.S1.Recurrence.Invariants.HannaA378258SquareRootParity

open PowerSeries
open D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators (Agree)

/-- OEIS A378258: "G.f. satisfies A(x) = B(x) + 5*A(x)^2 where B(A(x) - A(x)^2) = x.", offset 1,
  a(1) = 1. -/
def IsGF (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 0 ∧ coeff 1 A = 1 ∧
    ∃ B : PowerSeries ℚ, A = B + 5 * A ^ 2 ∧ PowerSeries.subst (A - A ^ 2) B = X

/-- OEIS A378258 (P. D. Hanna), conjecture: "a(n) is odd iff n is a power of 2." -/
def claim : Prop :=
  (∃ A, IsGF A) ∧
    ∀ A, IsGF A → ∀ n : ℕ, 1 ≤ n → ∃ m : ℤ, coeff n A = m ∧ (Odd m ↔ ∃ k : ℕ, n = 2 ^ k)

end D5.S1.Recurrence.Invariants.HannaA378258SquareRootParity

namespace D5.S1.Recurrence.Invariants.HannaA378258SquareRootParity.IntegralSquareRoot
open PowerSeries
open D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators (Agree)

private noncomputable def residual (H p : PowerSeries ℤ) : PowerSeries ℤ :=
  p.subst p - X - 4 * H

private noncomputable def correction (H p : PowerSeries ℤ) (n : ℕ) : ℤ :=
  -(coeff n (residual H p) / 2)

private noncomputable def extend (H p : PowerSeries ℤ) (n : ℕ) : PowerSeries ℤ :=
  p + C (correction H p n) * X ^ n

private theorem residual_agree {d : ℕ} (H : PowerSeries ℤ) {p q : PowerSeries ℤ}
    (hp : constantCoeff p = 0) (hq : constantCoeff q = 0) (h : Agree d p q) :
    Agree d (residual H p) (residual H q) := by
  intro n hn
  have hs := D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.agree_subst hp hq h h
    n hn
  simp only [residual, map_sub, hs]

private theorem residual_four (H : PowerSeries ℤ) {p : PowerSeries ℤ}
    (hp : constantCoeff p = 0) (h : C (2 : ℤ) ∣ p - X) :
    C (4 : ℤ) ∣ residual H p := by
  have hold := D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.residual_four hp h
  change C (4 : ℤ) ∣ p.subst p - X - 4 * X * p at hold
  have hnew : C (4 : ℤ) ∣ 4 * (X * p - H) := dvd_mul_right (C 4) (X * p - H)
  convert dvd_add hold hnew using 1
  dsimp [residual]
  ring

private theorem correction_even (H : PowerSeries ℤ) {p : PowerSeries ℤ}
    (hp : constantCoeff p = 0) (h : C (2 : ℤ) ∣ p - X) (n : ℕ) :
    2 ∣ correction H p n ∧ 2 * correction H p n = -coeff n (residual H p) := by
  obtain ⟨q, hq⟩ := (D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.C_dvd_iff_coeff
      _ _).mp
    (residual_four H hp h) n
  dsimp [correction]
  rw [hq]
  constructor
  · refine ⟨-q, ?_⟩
    omega
  · omega

private theorem extend_agree (H p : PowerSeries ℤ) (n : ℕ) : Agree n (extend H p n) p := by
  intro k hk
  simp only [extend, map_add, coeff_C_mul, coeff_X_pow, ite_eq_right (ne_of_lt hk),
    mul_zero, add_zero]

private theorem extend_zero (H : PowerSeries ℤ) {p : PowerSeries ℤ} (hp : constantCoeff p = 0)
    {n : ℕ} (hn : 2 ≤ n) : constantCoeff (extend H p n) = 0 := by
  simpa only [coeff_zero_eq_constantCoeff, hp] using extend_agree H p n 0 (by omega)

private theorem extend_one (H : PowerSeries ℤ) {p : PowerSeries ℤ} (hp1 : coeff 1 p = 1)
    {n : ℕ} (hn : 2 ≤ n) : coeff 1 (extend H p n) = 1 := by
  exact (extend_agree H p n 1 hn).trans hp1

private theorem extend_even (H : PowerSeries ℤ) {p : PowerSeries ℤ} (hp : constantCoeff p = 0)
    (h : C (2 : ℤ) ∣ p - X) (n : ℕ) : C (2 : ℤ) ∣ extend H p n - X := by
  have hc := (correction_even H hp h n).1
  have hd : C (2 : ℤ) ∣ C (correction H p n) * X ^ n :=
    dvd_mul_of_dvd_left (map_dvd C hc) _
  convert dvd_add h hd using 1
  dsimp [extend]
  ring

private theorem extend_residual (H : PowerSeries ℤ) {p : PowerSeries ℤ} (hp : constantCoeff p = 0)
    (hp1 : coeff 1 p = 1) (h : C (2 : ℤ) ∣ p - X) {n : ℕ} (hn : 2 ≤ n)
    (hr : Agree n (residual H p) 0) : Agree (n+1) (residual H (extend H p n)) 0 := by
  have he0 := extend_zero H hp hn
  have he1 := extend_one H hp1 hn
  intro k hk
  by_cases hkn : k < n
  · exact (residual_agree H he0 hp (extend_agree H p n) k hkn).trans (hr k hkn)
  · have hkn : k = n := Nat.eq_of_lt_succ_of_not_lt hk hkn
    subst k
    have ht := D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.composition_top
      he0 hp he1 hp1 (extend_agree H p n)
    have hc := (correction_even H hp h n).2
    have he : coeff n (extend H p n) = coeff n p + correction H p n := by
      simp only [extend, map_add, coeff_C_mul, coeff_X_pow_self, mul_one]
    simp only [residual, map_sub] at hc ⊢
    simp only [map_zero]
    linear_combination ht + 2 * he + hc

private noncomputable def approximation (H : PowerSeries ℤ) : ℕ → PowerSeries ℤ
  | 0 => X
  | n+1 => extend H (approximation H n) (n+2)

private theorem approximation_spec (H : PowerSeries ℤ) (hH : X ^ 2 ∣ H) (n : ℕ) :
    constantCoeff (approximation H n) = 0 ∧ coeff 1 (approximation H n) = 1 ∧
    C (2 : ℤ) ∣ approximation H n - X ∧ Agree (n+2) (residual H (approximation H n)) 0 := by
  induction n with
  | zero =>
    refine ⟨by simp [approximation], by simp [approximation], by simp [approximation], ?_⟩
    intro k hk
    have he : residual H (X : PowerSeries ℤ) = -(4 * H) := by simp [residual]
    change coeff k (residual H (X : PowerSeries ℤ)) = coeff k 0
    rw [he]
    have hfour : (4 : PowerSeries ℤ) = C 4 := (map_ofNat _ 4).symm
    rw [hfour]
    simp only [map_neg, coeff_C_mul, X_pow_dvd_iff.mp hH k hk, mul_zero, neg_zero, map_zero]
  | succ n ih =>
    exact ⟨extend_zero H ih.1 (by omega), extend_one H ih.2.1 (by omega),
      extend_even H ih.1 ih.2.2.1 _, extend_residual H ih.1 ih.2.1 ih.2.2.1 (by omega) ih.2.2.2⟩

private theorem approximation_stable (H : PowerSeries ℤ) {n m : ℕ} (h : n ≤ m) :
    Agree (n+2) (approximation H m) (approximation H n) := by
  induction m, h using Nat.le_induction with
  | base => intro k hk; rfl
  | succ m h ih =>
    intro k hk
    exact (extend_agree H (approximation H m) (m+2) k (by omega)).trans (ih k hk)

private noncomputable def root (H : PowerSeries ℤ) : PowerSeries ℤ :=
  mk (fun n => coeff n (approximation H n))

private theorem root_agree (H : PowerSeries ℤ) (n : ℕ) : Agree (n+2) (root H) (approximation H n)
  := by
  intro k hk
  simp only [root, coeff_mk]
  by_cases hkn : k ≤ n
  · exact (approximation_stable H hkn k (by omega)).symm
  · exact approximation_stable H (by omega : n ≤ k) k hk

private theorem root_spec (H : PowerSeries ℤ) (hH : X ^ 2 ∣ H) :
    constantCoeff (root H) = 0 ∧ coeff 1 (root H) = 1 ∧
    C (2 : ℤ) ∣ root H - X ∧ (root H).subst (root H) = X + 4 * H := by
  have hz : constantCoeff (root H) = 0 := by
    simpa only [coeff_zero_eq_constantCoeff] using
      (root_agree H 0 0 (by omega)).trans (by simp [approximation])
  have ho : coeff 1 (root H) = 1 :=
    (root_agree H 0 1 (by omega)).trans (by simp [approximation])
  refine ⟨hz, ho, ?_, ?_⟩
  · apply (D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.C_dvd_iff_coeff _ _).mpr
    intro n
    rw [map_sub, root_agree H n n (by omega)]
    simpa only [map_sub] using
      (D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.C_dvd_iff_coeff
      _ _).mp
      (approximation_spec H hH n).2.2.1 n
  · have hr : residual H (root H) = 0 := by
      ext n
      exact (residual_agree H hz (approximation_spec H hH n).1 (root_agree H n)
        n (by omega)).trans ((approximation_spec H hH n).2.2.2 n (by omega))
    dsimp [residual] at hr
    linear_combination hr

end D5.S1.Recurrence.Invariants.HannaA378258SquareRootParity.IntegralSquareRoot
namespace D5.S1.Recurrence.Invariants.HannaA378258SquareRootParity
open PowerSeries
open D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity
  (catalan_equation binary_catalan)
local notation "K" => D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanSeries

private theorem subst_one {R : Type*} [CommRing R] (f u : PowerSeries R) (hu : constantCoeff u =
  0) :
    coeff 1 (f.subst u) = coeff 1 f * coeff 1 u := by
  rw [D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.coeff_subst_sum hu]
  simp [Finset.sum_range_succ]

private theorem map_comp {R S : Type*} [CommRing R] [CommRing S]
    (f u : PowerSeries R) (hu : constantCoeff u = 0) (hom : R →+* S) :
    PowerSeries.map hom (PowerSeries.subst u f) =
      PowerSeries.subst (PowerSeries.map hom u) (PowerSeries.map hom f) := by
  exact map_subst (.of_constantCoeff_zero hu) f

private theorem h_order : (X : PowerSeries ℤ) ^ 2 ∣ X - K := by
  have h := dvd_neg.mpr (pow_dvd_pow_of_dvd (X_dvd_iff.mpr catalan_equation.1) 2)
  convert h using 1
  linear_combination -catalan_equation.2.2

private noncomputable def squareRoot : PowerSeries ℤ := IntegralSquareRoot.root (X - K)

private theorem square_root_spec :
    constantCoeff squareRoot = 0 ∧ coeff 1 squareRoot = 1 ∧
    C (2 : ℤ) ∣ squareRoot - X ∧ squareRoot.subst squareRoot = 5 * X - 4 * K := by
  have h := IntegralSquareRoot.root_spec (X - K) h_order
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  change (IntegralSquareRoot.root (X - K)).subst (IntegralSquareRoot.root (X - K)) = _
  rw [h.2.2.2]
  ring

private theorem square_root_unit : IsUnit (coeff 1 squareRoot) := by
  exact square_root_spec.2.1 ▸ isUnit_one

private noncomputable def inverseRoot : PowerSeries ℤ := squareRoot.substInvOfIsUnit
  square_root_unit
private noncomputable def integralSeries : PowerSeries ℤ := (K).subst inverseRoot

private theorem inverse_root_spec :
    constantCoeff inverseRoot = 0 ∧ coeff 1 inverseRoot = 1 ∧
    squareRoot.subst inverseRoot = X ∧ inverseRoot.subst squareRoot = X := by
  have hunit : square_root_unit.unit = 1 := by
    apply Units.ext
    simpa using square_root_spec.2.1
  refine ⟨constantCoeff_substInvOfIsUnit _ _, ?_,
    subst_substInvOfIsUnit_right _ square_root_spec.1 _,
    subst_substInvOfIsUnit_left _ square_root_spec.1 _⟩
  rw [inverseRoot, coeff_one_substInvOfIsUnit, hunit]
  rfl

private theorem integral_series_spec :
    constantCoeff integralSeries = 0 ∧ coeff 1 integralSeries = 1 ∧
    integralSeries = squareRoot + 5 * integralSeries ^ 2 ∧
    squareRoot.subst (integralSeries - integralSeries ^ 2) = X ∧
    integralSeries.subst squareRoot = K := by
  have hz := inverse_root_spec.1
  have hs : HasSubst inverseRoot := .of_constantCoeff_zero hz
  have hb : HasSubst squareRoot := .of_constantCoeff_zero square_root_spec.1
  have hc : K - K ^ 2 = X := by linear_combination catalan_equation.2.2
  have hc5 : K - 5 * K ^ 2 = squareRoot.subst squareRoot := by
    rw [square_root_spec.2.2.2]
    linear_combination 5 * catalan_equation.2.2
  have hsq : integralSeries - integralSeries ^ 2 = inverseRoot := by
    have he := congrArg (substAlgHom hs) hc
    simp only [map_sub, map_pow, coe_substAlgHom, subst_X hs] at he
    exact he
  have hsq5 : integralSeries - 5 * integralSeries ^ 2 = squareRoot := by
    have he := congrArg (substAlgHom hs) hc5
    simp only [map_sub, map_mul, map_pow, map_ofNat, coe_substAlgHom] at he
    rw [subst_comp_subst_apply hb hs, inverse_root_spec.2.2.1, X_subst] at he
    exact he
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (constantCoeff_subst_eq_zero hz _ catalan_equation.1)
  · rw [integralSeries, subst_one _ _ hz, catalan_equation.2.1, inverse_root_spec.2.1, mul_one]
  · linear_combination hsq5
  · rw [hsq, inverse_root_spec.2.2.1]
  · rw [integralSeries, subst_comp_subst_apply hs hb, inverse_root_spec.2.2.2, X_subst]

private noncomputable def rationalSeries : PowerSeries ℚ := integralSeries.map (Int.castRingHom ℚ)

private theorem rational_series_spec : IsGF rationalSeries := by
  refine ⟨?_, ?_, squareRoot.map (Int.castRingHom ℚ), ?_, ?_⟩
  · rw [rationalSeries, ← coeff_zero_eq_constantCoeff, coeff_map,
      coeff_zero_eq_constantCoeff, integral_series_spec.1, map_zero]
  · simp [rationalSeries, coeff_map, integral_series_spec.2.1]
  · simpa [rationalSeries, map_ofNat] using congrArg (PowerSeries.map (Int.castRingHom ℚ))
      integral_series_spec.2.2.1
  · have hz : constantCoeff (integralSeries - integralSeries ^ 2) = 0 := by
      simp [integral_series_spec.1]
    have he := congrArg (PowerSeries.map (Int.castRingHom ℚ)) integral_series_spec.2.2.2.1
    rw [map_comp _ _ hz] at he
    simpa [rationalSeries] using he

private theorem square_root_mod_two : squareRoot.map (Int.castRingHom (ZMod 2)) = X := by
  obtain ⟨d, hd⟩ := square_root_spec.2.2.1
  have he := congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) hd
  have h2 : ((Int.castRingHom (ZMod 2)) 2) = 0 := (ZMod.val_eq_zero _).mp rfl
  simpa only [map_sub, map_X, map_mul, map_C, h2, map_zero, zero_mul, sub_eq_zero] using he

private theorem integral_mod_two : integralSeries.map (Int.castRingHom (ZMod 2)) =
    (K).map (Int.castRingHom (ZMod 2)) := by
  have he := congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) integral_series_spec.2.2.2.2
  rw [map_comp _ _ square_root_spec.1, square_root_mod_two, X_subst] at he
  exact he

end D5.S1.Recurrence.Invariants.HannaA378258SquareRootParity
namespace D5.S1.Recurrence.Invariants.HannaA378258SquareRootParity
open PowerSeries
local notation "K" => D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanSeries
local notation "KQ" => PowerSeries.map (Int.castRingHom ℚ)
  D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanSeries

private theorem rational_catalan_spec : constantCoeff KQ = 0 ∧ coeff 1 KQ = 1 ∧ KQ = X + KQ ^ 2
  := by
  have h := D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalan_equation
  refine ⟨?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, h.1, map_zero]
  · simp [coeff_map, h.2.1]
  · simpa using congrArg (PowerSeries.map (Int.castRingHom ℚ)) h.2.2

private theorem rational_square_root_spec :
    constantCoeff (squareRoot.map (Int.castRingHom ℚ)) = 0 ∧
    coeff 1 (squareRoot.map (Int.castRingHom ℚ)) = 1 ∧
    (squareRoot.map (Int.castRingHom ℚ)).subst (squareRoot.map (Int.castRingHom ℚ)) =
      5 * X - 4 * KQ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      square_root_spec.1, map_zero]
  · simp [coeff_map, square_root_spec.2.1]
  · have he := congrArg (PowerSeries.map (Int.castRingHom ℚ)) square_root_spec.2.2.2
    rw [map_comp _ _ square_root_spec.1] at he
    simpa [map_ofNat] using he

private theorem solution_unique (A : PowerSeries ℚ) (hA : IsGF A) : A = rationalSeries := by
  rcases hA with ⟨ha0, ha1, B, hab, hbu⟩
  have hb0 : constantCoeff B = 0 := by
    have hc := congrArg constantCoeff hab
    simpa [ha0] using hc.symm
  have hb1 : coeff 1 B = 1 := by
    have hc := congrArg (coeff 1) hab
    simpa [coeff_one_mul, coeff_one_pow, ha0, ha1] using hc.symm
  have hb : HasSubst B := .of_constantCoeff_zero hb0
  have hu0 : constantCoeff (A - A ^ 2) = 0 := by simp [ha0]
  have hu : HasSubst (A - A ^ 2) := .of_constantCoeff_zero hu0
  have hub : (A - A ^ 2).subst B = X :=
    subst_eq_X_of_subst_eq_X B hb0 (hb1 ▸ isUnit_one) hu hbu
  rw [subst_sub hb, subst_pow hb] at hub
  have hak : A.subst B = KQ := by
    have hq : A.subst B = X + (A.subst B) ^ 2 := (add_eq_of_eq_sub hub.symm).symm
    have hf0 := constantCoeff_subst_eq_zero hb0 A ha0
    have hpf : (X - X ^ 2 : PowerSeries ℚ).subst (A.subst B) = X := by
      rw [subst_sub (.of_constantCoeff_zero hf0), subst_X (.of_constantCoeff_zero hf0),
        subst_pow (.of_constantCoeff_zero hf0), subst_X (.of_constantCoeff_zero hf0)]
      exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hq)
    have hpg : (X - X ^ 2 : PowerSeries ℚ).subst KQ = X := by
      rw [subst_sub (.of_constantCoeff_zero rational_catalan_spec.1),
        subst_X (.of_constantCoeff_zero rational_catalan_spec.1),
        subst_pow (.of_constantCoeff_zero rational_catalan_spec.1),
        subst_X (.of_constantCoeff_zero rational_catalan_spec.1)]
      exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using rational_catalan_spec.2.2)
    have hp : constantCoeff (X - X ^ 2 : PowerSeries ℚ) = 0 := by simp
    have hu : IsUnit (coeff 1 (X - X ^ 2 : PowerSeries ℚ)) := by
      simp [coeff_X]
    exact (eq_substInvOfIsUnit_of_subst_eq_X _ hp hu (.of_constantCoeff_zero hf0) hpf).trans
      (eq_substInvOfIsUnit_of_subst_eq_X _ hp hu
        (.of_constantCoeff_zero rational_catalan_spec.1) hpg).symm
  have hbb : B.subst B = 5 * X - 4 * KQ := by
    have he := congrArg (substAlgHom hb) hab
    simp only [map_add, map_mul, map_pow, map_ofNat, coe_substAlgHom, hak] at he
    linear_combination -he + 5 * rational_catalan_spec.2.2
  have hbeq : B = squareRoot.map (Int.castRingHom ℚ) :=
    D5.S1.Recurrence.Invariants.HannaHalfIterateCubicModThree.half_unique
      (by norm_num : (2 : ℚ) ≠ 0) hb0 rational_square_root_spec.1 hb1
      rational_square_root_spec.2.1 hbb rational_square_root_spec.2.2
  let J := inverseRoot.map (Int.castRingHom ℚ)
  have hj0 : constantCoeff J = 0 := by
    dsimp [J]
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      inverse_root_spec.1, map_zero]
  have hj : HasSubst J := .of_constantCoeff_zero hj0
  have hbj : B.subst J = X := by
    have he := congrArg (PowerSeries.map (Int.castRingHom ℚ)) inverse_root_spec.2.2.1
    rw [map_comp _ _ inverse_root_spec.1] at he
    simpa [hbeq, J] using he
  have he := congrArg (subst J) hak
  rw [subst_comp_subst_apply hb hj, hbj, X_subst] at he
  rw [he]
  exact (map_comp (K) inverseRoot inverse_root_spec.1 (Int.castRingHom ℚ)).symm

theorem result : claim := by
  refine ⟨⟨rationalSeries, rational_series_spec⟩, ?_⟩
  intro A hA n hn
  rw [solution_unique A hA]
  refine ⟨coeff n integralSeries, ?_, ?_⟩
  · simp [rationalSeries, coeff_map]
  · rw [← ZMod.intCast_eq_one_iff_odd]
    have hc := congrArg (coeff n) integral_mod_two
    rw [coeff_map] at hc
    change ((coeff n integralSeries : ℤ) : ZMod 2) = _ at hc
    rw [hc]
    exact D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.binary_catalan n

end D5.S1.Recurrence.Invariants.HannaA378258SquareRootParity
