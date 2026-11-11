/- GID: D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDerivationRigidity
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDerivationRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Derivation.Basic]
   utility: none
   digest: Derivations classify removable highest jets over arbitrary fields. -/
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
import Mathlib.RingTheory.Derivation.Basic

/-! Derivation rigidity for the actual highest-jet original-group actions. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity

open Polynomial Finset Module OddPrimeJetDeformation
open scoped BigOperators

universe uK
variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable {K : Type uK} [Field K] [Algebra (ZMod p) K]
local notation "F" => ZMod p
local notation "V" => Polynomial.degreeLT K p
local notation "E" => Multiplicative K
local notation "D" => derivativeEnd (p := p) (K := K)

theorem leibniz_of_commutator (q Q : K →ₗ[F] K)
    (h : ∀ a s : K, a * Q s - Q (a*s) = q a * s) (a b : K) :
    q (a*b) = a * q b + b * q a := by
  have hb := h b 1
  have hab := h (a*b) 1
  have hs := h a b
  simp only [mul_one] at hb hab
  linear_combination -hab + hs + a * hb

private theorem necessary (q : K →ₗ[F] K) (hq1 : q 1 = 0)
    (φ : E ≃* E) (P : V ≃ₗ[F] V)
    (hP : ∀ (g : E) (v : V), P (originalRepresentation (p := p) q g v) =
      ordinaryRepresentation (φ g) (P v)) :
    ∀ a b : K, q (a*b) = a * q b + b * q a := by
  let c : K := automorphismLinear (p := p) φ 1
  have hc : c ≠ 0 := by
    intro hz
    have hφ : φ (Multiplicative.ofAdd (1 : K)) = 1 := congrArg Multiplicative.ofAdd hz
    have hx := φ.injective (hφ.trans φ.map_one.symm)
    exact one_ne_zero (congrArg Multiplicative.toAdd hx)
  let S : V ≃ₗ[K] V := diagonalScale c hc
  let P' : V ≃ₗ[F] V := P.trans (S.restrictScalars F)
  have hnorm (x : K) (v : V) :
      P' (jetOperator q x v) = (automorphismLinear (p := p) φ x / c) • D (P' v) := by
    change S (P (jetOperator q x v)) = _
    rw [log_intertwining q φ P hP, S.map_smul, diagonalScale_derivative]
    simp only [P', LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
      smul_smul, div_eq_mul_inv, S]
  have hD : ∀ v : V, P' (D v) = D (P' v) := by
    intro v
    have h := hnorm 1 v
    simpa only [jetOperator, hq1, zero_smul, add_zero, one_smul,
      ← show c = automorphismLinear (p := p) φ 1 from rfl, div_self hc, one_smul] using h
  apply leibniz_of_commutator q (constantCommutator P' hD)
  intro a s
  exact structural_commutator P' hD a (q a)
    (automorphismLinear (p := p) φ a / c) (hnorm a) s

private def coefficientDerivation (δ : Derivation F K K) : Module.End F V :=
  let e := (degreeLTEquiv K p).restrictScalars F
  e.symm.toLinearMap.comp ((δ.toLinearMap.compLeft (Fin p)).comp e.toLinearMap)

private theorem coefficientDerivation_coeff (δ : Derivation F K K) (v : V) (n : ℕ) :
    (coefficientDerivation δ v : K[X]).coeff n = δ ((v : K[X]).coeff n) := by
  by_cases hn : n < p
  · change (degreeLTEquiv K p) (coefficientDerivation δ v) ⟨n,hn⟩ = _
    exact congrFun ((degreeLTEquiv K p).apply_symm_apply
      (fun i => δ ((v : K[X]).coeff i))) ⟨n,hn⟩
  · have hz (w : V) : (w : K[X]).coeff n = 0 :=
      coeff_eq_zero_of_degree_lt ((mem_degreeLT.mp w.property).trans_le
        (by exact_mod_cast (by omega : p ≤ n)))
    rw [hz, hz, map_zero]

private theorem coefficientDerivation_smul (δ : Derivation F K K) (a : K) (v : V) :
    coefficientDerivation δ (a • v) =
      a • coefficientDerivation δ v + δ a • v := by
  apply Subtype.ext
  apply Polynomial.ext
  intro n
  simp only [coefficientDerivation_coeff, Submodule.coe_smul, coeff_smul,
    Submodule.coe_add, coeff_add, smul_eq_mul, Derivation.leibniz]
  ring

private theorem coefficientDerivation_derivative (δ : Derivation F K K) (v : V) :
    coefficientDerivation δ (D v) = D (coefficientDerivation δ v) := by
  apply Subtype.ext
  apply Polynomial.ext
  intro n
  change (coefficientDerivation δ (D v) : K[X]).coeff n =
    (derivative (coefficientDerivation δ v : K[X])).coeff n
  rw [coefficientDerivation_coeff, coeff_derivative, coefficientDerivation_coeff]
  change δ ((derivative (v : K[X])).coeff n) = _
  rw [coeff_derivative]
  simp only [← Nat.cast_add_one, Derivation.leibniz, Derivation.map_natCast,
    smul_eq_mul, mul_zero, zero_add]
  ring

private theorem restricted_derivative_pow (n : ℕ) (v : V) :
    (((D).restrictScalars F)^n) v = (D^n) v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
    rfl

private def gaugeNilpotent (δ : Derivation F K K) : Module.End F V :=
  coefficientDerivation δ * ((D).restrictScalars F)^(p-2)

private theorem gaugeNilpotent_apply (δ : Derivation F K K) (v : V) :
    gaugeNilpotent δ v = coefficientDerivation δ ((D^(p-2)) v) := by
  simp only [gaugeNilpotent, Module.End.mul_apply, restricted_derivative_pow]

private theorem gaugeNilpotent_cube (δ : Derivation F K K) :
    (gaugeNilpotent δ)^3 = 0 := by
  have hp : 2 < p := Fact.out
  let d := (D).restrictScalars F
  have hd : d^p = 0 := by
    apply LinearMap.ext
    intro v
    change (((D).restrictScalars F)^p) v = 0
    rw [restricted_derivative_pow, derivative_pow_prime, LinearMap.zero_apply]
  have hc : Commute (coefficientDerivation δ) d := by
    apply LinearMap.ext
    exact coefficientDerivation_derivative δ
  rw [gaugeNilpotent, (hc.pow_right (p-2)).mul_pow, ← pow_mul,
    pow_eq_zero_of_le (by omega : p ≤ (p-2)*3) hd, mul_zero]

private theorem gaugeNilpotent_top (δ : Derivation F K K) (a : K) (v : V) :
    gaugeNilpotent δ (a • (D^(p-1)) v) = 0 := by
  have hp : 2 < p := Fact.out
  rw [gaugeNilpotent_apply, map_smul, ← Module.End.mul_apply, ← pow_add,
    pow_eq_zero_of_le (by omega : p ≤ (p-2)+(p-1)) derivative_pow_prime,
    LinearMap.zero_apply, smul_zero, map_zero]

private theorem gaugeNilpotent_commutator (δ : Derivation F K K) (a : K) (v : V) :
    gaugeNilpotent δ (a • D v) =
      a • D (gaugeNilpotent δ v) + δ a • (D^(p-1)) v := by
  have hp : 2 < p := Fact.out
  rw [gaugeNilpotent_apply, map_smul, coefficientDerivation_smul,
    gaugeNilpotent_apply, ← coefficientDerivation_derivative,
    ← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_succ, ← pow_succ',
    show p-2+1=p-1 by omega]

private theorem cubic_geometric_inverse {R : Type*} [Ring R] (N : R) (hN : N^3 = 0) :
    (1 + N + N^2) * (1-N) = 1 ∧ (1-N) * (1 + N + N^2) = 1 := by
  constructor
  · calc
      _ = 1 - N^3 := by noncomm_ring
      _ = 1 := by rw [hN, sub_zero]
  · calc
      _ = 1 - N^3 := by noncomm_ring
      _ = 1 := by rw [hN, sub_zero]

def gauge (δ : Derivation F K K) : V ≃ₗ[F] V := by
  let N := gaugeNilpotent δ
  have h := cubic_geometric_inverse N (gaugeNilpotent_cube δ)
  exact LinearEquiv.ofLinearMap (f := 1-N) (g := 1+N+N^2) h.2 h.1

private theorem gauge_operator (δ : Derivation F K K) (a : K) (v : V) :
    gauge δ (jetOperator δ.toLinearMap a v) = a • D (gauge δ v) := by
  change (a • D v + δ a • (D^(p-1)) v) -
    gaugeNilpotent δ (a • D v + δ a • (D^(p-1)) v) =
    a • D (v - gaugeNilpotent δ v)
  rw [map_add, gaugeNilpotent_top, add_zero, gaugeNilpotent_commutator,
    map_sub, smul_sub]
  abel

theorem finiteExp_intertwining (P : V →ₗ[F] V)
    (A B : Module.End K V) (h : ∀ v, P (A v) = B (P v)) (v : V) :
    P (finiteExp A v) = finiteExp B (P v) := by
  have hpow (n : ℕ) (w : V) : P ((A^n) w) = (B^n) (P w) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h, ih]
  have hs (n : ℕ) (w : V) : P ((n.factorial : K)⁻¹ • w) =
      (n.factorial : K)⁻¹ • P w := by
    have he : (n.factorial : K)⁻¹ = algebraMap F K ((n.factorial : F)⁻¹) := by simp
    rw [he, algebraMap_smul, algebraMap_smul, map_smul]
  simp only [finiteExp, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, hs, hpow]


private theorem derivative_pow_gaugeNilpotent (δ : Derivation F K K) (v : V) :
    (D^(p-1)) (gaugeNilpotent δ v) = 0 := by
  have hp : 2 < p := Fact.out
  have hpow (n : ℕ) (w : V) : coefficientDerivation δ ((D^n) w) =
      (D^n) (coefficientDerivation δ w) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply,
        coefficientDerivation_derivative, ih]
  rw [gaugeNilpotent_apply, ← hpow, ← Module.End.mul_apply, ← pow_add,
    pow_eq_zero_of_le (by omega : p ≤ (p-1)+(p-2)) derivative_pow_prime,
    LinearMap.zero_apply, map_zero]

/-- The derivation gauge shifts every highest jet by the original derivation. -/
theorem gauge_pair_operator (δ : Derivation F K K) (q : K →ₗ[F] K) (a : K) (v : V) :
    gauge δ (jetOperator q a v) =
      jetOperator (q-δ.toLinearMap) a (gauge δ v) := by
  change (a • D v + q a • (D^(p-1)) v) -
    gaugeNilpotent δ (a • D v + q a • (D^(p-1)) v) =
    a • D (v - gaugeNilpotent δ v) + (q a-δ a) • (D^(p-1)) (v-gaugeNilpotent δ v)
  rw [map_add, gaugeNilpotent_top, add_zero, gaugeNilpotent_commutator,
    map_sub, map_sub, derivative_pow_gaugeNilpotent, sub_zero, smul_sub, sub_smul]
  abel

private theorem sufficient (δ : Derivation F K K) :
    ∃ (φ : E ≃* E) (P : V ≃ₗ[F] V),
      ∀ (g : E) (v : V), P (originalRepresentation (p := p) δ.toLinearMap g v) =
        ordinaryRepresentation (φ g) (P v) := by
  refine ⟨MulEquiv.refl E, gauge δ, ?_⟩
  intro g v
  change gauge δ (finiteExp (jetOperator δ.toLinearMap (Multiplicative.toAdd g)) v) =
    finiteExp (jetOperator (0 : K →ₗ[F] K) (Multiplicative.toAdd g)) (gauge δ v)
  apply finiteExp_intertwining (gauge δ).toLinearMap
  intro w
  change gauge δ (jetOperator δ.toLinearMap (Multiplicative.toAdd g) w) =
    (jetOperator (0 : K →ₗ[F] K) (Multiplicative.toAdd g)) (gauge δ w)
  simpa only [jetOperator, LinearMap.zero_apply, zero_smul, add_zero,
    LinearMap.smul_apply] using gauge_operator δ (Multiplicative.toAdd g) w

/-- An arbitrary automorphism of the original parameter group and an arbitrary
prime-field-linear intertwiner remove the highest jet exactly for derivations.
No finiteness or finite-dimensionality of the field extension is assumed. -/
theorem intertwining_iff_derivation (q : K →ₗ[F] K) (hq1 : q 1 = 0) :
    (∃ (φ : E ≃* E) (P : V ≃ₗ[F] V),
      ∀ (g : E) (v : V), P (originalRepresentation (p := p) q g v) =
        ordinaryRepresentation (φ g) (P v)) ↔
    ∃ δ : Derivation F K K, δ.toLinearMap = q := by
  constructor
  · rintro ⟨φ,P,hP⟩
    refine ⟨{ q with map_one_eq_zero' := hq1, leibniz' := ?_ }, rfl⟩
    intro a b
    exact necessary q hq1 φ P hP a b
  · rintro ⟨δ,rfl⟩
    exact sufficient δ

end D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity
