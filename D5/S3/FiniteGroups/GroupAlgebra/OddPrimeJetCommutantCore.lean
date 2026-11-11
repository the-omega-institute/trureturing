/- GID: D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetCommutantCore
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/OddPrimeJetCommutantCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Nilpotent.Basic]
   utility: none
   digest: Generated-action bridge, unique degree coordinates and units of the actual Fp-linear commutant. -/
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Normal form and units of the original odd-prime jet commutant

The original polynomial representation is retained on `Polynomial.degreeLT K p`.
Only prime-field linearity is imposed on its endomorphisms. The lower blocks
are scalars and the highest block is an arbitrary prime-field-linear map.

The divided-monomial centralizer computation is classical. The original-action
logarithm and polynomial suppliers are reused from `OddPrimeJetDeformation`;
nilpotent-unit calculus is reused from pinned Mathlib. No novelty is asserted.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutant

open Polynomial Finset Module OddPrimeJetDeformation
open scoped BigOperators

universe uK
variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable {K : Type uK} [Field K] [Algebra (ZMod p) K]

local notation "F" => ZMod p
local notation "V" => Polynomial.degreeLT K p
local notation "E" => Multiplicative K
local notation "D" => derivativeEnd (p := p) (K := K)

def commutesOriginal (q : K →ₗ[F] K) (X : V →ₗ[F] V) : Prop :=
  ∀ (g : E) (v : V),
    X ((originalRepresentation (p := p) q) g v) =
      (originalRepresentation (p := p) q) g (X v)

def commutesJet (q : K →ₗ[F] K) (X : V →ₗ[F] V) : Prop :=
  ∀ (a : K) (v : V), X (jetOperator q a v) = jetOperator q a (X v)

private theorem commutesOriginal_jet (q : K →ₗ[F] K) (X : V →ₗ[F] V)
    (hX : commutesOriginal (p := p) (K := K) q X) :
    commutesJet (p := p) (K := K) q X := by
  intro a v
  have h := congrArg X (polynomial_log_action (p := p) (K := K) q a v)
  rw [map_neg, map_sum] at h
  simp only [map_smul] at h
  change ∀ (g : E) (w : V),
    X ((originalRepresentation (p := p) q) g w) =
      (originalRepresentation (p := p) q) g (X w) at hX
  simp_rw [hX] at h
  rw [← polynomial_log_action (p := p) (K := K) q a (X v)]
  exact h.symm

private theorem commutesJet_original (q : K →ₗ[F] K) (X : V →ₗ[F] V)
    (hX : commutesJet (p := p) (K := K) q X) :
    commutesOriginal (p := p) (K := K) q X := by
  intro g v
  change X (finiteExp (jetOperator q (Multiplicative.toAdd g)) v) =
    finiteExp (jetOperator q (Multiplicative.toAdd g)) (X v)
  have hpow : ∀ n (w : V),
      X (((jetOperator q (Multiplicative.toAdd g)) ^ n) w) =
        ((jetOperator q (Multiplicative.toAdd g)) ^ n) (X w) := by
    intro n w
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, hX,
          ih]
  have hs (n : ℕ) (w : V) :
      X ((n.factorial : K)⁻¹ • w) = (n.factorial : K)⁻¹ • X w := by
    have he : (n.factorial : K)⁻¹ =
        algebraMap F K ((n.factorial : F)⁻¹) := by simp
    calc
      X ((n.factorial : K)⁻¹ • w) =
          X ((algebraMap F K ((n.factorial : F)⁻¹)) • w) := by rw [he]
      _ = X ((n.factorial : F)⁻¹ • w) := by rw [algebraMap_smul]
      _ = (n.factorial : F)⁻¹ • X w := map_smul X _ _
      _ = (n.factorial : K)⁻¹ • X w := by rw [he, algebraMap_smul]
  simp only [finiteExp, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hs, hpow]

theorem actual_commutant_iff_jet (q : K →ₗ[F] K) (X : V →ₗ[F] V) :
    commutesOriginal (p := p) (K := K) q X ↔
      commutesJet (p := p) (K := K) q X := by
  constructor
  · exact commutesOriginal_jet (p := p) (K := K) q X
  · exact commutesJet_original (p := p) (K := K) q X

private theorem jet_commutes_derivative (q : K →ₗ[F] K) (hq1 : q 1 = 0)
    (X : V →ₗ[F] V) (hX : commutesJet (p := p) (K := K) q X) :
    ∀ v, X (D v) = D (X v) := by
  intro v
  have h := hX 1 v
  simpa [jetOperator, hq1] using h

private theorem jet_commutes_top (q : K →ₗ[F] K) (hq1 : q 1 = 0)
    (X : V →ₗ[F] V) (hX : commutesJet (p := p) (K := K) q X) (b : K) :
    ∀ v, X (b • (D ^ (p - 1)) v) = b • (D ^ (p - 1)) (X v) := by
  have hD := jet_commutes_derivative (p := p) (K := K) q hq1 X hX
  have hpow : ∀ n (w : V), X ((D ^ n) w) = (D ^ n) (X w) := by
    intro n w
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, hD, ih]
  intro v
  have h := hX b ((D ^ (p - 2)) v)
  simp only [jetOperator, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.mul_apply] at h
  rw [hpow (p - 2) v] at h
  have hz (w : V) : (D ^ (p - 1)) ((D ^ (p - 2)) w) = 0 := by
    have hp : 2 < p := Fact.out
    rw [← Module.End.mul_apply, ← pow_add,
      pow_eq_zero_of_le (by omega : p ≤ (p - 1) + (p - 2))
      (derivative_pow_prime (p := p) (K := K))]
    rfl
  rw [hz v, hz (X v), smul_zero, add_zero] at h
  have hrel (w : V) : D ((D ^ (p - 2)) w) = (D ^ (p - 1)) w := by
    have hp : 2 < p := Fact.out
    have hp1 : p - 2 + 1 = p - 1 := by omega
    calc
      D ((D ^ (p - 2)) w) = (D * (D ^ (p - 2))) w := rfl
      _ = (D ^ (p - 2 + 1)) w := by rw [pow_succ']
      _ = (D ^ (p - 1)) w := by rw [hp1]
  simpa [hrel] using h

private theorem jet_commutes_scalar_derivative (q : K →ₗ[F] K) (hq1 : q 1 = 0)
    (X : V →ₗ[F] V) (hX : commutesJet (p := p) (K := K) q X) (a : K) :
    ∀ v, X (a • D v) = a • D (X v) := by
  have htop := jet_commutes_top (p := p) (K := K) q hq1 X hX
  intro v
  have h := hX a v
  simp only [jetOperator, LinearMap.add_apply, LinearMap.smul_apply] at h
  have ht := htop (q a) v
  rw [map_add] at h
  calc
    X (a • D v) = X (a • D v) + X (q a • (D ^ (p - 1)) v) -
        X (q a • (D ^ (p - 1)) v) := by abel
    _ = (a • D (X v) + q a • (D ^ (p - 1)) (X v)) -
        X (q a • (D ^ (p - 1)) v) := by rw [h]
    _ = a • D (X v) := by rw [ht]; abel

theorem actual_commutant_generated_bridge (q : K →ₗ[F] K) (hq1 : q 1 = 0)
    (X : V →ₗ[F] V) :
    commutesOriginal (p := p) (K := K) q X ↔
      (∀ v, X (D v) = D (X v)) ∧
      (∀ (a : K) (v : V), X (a • D v) = a • D (X v)) := by
  rw [actual_commutant_iff_jet]
  constructor
  · intro h
    exact ⟨jet_commutes_derivative (p := p) (K := K) q hq1 X h,
      fun a => jet_commutes_scalar_derivative (p := p) (K := K) q hq1 X h a⟩
  · rintro ⟨hD, hM⟩ a v
    change X (a • D v + q a • (D ^ (p - 1)) v) =
      a • D (X v) + q a • (D ^ (p - 1)) (X v)
    rw [map_add, hM a v]
    have hpow : ∀ n (w : V), X ((D ^ n) w) = (D ^ n) (X w) := by
      intro n w
      induction n generalizing w with
      | zero => rfl
      | succ n ih =>
          rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, hD, ih]
    have hrel (w : V) : D ((D ^ (p - 2)) w) = (D ^ (p - 1)) w := by
      have hp : 2 < p := Fact.out
      have hp1 : p - 2 + 1 = p - 1 := by omega
      calc
        D ((D ^ (p - 2)) w) = (D * (D ^ (p - 2))) w := rfl
        _ = (D ^ (p - 2 + 1)) w := by rw [pow_succ']
        _ = (D ^ (p - 1)) w := by rw [hp1]
    have htop : X (q a • (D ^ (p - 1)) v) =
        q a • (D ^ (p - 1)) (X v) := by
      have hh := hM (q a) ((D ^ (p - 2)) v)
      rw [hrel, hpow (p - 2) v, hrel] at hh
      exact hh
    rw [htop]

def scalarMap (a : K) : V →ₗ[F] V :=
  (Algebra.lsmul F K V a).restrictScalars F

def topMap (T : K →ₗ[F] K) : V →ₗ[F] V :=
  ((constantLinear (p := p) (K := K)).restrictScalars F).comp
    ((T.comp ((coefficientZero (p := p) (K := K)).restrictScalars F)).comp
      (((D).restrictScalars F) ^ (p - 1)))

def toeplitz (a : Fin (p - 1) → K) (T : K →ₗ[F] K) : V →ₗ[F] V :=
  (∑ r : Fin (p - 1), scalarMap (p := p) (K := K) (a r) *
      ((D).restrictScalars F) ^ r.val) + topMap (p := p) (K := K) T

private theorem divided_top_power (j : ℕ) (hj : j < p) (z : K) :
    (D ^ (p - 1 - j))
        (dividedMonomial (p - 1) (by have := (Fact.out : p.Prime); omega) z) =
      dividedMonomial j hj z := by
  have hp : 2 < p := Fact.out
  have hpow : ∀ n : ℕ, n ≤ p - 1 →
      (D ^ n) (dividedMonomial (p - 1)
        (by have := (Fact.out : p.Prime); omega) z) =
        dividedMonomial (p - 1 - n) (by omega) z := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, ih (by omega)]
        have hs := dividedMonomial_succ (p := p) (K := K) (p - 2 - n)
          (by omega) z
        simpa [show p - 1 - n = (p - 2 - n) + 1 by omega,
          show p - 1 - (n + 1) = p - 2 - n by omega] using hs
  have hjle : j ≤ p - 1 := by omega
  have heq : p - 1 - (p - 1 - j) = j := by omega
  simpa [heq] using hpow (p - 1 - j) (by omega)

private theorem top_decomposition (v : V) :
    v = ∑ j : Fin p,
      dividedMonomial j.val j.isLt
        ((v : K[X]).coeff j.val * (j.val.factorial : K)) := by
  apply Subtype.ext
  apply Polynomial.ext
  intro n
  by_cases hn : n < p
  · simp only [Submodule.coe_sum]
    change (v : K[X]).coeff n =
      Polynomial.lcoeff K n (∑ i : Fin p,
        (dividedMonomial i.val i.isLt
          ((v : K[X]).coeff i.val * (i.val.factorial : K)) : K[X]))
    rw [map_sum]
    rw [Finset.sum_eq_single ⟨n, hn⟩]
    · simp [dividedMonomial]
      have hchar : CharP K p :=
        charP_of_injective_algebraMap (algebraMap F K).injective p
      have hfac : (n.factorial : K) ≠ 0 := by
        rw [Ne, CharP.cast_eq_zero_iff K p]
        exact fun h => (not_le_of_gt hn)
          ((Fact.out : p.Prime).dvd_factorial.mp h)
      field_simp
    · intro b hb hbn
      have hneq : n ≠ b.val := by
        intro he
        apply hbn
        exact Fin.ext he.symm
      simp [dividedMonomial, hneq]
    · simp [hn]
  · have hz : (v : K[X]).coeff n = 0 :=
      coeff_eq_zero_of_degree_lt ((mem_degreeLT.mp v.property).trans_le
        (by exact_mod_cast (by omega : p ≤ n)))
    rw [hz]
    simp only [Submodule.coe_sum]
    change 0 =
      Polynomial.lcoeff K n (∑ i : Fin p,
        (dividedMonomial i.val i.isLt
          ((v : K[X]).coeff i.val * (i.val.factorial : K)) : K[X]))
    rw [map_sum]
    symm
    apply Fintype.sum_eq_zero
    intro b
    exact coeff_eq_zero_of_degree_lt
      ((mem_degreeLT.mp (dividedMonomial b.val b.isLt
        ((v : K[X]).coeff b.val * (b.val.factorial : K))).property).trans_le
        (by exact_mod_cast (by omega : p ≤ n)))

theorem derivative_pow_coe_local (n : ℕ) (w : V) :
    ((D ^ n) w : K[X]) = Polynomial.derivative^[n] (w : K[X]) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      change Polynomial.derivative ((D ^ n) w : K[X]) = _
      rw [ih, Function.iterate_succ_apply']

private theorem reconstruct_from_derivatives (w : V) :
    w = ∑ j : Fin p,
      dividedMonomial j.val j.isLt
        ((coefficientZero ((D ^ j.val) w))) := by
  have hc (j : Fin p) : coefficientZero ((D ^ j.val) w) =
      (j.val.factorial : K) * (w : K[X]).coeff j.val := by
    change ((D ^ j.val) w : K[X]).coeff 0 = _
    rw [derivative_pow_coe_local, coeff_iterate_derivative]
    simp [Nat.descFactorial_eq_factorial_mul_choose]
  calc
    w = ∑ j : Fin p,
        dividedMonomial j.val j.isLt
          ((w : K[X]).coeff j.val * (j.val.factorial : K)) :=
      top_decomposition w
    _ = ∑ j : Fin p,
        dividedMonomial j.val j.isLt
          (coefficientZero ((D ^ j.val) w)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hc]
      congr 1
      ring

def topInput : K →ₗ[F] V :=
  (dividedMonomial (p - 1) (by
    have hp : 2 < p := Fact.out
    omega)).restrictScalars F

def topCoefficient (X : V →ₗ[F] V) (j : Fin p) : K →ₗ[F] K :=
  ((coefficientZero (p := p) (K := K)).restrictScalars F).comp
    ((((D).restrictScalars F) ^ j.val).comp
      (X.comp (topInput (p := p) (K := K))))

def toeplitzDegree (c : Fin p → K) (T : K →ₗ[F] K) : V →ₗ[F] V :=
  (∑ j : Fin p,
      scalarMap (p := p) (K := K) (c j) *
        ((D).restrictScalars F) ^ (p - 1 - j.val)) +
    topMap (p := p) (K := K) T

def commutantFamily (X : V →ₗ[F] V) : Fin p → K := fun j =>
  if j = 0 then 0 else topCoefficient (p := p) (K := K) X j 1

theorem restricted_derivative_pow_local (n : ℕ) (v : V) :
    (((D).restrictScalars F) ^ n) v = (D ^ n) v := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
      rfl

theorem topCoefficient_apply (X : V →ₗ[F] V) (j : Fin p) (z : K) :
    topCoefficient (p := p) (K := K) X j z =
      coefficientZero ((D ^ j.val) (X (topInput (p := p) (K := K) z))) := by
  simp [topCoefficient, topInput, LinearMap.comp_apply,
    restricted_derivative_pow_local]

theorem top_coefficient_reconstruct (X : V →ₗ[F] V) (z : K) :
    X (topInput (p := p) (K := K) z) =
      ∑ j : Fin p,
        dividedMonomial j.val j.isLt
          (topCoefficient (p := p) (K := K) X j z) := by
  have h := reconstruct_from_derivatives (p := p) (K := K)
    (X (topInput (p := p) (K := K) z))
  simpa [topCoefficient_apply (p := p) (K := K) X] using h

private theorem top_input_smul (a z : K) :
    topInput (p := p) (K := K) (a * z) = a • topInput (p := p) (K := K) z := by
  change dividedMonomial (p - 1) _ (a * z) =
    a • dividedMonomial (p - 1) _ z
  simpa [smul_eq_mul] using
    (dividedMonomial (p - 1) (by have hp : 2 < p := Fact.out; omega)).map_smul a z

private theorem top_derivative_smul (X : V →ₗ[F] V)
    (hD : ∀ v, X (D v) = D (X v))
    (hM : ∀ (a : K) (v : V), X (a • D v) = a • D (X v)) :
    ∀ (a z : K), D (X (topInput (p := p) (K := K) (a * z))) =
      a • D (X (topInput (p := p) (K := K) z)) := by
  intro a z
  calc
    D (X (topInput (p := p) (K := K) (a * z))) =
        X (D (topInput (p := p) (K := K) (a * z))) := hD _ |>.symm
    _ = X (a • D (topInput (p := p) (K := K) z)) := by
      rw [top_input_smul, map_smul]
    _ = a • D (X (topInput (p := p) (K := K) z)) := hM a _

private theorem top_derivative_pow_smul (X : V →ₗ[F] V)
    (hD : ∀ v, X (D v) = D (X v))
    (hM : ∀ (a : K) (v : V), X (a • D v) = a • D (X v)) :
    ∀ n : ℕ, 1 ≤ n → ∀ (a z : K),
      (D ^ n) (X (topInput (p := p) (K := K) (a * z))) =
        a • (D ^ n) (X (topInput (p := p) (K := K) z)) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      intro a z
      simpa using top_derivative_smul X hD hM a z
  | succ n hn ih =>
      intro a z
      rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      rw [ih a z, map_smul]

private theorem topCoefficient_smul (X : V →ₗ[F] V)
    (hD : ∀ v, X (D v) = D (X v))
    (hM : ∀ (a : K) (v : V), X (a • D v) = a • D (X v))
    (j : Fin p) (hj : j ≠ 0) (a z : K) :
    topCoefficient (p := p) (K := K) X j (a * z) =
      a * topCoefficient (p := p) (K := K) X j z := by
  rw [topCoefficient_apply, topCoefficient_apply,
    top_derivative_pow_smul X hD hM j.val (by
      have hne : j.val ≠ 0 := by
        intro hz
        apply hj
        exact Fin.ext hz
      omega) a z]
  simp [coefficientZero, smul_eq_mul]

theorem scalarMap_apply (a : K) (v : V) :
    scalarMap (p := p) (K := K) a v = a • v := by
  rfl

private theorem scalarMap_derivative (a : K) (v : V) :
    scalarMap (p := p) (K := K) a (D v) =
      D (scalarMap (p := p) (K := K) a v) := by
  simp [scalarMap_apply, map_smul]

private theorem scalar_term_topInput (a : K) (j : Fin p) (z : K) :
    scalarMap (p := p) (K := K) a
        ((((D).restrictScalars F) ^ (p - 1 - j.val))
          (topInput (p := p) (K := K) z)) =
      dividedMonomial j.val j.isLt (a * z) := by
  simp only [topInput, LinearMap.restrictScalars_apply]
  rw [restricted_derivative_pow_local]
  have htop := divided_top_power (p := p) (K := K) j.val j.isLt z
  rw [htop]
  change a • dividedMonomial j.val j.isLt z =
    dividedMonomial j.val j.isLt (a * z)
  simpa [smul_eq_mul] using
    ((dividedMonomial (p := p) (K := K) j.val j.isLt).map_smul a z).symm

theorem topMap_topInput (T : K →ₗ[F] K) (z : K) :
    topMap (p := p) (K := K) T (topInput (p := p) (K := K) z) =
      dividedMonomial 0 (by have hp : 2 < p := Fact.out; omega) (T z) := by
  simp only [topMap, LinearMap.comp_apply, topInput,
    LinearMap.restrictScalars_apply, restricted_derivative_pow_local]
  have htop := divided_top_power (p := p) (K := K) (0 : ℕ)
    (by have hp : 2 < p := Fact.out; omega) z
  have htop' : (D ^ (p - 1))
      (dividedMonomial (p - 1)
        (by have hp : 2 < p := Fact.out; omega) z) =
      dividedMonomial 0 (by have hp : 2 < p := Fact.out; omega) z := by
    simpa only [Nat.sub_zero] using htop
  rw [htop']
  apply Subtype.ext
  simp [coefficientZero, constantLinear, dividedMonomial]
  rw [Polynomial.C_eq_algebraMap]
  rw [Algebra.smul_def, mul_one]

theorem toeplitzDegree_topInput (c : Fin p → K) (hc0 : c 0 = 0)
    (T : K →ₗ[F] K) (z : K) :
    toeplitzDegree (p := p) (K := K) c T
        (topInput (p := p) (K := K) z) =
      ∑ j : Fin p, dividedMonomial j.val j.isLt
        (if j = 0 then T z else c j * z) := by
  classical
  simp only [toeplitzDegree, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, Module.End.mul_apply]
  rw [topMap_topInput]
  simp_rw [scalar_term_topInput]
  conv_lhs =>
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin p))]
  conv_rhs =>
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin p))]
  simp only [Fin.val_zero, ite_true, hc0, zero_mul, map_zero, add_zero]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro j hj
    rw [if_neg (Finset.mem_erase.mp hj).1]
  · rfl

private theorem topMap_derivative (T : K →ₗ[F] K) (v : V) :
    topMap (p := p) (K := K) T (D v) =
      D (topMap (p := p) (K := K) T v) := by
  simp only [topMap, LinearMap.comp_apply, Module.End.mul_apply]
  have hp : 2 < p := Fact.out
  have hzero : (((D).restrictScalars F) ^ (p - 1)) (D v) = 0 := by
    rw [restricted_derivative_pow_local, ← Module.End.mul_apply, ← pow_succ,
      Nat.sub_add_cancel (by omega : 1 ≤ p), derivative_pow_prime]
    rfl
  rw [hzero]
  simp only [map_zero]
  simp only [LinearMap.restrictScalars_apply]
  rw [constant_derivative]

theorem toeplitzDegree_derivative (c : Fin p → K) (T : K →ₗ[F] K) (v : V) :
    toeplitzDegree (p := p) (K := K) c T (D v) =
      D (toeplitzDegree (p := p) (K := K) c T v) := by
  simp only [toeplitzDegree, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, Module.End.mul_apply]
  rw [map_add, map_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro j hj
    have hpow_comm (n : ℕ) (w : V) :
        (D ^ n) (D w) = D ((D ^ n) w) := by
      induction n generalizing w with
      | zero => rfl
      | succ n ih =>
          calc
            (D ^ (n + 1)) (D w) = (D ^ n) (D (D w)) := by
              rw [pow_succ, Module.End.mul_apply]
            _ = D ((D ^ n) (D w)) := by rw [ih (D w)]
            _ = D ((D ^ (n + 1)) w) := by
              rw [pow_succ, Module.End.mul_apply]
    rw [restricted_derivative_pow_local, hpow_comm]
    simpa only [restricted_derivative_pow_local] using
      (scalarMap_derivative (p := p) (K := K) (c j)
        ((D ^ (p - 1 - j.val)) v))
  · exact (topMap_derivative (p := p) (K := K) T v)

private theorem commutes_pow (X : V →ₗ[F] V)
    (hD : ∀ v, X (D v) = D (X v)) (n : ℕ) (v : V) :
    X ((D ^ n) v) = (D ^ n) (X v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply]
      rw [hD, ih]

theorem commuting_ext (X Y : V →ₗ[F] V)
    (hX : ∀ v, X (D v) = D (X v))
    (hY : ∀ v, Y (D v) = D (Y v))
    (htop : ∀ z, X (topInput (p := p) (K := K) z) = Y (topInput z)) : X = Y := by
  apply LinearMap.ext
  intro v
  rw [top_decomposition v, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← divided_top_power j.val j.isLt,
    commutes_pow X hX, commutes_pow Y hY]
  exact congrArg (fun w => (D ^ (p - 1 - j.val)) w) (htop _)

private theorem normal_form_of_generated (X : V →ₗ[F] V)
    (hD : ∀ v, X (D v) = D (X v))
    (hM : ∀ (a : K) (v : V), X (a • D v) = a • D (X v)) :
    X = toeplitzDegree (p := p) (K := K) (commutantFamily X)
      (topCoefficient X 0) := by
  classical
  apply commuting_ext X _ hD (toeplitzDegree_derivative _ _)
  intro z
  rw [top_coefficient_reconstruct, toeplitzDegree_topInput _ (by
    simp [commutantFamily])]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : j = 0
  · subst j; simp
  · rw [if_neg h]
    congr 1
    simp only [commutantFamily, if_neg h]
    have hs := topCoefficient_smul X hD hM j h z 1
    simpa only [mul_one, mul_comm] using hs

private theorem topMap_scalar_derivative (T : K →ₗ[F] K) (a : K) (v : V) :
    topMap (p := p) (K := K) T (a • D v) = 0 := by
  simp only [topMap, LinearMap.comp_apply, restricted_derivative_pow_local]
  rw [map_smul]
  have hzero : (D ^ (p - 1)) (D v) = 0 := by
    rw [← Module.End.mul_apply, ← pow_succ,
      Nat.sub_add_cancel (by have hp : 2 < p := Fact.out; omega), derivative_pow_prime]
    rfl
  rw [hzero, smul_zero]
  simp

private theorem toeplitzDegree_scalar_derivative (c : Fin p → K)
    (T : K →ₗ[F] K) (a : K) (v : V) :
    toeplitzDegree (p := p) (K := K) c T (a • D v) =
      a • D (toeplitzDegree c T v) := by
  rw [← toeplitzDegree_derivative]
  simp only [toeplitzDegree, LinearMap.add_apply, LinearMap.sum_apply,
    Module.End.mul_apply, topMap_scalar_derivative, add_zero]
  have ht := topMap_scalar_derivative T 1 v
  simp only [one_smul] at ht
  rw [ht, add_zero, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [restricted_derivative_pow_local, map_smul, scalarMap_apply,
    smul_smul, mul_comm]

/-- Normal form on the original polynomial carrier. The coordinate at degree zero
is reserved for the arbitrary prime-field-linear top map. -/
theorem actual_commutant_normal_form (q : K →ₗ[F] K) (hq1 : q 1 = 0)
    (X : V →ₗ[F] V) :
    commutesOriginal (p := p) (K := K) q X ↔
      ∃ (c : Fin p → K) (T : K →ₗ[F] K), c 0 = 0 ∧ X = toeplitzDegree c T := by
  rw [actual_commutant_generated_bridge q hq1]
  constructor
  · rintro ⟨hD, hM⟩
    exact ⟨commutantFamily X, topCoefficient X 0, by simp [commutantFamily],
      normal_form_of_generated X hD hM⟩
  · rintro ⟨c, T, hc, rfl⟩
    exact ⟨toeplitzDegree_derivative c T, toeplitzDegree_scalar_derivative c T⟩

theorem factorial_ne_zero (j : Fin p) : (j.val.factorial : K) ≠ 0 := by
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap F K).injective p
  rw [Ne, CharP.cast_eq_zero_iff K p]
  exact fun h => (not_le_of_gt j.isLt) ((Fact.out : p.Prime).dvd_factorial.mp h)

theorem divided_sum_coefficient (f : Fin p → K) (j : Fin p) :
    ((∑ i : Fin p, dividedMonomial i.val i.isLt (f i) : V) : K[X]).coeff j.val =
      f j * (j.val.factorial : K)⁻¹ := by
  classical
  simp only [Submodule.coe_sum]
  change Polynomial.lcoeff K j.val (∑ i : Fin p,
    (dividedMonomial i.val i.isLt (f i) : K[X])) = _
  rw [map_sum, Finset.sum_eq_single j]
  · simp [dividedMonomial, smul_eq_mul]
  · intro b hb hbj
    have hne : j.val ≠ b.val := fun h => hbj (Fin.ext h.symm)
    simp [dividedMonomial, hne]
  · simp

private theorem divided_sum_injective (f g : Fin p → K)
    (h : (∑ i : Fin p, dividedMonomial i.val i.isLt (f i)) =
      ∑ i : Fin p, dividedMonomial i.val i.isLt (g i)) : f = g := by
  funext j
  have hc := congrArg (fun v : V => (v : K[X]).coeff j.val) h
  rw [divided_sum_coefficient, divided_sum_coefficient] at hc
  exact (mul_right_cancel₀ (inv_ne_zero (factorial_ne_zero j))) hc

/-- Both the scalar coordinates and the unrestricted top endomorphism are unique. -/
theorem toeplitzDegree_injective (c d : Fin p → K) (hc : c 0 = 0) (hd : d 0 = 0)
    (T U : K →ₗ[F] K)
    (h : toeplitzDegree (p := p) c T = toeplitzDegree d U) : c = d ∧ T = U := by
  classical
  have hcoords (z : K) := congrArg (fun X : V →ₗ[F] V => X (topInput z)) h
  simp only [toeplitzDegree_topInput c hc, toeplitzDegree_topInput d hd] at hcoords
  have he (z : K) := congrFun (divided_sum_injective _ _ (hcoords z))
  constructor
  · funext j
    by_cases hj : j = 0
    · subst j; exact hc.trans hd.symm
    · simpa only [if_neg hj, mul_one] using he 1 j
  · apply LinearMap.ext
    intro z
    simpa using he z (0 : Fin p)

/-- Explicit coordinates of the full commutant; no finite-dimensional hypothesis. -/
def coordinatesEquiv (q : K →ₗ[F] K) (hq1 : q 1 = 0) :
    {X : V →ₗ[F] V // commutesOriginal q X} ≃
      ({c : Fin p → K // c 0 = 0} × (K →ₗ[F] K)) where
  toFun X := (⟨commutantFamily X.val, by simp [commutantFamily]⟩, topCoefficient X.val 0)
  invFun c := ⟨toeplitzDegree c.1.val c.2,
    (actual_commutant_normal_form q hq1 _).mpr ⟨c.1.val, c.2, c.1.property, rfl⟩⟩
  left_inv X := by
    apply Subtype.ext
    exact (normal_form_of_generated X.val
      ((actual_commutant_generated_bridge q hq1 X.val).mp X.property).1
      ((actual_commutant_generated_bridge q hq1 X.val).mp X.property).2).symm
  right_inv c := by
    have hgen := (actual_commutant_generated_bridge q hq1 (toeplitzDegree c.1.val c.2)).mp
      ((actual_commutant_normal_form q hq1 _).mpr ⟨_, _, c.1.property, rfl⟩)
    have h := toeplitzDegree_injective _ _ (by simp [commutantFamily]) c.1.property
      _ _ (normal_form_of_generated _ hgen.1 hgen.2).symm
    exact Prod.ext (Subtype.ext h.1) h.2

private theorem derivative_commutes_end_pow (X : V →ₗ[F] V)
    (hD : ∀ v, X (D v) = D (X v)) (n : ℕ) (v : V) :
    (X ^ n) (D v) = D ((X ^ n) v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply]
      rw [ih, hD]

theorem nilpotent_of_constants_zero (X : V →ₗ[F] V)
    (hD : ∀ v, X (D v) = D (X v))
    (hc : ∀ z, X (constantLinear z) = 0) : X ^ p = 0 := by
  have hkill : ∀ n (v : V), (D ^ n) v = 0 → (X ^ n) v = 0 := by
    intro n
    induction n with
    | zero => intro v hv; exact hv
    | succ n ih =>
        intro v hv
        have hker : D ((X ^ n) v) = 0 := by
          rw [← derivative_commutes_end_pow X hD]
          apply ih
          simpa only [pow_succ, Module.End.mul_apply] using hv
        have he : (X ^ n) v = constantLinear (((X ^ n) v : K[X]).coeff 0) :=
          Subtype.ext (derivative_kernel _ hker)
        rw [pow_succ', Module.End.mul_apply, he, hc]
  apply LinearMap.ext
  intro v
  apply hkill
  rw [derivative_pow_prime]
  rfl

theorem derivative_pow_constant (n : ℕ) (hn : 0 < n) (z : K) :
    (D ^ n) (constantLinear z) = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [pow_succ, Module.End.mul_apply, constant_derivative, map_zero]

def leadingIndex : Fin p := ⟨p - 1, by have hp : 2 < p := Fact.out; omega⟩

theorem toeplitzDegree_constant (c : Fin p → K) (T : K →ₗ[F] K) (z : K) :
    toeplitzDegree (p := p) c T (constantLinear z) =
      constantLinear (c (leadingIndex (p := p)) * z) := by
  classical
  have hp : 2 < p := Fact.out
  have htop : topMap (p := p) T (constantLinear z) = 0 := by
    simp only [topMap, LinearMap.comp_apply, restricted_derivative_pow_local]
    rw [derivative_pow_constant (p - 1) (by omega)]
    simp
  simp only [toeplitzDegree, LinearMap.add_apply, LinearMap.sum_apply,
    Module.End.mul_apply, htop, add_zero]
  rw [Finset.sum_eq_single (leadingIndex (p := p))]
  · simp only [leadingIndex, Nat.sub_self, pow_zero, Module.End.one_apply,
      scalarMap_apply]
    simpa only [leadingIndex, smul_eq_mul] using (constantLinear (p := p) (K := K)).map_smul
      (c (leadingIndex (p := p))) z |>.symm
  · intro b hb hbl
    have hlt : b.val < p - 1 := by
      have hne : b.val ≠ p - 1 := fun h => hbl (Fin.ext h)
      omega
    rw [restricted_derivative_pow_local, derivative_pow_constant _ (by omega), map_zero]
  · simp

private theorem scalarMap_isUnit (a : K) (ha : a ≠ 0) :
    IsUnit (scalarMap (p := p) (K := K) a) := by
  refine ⟨⟨scalarMap a, scalarMap a⁻¹, ?_, ?_⟩, rfl⟩
  · apply LinearMap.ext
    intro v
    simp [Module.End.mul_apply, scalarMap_apply, smul_smul, ha]
  · apply LinearMap.ext
    intro v
    simp [Module.End.mul_apply, scalarMap_apply, smul_smul, ha]

/-- The invertibility criterion concerns actual F-linear operators, even when K is infinite. -/
theorem toeplitzDegree_isUnit_iff (c : Fin p → K) (T : K →ₗ[F] K) :
    IsUnit (toeplitzDegree (p := p) c T) ↔ c (leadingIndex (p := p)) ≠ 0 := by
  let X := toeplitzDegree (p := p) c T
  let a := c (leadingIndex (p := p))
  have hnonzero : constantLinear (p := p) (K := K) 1 ≠ (0 : V) := by
    intro h
    have hh := congrArg (fun v : V => (v : K[X]).coeff 0) h
    simpa [constantLinear] using hh
  letI : Nontrivial V := ⟨⟨constantLinear 1, 0, hnonzero⟩⟩
  constructor
  · intro hX ha
    have hn : IsNilpotent X := ⟨p, nilpotent_of_constants_zero X
      (toeplitzDegree_derivative c T) (by
        intro z
        simp only [X, toeplitzDegree_constant, ha, zero_mul, map_zero])⟩
    exact hn.not_isUnit hX
  · intro ha
    have ha' : a ≠ 0 := ha
    let Z : V →ₗ[F] V := scalarMap a⁻¹ * X - 1
    have hZD (v : V) : Z (D v) = D (Z v) := by
      simp only [Z, LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply,
        map_sub, X, toeplitzDegree_derivative, scalarMap_derivative]
    have hZc (z : K) : Z (constantLinear z) = 0 := by
      simp only [Z, LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply,
        X, toeplitzDegree_constant, scalarMap_apply]
      rw [← (constantLinear (p := p) (K := K)).map_smul]
      simp [a, smul_eq_mul, ha]
    have hn : IsNilpotent Z := ⟨p, nilpotent_of_constants_zero Z hZD hZc⟩
    have hu := (scalarMap_isUnit (p := p) a ha).mul hn.isUnit_one_add
    have he : scalarMap (p := p) a * (1 + Z) = X := by
      apply LinearMap.ext
      intro v
      simp [Z, Module.End.mul_apply, scalarMap_apply, smul_sub, smul_add,
        smul_smul, ha']
    rwa [he] at hu

end D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutant
