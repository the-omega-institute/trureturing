/- GID: D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDeformation
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDeformation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Algebra.Tower, mathlib/module/Mathlib.Algebra.Module.ZMod, mathlib/module/Mathlib.Algebra.Polynomial.Derivative, mathlib/module/Mathlib.Algebra.Polynomial.Taylor, mathlib/module/Mathlib.Algebra.CharP.Algebra, mathlib/module/Mathlib.Algebra.BigOperators.Field, mathlib/module/Mathlib.Data.Fintype.Card, mathlib/module/Mathlib.GroupTheory.SpecificGroups.Cyclic, mathlib/module/Mathlib.Data.Nat.Prime.Factorial, mathlib/module/Mathlib.RingTheory.Trace.Defs, mathlib/module/Mathlib.Data.ZMod.Basic, mathlib/module/Mathlib.FieldTheory.Finite.Basic, mathlib/module/Mathlib.LinearAlgebra.FiniteDimensional.Basic, mathlib/module/Mathlib.RingTheory.Polynomial.DegreeLT, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Odd-prime higher-jet representations and their arbitrary-linear trace obstruction. -/
import D5.S3.FiniteGroups.GroupAlgebra.TruncatedPolynomialCyclicCriterion
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.RingTheory.Trace.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic

/-!
# Odd-prime higher-jet representations

For an odd prime p and a finite extension K of F = ZMod p, the original additive
group of K acts on polynomials of degree less than p by

  rho_x = exp (x D + q(x) D^(p-1)),

where q is F-linear and q(1)=0. Each original cyclic restriction is projective,
while the full norm vanishes and the full module is not projective when
[K:F] is at least two. The ordinary action is actual polynomial translation.

A nonzero field trace of some q(a) obstructs an equivalence to ordinary
translations even after an arbitrary automorphism of the original group.
The intertwining equivalence is only F-linear. A polynomial logarithm,
diagonal normalization, restriction to constants, and a commutator trace
identity give the obstruction without a centralizer classification.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation

open Polynomial Finset Module
open scoped BigOperators TensorProduct MonoidAlgebra

universe uK

variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable {K : Type uK} [Field K] [Algebra (ZMod p) K]

local notation "F" => ZMod p
local notation "V" => Polynomial.degreeLT K p
local notation "E" => Multiplicative K

private theorem fieldChar : CharP K p :=
  charP_of_injective_algebraMap (algebraMap F K).injective p

private theorem primeCast_eq_zero : (p : K) = 0 := by
  calc
    (p : K) = algebraMap F K (p : F) := (map_natCast _ _).symm
    _ = 0 := by rw [ZMod.natCast_self, map_zero]

def derivativeEnd : Module.End K V where
  toFun f := ⟨Polynomial.derivative (f : K[X]),
    Polynomial.mem_degreeLT.mpr
      (Polynomial.degree_derivative_le.trans_lt (Polynomial.mem_degreeLT.mp f.property))⟩
  map_add' _ _ := Subtype.ext (Polynomial.derivative.map_add _ _)
  map_smul' c _ := Subtype.ext (Polynomial.derivative.map_smul c _)

local notation "D" => derivativeEnd (p := p) (K := K)

private theorem derivative_pow_coe (n : ℕ) (f : V) :
    ((D ^ n) f : K[X]) = Polynomial.derivative^[n] (f : K[X]) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      change Polynomial.derivative ((D ^ n) f : K[X]) = _
      rw [ih, Function.iterate_succ_apply']

theorem derivative_pow_prime : D ^ p = 0 := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  simpa only [derivative_pow_coe, LinearMap.zero_apply, ZeroMemClass.coe_zero] using
    (Polynomial.iterate_derivative_eq_zero_of_degree_lt
      (Polynomial.mem_degreeLT.mp f.property))

private theorem factorial_ne_zero (j : ℕ) (hj : j < p) :
    (j.factorial : K) ≠ 0 := by
  letI : CharP K p := fieldChar
  rw [Ne, CharP.cast_eq_zero_iff K p]
  exact fun h => (not_le_of_gt hj) ((Fact.out : p.Prime).dvd_factorial.mp h)

def finiteExp (A : Module.End K V) : Module.End K V :=
  ∑ j ∈ range p, (j.factorial : K)⁻¹ • A ^ j

private theorem finiteExp_zero : finiteExp (p := p) (K := K) 0 = 1 := by
  classical
  rw [finiteExp, sum_eq_single 0]
  · simp
  · intro j _ hj; simp [zero_pow hj]
  · simp [(Fact.out : p.Prime).pos]

/-- The infinitesimal operator on the actual truncated polynomial space. -/
def jetOperator (q : K →ₗ[F] K) (x : K) : Module.End K V :=
  x • D + q x • D ^ (p - 1)

private theorem jetOperator_zero (q : K →ₗ[F] K) :
    jetOperator (p := p) q 0 = 0 := by simp [jetOperator]

private theorem jetOperator_add (q : K →ₗ[F] K) (x y : K) :
    jetOperator (p := p) q (x + y) = jetOperator q x + jetOperator q y := by
  simp only [jetOperator, map_add, add_smul]
  abel

private theorem derivative_pow_vanish (n : ℕ) (hn : p ≤ n) : D ^ n = 0 :=
  pow_eq_zero_of_le hn derivative_pow_prime

private theorem jetOperator_sq (q : K →ₗ[F] K) (x : K) :
    (jetOperator (p := p) q x)^2 = x^2 • D^2 := by
  have hp : 2 < p := Fact.out
  have hm : D * D^(p-1) = 0 := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p), derivative_pow_prime]
  have hm' : D^(p-1) * D = 0 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p), derivative_pow_prime]
  have ht : D^(p-1) * D^(p-1) = 0 := by
    rw [← pow_add]; exact derivative_pow_vanish _ (by omega)
  simp only [jetOperator, pow_two, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, smul_smul, hm, hm', ht, smul_zero, add_zero, zero_add]

private theorem jetOperator_pow (q : K →ₗ[F] K) (x : K)
    (n : ℕ) (hn : 2 ≤ n) : (jetOperator (p := p) q x)^n = x^n • D^n := by
  have hp : 2 < p := Fact.out
  induction n, hn using Nat.le_induction with
  | base => exact jetOperator_sq q x
  | succ n hn ih =>
      have ht : D^n * D^(p-1) = 0 := by
        rw [← pow_add]; exact derivative_pow_vanish _ (by omega)
      rw [pow_succ, ih, jetOperator, mul_add]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ht, smul_zero, add_zero,
        ← pow_succ]
      rw [← pow_succ']

private def translationSeries (x : K) : Module.End K V :=
  ∑ j ∈ range p, (x^j / (j.factorial : K)) • D^j

private theorem translationSeries_taylor (x : K) (v : V) :
    (translationSeries (p := p) x v : K[X]) = (v : K[X]).comp (X + C x) := by
  classical
  have he : (degreeLT K p).subtype.comp (translationSeries x) =
      (Polynomial.taylor x).comp (degreeLT K p).subtype := by
    apply (Polynomial.degreeLT.basis K p).ext
    intro n
    change ((translationSeries x) ((degreeLT.basis K p) n) : K[X]) =
      Polynomial.taylor x ((degreeLT.basis K p) n : K[X])
    simp only [translationSeries, LinearMap.sum_apply, LinearMap.smul_apply,
      AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, derivative_pow_coe,
      Polynomial.degreeLT.basis_val, Polynomial.taylor_X_pow]
    have hterm (j : ℕ) (hj : j < p) :
        (x^j / (j.factorial : K)) • Polynomial.derivative^[j] (X^(n : ℕ)) =
          (C x)^j * X^((n : ℕ)-j) * ((n : ℕ).choose j : K[X]) := by
      rw [Polynomial.iterate_derivative_X_pow_eq_smul,
        Nat.descFactorial_eq_factorial_mul_choose, smul_smul, Nat.cast_mul]
      have hfac := factorial_ne_zero (K := K) j hj
      have hc : x^j / (j.factorial : K) *
          ((j.factorial : K) * ((n : ℕ).choose j : K)) =
          x^j * ((n : ℕ).choose j : K) := by field_simp
      rw [hc, Polynomial.smul_eq_C_mul, C_mul, C_pow, C_eq_natCast]
      ring
    rw [Finset.sum_congr rfl (fun j hj => hterm j (mem_range.mp hj))]
    rw [show X + C x = C x + (X : K[X]) from add_comm _ _, add_pow]
    symm
    apply Finset.sum_subset (range_mono (show (n : ℕ)+1 ≤ p by omega))
    intro j hj hnot
    have hn : (n : ℕ) < j := by simpa using hnot
    simp [Nat.choose_eq_zero_of_lt hn]
  exact LinearMap.congr_fun he v

private theorem translationSeries_add (x y : K) :
    translationSeries (p := p) (x+y) = translationSeries x * translationSeries y := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change (translationSeries (x+y) v : K[X]) =
    (translationSeries x (translationSeries y v) : K[X])
  simp only [translationSeries_taylor]
  exact (Polynomial.taylor_taylor (v : K[X]) x y).symm

private theorem finiteExp_jet (q : K →ₗ[F] K) (x : K) :
    finiteExp (jetOperator (p := p) q x) = translationSeries x + q x • D^(p-1) := by
  classical
  have hp : 2 < p := Fact.out
  have hterm (j : ℕ) (hj : j ∈ range p) :
      (j.factorial : K)⁻¹ • (jetOperator q x)^j =
        (x^j / (j.factorial : K)) • D^j +
          if j = 1 then q x • D^(p-1) else 0 := by
    by_cases h0 : j = 0
    · subst j; simp
    by_cases h1 : j = 1
    · subst j; simp [jetOperator]
    rw [jetOperator_pow q x j (by omega)]
    simp [h1, div_eq_mul_inv, smul_smul, mul_comm]
  simp_rw [finiteExp, sum_congr rfl hterm, sum_add_distrib]
  simp [translationSeries, show 1 < p by omega]

private theorem translationSeries_mul_top (x : K) :
    translationSeries (p := p) x * D^(p-1) = D^(p-1) := by
  classical
  have hp : 2 < p := Fact.out
  rw [translationSeries, sum_mul, sum_eq_single 0]
  · simp
  · intro j hj hj0
    rw [smul_mul_assoc, ← pow_add, derivative_pow_vanish _ (by omega), smul_zero]
  · simp [show 0 < p by omega]

private theorem top_mul_translationSeries (x : K) :
    D^(p-1) * translationSeries (p := p) x = D^(p-1) := by
  classical
  have hp : 2 < p := Fact.out
  rw [translationSeries, mul_sum, sum_eq_single 0]
  · simp
  · intro j hj hj0
    rw [mul_smul_comm, ← pow_add, derivative_pow_vanish _ (by omega), smul_zero]
  · simp [show 0 < p by omega]

private theorem finiteExp_jet_add (q : K →ₗ[F] K) (x y : K) :
    finiteExp (jetOperator (p := p) q x + jetOperator q y) =
      finiteExp (jetOperator q x) * finiteExp (jetOperator q y) := by
  have hp : 2 < p := Fact.out
  have ht : D^(p-1) * D^(p-1) = 0 := by
    rw [← pow_add]; exact derivative_pow_vanish _ (by omega)
  rw [← jetOperator_add, finiteExp_jet, finiteExp_jet, finiteExp_jet,
    translationSeries_add]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    translationSeries_mul_top, top_mul_translationSeries, ht, smul_zero,
    map_add, add_smul, add_zero]
  abel

/-- The actual exponential representation of the additive group of `K`. -/
def originalRepresentation (q : K →ₗ[F] K) : Representation F E V where
  toFun g := (finiteExp (jetOperator q (Multiplicative.toAdd g))).restrictScalars F
  map_one' := by
    apply LinearMap.ext
    intro v
    change finiteExp (jetOperator q 0) v = v
    rw [jetOperator_zero, finiteExp_zero]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    change finiteExp (jetOperator q (Multiplicative.toAdd g + Multiplicative.toAdd h)) v =
      (finiteExp (jetOperator q (Multiplicative.toAdd g)) *
        finiteExp (jetOperator q (Multiplicative.toAdd h))) v
    rw [jetOperator_add, finiteExp_jet_add]

/-- Ordinary polynomial translations, expressed by their truncated exponential. -/
def ordinaryRepresentation : Representation F E V := originalRepresentation 0

def constantLinear : K →ₗ[K] V where
  toFun c := ⟨C c, mem_degreeLT.mpr (degree_C_le.trans_lt
    (by exact_mod_cast (Fact.out : p.Prime).pos))⟩
  map_add' _ _ := Subtype.ext (map_add C _ _)
  map_smul' _ _ := Subtype.ext (by simp)

private def fieldFintype [FiniteDimensional (ZMod p) K] : Fintype K := by
  have : Finite K := Module.finite_of_finite F
  exact Fintype.ofFinite K

private def restrictedRepresentation (q : K →ₗ[F] K) (H : Subgroup E) :
    Representation F H V := (originalRepresentation q).comp H.subtype

theorem constant_derivative (c : K) : D (constantLinear c) = 0 := by
  apply Subtype.ext
  simp [derivativeEnd, constantLinear]

theorem pow_constant (j : ℕ) (hj : 0 < j) (c : K) :
    (D^j) (constantLinear c) = 0 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  rw [pow_succ, Module.End.mul_apply, constant_derivative, map_zero]

private theorem constants_fixed (q : K →ₗ[F] K) (c : K) (g : E) :
    originalRepresentation (p := p) q g (constantLinear c) = constantLinear c := by
  classical
  have hp : 2 < p := Fact.out
  change finiteExp (jetOperator q (Multiplicative.toAdd g)) (constantLinear c) = _
  rw [finiteExp_jet]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, pow_constant (p-1) (by omega), smul_zero, add_zero,
    translationSeries, LinearMap.sum_apply]
  rw [sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [pow_constant j (Nat.pos_of_ne_zero hj)]
  · simp [show 0 < p by omega]

private def linearMonomial : V := (degreeLT.basis K p) ⟨1, by
  have : 2 < p := Fact.out; omega⟩

private theorem linearMonomial_derivative : D (linearMonomial (p := p) (K := K)) =
    constantLinear 1 := by
  apply Subtype.ext
  simp [derivativeEnd, linearMonomial, constantLinear]

private theorem linearMonomial_pow (j : ℕ) (hj : 2 ≤ j) :
    (D^j) (linearMonomial (p := p) (K := K)) = 0 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hj
  have h2 : (D^2) linearMonomial = 0 := by
    rw [pow_two, Module.End.mul_apply, linearMonomial_derivative, constant_derivative]
  rw [show 2+n=n+2 by omega, pow_add, Module.End.mul_apply, h2, map_zero]

private theorem action_linearMonomial (q : K →ₗ[F] K) (x : K) :
    originalRepresentation (p := p) q (Multiplicative.ofAdd x) linearMonomial =
      linearMonomial + constantLinear x := by
  classical
  have hp : 2 < p := Fact.out
  change finiteExp (jetOperator q x) linearMonomial = _
  rw [finiteExp_jet]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, linearMonomial_pow (p-1) (by omega), smul_zero,
    add_zero, translationSeries, LinearMap.sum_apply, LinearMap.smul_apply]
  have hsub : ({0,1} : Finset ℕ) ⊆ range p := by
    simp only [insert_subset_iff, singleton_subset_iff, mem_range]; omega
  have heq := sum_subset hsub (f := fun j : ℕ =>
    (x^j / (j.factorial : K)) • (D^j) linearMonomial) (by
      intro j hj hnot
      have hj2 : 2 ≤ j := by simp only [mem_insert, mem_singleton] at hnot; omega
      rw [linearMonomial_pow j hj2, smul_zero])
  rw [← heq]
  simp [linearMonomial_derivative, show (1:ℕ) ≠ 0 by omega, constantLinear, Polynomial.smul_eq_C_mul]

theorem faithful_action (q : K →ₗ[F] K) :
    Function.Injective (originalRepresentation (p := p) q) := by
  intro x y h
  have hv := congrArg (fun A : Module.End F V => A linearMonomial) h
  have hx := action_linearMonomial q (Multiplicative.toAdd x)
  simp only [ofAdd_toAdd] at hx
  have hy := action_linearMonomial q (Multiplicative.toAdd y)
  simp only [ofAdd_toAdd] at hy
  rw [hx, hy, add_left_cancel_iff] at hv
  have hc := congrArg (fun f : V => (f : K[X]).coeff 0) hv
  simpa [constantLinear] using hc

private theorem norm_vanish [FiniteDimensional (ZMod p) K] (q : K →ₗ[F] K) (hr : 2 ≤ finrank F K) :
    letI : Fintype K := fieldFintype (p := p) (K := K)
    (originalRepresentation (p := p) q).norm = 0 := by
  classical
  letI : Fintype K := fieldFintype (p := p) (K := K)
  have hp : 2 < p := Fact.out
  have hcard : Fintype.card K = p ^ finrank F K := by
    simpa only [ZMod.card] using ((Module.card_eq_pow_finrank (K := F) : Fintype.card K = Fintype.card F ^ finrank F K))
  have hbound : p < Fintype.card K := by
    have hpow := Nat.pow_le_pow_right (by omega : 0 < p) hr
    rw [hcard]
    nlinarith [show p^2 ≤ p^(finrank F K) from hpow]
  have hpower (j : ℕ) (hj : j < p) : ∑ x : K, x^j = 0 :=
    FiniteField.sum_pow_lt_card_sub_one K j (by omega)
  have hq : ∑ x : K, q x = 0 := by
    rw [← map_sum]
    simp [show ∑ x : K, x = 0 by simpa using hpower 1 (by omega)]
  have htrans : ∑ x : K, translationSeries (p := p) x = 0 := by
    simp only [translationSeries]
    rw [sum_comm]
    apply sum_eq_zero
    intro j hj
    rw [← sum_smul]
    simp only [div_eq_mul_inv, ← sum_mul, hpower j (mem_range.mp hj), zero_mul, zero_smul]
  have hsum : ∑ x : K, finiteExp (jetOperator (p := p) q x) = 0 := by
    simp_rw [finiteExp_jet]
    rw [sum_add_distrib, htrans, ← sum_smul, hq, zero_smul, add_zero]
  apply LinearMap.ext
  intro v
  simp only [Representation.norm, LinearMap.sum_apply, LinearMap.zero_apply]
  calc
    (∑ g : E, originalRepresentation q g v) =
        ∑ x : K, (finiteExp (jetOperator q x)) v :=
      (Fintype.sum_equiv (Multiplicative.ofAdd : K ≃ E) _ _ (fun _ => rfl)).symm
    _ = 0 := by
      simpa only [LinearMap.sum_apply, LinearMap.zero_apply] using
        congrArg (fun A : Module.End K V => A v) hsum

private theorem prime_moment (j : ℕ) (hj : j < p) :
    (∑ i : F, i^(p-2+j)) = if j = 1 then -1 else 0 := by
  classical
  have hp : 2 < p := Fact.out
  by_cases h1 : j = 1
  · subst j
    have ht (i : F) : i^(p-2+1) = 1 - if i=0 then 1 else 0 := by
      by_cases hi : i=0
      · subst i; simp [show p-2+1 ≠ 0 by omega]
      · rw [show p-2+1=p-1 by omega]
        simpa [hi, ZMod.card] using FiniteField.pow_card_sub_one_eq_one i hi
    simp_rw [ht]
    simp [sum_sub_distrib, ZMod.card, ZMod.natCast_self]
  · rw [if_neg h1]
    by_cases h0 : j = 0
    · subst j
      simpa only [Nat.add_zero] using
        FiniteField.sum_pow_lt_card_sub_one F (p-2) (by simp [ZMod.card]; omega)
    · calc
        (∑ i : F, i^(p-2+j)) = ∑ i : F, i^(j-1) := by
          apply sum_congr rfl
          intro i _
          rw [show p-2+j=p+(j-2) by omega, pow_add,
            show i^p=i by simpa only [ZMod.card] using FiniteField.pow_card i,
            ← pow_succ', show j-2+1=j-1 by omega]
        _ = 0 := FiniteField.sum_pow_lt_card_sub_one F (j-1) (by simp [ZMod.card]; omega)

private theorem cast_moment (j : ℕ) (hj : j < p) :
    (∑ i : F, (algebraMap F K i)^(p-2+j)) = if j=1 then -1 else 0 := by
  calc
    (∑ i : F, (algebraMap F K i)^(p-2+j)) =
        algebraMap F K (∑ i : F, i^(p-2+j)) := by simp only [map_sum, map_pow]
    _ = _ := by
      rw [prime_moment j hj]
      split_ifs <;> simp

private theorem weighted_translation (x : K) :
    (∑ i : F, (algebraMap F K i)^(p-2) •
      translationSeries (p := p) (algebraMap F K i * x)) = -(x • D) := by
  classical
  have hp : 2 < p := Fact.out
  simp only [translationSeries, smul_sum, smul_smul]
  rw [sum_comm]
  have hterm (j : ℕ) (hj : j ∈ range p) :
      (∑ i : F, ((algebraMap F K i)^(p-2) *
        ((algebraMap F K i * x)^j / (j.factorial : K))) • D^j) =
          if j=1 then -(x • D) else 0 := by
    rw [← sum_smul]
    have hs : (∑ i : F, (algebraMap F K i)^(p-2) *
        ((algebraMap F K i * x)^j / (j.factorial : K))) =
        (∑ i : F, (algebraMap F K i)^(p-2+j)) * (x^j/(j.factorial : K)) := by
      rw [sum_mul]
      apply sum_congr rfl
      intro i _
      simp only [pow_add, mul_pow, div_eq_mul_inv]
      ring
    rw [hs, cast_moment j (mem_range.mp hj)]
    by_cases hj1 : j=1
    · subst j; simp
    · simp [hj1]
  rw [sum_congr rfl hterm]
  simp [show 1 < p by omega]

private theorem weighted_exponential (q : K →ₗ[F] K) (x : K) :
    -(∑ i : F, (algebraMap F K i)^(p-2) •
      finiteExp (jetOperator (p := p) q (algebraMap F K i * x))) = jetOperator q x := by
  classical
  have hp : 2 < p := Fact.out
  have hq (i : F) : q (algebraMap F K i * x) = algebraMap F K i * q x := by
    simpa only [Algebra.smul_def] using q.map_smul i x
  simp_rw [finiteExp_jet, hq, smul_add, smul_smul]
  rw [sum_add_distrib, weighted_translation]
  have hs : (∑ i : F, ((algebraMap F K i)^(p-2) *
      (algebraMap F K i * q x)) • D^(p-1)) = -(q x • D^(p-1)) := by
    simp_rw [← mul_assoc, ← pow_succ]
    rw [← sum_smul, ← sum_mul, cast_moment 1 (by omega)]
    simp
  rw [hs, neg_add, neg_neg, neg_neg]
  rfl

theorem polynomial_log_action (q : K →ₗ[F] K) (x : K) (v : V) :
    -(∑ i : F, i^(p-2) • originalRepresentation (p := p) q
      (Multiplicative.ofAdd (i • x)) v) = jetOperator q x v := by
  change -(∑ i : F, i^(p-2) • (finiteExp (jetOperator q (i • x))) v) = _
  have h := congrArg (fun A : Module.End K V => A v) (weighted_exponential q x)
  simp only [LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    ← map_pow, algebraMap_smul] at h
  simpa only [← Algebra.smul_def] using h

def automorphismLinear (φ : E ≃* E) : K →ₗ[F] K :=
  ({ toFun := fun x => Multiplicative.toAdd (φ (Multiplicative.ofAdd x))
     map_zero' := by
       change Multiplicative.toAdd (φ 1) = 0
       rw [φ.map_one]; rfl
     map_add' := fun x y => congrArg Multiplicative.toAdd
       (φ.map_mul (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)) } : K →+ K).toZModLinearMap p

theorem log_intertwining (q : K →ₗ[F] K) (φ : E ≃* E) (P : V ≃ₗ[F] V)
    (hP : ∀ (g : E) (v : V), P (originalRepresentation (p := p) q g v) =
      ordinaryRepresentation (φ g) (P v)) (x : K) (v : V) :
    P (jetOperator q x v) = automorphismLinear (p := p) φ x • D (P v) := by
  rw [← polynomial_log_action q x v, map_neg, map_sum]
  simp_rw [map_smul, hP]
  have hφ (i : F) : φ (Multiplicative.ofAdd (i • x)) =
      Multiplicative.ofAdd (i • automorphismLinear (p := p) φ x) := by
    have h := (automorphismLinear (p := p) φ).map_smul i x
    exact congrArg Multiplicative.ofAdd h
  simp_rw [hφ]
  have h := polynomial_log_action (0 : K →ₗ[F] K) (automorphismLinear (p := p) φ x) (P v)
  simpa only [ordinaryRepresentation, jetOperator, LinearMap.zero_apply, zero_smul, add_zero,
    LinearMap.smul_apply] using h

private theorem scalar_ne_zero (j : ℕ) (hj0 : 0 < j) (hjp : j < p) :
    (j : K) ≠ 0 := by
  letI : CharP K p := fieldChar
  rw [Ne, CharP.cast_eq_zero_iff K p]
  exact Nat.not_dvd_of_pos_of_lt hj0 hjp

theorem derivative_kernel (v : V) (hv : D v = 0) :
    (v : K[X]) = C ((v : K[X]).coeff 0) := by
  apply Polynomial.ext
  intro n
  by_cases hn : n=0
  · subst n; simp
  have hcoeff : (v : K[X]).coeff n = 0 := by
    by_cases hnp : n < p
    · have h := congrArg (fun w : V => (w : K[X]).coeff (n-1)) hv
      change (Polynomial.derivative (v : K[X])).coeff (n-1) = 0 at h
      rw [coeff_derivative, Nat.sub_add_cancel (by omega : 1 ≤ n)] at h
      have hne : ((n-1 : ℕ) : K)+1 ≠ 0 := by
        simpa only [← Nat.cast_add_one, Nat.sub_add_cancel (by omega : 1 ≤ n)] using
          scalar_ne_zero (p := p) (K := K) n (by omega) hnp
      exact (mul_eq_zero.mp h).resolve_right hne
    · exact coeff_eq_zero_of_degree_lt ((mem_degreeLT.mp v.property).trans_le
        (by exact_mod_cast (by omega : p ≤ n)))
  simp [coeff_C, hn, hcoeff]

def dividedMonomial (j : ℕ) (hj : j < p) : K →ₗ[K] V where
  toFun s := s • ((j.factorial : K)⁻¹ • (degreeLT.basis K p) ⟨j,hj⟩)
  map_add' _ _ := add_smul _ _ _
  map_smul' _ _ := smul_assoc _ _ _

private theorem dividedMonomial_coe (j : ℕ) (hj : j < p) (s : K) :
    (dividedMonomial j hj s : K[X]) = C (s / (j.factorial : K)) * X^j := by
  simp [dividedMonomial, Polynomial.smul_eq_C_mul, div_eq_mul_inv, mul_assoc]

theorem dividedMonomial_zero (h0 : 0 < p) (s : K) :
    dividedMonomial 0 h0 s = constantLinear s := by
  apply Subtype.ext
  simp [dividedMonomial_coe, constantLinear]

theorem dividedMonomial_succ (j : ℕ) (hj : j + 1 < p) (s : K) :
    D (dividedMonomial (j+1) hj s) = dividedMonomial j (by omega) s := by
  apply Subtype.ext
  change derivative (dividedMonomial (j+1) hj s : K[X]) = _
  rw [dividedMonomial_coe, derivative_C_mul_X_pow, dividedMonomial_coe]
  simp only [Nat.add_sub_cancel, ← C_mul]
  congr 2
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hn := scalar_ne_zero (p := p) (K := K) (j+1) (by omega) hj
  field_simp

private theorem invariants_constants (q : K →ₗ[F] K) (hq1 : q 1 = 0) (v : V) :
    (∀ g : E, originalRepresentation (p := p) q g v = v) ↔
      ∃ c : K, (v : K[X]) = C c := by
  classical
  have hp : 2 < p := Fact.out
  constructor
  · intro hv
    have hs : (∑ i : F, i^(p-2)) = 0 := by
      simpa using prime_moment (p := p) 0 (by omega)
    have hl := polynomial_log_action q 1 v
    simp only [hv, ← sum_smul, hs, zero_smul, neg_zero, jetOperator, hq1,
      one_smul, zero_smul, add_zero] at hl
    exact ⟨(v : K[X]).coeff 0, derivative_kernel v hl.symm⟩
  · rintro ⟨c,hc⟩
    have hvc : v = constantLinear c := Subtype.ext hc
    subst v
    exact constants_fixed q c

private theorem nonprojective_action [FiniteDimensional (ZMod p) K] (q : K →ₗ[F] K) (hr : 2 ≤ finrank F K) :
    ¬ Module.Projective F[E] (originalRepresentation (p := p) q).asModule := by
  classical
  letI : Fintype K := fieldFintype (p := p) (K := K)
  have hgroup : IsPGroup p E := isPGroup_iff_pow_pow_eq_one.mpr (by
    intro g
    refine ⟨1, ?_⟩
    change Multiplicative.ofAdd ((p^1) • Multiplicative.toAdd g) = 1
    simp [nsmul_eq_mul, primeCast_eq_zero (p := p) (K := K)])
  intro hproj
  have hn := (PGroupProjectiveNormRing.projective_iff_projective_invariants_and_norm_surjective
    (R := F) p 1 (by omega) (by simp [ZMod.natCast_self]) hgroup
      (originalRepresentation (p := p) q)).mp hproj
  let w : (originalRepresentation (p := p) q).invariants :=
    ⟨constantLinear 1, constants_fixed q 1⟩
  obtain ⟨v,hv⟩ := hn.2 w
  rw [norm_vanish q hr] at hv
  have hc := congrArg (fun z : V => (z : K[X]).coeff 0) hv
  have : (0 : K) = 1 := by simpa [w, constantLinear] using hc
  exact zero_ne_one this

def coefficientZero : V →ₗ[K] K :=
  (Polynomial.lcoeff K 0).comp (Polynomial.degreeLT K p).subtype

def diagonalScale (c : K) (hc : c ≠ 0) : V ≃ₗ[K] V :=
  (degreeLT.basis K p).equivFun ≪≫ₗ
    (LinearEquiv.piCongrRight (fun i : Fin p =>
      LinearEquiv.smulOfNeZero K K (c^i.val) (pow_ne_zero _ hc))) ≪≫ₗ
    (degreeLT.basis K p).equivFun.symm

theorem diagonalScale_coeff (c : K) (hc : c ≠ 0) (v : V) (i : Fin p) :
    (diagonalScale c hc v : K[X]).coeff i = c^i.val * (v : K[X]).coeff i := by
  change (degreeLT.basis K p).equivFun (diagonalScale c hc v) i = _
  simp only [diagonalScale, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.piCongrRight_apply, LinearEquiv.smulOfNeZero_apply, smul_eq_mul,
    Basis.equivFun_apply, degreeLT.basis_repr]

theorem diagonalScale_derivative (c : K) (hc : c ≠ 0) (v : V) :
    diagonalScale c hc (D v) = c⁻¹ • D (diagonalScale c hc v) := by
  apply (degreeLT.basis K p).repr.injective
  apply Finsupp.ext
  intro i
  simp only [degreeLT.basis_repr, diagonalScale_coeff, Submodule.coe_smul,
    coeff_smul, smul_eq_mul]
  change c^i.val * (derivative (v : K[X])).coeff i.val =
    c⁻¹ * (derivative (diagonalScale c hc v : K[X])).coeff i.val
  simp only [coeff_derivative]
  by_cases hi : i.val+1 < p
  · rw [diagonalScale_coeff c hc v ⟨i.val+1,hi⟩]
    simp only [pow_succ]
    field_simp
  · have h0 (w : V) : (w : K[X]).coeff (i.val+1) = 0 :=
      coeff_eq_zero_of_degree_lt ((mem_degreeLT.mp w.property).trans_le
        (by exact_mod_cast (by omega : p ≤ i.val+1)))
    rw [h0, h0]; simp

theorem constant_image (P : V ≃ₗ[F] V)
    (hD : ∀ v : V, P (D v) = D (P v)) (s : K) :
    P (constantLinear s) = constantLinear (coefficientZero (P (constantLinear s))) := by
  apply Subtype.ext
  apply derivative_kernel
  rw [← hD, constant_derivative, map_zero]

def constantsEquiv (P : V ≃ₗ[F] V)
    (hD : ∀ v : V, P (D v) = D (P v)) : K ≃ₗ[F] K := by
  let f : K →ₗ[F] K := (coefficientZero.restrictScalars F).comp
    (P.toLinearMap.comp (constantLinear.restrictScalars F))
  let g : K →ₗ[F] K := (coefficientZero.restrictScalars F).comp
    (P.symm.toLinearMap.comp (constantLinear.restrictScalars F))
  have hi : ∀ v : V, P.symm (D v) = D (P.symm v) := by
    intro v
    apply P.injective
    rw [P.apply_symm_apply, hD, P.apply_symm_apply]
  refine { f with invFun := g, left_inv := ?_, right_inv := ?_ }
  · intro s
    have h := congrArg (fun v : V => coefficientZero v) (P.symm_apply_apply (constantLinear s))
    rw [constant_image P hD] at h
    simpa [f, g, coefficientZero, constantLinear] using h
  · intro s
    have h := congrArg (fun v : V => coefficientZero v) (P.apply_symm_apply (constantLinear s))
    rw [constant_image P.symm hi] at h
    simpa [f, g, coefficientZero, constantLinear] using h

private theorem dividedMonomial_power (j n : ℕ) (hjn : j + n < p) (s : K) :
    (D^n) (dividedMonomial (j+n) hjn s) = dividedMonomial j (by omega) s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply]
    have heq : D (dividedMonomial (j+(n+1)) hjn s) =
        dividedMonomial (j+n) (by omega) s := by
      simpa only [Nat.add_assoc] using
        dividedMonomial_succ (p := p) (K := K) (j+n) (by omega) s
    rw [heq]
    exact ih (by omega)

theorem dividedMonomial_top (s : K) :
    (D^(p-1)) (dividedMonomial (p-1) (by have : 2 < p := Fact.out; omega) s) =
      constantLinear s := by
  have hp : 2 < p := Fact.out
  simpa only [Nat.zero_add, dividedMonomial_zero] using
    dividedMonomial_power (p := p) (K := K) 0 (p-1) (by omega) s

theorem dividedMonomial_one_top (s : K) :
    (D^(p-1)) (dividedMonomial 1 (by have : 2 < p := Fact.out; omega) s) = 0 := by
  have hp : 2 < p := Fact.out
  have h : dividedMonomial (p := p) 1 (by omega) s = s • linearMonomial := by
    apply Subtype.ext
    simp [dividedMonomial_coe, linearMonomial, Polynomial.smul_eq_C_mul]
  rw [h, map_smul, linearMonomial_pow (p-1) (by omega), smul_zero]

/-- The same coefficient map is used for every parameter of an intertwining. -/
def constantCommutator (P : V ≃ₗ[F] V)
    (hD : ∀ v : V, P (D v) = D (P v)) : K →ₗ[F] K :=
  (constantsEquiv P hD).symm.toLinearMap.comp
    ((coefficientZero.restrictScalars F).comp
      (P.toLinearMap.comp ((dividedMonomial (p-2)
        (by have : 2 < p := Fact.out; omega)).restrictScalars F)))

/-- Extract the multiplication commutator without any scalar-linearity assumption
beyond the prime field. The extracted map is independent of `a`, `b`, and `e`. -/
theorem structural_commutator (P : V ≃ₗ[F] V)
    (hD : ∀ v : V, P (D v) = D (P v)) (a b e : K)
    (hL : ∀ v : V, P (a • D v + b • (D^(p-1)) v) = e • D (P v)) :
    ∀ s : K, a * constantCommutator P hD s - constantCommutator P hD (a*s) = b*s := by
  have hp : 2 < p := Fact.out
  let P0 : K ≃ₗ[F] K := constantsEquiv P hD
  let T : K →ₗ[F] K := (coefficientZero.restrictScalars F).comp
    (P.toLinearMap.comp ((dividedMonomial (p-2) (by omega)).restrictScalars F))
  have hconst (s : K) : P (constantLinear s) = constantLinear (P0 s) :=
    constant_image P hD s
  have h1D (s : K) : D (dividedMonomial 1 (by omega) s) = constantLinear s := by
    simpa only [dividedMonomial_zero] using dividedMonomial_succ (p := p) 0 (by omega) s
  have hsecond (s : K) : P0 (a*s) = e * P0 s := by
    have h := hL (dividedMonomial 1 (by omega) s)
    rw [h1D, dividedMonomial_one_top, smul_zero, add_zero, ← hD, h1D,
      ← (constantLinear (p := p) (K := K)).map_smul a s, hconst, hconst] at h
    have hc := congrArg (fun v : V => coefficientZero v) h
    simpa [coefficientZero, constantLinear] using hc
  have htopD (s : K) :
      D (dividedMonomial (p-1) (by omega) s) = dividedMonomial (p-2) (by omega) s := by
    simpa only [show p-2+1=p-1 by omega] using
      dividedMonomial_succ (p := p) (K := K) (p-2) (by omega) s
  have htop (s : K) : T (a*s) + P0 (b*s) = e * T s := by
    have h := hL (dividedMonomial (p-1) (by omega) s)
    rw [htopD, dividedMonomial_top, ← hD, htopD,
      ← (dividedMonomial (p-2) (by omega)).map_smul a s,
      ← (constantLinear (p := p) (K := K)).map_smul b s, map_add, hconst] at h
    have hc := congrArg (fun v : V => coefficientZero v) h
    simpa [T, coefficientZero, constantLinear] using hc
  let Q : K →ₗ[F] K := constantCommutator P hD
  have hcomm (s : K) : a * Q s - Q (a*s) = b*s := by
    apply P0.injective
    rw [map_sub, hsecond]
    change e * P0 (P0.symm (T s)) - P0 (P0.symm (T (a*s))) = P0 (b*s)
    rw [P0.apply_symm_apply, P0.apply_symm_apply]
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using (htop s).symm)
  exact hcomm

private theorem trace_structural [FiniteDimensional (ZMod p) K] (P : V ≃ₗ[F] V)
    (hD : ∀ v : V, P (D v) = D (P v)) (a b e : K)
    (hL : ∀ v : V, P (a • D v + b • (D^(p-1)) v) = e • D (P v)) :
    Algebra.trace F K b = 0 := by
  let Q := constantCommutator P hD
  have hcomm := structural_commutator P hD a b e hL
  have he : Algebra.lmul F K a * Q - Q * Algebra.lmul F K a = Algebra.lmul F K b := by
    apply LinearMap.ext
    exact hcomm
  have ht := congrArg (LinearMap.trace F K) he
  have hb : LinearMap.trace F K (Algebra.lmul F K b) = 0 := by
    simpa only [map_sub, LinearMap.trace_mul_comm, sub_self] using ht.symm
  exact hb

private theorem trace_obstruction [FiniteDimensional (ZMod p) K] (q : K →ₗ[F] K) (hq1 : q 1 = 0)
    (ha : ∃ a : K, Algebra.trace F K (q a) ≠ 0) :
    ∀ (φ : E ≃* E) (P : V ≃ₗ[F] V),
      ¬ ∀ (g : E) (v : V), P (originalRepresentation (p := p) q g v) =
        ordinaryRepresentation (φ g) (P v) := by
  intro φ P hP
  obtain ⟨a,ha⟩ := ha
  let c : K := automorphismLinear (p := p) φ 1
  have hc : c ≠ 0 := by
    intro hz
    have hφ : φ (Multiplicative.ofAdd (1 : K)) = 1 := congrArg Multiplicative.ofAdd hz
    have hx := φ.injective (hφ.trans φ.map_one.symm)
    have hh := congrArg Multiplicative.toAdd hx
    exact one_ne_zero hh
  let S : V ≃ₗ[K] V := diagonalScale c hc
  let P' : V ≃ₗ[F] V := P.trans (S.restrictScalars F)
  have hnorm (x : K) (v : V) :
      P' (jetOperator q x v) = (automorphismLinear (p := p) φ x / c) • D (P' v) := by
    change S (P (jetOperator q x v)) = _
    rw [log_intertwining q φ P hP, S.map_smul, diagonalScale_derivative]
    simp only [P', LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, smul_smul,
      div_eq_mul_inv, S]
  have hD : ∀ v : V, P' (D v) = D (P' v) := by
    intro v
    have h := hnorm 1 v
    simpa only [jetOperator, hq1, zero_smul, add_zero, one_smul, ← show c =
      automorphismLinear (p := p) φ 1 from rfl, div_self hc, one_smul] using h
  apply ha
  apply trace_structural P' hD a (q a) (automorphismLinear (p := p) φ a / c)
  intro v
  exact hnorm a v

private def exponentialPolynomial (q : K →ₗ[F] K) (x : K) : K[X] :=
  (∑ j ∈ range p, C (x^j / (j.factorial : K)) * X^j) - 1 + C (q x) * X^(p-1)

private theorem exponentialPolynomial_zero (q : K →ₗ[F] K) (x : K) :
    (exponentialPolynomial (p := p) q x).coeff 0 = 0 := by
  classical
  have hp : 2 < p := Fact.out
  simp [exponentialPolynomial, coeff_C_mul, coeff_X_pow, show 0 < p by omega,
    show (0:ℕ) ≠ p-1 by omega]

private theorem exponentialPolynomial_one (q : K →ₗ[F] K) (x : K) :
    (exponentialPolynomial (p := p) q x).coeff 1 = x := by
  classical
  have hp : 2 < p := Fact.out
  simp [exponentialPolynomial, coeff_C_mul, coeff_X_pow, show 1 < p by omega,
    show (1:ℕ) ≠ p-1 by omega, coeff_one]

private theorem exponentialPolynomial_eval (q : K →ₗ[F] K) (x : K) :
    aeval D (exponentialPolynomial (p := p) q x) =
      translationSeries x - 1 + q x • D^(p-1) := by
  classical
  simp only [exponentialPolynomial, map_add, map_sub, map_sum, map_mul, map_pow,
    aeval_C, aeval_X, map_one, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul, translationSeries]

private theorem parent_generator (q : K →ₗ[F] K) (x : K) :
    TruncatedPolynomialCyclicCriterion.cyclicAction (R := F)
      (primeCast_eq_zero (p := p) (K := K)) (exponentialPolynomial q x)
        (exponentialPolynomial_zero q x) (Multiplicative.ofAdd (1 : F)) =
      originalRepresentation q (Multiplicative.ofAdd x) := by
  change ((1 + aeval D (exponentialPolynomial q x)) ^ (1 : F).val).restrictScalars F =
    (finiteExp (jetOperator q x)).restrictScalars F
  rw [ZMod.val_one, pow_one, exponentialPolynomial_eval, finiteExp_jet]
  congr 1
  abel

private theorem reindexProjective {G H : Type*} [Group G] [Group H]
    (σ : Representation F G V) (τ : Representation F H V) (e : G ≃* H)
    (he : ∀ g, σ g = τ (e g)) [Module.Projective F[G] σ.asModule] :
    Module.Projective F[H] τ.asModule := by
  let f := (MonoidAlgebra.domCongr F F e).toRingEquiv
  letI : RingHomInvPair f.toRingHom f.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv f
  letI : RingHomInvPair f.symm.toRingHom f.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm f
  let P : σ.asModule ≃ₛₗ[f.toRingHom] τ.asModule :=
    { toFun := fun v => v
      invFun := fun v => v
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun m v => by
        change σ.asAlgebraHom m v =
          τ.asAlgebraHom ((MonoidAlgebra.domCongr F F e) m) v
        induction m using MonoidAlgebra.induction_on with
        | of g =>
          simp only [MonoidAlgebra.of_apply, MonoidAlgebra.domCongr_single,
            Representation.asAlgebraHom_single, one_smul, he]
        | add m n hm hn =>
          simp only [map_add]
          exact congrArg₂ (· + ·) hm hn
        | smul a m hm =>
          simp only [map_smul]
          exact congrArg (a • ·) hm }
  exact Module.Projective.of_equiv P

private theorem trivialProjective {H : Type*} [Group H] [Subsingleton H]
    (τ : Representation F H V) : Module.Projective F[H] τ.asModule := by
  let f : F[H] ≃+* F := (MonoidAlgebra.uniqueAlgEquiv (A := F) F H).toRingEquiv
  letI : RingHomInvPair f.toRingHom f.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv f
  letI : RingHomInvPair f.symm.toRingHom f.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm f
  let P : V ≃ₛₗ[f.symm.toRingHom] τ.asModule :=
    { toFun := fun v => v
      invFun := fun v => v
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun a v => by
        change a • v = τ.asAlgebraHom ((MonoidAlgebra.uniqueAlgEquiv F H).symm a) v
        simp [MonoidAlgebra.uniqueAlgEquiv_symm_apply, Representation.asAlgebraHom_single] }
  exact Module.Projective.of_equiv P

private theorem original_cyclic_restrictions (q : K →ₗ[F] K)
    (H : Subgroup E) (hH : IsCyclic H) :
    Module.Projective F[H] (restrictedRepresentation (p := p) q H).asModule := by
  classical
  let τ : Representation F H V := restrictedRepresentation q H
  rcases subsingleton_or_nontrivial H with htriv | hnontriv
  · letI := htriv
    exact trivialProjective τ
  · letI := hnontriv
    letI := hH
    obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := H)
    have hg1 : g ≠ 1 := by
      intro h
      obtain ⟨y,hy⟩ := exists_ne (1 : H)
      obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp (hg y)
      rw [h, one_zpow] at hn
      exact hy hn.symm
    have hpow : g^p = 1 := by
      apply Subtype.ext
      change Multiplicative.ofAdd (p • Multiplicative.toAdd (g : E)) = 1
      simp [nsmul_eq_mul, primeCast_eq_zero (p := p) (K := K)]
    have hord : orderOf g = p := orderOf_eq_prime hpow hg1
    have hcard : Nat.card H = p :=
      (orderOf_eq_card_of_forall_mem_zpowers hg).symm.trans hord
    let e : Multiplicative F ≃* H := zmodMulEquivOfGenerator hg hcard
    let x : K := Multiplicative.toAdd (g : E)
    have hx : x ≠ 0 := by
      intro hz
      apply hg1
      apply Subtype.ext
      exact congrArg Multiplicative.ofAdd hz
    let σ : Representation F (Multiplicative F) V :=
      TruncatedPolynomialCyclicCriterion.cyclicAction (R := F)
        (primeCast_eq_zero (p := p) (K := K)) (exponentialPolynomial q x)
          (exponentialPolynomial_zero q x)
    have hs : Module.Projective F[Multiplicative F] σ.asModule := by
      apply (TruncatedPolynomialCyclicCriterion.projective_iff_projective_coeff_and_isUnit_coeff_one
        (R := F) (primeCast_eq_zero (p := p) (K := K)) (exponentialPolynomial q x)
          (exponentialPolynomial_zero q x)).mpr
      refine ⟨inferInstance, ?_⟩
      rw [exponentialPolynomial_one]
      exact isUnit_iff_ne_zero.mpr hx
    letI := hs
    have hgen : σ (Multiplicative.ofAdd (1 : F)) = τ (e (Multiplicative.ofAdd (1 : F))) := by
      rw [show e (Multiplicative.ofAdd (1 : F)) = g from
        zmodMulEquivOfGenerator_apply_ofAdd_one hg hcard]
      exact parent_generator q x
    have he (i : Multiplicative F) : σ i = τ (e i) := by
      have hi : (Multiplicative.ofAdd (1 : F))^(Multiplicative.toAdd i).val = i := by
        change Multiplicative.ofAdd ((Multiplicative.toAdd i).val • (1 : F)) = i
        simpa only [nsmul_eq_mul, mul_one, ofAdd_toAdd] using
          congrArg Multiplicative.ofAdd (ZMod.natCast_zmod_val (Multiplicative.toAdd i))
      rw [← hi, map_pow, map_pow, map_pow, hgen]
    exact reindexProjective σ τ e he

/-- The full original-group higher-jet family, including arbitrary scalar-linear
intertwiners and arbitrary automorphisms of the original group. -/
theorem full_family [FiniteDimensional (ZMod p) K] (q : K →ₗ[F] K) (hq1 : q 1 = 0) (hr : 2 ≤ finrank F K) :
    Function.Injective (originalRepresentation (p := p) q) ∧
    (∀ H : Subgroup E, IsCyclic H →
      Module.Projective F[H] (restrictedRepresentation (p := p) q H).asModule) ∧
    (∀ v : V, (∀ g : E, originalRepresentation (p := p) q g v = v) ↔
      ∃ c : K, (v : K[X]) = C c) ∧
    (letI : Fintype K := fieldFintype (p := p) (K := K)
     (originalRepresentation (p := p) q).norm = 0) ∧
    ¬ Module.Projective F[E] (originalRepresentation (p := p) q).asModule ∧
    finrank F V = p * finrank F K ∧
    (∀ (x : K) (v : V),
      (ordinaryRepresentation (p := p) (Multiplicative.ofAdd x) v : K[X]) =
        (v : K[X]).comp (X + C x)) ∧
    ((∃ a : K, Algebra.trace F K (q a) ≠ 0) →
      ∀ (φ : E ≃* E) (P : V ≃ₗ[F] V),
        ¬ ∀ (g : E) (v : V), P (originalRepresentation (p := p) q g v) =
          ordinaryRepresentation (p := p) (φ g) (P v)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact faithful_action q
  · exact original_cyclic_restrictions q
  · exact invariants_constants q hq1
  · exact norm_vanish q hr
  · exact nonprojective_action q hr
  · rw [← Module.finrank_mul_finrank F K V,
      Module.finrank_eq_card_basis (Polynomial.degreeLT.basis K p), Fintype.card_fin]
    exact Nat.mul_comm _ _
  · intro x v
    change (finiteExp (jetOperator (0 : K →ₗ[F] K) x) v : K[X]) = _
    rw [finiteExp_jet]
    simp only [LinearMap.zero_apply, zero_smul, add_zero]
    exact translationSeries_taylor x v
  · exact trace_obstruction q hq1

end D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
