/- GID: D5/S3/FiniteGroups/GroupAlgebra/TruncatedPolynomialCyclicCriterion
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/TruncatedPolynomialCyclicCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.CharP.Lemmas, mathlib/module/Mathlib.Algebra.Polynomial.Derivative, mathlib/module/Mathlib.Algebra.Polynomial.Div, mathlib/module/Mathlib.Algebra.Ring.GeomSum, mathlib/module/Mathlib.Data.ZMod.Basic, mathlib/module/Mathlib.Data.Fin.Rev, mathlib/module/Mathlib.LinearAlgebra.Matrix.ToLinearEquiv, mathlib/module/Mathlib.LinearAlgebra.Matrix.Block, mathlib/module/Mathlib.RingTheory.Polynomial.DegreeLT, mathlib/module/Mathlib.RingTheory.TensorProduct.MonoidAlgebra, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Cyclic truncated-polynomial projectivity has two intrinsic obstructions. -/

import D5.S3.FiniteGroups.GroupAlgebra.PGroupProjectiveNormRing
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.Tactic

/-! # Two intrinsic obstructions for truncated-polynomial cyclic projectivity

R and A are arbitrary commutative rings, in independent universes, with A an
R-algebra. Only (p : A) = 0 is assumed. The actual generator on degreeLT A p
is 1 + h(D), where h.coeff 0 = 0. Projectivity over R[Cp] is equivalent to
projectivity of A over R together with invertibility of h.coeff 1 in A.

Characteristic-p polynomial identities are evaluated through ZMod p -> A,
derived from (p : A) = 0 using ringChar.dvd. This does not install CharP A p
(which fails for the zero ring), CharP R p, or an invalid ZMod p -> R tower.
Sufficiency uses the actual cyclic vector X^(p-1), a triangular matrix with
unit diagonal, and the public projective tensor-product/base-change APIs.
Necessity consumes only the public finite-group coefficient and orbit-section
APIs; the p-nilpotent projectivity criterion is not used over R.

The unnormalised group norm is beta^(p-1) times the top derivative. A norm
preimage of the constant 1 forces beta to be a unit. Conversely, the chain
h(D)^i X^(p-1) gives a triangular basis and an actual regular A[Cp]-module
equivalence. Extension of scalars transfers coefficient projectivity from R
to R[Cp]. The argument includes p=2 and zero coefficient and base rings.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.TruncatedPolynomialCyclicCriterion

open Polynomial Finset
open scoped TensorProduct MonoidAlgebra

universe uR uA

variable {R : Type uR} [CommRing R] {A : Type uA} [CommRing A] [Algebra R A]
  {p : ℕ} [Fact p.Prime]

local notation "P" => Polynomial.degreeLT A p
local notation "Cp" => Multiplicative (ZMod p)

private def derivativeEnd : Module.End A P where
  toFun q := ⟨Polynomial.derivative (q : A[X]),
    Polynomial.mem_degreeLT.mpr
      (Polynomial.degree_derivative_le.trans_lt (Polynomial.mem_degreeLT.mp q.property))⟩
  map_add' _ _ := Subtype.ext (Polynomial.derivative.map_add _ _)
  map_smul' c _ := Subtype.ext (Polynomial.derivative.map_smul c _)

local notation "D" => derivativeEnd (A := A) (p := p)

-- This is the actual restriction of each A-linear operator, including its
-- multiplication (composition); no R-linear action is supplied as an input.
private def restrictEnd : Module.End A P →+* Module.End R P where
  toFun f := f.restrictScalars R
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

local notation "res" => restrictEnd (R := R) (A := A) (p := p)

private theorem derivativeEnd_pow_coe (n : ℕ) (q : P) :
    ((D ^ n) q : A[X]) = Polynomial.derivative^[n] (q : A[X]) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    change Polynomial.derivative ((D ^ n) q : A[X]) = _
    rw [ih, Function.iterate_succ_apply']

private theorem derivativeEnd_pow_prime : D ^ p = 0 := by
  apply LinearMap.ext
  intro q
  apply Subtype.ext
  simpa only [derivativeEnd_pow_coe, LinearMap.zero_apply, ZeroMemClass.coe_zero] using
    (Polynomial.iterate_derivative_eq_zero_of_degree_lt
      (Polynomial.mem_degreeLT.mp q.property))

private def constant (c : A) : P :=
  ⟨Polynomial.C c, Polynomial.mem_degreeLT.mpr
    (Polynomial.degree_C_le.trans_lt (by
      exact_mod_cast (Fact.out : p.Prime).pos))⟩

private theorem derivativeEnd_constant (c : A) : D (constant (p := p) c) = 0 := by
  apply Subtype.ext
  exact Polynomial.derivative_C

private def topMonomial : P :=
  Polynomial.degreeLT.basis A p ⟨p - 1, by have := (Fact.out : p.Prime).two_le; omega⟩

-- This formula, rather than a dimension argument, supplies the obstruction.
private theorem derivativeEnd_top_formula (q : P) :
    (D ^ (p - 1)) q =
      constant (p := p) ((((p - 1).factorial : ℕ) : A) * (q : A[X]).coeff (p - 1)) := by
  apply Subtype.ext
  rw [derivativeEnd_pow_coe]
  apply Polynomial.ext
  intro j
  cases j with
  | zero =>
    simpa [constant, Polynomial.coeff_iterate_derivative, Nat.descFactorial_self,
      nsmul_eq_mul]
  | succ n =>
    change (Polynomial.derivative^[p - 1] (q : A[X])).coeff (n + 1) =
      (C ((((p - 1).factorial : ℕ) : A) * (q : A[X]).coeff (p - 1))).coeff (n + 1)
    rw [Polynomial.coeff_C_of_ne_zero (Nat.succ_ne_zero n),
      Polynomial.coeff_iterate_derivative]
    have hz : (q : A[X]).coeff (n + 1 + (p - 1)) = 0 := by
      apply Polynomial.coeff_eq_zero_of_degree_lt
      apply (Polynomial.mem_degreeLT.mp q.property).trans_le
      exact_mod_cast (show p ≤ n + 1 + (p - 1) by
        have := (Fact.out : p.Prime).pos
        omega)
    rw [hz, smul_zero]

private theorem factor_X (h : A[X]) (h0 : h.coeff 0 = 0) : h = X * h.divX := by
  simpa only [h0, map_zero, add_zero] using (Polynomial.X_mul_divX_add h).symm

private theorem aeval_pow_prime_zero (h : A[X]) (h0 : h.coeff 0 = 0) :
    (aeval D h) ^ p = 0 := by
  calc
    (aeval D h) ^ p = aeval D (h ^ p) := (map_pow (aeval D) h p).symm
    _ = aeval D ((X : A[X]) ^ p * h.divX ^ p) := by
      conv_lhs => rw [factor_X h h0, mul_pow]
    _ = 0 := by
      simp only [map_mul, map_pow, Polynomial.aeval_X, derivativeEnd_pow_prime, zero_mul]

-- The canonical Fp -> A exists even if A is the zero ring.
private abbrev primeAlgebra (hpA : (p : A) = 0) : Algebra (ZMod p) A :=
  (ZMod.castHom (ringChar.dvd hpA) A).toAlgebra

private theorem nat_unit (hpA : (p : A) = 0) (n : ℕ)
    (hn : 0 < n) (hnp : n < p) : IsUnit (n : A) := by
  have hz : (n : ZMod p) ≠ 0 := by
    intro hz
    have hdvd := (ZMod.natCast_eq_zero_iff n p).mp hz
    have := Nat.le_of_dvd hn hdvd
    omega
  simpa only [map_natCast] using
    (isUnit_iff_ne_zero.mpr hz).map (ZMod.castHom (ringChar.dvd hpA) A)

private theorem generator_pow_prime (hpA : (p : A) = 0)
    (h : A[X]) (h0 : h.coeff 0 = 0) : (1 + aeval D h) ^ p = 1 := by
  letI : Algebra (ZMod p) A := primeAlgebra hpA
  have hf : ((1 : (ZMod p)[X]) + X) ^ p = 1 + X ^ p := by
    simpa only [one_pow] using add_pow_char (1 : (ZMod p)[X]) X p
  have he := congrArg (aeval (R := ZMod p) (aeval D h)) hf
  simpa only [map_pow, map_add, map_one, Polynomial.aeval_X,
    aeval_pow_prime_zero h h0, add_zero] using he

private theorem generator_pow_mod (hpA : (p : A) = 0)
    (h : A[X]) (h0 : h.coeff 0 = 0) (n : ℕ) :
    (1 + aeval D h) ^ (n % p) = (1 + aeval D h) ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n p]
  rw [pow_add, pow_mul, generator_pow_prime hpA h h0, one_pow, mul_one]

/-- The actual R-linear Cp action on degreeLT A p. Its distinguished generator
is 1+h(D), restricted from A-linear operators. Only p=0 in A is assumed. -/
def cyclicAction (hpA : (p : A) = 0) (h : A[X]) (h0 : h.coeff 0 = 0) :
    Representation R Cp P where
  toFun g := res ((1 + aeval D h) ^ (Multiplicative.toAdd g).val)
  map_one' := by
    change res ((1 + aeval D h) ^ (0 : ZMod p).val) = 1
    rw [ZMod.val_zero, pow_zero, map_one]
  map_mul' g l := by
    change res ((1 + aeval D h) ^ (Multiplicative.toAdd g + Multiplicative.toAdd l).val) = _
    rw [ZMod.val_add, generator_pow_mod hpA h h0, pow_add, map_mul]

private theorem cyclicAction_generator (hpA : (p : A) = 0)
    (h : A[X]) (h0 : h.coeff 0 = 0) :
    cyclicAction (R := R) hpA h h0 (Multiplicative.ofAdd (1 : ZMod p)) =
      res (1 + aeval D h) := by
  change res ((1 + aeval D h) ^ (1 : ZMod p).val) = _
  have hval : (1 : ZMod p).val = 1 := by
    simpa only [Nat.cast_one] using
      (ZMod.val_natCast_of_lt (Fact.out : p.Prime).one_lt)
  rw [hval, pow_one]

private theorem cyclicAction_norm_sum (hpA : (p : A) = 0) (h : A[X]) (h0 : h.coeff 0 = 0) :
    (cyclicAction (R := R) hpA h h0).norm = res (∑ i ∈ range p, (1 + aeval D h) ^ i) := by
  classical
  rw [map_sum]
  change (∑ g : Cp, res ((1 + aeval D h) ^ (Multiplicative.toAdd g).val)) = _
  symm
  refine Finset.sum_nbij'
    (fun i : ℕ => Multiplicative.ofAdd (i : ZMod p))
    (fun g : Cp => (Multiplicative.toAdd g).val) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_univ _
  · intro g hg
    exact Finset.mem_range.mpr (ZMod.val_lt (Multiplicative.toAdd g))
  · intro i hi
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hi)
  · intro g hg
    exact congrArg Multiplicative.ofAdd (ZMod.natCast_zmod_val (Multiplicative.toAdd g))
  · intro i hi
    dsimp only [toAdd_ofAdd]
    rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hi)]

-- Cancellation here is in Fp[X]; no cancellation in A is asserted.
private theorem norm_polynomial :
    (∑ i ∈ range p, ((1 : (ZMod p)[X]) + X) ^ i) = X ^ (p - 1) := by
  apply mul_left_cancel₀ (Polynomial.X_ne_zero : (X : (ZMod p)[X]) ≠ 0)
  have hgeom := mul_geom_sum ((1 : (ZMod p)[X]) + X) p
  have hx : (1 : (ZMod p)[X]) + X - 1 = X := by ring
  rw [hx] at hgeom
  calc
    X * (∑ i ∈ range p, ((1 : (ZMod p)[X]) + X) ^ i) = (1 + X) ^ p - 1 := hgeom
    _ = X ^ p := by rw [add_pow_char (1 : (ZMod p)[X]) X p, one_pow]; ring
    _ = X * X ^ (p - 1) := by
      rw [← pow_succ']
      congr 1
      have := (Fact.out : p.Prime).pos
      omega

private theorem cyclicAction_norm_power (hpA : (p : A) = 0)
    (h : A[X]) (h0 : h.coeff 0 = 0) :
    (cyclicAction (R := R) hpA h h0).norm = res ((aeval D h) ^ (p - 1)) := by
  rw [cyclicAction_norm_sum]
  apply congrArg res
  letI : Algebra (ZMod p) A := primeAlgebra hpA
  have he := congrArg (aeval (R := ZMod p) (aeval D h)) (norm_polynomial (p := p))
  simpa only [map_sum, map_pow, map_add, map_one, Polynomial.aeval_X] using he

private theorem aeval_top_power (h : A[X]) (h0 : h.coeff 0 = 0) :
    (aeval D h) ^ (p - 1) = h.coeff 1 ^ (p - 1) • D ^ (p - 1) := by
  have hdvd : (X : A[X]) ∣ h.divX ^ (p - 1) - (C (h.coeff 1)) ^ (p - 1) := by
    apply dvd_trans (b := h.divX - C (h.coeff 1))
    · apply Polynomial.X_dvd_iff.mpr
      simp only [coeff_sub, Polynomial.coeff_divX, zero_add, coeff_C_zero, sub_self]
    · exact sub_dvd_pow_sub_pow _ _ _
  obtain ⟨v, hv⟩ := hdvd
  have hn : p - 1 + 1 = p := by have := (Fact.out : p.Prime).pos; omega
  have heq : h ^ (p - 1) - X ^ (p - 1) * (C (h.coeff 1)) ^ (p - 1) = X ^ p * v := by
    calc
      _ = X ^ (p - 1) * (h.divX ^ (p - 1) - (C (h.coeff 1)) ^ (p - 1)) := by
        nth_rw 1 [factor_X h h0]
        rw [mul_pow]
        ring
      _ = X ^ (p - 1) * (X * v) := by rw [hv]
      _ = X ^ p * v := by rw [← mul_assoc, ← pow_succ, hn]
  have heval : aeval D (h ^ (p - 1) - X ^ (p - 1) * (C (h.coeff 1)) ^ (p - 1)) = 0 := by
    rw [heq]
    simp only [map_mul, map_pow, Polynomial.aeval_X, derivativeEnd_pow_prime, zero_mul]
  have hpower : (aeval D h) ^ (p - 1) =
      D ^ (p - 1) * (algebraMap A (Module.End A P) (h.coeff 1)) ^ (p - 1) := by
    apply sub_eq_zero.mp
    simpa only [map_sub, map_pow, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] using heval
  calc
    (aeval D h) ^ (p - 1) =
        D ^ (p - 1) * (algebraMap A (Module.End A P) (h.coeff 1)) ^ (p - 1) := hpower
    _ = D ^ (p - 1) * algebraMap A (Module.End A P) (h.coeff 1 ^ (p - 1)) := by
      rw [map_pow]
    _ = h.coeff 1 ^ (p - 1) • D ^ (p - 1) := by
      rw [Algebra.smul_def, Algebra.commutes]

private theorem cyclicAction_norm_apply (hpA : (p : A) = 0) (h : A[X]) (h0 : h.coeff 0 = 0) (q : P) :
    (cyclicAction (R := R) hpA h h0).norm q =
      constant (p := p) ((h.coeff 1 ^ (p - 1) * (((p - 1).factorial : ℕ) : A)) *
        (q : A[X]).coeff (p - 1)) := by
  rw [cyclicAction_norm_power, aeval_top_power h h0]
  change (h.coeff 1 ^ (p - 1) • (D ^ (p - 1))) q = _
  rw [LinearMap.smul_apply, derivativeEnd_top_formula]
  apply Subtype.ext
  change h.coeff 1 ^ (p - 1) • C _ = C _
  simp only [smul_eq_C_mul, ← Polynomial.C_mul, mul_assoc]

-- Coefficient bounds, rather than distinct degrees, include the zero ring.
private theorem aeval_monomial_coe (m : ℕ) (c : A) (q : P) :
    ((aeval D (monomial m c)) q : A[X]) = c • Polynomial.derivative^[m] (q : A[X]) := by
  rw [Polynomial.aeval_monomial, ← Algebra.smul_def, LinearMap.smul_apply]
  change c • ((D ^ m) q : A[X]) = _
  rw [derivativeEnd_pow_coe]

private theorem aeval_preserves_bound (f : A[X]) (q : P) (n : ℕ)
    (hq : ∀ j, n < j → (q : A[X]).coeff j = 0) :
    ∀ j, n < j → ((aeval D f) q : A[X]).coeff j = 0 := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    intro j hj
    simpa only [map_add, LinearMap.add_apply, Submodule.coe_add, coeff_add,
      hf j hj, hg j hj, add_zero]
  | monomial m c =>
    intro j hj
    rw [aeval_monomial_coe, Polynomial.coeff_smul, Polynomial.coeff_iterate_derivative,
      hq (j + m) (by omega), smul_zero, smul_zero]

private theorem aeval_top_coeff (f : A[X]) (q : P) (n : ℕ)
    (hq : ∀ j, n < j → (q : A[X]).coeff j = 0) :
    ((aeval D f) q : A[X]).coeff n = f.coeff 0 * (q : A[X]).coeff n := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    simpa only [map_add, LinearMap.add_apply, Submodule.coe_add, coeff_add,
      add_mul, hf, hg]
  | monomial m c =>
    rw [aeval_monomial_coe, Polynomial.coeff_smul, Polynomial.coeff_iterate_derivative]
    cases m with
    | zero => simp
    | succ m => simp [hq (n + (m + 1)) (by omega)]

private theorem aeval_factor (h : A[X]) (h0 : h.coeff 0 = 0) :
    aeval D h = aeval D h.divX * D := by
  conv_lhs => rw [factor_X h h0, mul_comm (X : A[X]), map_mul, Polynomial.aeval_X]

private theorem N_lowers_bound (h : A[X]) (h0 : h.coeff 0 = 0) (q : P) (n : ℕ)
    (hq : ∀ j, n + 1 < j → (q : A[X]).coeff j = 0) :
    ∀ j, n < j → ((aeval D h) q : A[X]).coeff j = 0 := by
  rw [aeval_factor h h0, Module.End.mul_apply]
  apply aeval_preserves_bound
  intro j hj
  change (Polynomial.derivative (q : A[X])).coeff j = 0
  rw [Polynomial.coeff_derivative, hq (j + 1) (by omega), zero_mul]

private theorem N_top_coeff (h : A[X]) (h0 : h.coeff 0 = 0) (q : P) (n : ℕ)
    (hq : ∀ j, n + 1 < j → (q : A[X]).coeff j = 0) :
    ((aeval D h) q : A[X]).coeff n =
      h.coeff 1 * ((n + 1 : ℕ) : A) * (q : A[X]).coeff (n + 1) := by
  rw [aeval_factor h h0, Module.End.mul_apply]
  have hD : ∀ j, n < j → (D q : A[X]).coeff j = 0 := by
    intro j hj
    change (Polynomial.derivative (q : A[X])).coeff j = 0
    rw [Polynomial.coeff_derivative, hq (j + 1) (by omega), zero_mul]
  rw [aeval_top_coeff h.divX (D q) n hD, Polynomial.coeff_divX]
  change h.coeff 1 * (Polynomial.derivative (q : A[X])).coeff n = _
  rw [Polynomial.coeff_derivative]
  push_cast
  ring

-- delta_i = beta^i (p-1)(p-2)...(p-i), with no division in A.
private def chainDiagonal (β : A) : ℕ → A
  | 0 => 1
  | i + 1 => β * (((p - 1 - i : ℕ) : A)) * chainDiagonal β i

private theorem chainDiagonal_unit (hpA : (p : A) = 0) (β : A) (hβ : IsUnit β) :
    ∀ i, i < p → IsUnit (chainDiagonal (p := p) β i) := by
  intro i
  induction i with
  | zero => intro hi; exact isUnit_one
  | succ i ih =>
    intro hi
    exact (hβ.mul (nat_unit hpA (p - 1 - i) (by omega) (by omega))).mul
      (ih (by omega))

private theorem chain_control (h : A[X]) (h0 : h.coeff 0 = 0) :
    ∀ i, i < p →
      (∀ j, p - 1 - i < j →
        (((aeval D h) ^ i) (topMonomial (A := A) (p := p)) : A[X]).coeff j = 0) ∧
      ((((aeval D h) ^ i) (topMonomial (A := A) (p := p))) : A[X]).coeff
          (p - 1 - i) = chainDiagonal (p := p) (h.coeff 1) i := by
  intro i
  induction i with
  | zero =>
    intro hi
    constructor
    · intro j hj
      simp [topMonomial, Polynomial.degreeLT.basis_val, Polynomial.coeff_X_pow,
        show ¬j = p - 1 by omega]
    · simp [topMonomial, Polynomial.degreeLT.basis_val, chainDiagonal]
  | succ i ih =>
    intro hi
    obtain ⟨hb, hc⟩ := ih (by omega)
    have hn : p - 1 - (i + 1) + 1 = p - 1 - i := by omega
    have hb' : ∀ j, p - 1 - (i + 1) + 1 < j →
        (((aeval D h) ^ i) (topMonomial (A := A) (p := p)) : A[X]).coeff j = 0 := by
      simpa only [hn] using hb
    constructor
    · intro j hj
      rw [pow_succ', Module.End.mul_apply]
      exact N_lowers_bound h h0 _ (p - 1 - (i + 1)) hb' j hj
    · rw [pow_succ', Module.End.mul_apply, N_top_coeff h h0 _ _ hb', hn, hc]
      rfl

-- This map sends X^j to N^(p-1-j) X^(p-1). Its matrix is upper triangular.
private def chainMap (h : A[X]) : P →ₗ[A] P :=
  (Polynomial.degreeLT.basis A p).constr A
    (fun j => ((aeval D h) ^ (p - 1 - j.val)) (topMonomial (A := A) (p := p)))

private theorem chainMap_bijective (hpA : (p : A) = 0)
    (h : A[X]) (h0 : h.coeff 0 = 0) (h1 : IsUnit (h.coeff 1)) :
    Function.Bijective (chainMap (p := p) h) := by
  classical
  let b := Polynomial.degreeLT.basis A p
  let M := LinearMap.toMatrix b b (chainMap (p := p) h)
  have hentry (i j : Fin p) : M i j =
      (((aeval D h) ^ (p - 1 - j.val)) (topMonomial (A := A) (p := p)) : A[X]).coeff i.val := by
    simp only [M, b, LinearMap.toMatrix_apply, chainMap, Module.Basis.constr_basis,
      Polynomial.degreeLT.basis_repr]
  have htri : M.IsUpperTriangular := by
    intro i j hji
    rw [hentry]
    have hj : p - 1 - j.val < p := by omega
    have hcut : p - 1 - (p - 1 - j.val) = j.val := by omega
    exact (chain_control h h0 _ hj).1 i.val (by rw [hcut]; exact hji)
  have hdiag (i : Fin p) : IsUnit (M i i) := by
    rw [hentry]
    have hi : p - 1 - i.val < p := by omega
    have hcut : p - 1 - (p - 1 - i.val) = i.val := by omega
    have hc := (chain_control h h0 _ hi).2
    rw [hcut] at hc
    rw [hc]
    exact chainDiagonal_unit hpA (h.coeff 1) h1 _ hi
  have hdet : IsUnit M.det := by
    rw [Matrix.det_of_isUpperTriangular htri]
    exact IsUnit.prod_univ_iff.mpr hdiag
  have he : (Matrix.toLinearEquiv b M hdet).toLinearMap = chainMap (p := p) h := by
    change Matrix.toLin b b M = chainMap (p := p) h
    exact Matrix.toLin_toMatrix b b _
  rw [← he]
  exact (Matrix.toLinearEquiv b M hdet).bijective

private def finCpEquiv : Fin p ≃ Cp where
  toFun i := Multiplicative.ofAdd (i.val : ZMod p)
  invFun g := ⟨(Multiplicative.toAdd g).val, ZMod.val_lt _⟩
  left_inv i := Fin.ext (ZMod.val_natCast_of_lt i.isLt)
  right_inv g := congrArg Multiplicative.ofAdd (ZMod.natCast_zmod_val (Multiplicative.toAdd g))

private def groupGenerator : A[Cp] :=
  MonoidAlgebra.of A Cp (Multiplicative.ofAdd (1 : ZMod p))

private theorem groupGenerator_pow (n : ℕ) :
    groupGenerator (A := A) (p := p) ^ n =
      MonoidAlgebra.of A Cp (Multiplicative.ofAdd (n : ZMod p)) := by
  rw [groupGenerator, ← map_pow]
  congr 1
  rw [← ofAdd_nsmul]
  simp

-- X^i maps to g^i. This is an ordinary basis equivalence, not a quotient axiom.
private def groupCoeffEquiv : P ≃ₗ[A] A[Cp] :=
  (Polynomial.degreeLT.basis A p).equiv
    ((MonoidAlgebra.basis Cp A).reindex (finCpEquiv (p := p)).symm) (Equiv.refl _)

private theorem groupCoeffEquiv_aeval (q : P) :
    groupCoeffEquiv q = aeval (groupGenerator (A := A) (p := p)) (q : A[X]) := by
  have heq : (groupCoeffEquiv (A := A) (p := p)).toLinearMap =
      (aeval (groupGenerator (A := A) (p := p))).toLinearMap.comp
        (Polynomial.degreeLT A p).subtype := by
    apply (Polynomial.degreeLT.basis A p).ext
    intro i
    simp [groupCoeffEquiv, Module.Basis.equiv_apply, Module.Basis.reindex_apply,
      finCpEquiv, Polynomial.degreeLT.basis_val, groupGenerator_pow, MonoidAlgebra.basis_apply]
  exact LinearMap.congr_fun heq q

private def regularOrbit (hpA : (p : A) = 0) (h : A[X]) (h0 : h.coeff 0 = 0) :
    A[Cp] →ₗ[A[Cp]] (cyclicAction (R := A) hpA h h0).asModule :=
  LinearMap.toSpanSingleton A[Cp] _
    ((cyclicAction (R := A) hpA h h0).asModuleEquiv.symm (topMonomial (A := A) (p := p)))

private def orbitLinear (hpA : (p : A) = 0) (h : A[X]) (h0 : h.coeff 0 = 0) :
    A[Cp] →ₗ[A] P :=
  (cyclicAction (R := A) hpA h h0).asModuleEquiv.toLinearMap.comp
    ((regularOrbit hpA h h0).restrictScalars A)

private theorem orbitLinear_aeval (hpA : (p : A) = 0)
    (h : A[X]) (h0 : h.coeff 0 = 0) (f : A[X]) :
    orbitLinear hpA h h0 (aeval (groupGenerator (A := A) (p := p)) f) =
      aeval (1 + aeval D h) f (topMonomial (A := A) (p := p)) := by
  let ρ := cyclicAction (R := A) hpA h h0
  have heq : ρ.asAlgebraHom.comp (aeval (groupGenerator (A := A) (p := p))) =
      aeval (1 + aeval D h) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.aeval_X, groupGenerator,
      Representation.asAlgebraHom_of]
    exact cyclicAction_generator hpA h h0
  change ρ.asAlgebraHom (aeval (groupGenerator (A := A) (p := p)) f)
    (topMonomial (A := A) (p := p)) = _
  rw [show ρ.asAlgebraHom (aeval (groupGenerator (A := A) (p := p)) f) =
    aeval (1 + aeval D h) f from DFunLike.congr_fun heq f]

-- Taylor by -1 sends X^i to (X-1)^i, so the resulting group basis is (g-1)^i.
private theorem orbit_shifted_basis (hpA : (p : A) = 0)
    (h : A[X]) (h0 : h.coeff 0 = 0) (i : Fin p) :
    orbitLinear hpA h h0
      (groupCoeffEquiv (Polynomial.taylorLinearEquiv (-1 : A) p
        (Polynomial.degreeLT.basis A p i))) =
      ((aeval D h) ^ i.val) (topMonomial (A := A) (p := p)) := by
  rw [groupCoeffEquiv_aeval, orbitLinear_aeval]
  have hz : (1 + aeval D h) + algebraMap A (Module.End A P) (-1) = aeval D h := by
    rw [map_neg, map_one]
    abel
  rw [Polynomial.taylorLinearEquiv_apply_coe]
  change aeval (1 + aeval D h)
    (Polynomial.taylor (-1 : A) ((Polynomial.degreeLT.basis A p i : P) : A[X]))
    (topMonomial (A := A) (p := p)) = _
  simp only [Polynomial.degreeLT.basis_val, Polynomial.taylor_X_pow, map_pow, map_add, Polynomial.aeval_X,
    Polynomial.aeval_C, hz]

-- An actual regular A[Cp]-module equivalence, consumed by the R[Cp] proof.
-- It is derived from the orbit map of X^(p-1), not supplied as an input.
private def regularEquiv (hpA : (p : A) = 0) (h : A[X]) (h0 : h.coeff 0 = 0)
    (h1 : IsUnit (h.coeff 1)) :
    A[Cp] ≃ₗ[A[Cp]] (cyclicAction (R := A) hpA h h0).asModule := by
  classical
  let b := Polynomial.degreeLT.basis A p
  let J : P ≃ₗ[A] A[Cp] :=
    (Polynomial.taylorLinearEquiv (-1 : A) p).trans groupCoeffEquiv
  let rev : P ≃ₗ[A] P := b.equiv b Fin.revPerm
  have heq : (orbitLinear hpA h h0).comp J.toLinearMap =
      (chainMap (p := p) h).comp rev.toLinearMap := by
    apply b.ext
    intro i
    change orbitLinear hpA h h0 (J (b i)) = chainMap (p := p) h (rev (b i))
    rw [show J (b i) = groupCoeffEquiv (Polynomial.taylorLinearEquiv (-1 : A) p (b i))
      from rfl, orbit_shifted_basis]
    simp only [rev, b, Module.Basis.equiv_apply, chainMap, Module.Basis.constr_basis,
      Fin.revPerm_apply, Fin.val_rev]
    congr 2
    omega
  have hc : Function.Bijective ((orbitLinear hpA h h0).comp J.toLinearMap) := by
    rw [heq]
    exact (chainMap_bijective hpA h h0 h1).comp rev.bijective
  have ho : Function.Bijective (orbitLinear hpA h h0) := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := J.surjective x
      obtain ⟨b, rfl⟩ := J.surjective y
      exact congrArg J (hc.1 hxy)
    · intro q
      obtain ⟨a, ha⟩ := hc.2 q
      exact ⟨J a, ha⟩
  apply LinearEquiv.ofBijective (regularOrbit hpA h h0)
  exact ⟨fun x y hxy => ho.1 (congrArg
      (cyclicAction (R := A) hpA h h0).asModuleEquiv hxy),
    fun q => by
      obtain ⟨x, hx⟩ := ho.2 ((cyclicAction (R := A) hpA h h0).asModuleEquiv q)
      exact ⟨x, (cyclicAction (R := A) hpA h h0).asModuleEquiv.injective hx⟩⟩

-- Activate coefficient extension only after constructing the A-regular module.
open scoped AlgebraMonoidAlgebra

private def regularEquivOverBase (hpA : (p : A) = 0)
    (h : A[X]) (h0 : h.coeff 0 = 0) (h1 : IsUnit (h.coeff 1)) :
    A[Cp] ≃ₗ[R[Cp]] (cyclicAction (R := R) hpA h h0).asModule := by
  let ρA := cyclicAction (R := A) hpA h h0
  let ρ := cyclicAction (R := R) hpA h h0
  let E := regularEquiv hpA h h0 h1
  let eA : A[Cp] ≃ₗ[A] P := (E.restrictScalars A).trans ρA.asModuleEquiv
  let e : A[Cp] ≃ₗ[R] P := eA.restrictScalars R
  have he (g : Cp) (z : A[Cp]) : e (MonoidAlgebra.of A Cp g * z) = ρ g (e z) := by
    have hm := congrArg ρA.asModuleEquiv (E.map_smul (MonoidAlgebra.of A Cp g) z)
    simp only [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of] at hm
    exact hm
  refine
    { toAddEquiv := e.toAddEquiv.trans ρ.asModuleEquiv.symm.toAddEquiv
      map_smul' := ?_ }
  intro x z
  apply ρ.asModuleEquiv.injective
  change e (x • z) = ρ.asAlgebraHom x (e z)
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    simpa only [Algebra.smul_def, MonoidAlgebra.algebraMap_def,
      MonoidAlgebra.of_apply, MonoidAlgebra.mapRingHom_single, map_one,
      Representation.asAlgebraHom_single_one] using he g z
  | add x y hx hy =>
    simpa only [add_smul, map_add, LinearMap.add_apply, hx, hy]
  | smul r x hx =>
    simpa only [smul_assoc, map_smul, LinearMap.smul_apply, hx]

-- This public Mathlib pushout identifies A[Cp] with R[Cp] tensor_R A as
-- R[Cp]-modules. Projective.tensorProduct tensors actual splits; no flatness.
private theorem coefficientGroup_projective (hA : Module.Projective R A) :
    Module.Projective R[Cp] A[Cp] := by
  letI : Module.Projective R A := hA
  letI : Module.Projective R[Cp] (R[Cp] ⊗[R] A) := inferInstance
  exact Module.Projective.of_equiv'
    (Algebra.IsPushout.equiv R R[Cp] A A[Cp]).toLinearEquiv

-- Narrow use of the PUBLIC orbit-section API: for a single actual invariant
-- vector, equivariance makes its image under the section constant. No private
-- norm-section theorem or private invariant/right-translation proof is used.
private theorem norm_preimage_of_projective
    {G : Type*} [Group G] [Fintype G] {V : Type*} [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) [Module.Projective R[G] ρ.asModule]
    (v : V) (hv : ∀ g, ρ g v = v) : ∃ x : V, ρ.norm x = v := by
  obtain ⟨S, hS⟩ := PGroupProjectiveNormRing.orbit_section_of_projective ρ
  have hc (g : G) : S v g = S v 1 := by
    have hg := congrFun
      (Representation.IntertwiningMap.isIntertwining ρ _ S g v)
      (1 : G)
    change S (ρ g v) 1 = S v (1 * g) at hg
    simpa only [hv g, one_mul] using hg.symm
  refine ⟨S v 1, ?_⟩
  have hsum := hS v
  change (∑ g : G, ρ g (S v g⁻¹)) = v at hsum
  simpa only [Representation.norm, LinearMap.sum_apply, hc] using hsum

private def constantLinear : A →ₗ[A] P where
  toFun := constant (p := p)
  map_add' a b := Subtype.ext (Polynomial.C_add)
  map_smul' a b := by
    apply Subtype.ext
    change C (a * b) = a • C b
    rw [Polynomial.smul_eq_C_mul, Polynomial.C_mul]

private def constantCoeff : P →ₗ[A] A :=
  (Polynomial.lcoeff A 0).comp (Polynomial.degreeLT A p).subtype

private theorem coefficient_projective (hpA : (p : A) = 0)
    (h : A[X]) (h0 : h.coeff 0 = 0)
    [Module.Projective R[Cp] (cyclicAction (R := R) hpA h h0).asModule] :
    Module.Projective R A := by
  letI : Module.Projective R P :=
    PGroupProjectiveNormRing.coefficient_projective_of_projective
      (cyclicAction (R := R) hpA h h0)
  apply Module.Projective.of_split
    ((constantLinear (A := A) (p := p)).restrictScalars R)
    ((constantCoeff (A := A) (p := p)).restrictScalars R)
  apply LinearMap.ext
  intro a
  exact Polynomial.coeff_C_zero

private theorem constants_fixed (hpA : (p : A) = 0)
    (h : A[X]) (h0 : h.coeff 0 = 0) (c : A) (g : Cp) :
    cyclicAction (R := R) hpA h h0 g (constant (p := p) c) = constant (p := p) c := by
  have hN : aeval D h (constant (p := p) c) = 0 := by
    rw [aeval_factor h h0, Module.End.mul_apply, derivativeEnd_constant, map_zero]
  have hT : (1 + aeval D h) (constant (p := p) c) = constant (p := p) c := by
    simp only [LinearMap.add_apply, Module.End.one_apply, hN, add_zero]
  change ((1 + aeval D h) ^ (Multiplicative.toAdd g).val) (constant (p := p) c) = _
  generalize (Multiplicative.toAdd g).val = n
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, hT]

/-- Over arbitrary commutative R and arbitrary commutative R-algebra A in an
independent universe, assuming only p prime and (p:A)=0, the actual action
1+h(D) on degreeLT A p is R[Cp]-projective iff A is R-projective and h.coeff 1
is a unit in A. In particular p need not vanish or be nilpotent in R. -/
theorem projective_iff_projective_coeff_and_isUnit_coeff_one
    (hpA : (p : A) = 0) (h : A[X]) (h0 : h.coeff 0 = 0) :
    Module.Projective R[Cp] (cyclicAction (R := R) hpA h h0).asModule ↔
      Module.Projective R A ∧ IsUnit (h.coeff 1) := by
  classical
  constructor
  · intro hproj
    letI : Module.Projective R[Cp] (cyclicAction (R := R) hpA h h0).asModule := hproj
    refine ⟨coefficient_projective hpA h h0, ?_⟩
    obtain ⟨q, hq⟩ := norm_preimage_of_projective
      (cyclicAction (R := R) hpA h h0) (constant (p := p) (1 : A))
      (constants_fixed hpA h h0 1)
    have hc := congrArg (fun z : P => (z : A[X]).coeff 0) hq
    rw [cyclicAction_norm_apply] at hc
    have hu : h.coeff 1 ^ (p - 1) *
        ((((p - 1).factorial : ℕ) : A) * (q : A[X]).coeff (p - 1)) = 1 := by
      simpa only [constant, Polynomial.coeff_C_zero, mul_assoc] using hc
    have hn : p - 2 + 1 = p - 1 := by
      have := (Fact.out : p.Prime).two_le
      omega
    apply isUnit_iff_exists_inv.mpr
    refine ⟨h.coeff 1 ^ (p - 2) *
      ((((p - 1).factorial : ℕ) : A) * (q : A[X]).coeff (p - 1)), ?_⟩
    rw [← mul_assoc, ← pow_succ', hn]
    exact hu
  · rintro ⟨hA, h1⟩
    letI : Module.Projective R[Cp] A[Cp] := coefficientGroup_projective hA
    exact Module.Projective.of_equiv' (regularEquivOverBase hpA h h0 h1)

end D5.S3.FiniteGroups.GroupAlgebra.TruncatedPolynomialCyclicCriterion
