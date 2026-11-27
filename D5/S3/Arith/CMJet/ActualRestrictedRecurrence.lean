/- GID: D5/S3/Arith/CMJet/ActualRestrictedRecurrence
   generality: G
   mirror-B: none(waiver:cm-jet-native-arithmetic)
   mirror-E: none(waiver:cm-jet-native-arithmetic)
   anchors: []
   utility: none
   digest: The nested CM polynomial derivation gives integral section jets and preserves their linear outer factor. -/

import D5.S3.Arith.CMJet.Integral
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Tactic

/-! Concrete polynomial extensions, integer jets, and restricted iterates. -/

noncomputable section

namespace D5.S3.Arith.CMJet.ActualRestricted

open Polynomial Finset Function
open scoped Polynomial BigOperators Differential

abbrev Base (R : Type*) [CommRing R] := Curve R
abbrev ZExt (R : Type*) [CommRing R] := (Base R)[X]
abbrev JetExt (R : Type*) [CommRing R] := (ZExt R)[X]

/-- The existing CM derivation, viewed as a derivation over the integers. -/
def baseDerivation (R : Type*) [CommRing R] :
    Derivation ℤ (Base R) (Base R) :=
  (D R).restrictScalars ℤ

instance baseDifferential (R : Type*) [CommRing R] : Differential (Base R) :=
  ⟨baseDerivation R⟩

/-- The coefficient derivation on `A[Z]`, with `Z' = 2 X²`. -/
def zSpeed (R : Type*) [CommRing R] : Base R :=
  2 * (x R) ^ 2

def zDerivation (R : Type*) [CommRing R] :
    Derivation ℤ (ZExt R) (ZExt R) :=
  Differential.implicitDeriv (C (zSpeed R))

instance zDifferential (R : Type*) [CommRing R] : Differential (ZExt R) :=
  ⟨zDerivation R⟩

/-- The outer polynomial derivation has `S' = h Z S`. -/
def sSpeed (R : Type*) [CommRing R] (h : ℤ) : ZExt R :=
  h • (X : ZExt R)

def extendedDerivation (R : Type*) [CommRing R] (h : ℤ) :
    Derivation ℤ (JetExt R) (JetExt R) :=
  Differential.implicitDeriv (C (sSpeed R h) * (X : JetExt R))

@[simp] lemma zDerivation_C (R : Type*) [CommRing R] (a : Base R) :
    zDerivation R (C a) = C (baseDerivation R a) := by
  exact Differential.implicitDeriv_C _ _

@[simp] lemma zDerivation_X (R : Type*) [CommRing R] :
    zDerivation R (X : ZExt R) = C (zSpeed R) := by
  exact Differential.implicitDeriv_X _

@[simp] lemma extendedDerivation_C (R : Type*) [CommRing R] (h : ℤ) (q : ZExt R) :
    extendedDerivation R h (C q) = C (zDerivation R q) := by
  exact Differential.implicitDeriv_C _ _

@[simp] lemma extendedDerivation_X (R : Type*) [CommRing R] (h : ℤ) :
    extendedDerivation R h (X : JetExt R) = C (sSpeed R h) * X := by
  exact Differential.implicitDeriv_X _

/-- Iterates of the concrete extension derivation. -/
def extendedIter (R : Type*) [CommRing R] (h : ℤ) (n : ℕ) :
    Module.End ℤ (JetExt R) :=
  (extendedDerivation R h).toLinearMap ^ n

lemma extendedIter_eq (R : Type*) [CommRing R] (h : ℤ) (n : ℕ) (q : JetExt R) :
    extendedIter R h n q = (extendedDerivation R h)^[n] q :=
  Module.End.pow_apply _ _ _

lemma extendedIter_zero (R : Type*) [CommRing R] (h : ℤ) (q : JetExt R) :
    extendedIter R h 0 q = q := by
  simp [extendedIter_eq]

lemma extendedIter_succ (R : Type*) [CommRing R] (h : ℤ) (n : ℕ) (q : JetExt R) :
    extendedIter R h (n + 1) q = extendedDerivation R h (extendedIter R h n q) := by
  simp [extendedIter_eq, Function.iterate_succ_apply']

lemma extendedIter_add (R : Type*) [CommRing R] (h : ℤ) (m n : ℕ) (q : JetExt R) :
    extendedIter R h (m + n) q =
      extendedIter R h m (extendedIter R h n q) := by
  simp [extendedIter_eq, Function.iterate_add_apply]

lemma s_multiple_derivative (R : Type*) [CommRing R] (h : ℤ) (q : ZExt R) :
    extendedDerivation R h (X * C q) =
      X * C (zDerivation R q + sSpeed R h * q) := by
  rw [Derivation.leibniz, extendedDerivation_X, extendedDerivation_C]
  simp only [smul_eq_mul]
  simp only [map_add, map_mul]
  ring

/-- The successive quotients by the outer variable, calculated in the coefficient ring. -/
def sectionQuotient (R : Type*) [CommRing R] (h : ℤ) (q : ZExt R) : ℕ → ZExt R
  | 0 => q
  | n + 1 =>
      zDerivation R (sectionQuotient R h q n) + sSpeed R h * sectionQuotient R h q n

theorem extendedIter_s_multiple (R : Type*) [CommRing R] (h : ℤ) (n : ℕ) (q : ZExt R) :
    extendedIter R h n (X * C q) = X * C (sectionQuotient R h q n) := by
  induction n with
  | zero => rw [extendedIter_zero, sectionQuotient]
  | succ n ih => rw [extendedIter_succ, ih, s_multiple_derivative, sectionQuotient]

theorem extendedIter_S (R : Type*) [CommRing R] (h : ℤ) (n : ℕ) :
    extendedIter R h n (X : JetExt R) = X * C (sectionQuotient R h 1 n) := by
  have hs := extendedIter_s_multiple R h n (1 : ZExt R)
  rwa [map_one, mul_one] at hs

theorem extendedIter_base (R : Type*) [CommRing R] (h : ℤ) (n : ℕ) (q : Base R) :
    extendedIter R h n (C (C q)) = C (C (iter n q)) := by
  induction n with
  | zero => rw [extendedIter_zero, iter_zero]
  | succ n ih =>
      rw [extendedIter_succ, ih, extendedDerivation_C, zDerivation_C, iter_succ]
      rfl

/-- The actual section `S * X^(2j)` in the nested polynomial extension. -/
def sectionElement (R : Type*) [CommRing R] (j : ℕ) : JetExt R :=
  X * C (C ((x R) ^ (2 * j)))

/-- Evaluation at `(X,Y,Z,S) = (0,1,0,1)`. -/
def atORingHom (R : Type*) [CommRing R] : Base R →+* R where
  toFun := atO
  map_one' := by
    norm_num [atO_apply, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_zero' := by simp [atO_apply]
  map_add' u v := by simp [atO_apply, add_left_comm, add_comm]
  map_mul' u v := atO_mul u v

def evalZ (R : Type*) [CommRing R] : ZExt R →+* R :=
  eval₂RingHom (atORingHom R) 0

def evalJet (R : Type*) [CommRing R] : JetExt R →+* R :=
  eval₂RingHom (evalZ R) 1

def jet (h n j : ℕ) : ℤ :=
  evalJet ℤ (extendedIter ℤ (h : ℤ) n (sectionElement ℤ j))

@[simp] lemma evalZ_C (R : Type*) [CommRing R] (q : Base R) :
    evalZ R (C q) = atORingHom R q := eval₂_C _ _

@[simp] lemma evalJet_C (R : Type*) [CommRing R] (q : ZExt R) :
    evalJet R (C q) = evalZ R q := eval₂_C _ _

@[simp] lemma evalJet_X (R : Type*) [CommRing R] :
    evalJet R (X : JetExt R) = 1 := eval₂_X _ _

theorem jet_zero_order (h j : ℕ) : jet h 0 j = if j = 0 then 1 else 0 := by
  have hx : atORingHom ℤ (x ℤ) = 0 := by
    change atO (x ℤ) = 0
    simp [x, atO_apply]
  rw [jet, extendedIter_zero, sectionElement, map_mul, evalJet_X, evalJet_C, evalZ_C,
    map_pow, hx, one_mul]
  cases j <;> simp

/-- The all-order binomial Leibniz formula for an actual derivation iterate. -/
lemma iterated_leibniz {R : Type*} [CommRing R] (d : Derivation ℤ R R) (n : ℕ) (u v : R) :
    d^[n] (u * v) =
      ∑ k ∈ range (n + 1), n.choose k •
        (d^[n - k] u * d^[k] v) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hshift :
          (∑ k ∈ range (n + 1), n.choose k •
              (d^[n - k + 1] u * d^[k] v)) =
          (∑ k ∈ range (n + 1), n.choose (k + 1) •
              (d^[n - k] u * d^[k + 1] v)) +
            d^[n + 1] u * v := by
        rw [sum_range_succ' _ n, Nat.choose_zero_right, Nat.sub_zero,
          Function.iterate_zero, one_nsmul]
        congr 1
        rw [sum_range_succ, Nat.choose_succ_self, zero_nsmul, add_zero]
        apply sum_congr rfl
        intro k hk
        have h := mem_range.mp hk
        rw [show n - (k + 1) + 1 = n - k by omega]
      calc
        d^[n + 1] (u * v) =
            d (∑ k ∈ range (n + 1), n.choose k •
              (d^[n - k] u * d^[k] v)) := by
          rw [Function.iterate_succ_apply', ih]
        _ = (∑ k ∈ range (n + 1), n.choose k •
              (d^[n - k + 1] u * d^[k] v)) +
            ∑ k ∈ range (n + 1), n.choose k •
              (d^[n - k] u * d^[k + 1] v) := by
          simp only [map_sum, map_nsmul, Derivation.leibniz, smul_eq_mul,
            Function.iterate_succ_apply', smul_add, sum_add_distrib, mul_comm]
        _ = ∑ k ∈ range (n + 2), (n + 1).choose k •
              (d^[(n + 1) - k] u * d^[k] v) := by
          rw [hshift, sum_range_succ' _ (n + 1), Nat.choose_zero_right,
            Nat.sub_zero, Function.iterate_zero, one_nsmul]
          simp only [Nat.choose_succ_succ, Nat.succ_sub_succ, add_nsmul,
            sum_add_distrib]
          ac_rfl

/-- In characteristic `p`, the actual `p`-fold iterate is a derivation. -/
def restrictedDerivation {R : Type*} [CommRing R] (d : Derivation ℤ R R)
    (p : ℕ) [Fact p.Prime] [CharP R p] : Derivation ℤ R R :=
  Derivation.mk' (d.toLinearMap ^ p) (by
    intro u v
    simp only [Module.End.pow_apply, smul_eq_mul]
    change d^[p] (u * v) = u * d^[p] v + v * d^[p] u
    rw [iterated_leibniz]
    have hp : p.Prime := Fact.out
    have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
    rw [sum_range_succ, Nat.choose_self, Nat.sub_self, Function.iterate_zero,
      one_nsmul]
    have hshift (f : ℕ → R) :
        (∑ k ∈ range p, f k) = (∑ k ∈ range (p - 1), f (k + 1)) + f 0 := by
      simpa only [hp1] using (sum_range_succ' f (p - 1))
    rw [hshift, Nat.choose_zero_right, Nat.sub_zero, Function.iterate_zero,
      one_nsmul]
    have hzero : (∑ k ∈ range (p - 1), p.choose (k + 1) •
        (d^[p - (k + 1)] u * d^[k + 1] v)) = 0 := by
      apply sum_eq_zero
      intro k hk
      have hklt : k < p - 1 := mem_range.mp hk
      have hkp : k + 1 < p := by omega
      have hz : (p.choose (k + 1) : R) = 0 := by
        rw [CharP.cast_eq_zero_iff R p]
        exact hp.dvd_choose_self (by omega) hkp
      rw [← Nat.cast_smul_eq_nsmul R, hz, zero_smul]
    rw [hzero, zero_add]
    simp only [id_eq]
    ring)

@[simp] lemma restrictedDerivation_apply {R : Type*} [CommRing R]
    (d : Derivation ℤ R R) (p : ℕ) [Fact p.Prime] [CharP R p] (q : R) :
    restrictedDerivation d p q = d^[p] q := by
  change (d.toLinearMap ^ p) q = d^[p] q
  exact Module.End.pow_apply _ _ _

instance baseCharP (R : Type*) [CommRing R] (p : ℕ) [CharP R p] : CharP (Base R) p :=
  charP_of_injective_algebraMap (R := R[X]) (A := Base R)
    (fun _ _ heq => by
      simpa only [QuadraticAlgebra.algebraMap_re] using congrArg QuadraticAlgebra.re heq) p

/-- The restricted derivation on the concrete residue-ring extension. -/
def extendedPrime (p : ℕ) [Fact p.Prime] (h : ℤ) :
    Derivation ℤ (JetExt (ZMod p)) (JetExt (ZMod p)) :=
  restrictedDerivation (extendedDerivation (ZMod p) h) p

@[simp] lemma extendedPrime_apply (p : ℕ) [Fact p.Prime] (h : ℤ) (q : JetExt (ZMod p)) :
    extendedPrime p h q = (extendedDerivation (ZMod p) h)^[p] q :=
  restrictedDerivation_apply _ _ _

/-- The actual restricted derivative agrees with the CM prime operator on the base. -/
theorem restricted_base (p : ℕ) [Fact p.Prime] (h : ℤ) (q : Base (ZMod p)) :
    ((extendedDerivation (ZMod p) h)^[p]) (C (C q)) = C (C (primeIter p q)) := by
  rw [← extendedIter_eq, extendedIter_base, primeIter_apply]

end D5.S3.Arith.CMJet.ActualRestricted
