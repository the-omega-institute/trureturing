/- GID: D5/S3/Constants/Moments/CoefficientNewtonSums
   generality: G
   mirror-B: D5/B/S3/Constants/Moments/CoefficientNewtonSums
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Partial Newton recursion and counted root enumeration interface. -/

import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/- Search receipt, 2026-09-08, issue #6377 L1: repository PCRE searches with
   the frozen NewtonHankel criterion as positive control found no coefficient
   recursion interface. Pinned Mathlib v4.33.0 supplies Newton identities,
   Vieta, and splitting over Complex, used directly below. Loogle confirmed
   psum_eq_mul_esymm_sub_sum; anonymous GitHub code search returned HTTP 401
   and grep.app returned a security checkpoint. No ecosystem-wide absence
   claim is made.
   Pre-registered escape: strong induction identifying the well-founded
   coefficient recursion with all root power sums, including repeated roots.
   Utility, declaration by declaration (all none):
   descendingCoeff: general coefficient function, without a certification claim.
   newtonSum: general recurrence, without a certificate or bounded search.
   newton_inner_antidiagonal_sum: arbitrary finite-sum reindexing equality.
   newton_sum_zero: the defining initial value for arbitrary degree and ring.
   newton_sum_succ: the defining recurrence at arbitrary order.
   newton_sum_unique: unbounded strong induction, not a fixed instance.
   rootElementaryCoeff: general signed symmetric functions, no checker.
   map_newton_sum: arbitrary ring homomorphism compatibility, no numerical premise.
   descending_coeff_eq_root_esymm: general Vieta equality, not certification.
   exists_root_enumeration: arbitrary-degree multiset enumeration existence,
     not bounded computational enumeration of candidate solutions.
   FullHermiteMatrix: a general structure type, with no certification operation.
   TruncatedHankelMatrix: a distinct general structure type, likewise.
   fullHermiteFromMoments: general indexing construction, no positivity claim.
   truncatedHankelFromMoments: general indexing construction, no positivity claim.
   None is a certified-instance, bounded-enumeration, checker, or
   numeric-reduction. Finite calibration probes are archived separately.
   Scope: the identification of the recursion with root sums remains open;
   no parity block identity or FFC positivity theorem is claimed here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Polynomial
open scoped BigOperators

namespace D5.S3.Constants.Moments.CoefficientNewtonSums

variable {K : Type*} [CommRing K]

/-- Descending coefficients, extended by zero past the specified degree. -/
def descendingCoeff (d : Nat) (p : K[X]) (k : Nat) : K :=
  if k ≤ d then p.coeff (d - k) else 0

/-- Newton power sums computed solely from descending coefficients.
For degree `d`, supply coefficients extended by zero beyond `d`. -/
def newtonSum (d : Nat) (c : Nat -> K) : Nat -> K
  | 0 => d
  | r + 1 => -(r + 1 : K) * c (r + 1) -
      ∑ k : Fin r, c (k.val + 1) * newtonSum d c (r - k.val)
termination_by r => r
decreasing_by omega

/-- Reindex the interior Newton antidiagonal without either endpoint. -/
theorem newton_inner_antidiagonal_sum (r : Nat) (f : Nat -> Nat -> K) :
    (∑ a ∈ Finset.antidiagonal (r + 1) with a.1 ∈ Set.Ioo 0 (r + 1),
      f a.1 a.2) = ∑ k : Fin r, f (k.val + 1) (r - k.val) := by
  classical
  symm
  apply Finset.sum_bij (fun k _ => (k.val + 1, r - k.val))
  · intro k _
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo]
    omega
  · intro a _ b _ h
    apply Fin.ext
    have := congrArg Prod.fst h
    dsimp at this
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo] at ha
    refine ⟨⟨a.1 - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Prod.ext <;> dsimp <;> omega
  · intro k _
    rfl

/-- The zeroth Newton sum counts roots with multiplicity. -/
theorem newton_sum_zero (d : Nat) (c : Nat -> K) : newtonSum d c 0 = d := by
  rw [newtonSum]

/-- The coefficient recursion in a form valid both below and above the degree. -/
theorem newton_sum_succ (d r : Nat) (c : Nat -> K) :
    newtonSum d c (r + 1) = -(r + 1 : K) * c (r + 1) -
      ∑ k : Fin r, c (k.val + 1) * newtonSum d c (r - k.val) := by
  rw [newtonSum]

/-- The recursion has a unique sequence, for all orders, over any commutative ring. -/
theorem newton_sum_unique (d : Nat) (c s : Nat -> K) (hzero : s 0 = d)
    (hstep : ∀ r, s (r + 1) = -(r + 1 : K) * c (r + 1) -
      ∑ k : Fin r, c (k.val + 1) * s (r - k.val)) :
    ∀ r, newtonSum d c r = s r := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => exact (newton_sum_zero d c).trans hzero.symm
    | succ r =>
      rw [newton_sum_succ, hstep]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [ih (r - k.val) (by omega)]

/-- Signed elementary symmetric functions of a list that retains repetitions. -/
def rootElementaryCoeff {d : Nat} (roots : Fin d -> K) (k : Nat) : K :=
  (-1 : K)^k * (Finset.univ.val.map roots).esymm k

/-- Newton recursion commutes with changing the coefficient ring. -/
theorem map_newton_sum {L : Type*} [CommRing L] (f : K →+* L)
    (d : Nat) (c : Nat -> K) (r : Nat) :
    f (newtonSum d c r) = newtonSum d (fun k => f (c k)) r := by
  symm
  apply newton_sum_unique d (fun k => f (c k)) (fun r => f (newtonSum d c r))
  · simp [newton_sum_zero]
  · intro r
    simp only [newton_sum_succ, map_sub, map_mul, map_neg, map_add,
      map_natCast, map_one, map_sum]

/-- Vieta identifies all descending coefficients, including the zero tail. -/
theorem descending_coeff_eq_root_esymm {F : Type*} [Field F]
    {d : Nat} (p : F[X]) (hp : p.Monic) (hd : p.natDegree = d)
    (roots : Fin d -> F) (hroots : Finset.univ.val.map roots = p.roots) :
    descendingCoeff d p = rootElementaryCoeff roots := by
  classical
  funext k
  by_cases hk : k ≤ d
  · have hcard : p.roots.card = p.natDegree := by
      rw [← hroots, Multiset.card_map, Finset.card_val, Finset.card_univ,
        Fintype.card_fin, hd]
    have h := Polynomial.coeff_eq_esymm_roots_of_card hcard
      (k := d - k) (by omega)
    have hsub : d - (d - k) = k := by omega
    simpa [descendingCoeff, hk, rootElementaryCoeff, hp.leadingCoeff, hd, hsub,
      hroots] using h
  · have hpow : Finset.powersetCard k (Finset.univ : Finset (Fin d)) = ∅ := by
      apply Finset.powersetCard_eq_empty.mpr
      simpa using Nat.lt_of_not_ge hk
    rw [descendingCoeff, if_neg hk, rootElementaryCoeff,
      ← MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin d) F k roots]
    simp [MvPolynomial.esymm, hpow]

/-- A complex polynomial has a finite root list retaining every multiplicity. -/
theorem exists_root_enumeration (p : Complex[X]) {d : Nat} (hd : p.natDegree = d) :
    ∃ roots : Fin d -> Complex, Finset.univ.val.map roots = p.roots := by
  have hlen : p.roots.toList.length = d := by
    rw [Multiset.length_toList, ← (IsAlgClosed.splits p).natDegree_eq_card_roots, hd]
  rw [← hlen]
  exact ⟨p.roots.toList.get, by rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]⟩

/-- A complete Hermite matrix has its own type, even at a shared dimension. -/
structure FullHermiteMatrix (d : Nat) (A : Type*) where
  entries : Matrix (Fin d) (Fin d) A

/-- A truncated Hankel matrix is not a complete Hermite matrix. -/
structure TruncatedHankelMatrix (d : Nat) (A : Type*) where
  entries : Matrix (Fin d) (Fin d) A

/-- Complete moments include the constant-polynomial row and column. -/
def fullHermiteFromMoments (d : Nat) (s : Nat -> K) : FullHermiteMatrix d K :=
  ⟨fun i j => s (i.val + j.val)⟩

/-- This truncation starts at powers `X, X^2, ...`, and omits `s_0`. -/
def truncatedHankelFromMoments (d : Nat) (s : Nat -> K) : TruncatedHankelMatrix d K :=
  ⟨fun i j => s (i.val + j.val + 2)⟩

#print axioms newton_sum_unique
#print axioms map_newton_sum
#print axioms descending_coeff_eq_root_esymm
#print axioms exists_root_enumeration

end D5.S3.Constants.Moments.CoefficientNewtonSums
