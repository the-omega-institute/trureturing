/- GID: D5/S3/ContinuousObservables/IntervalSOSCompletion
   generality: G
   mirror-B: D5/B/S3/ContinuousObservables/IntervalSOSCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Interval sum of squares constructs continuous determinant-one unitary circle fields. -/

import D5.S3.ContinuousObservables.CentralWinding
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Ring.Parity
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
Copyright (c) 2026 shosonoda. All rights reserved.
Authors of the transplanted proofs: shosonoda.
Released under Apache 2.0; the full license is in
`docs/reports/licenses/auto-res-lean-qsvt-LICENSE.txt`.

Modified source: selected declarations are assembled from auto-res/lean-qsvt,
commit 42c4b9149d5957db497e4226bc02da92d10f7a3c, files Polynomial/Parity,
Polynomial/SqrtPart, QSP/Poly, QSP/PolyW and QSP/Complementary.
Namespaces, helper visibility, imports and exposition are adapted; original proof bodies
are retained. The native signed-circle matrix completion is an additional application.

The construction peels real quadratic, double-root and conjugate quartic factors,
extends cofactor nonnegativity across finitely many zeros, and inducts on the degree.
An equivalent theorem at the receiver's pinned Mathlib revision should replace this
transplant when available. No phase factorization or effective QSVT is asserted.
-/

namespace D5.S3.ContinuousObservables.IntervalSOSCompletion

open Polynomial
open scoped BigOperators

namespace Poly

def IsEven (P : ℂ[X]) : Prop := ∀ k, Odd k → P.coeff k = 0

def IsOdd (P : ℂ[X]) : Prop := ∀ k, Even k → P.coeff k = 0

def HasParity (P : ℂ[X]) (n : ℕ) : Prop :=
  (Even n → IsEven P) ∧ (Odd n → IsOdd P)

private theorem IsEven.hasParity {P : ℂ[X]} (h : IsEven P) {n : ℕ} (hn : Even n) : HasParity P n :=
  ⟨fun _ => h, fun hn' => absurd hn (Nat.not_even_iff_odd.mpr hn')⟩

private theorem IsOdd.hasParity {P : ℂ[X]} (h : IsOdd P) {n : ℕ} (hn : Odd n) : HasParity P n :=
  ⟨fun hn' => absurd hn' (Nat.not_even_iff_odd.mpr hn), fun _ => h⟩

private noncomputable def evenPart (P : ℂ[X]) : ℂ[X] :=
  ⟨⟨P.toFinsupp.coeff.filter Even⟩⟩

private noncomputable def oddPart (P : ℂ[X]) : ℂ[X] :=
  ⟨⟨P.toFinsupp.coeff.filter Odd⟩⟩

@[simp]
private theorem coeff_evenPart (P : ℂ[X]) (k : ℕ) :
    (evenPart P).coeff k = if Even k then P.coeff k else 0 := by
  simp only [evenPart, Polynomial.coeff_ofFinsupp, Finsupp.filter_apply, Polynomial.toFinsupp_apply]

@[simp]
private theorem coeff_oddPart (P : ℂ[X]) (k : ℕ) :
    (oddPart P).coeff k = if Odd k then P.coeff k else 0 := by
  simp only [oddPart, Polynomial.coeff_ofFinsupp, Finsupp.filter_apply, Polynomial.toFinsupp_apply]

private theorem evenPart_add_oddPart (P : ℂ[X]) : evenPart P + oddPart P = P := by
  ext k
  rw [coeff_add, coeff_evenPart, coeff_oddPart]
  rcases Nat.even_or_odd k with hk | hk
  · simp [hk, Nat.not_odd_iff_even.mpr hk]
  · simp [hk, Nat.not_even_iff_odd.mpr hk]

private theorem isEven_evenPart (P : ℂ[X]) : IsEven (evenPart P) := by
  intro k hk
  rw [coeff_evenPart, ite_eq_right (Nat.not_even_iff_odd.mpr hk)]

private theorem isOdd_oddPart (P : ℂ[X]) : IsOdd (oddPart P) := by
  intro k hk
  rw [coeff_oddPart, ite_eq_right (Nat.not_odd_iff_even.mpr hk)]

private theorem oddPart_eq_of_add {P E O : ℂ[X]} (hE : IsEven E) (hO : IsOdd O) (h : E + O = P) :
    oddPart P = O := by
  ext k
  rw [coeff_oddPart, ← h, coeff_add]
  rcases Nat.even_or_odd k with hk | hk
  · rw [ite_eq_right (Nat.not_odd_iff_even.mpr hk), hO k hk]
  · rw [ite_eq_left hk, hE k hk, zero_add]

private theorem isEven_zero : IsEven (0 : ℂ[X]) := fun _ _ => Polynomial.coeff_zero _

private theorem isOdd_zero : IsOdd (0 : ℂ[X]) := fun _ _ => Polynomial.coeff_zero _

private theorem isEven_C (a : ℂ) : IsEven (C a) := by
  intro k hk
  rw [Polynomial.coeff_C, ite_eq_right]
  rintro rfl
  exact (Nat.not_even_iff_odd.mpr hk) ⟨0, rfl⟩

private theorem isOdd_X : IsOdd (X : ℂ[X]) := by
  intro k hk
  rw [Polynomial.coeff_X]
  split_ifs with h
  · subst h
    exact absurd hk (by decide)
  · rfl

private theorem IsEven.add {P Q : ℂ[X]} (hP : IsEven P) (hQ : IsEven Q) : IsEven (P + Q) := by
  intro k hk
  rw [Polynomial.coeff_add, hP k hk, hQ k hk, add_zero]

private theorem IsOdd.add {P Q : ℂ[X]} (hP : IsOdd P) (hQ : IsOdd Q) : IsOdd (P + Q) := by
  intro k hk
  rw [Polynomial.coeff_add, hP k hk, hQ k hk, add_zero]

private theorem IsEven.sub {P Q : ℂ[X]} (hP : IsEven P) (hQ : IsEven Q) : IsEven (P - Q) := by
  intro k hk
  rw [Polynomial.coeff_sub, hP k hk, hQ k hk, sub_zero]

private theorem IsOdd.sub {P Q : ℂ[X]} (hP : IsOdd P) (hQ : IsOdd Q) : IsOdd (P - Q) := by
  intro k hk
  rw [Polynomial.coeff_sub, hP k hk, hQ k hk, sub_zero]

private theorem IsEven.C_mul {P : ℂ[X]} (hP : IsEven P) (a : ℂ) : IsEven (C a * P) := by
  intro k hk
  rw [Polynomial.coeff_C_mul, hP k hk, mul_zero]

private theorem IsOdd.C_mul {P : ℂ[X]} (hP : IsOdd P) (a : ℂ) : IsOdd (C a * P) := by
  intro k hk
  rw [Polynomial.coeff_C_mul, hP k hk, mul_zero]

private theorem IsEven.X_mul {P : ℂ[X]} (hP : IsEven P) : IsOdd (X * P) := by
  intro k hk
  rcases k with _ | m
  · exact Polynomial.coeff_X_mul_zero P
  · rw [Polynomial.coeff_X_mul]
    exact hP m (Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hk))

private theorem IsOdd.X_mul {P : ℂ[X]} (hP : IsOdd P) : IsEven (X * P) := by
  intro k hk
  rcases k with _ | m
  · exact absurd hk (by decide)
  · rw [Polynomial.coeff_X_mul]
    exact hP m (Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hk))

private theorem IsEven.one_sub_X_sq_mul {P : ℂ[X]} (hP : IsEven P) : IsEven ((1 - X ^ 2) * P) := by
  have h : (1 - X ^ 2) * P = P - X * (X * P) := by ring
  rw [h]
  exact hP.sub hP.X_mul.X_mul

private theorem IsOdd.one_sub_X_sq_mul {P : ℂ[X]} (hP : IsOdd P) : IsOdd ((1 - X ^ 2) * P) := by
  have h : (1 - X ^ 2) * P = P - X * (X * P) := by ring
  rw [h]
  exact hP.sub hP.X_mul.X_mul

private theorem hasParity_zero (n : ℕ) : HasParity (0 : ℂ[X]) n :=
  ⟨fun _ => isEven_zero, fun _ => isOdd_zero⟩

private theorem hasParity_C (a : ℂ) : HasParity (C a) 0 :=
  (isEven_C a).hasParity (by decide)

private theorem hasParity_X : HasParity (X : ℂ[X]) 1 :=
  isOdd_X.hasParity odd_one

private theorem HasParity.add {P Q : ℂ[X]} {n : ℕ} (hP : HasParity P n) (hQ : HasParity Q n) :
    HasParity (P + Q) n :=
  ⟨fun hn => (hP.1 hn).add (hQ.1 hn), fun hn => (hP.2 hn).add (hQ.2 hn)⟩

private theorem HasParity.sub {P Q : ℂ[X]} {n : ℕ} (hP : HasParity P n) (hQ : HasParity Q n) :
    HasParity (P - Q) n :=
  ⟨fun hn => (hP.1 hn).sub (hQ.1 hn), fun hn => (hP.2 hn).sub (hQ.2 hn)⟩

private theorem HasParity.C_mul {P : ℂ[X]} {n : ℕ} (hP : HasParity P n) (a : ℂ) :
    HasParity (C a * P) n :=
  ⟨fun hn => (hP.1 hn).C_mul a, fun hn => (hP.2 hn).C_mul a⟩

private theorem HasParity.X_mul {P : ℂ[X]} {n : ℕ} (hP : HasParity P n) : HasParity (X * P) (n + 1) :=
  ⟨fun hn => (hP.2 (Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hn))).X_mul,
    fun hn => (hP.1 (Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hn))).X_mul⟩

private theorem HasParity.add_two {P : ℂ[X]} {n : ℕ} (hP : HasParity P n) : HasParity P (n + 2) :=
  ⟨fun hn => hP.1 ((Nat.even_add.mp hn).mpr even_two),
    fun hn => hP.2 ((Nat.odd_add.mp hn).mpr even_two)⟩

private noncomputable def evenRoot (P : ℂ[X]) : ℂ[X] := contract 2 P

private noncomputable def oddRoot (P : ℂ[X]) : ℂ[X] := contract 2 P.divX

@[simp]
private theorem coeff_evenRoot (P : ℂ[X]) (k : ℕ) : (evenRoot P).coeff k = P.coeff (2 * k) := by
  rw [evenRoot, coeff_contract two_ne_zero, mul_comm]

@[simp]
private theorem coeff_oddRoot (P : ℂ[X]) (k : ℕ) : (oddRoot P).coeff k = P.coeff (2 * k + 1) := by
  rw [oddRoot, coeff_contract two_ne_zero, coeff_divX, mul_comm]

private theorem coeff_comp_X_sq (R : ℂ[X]) (k : ℕ) :
    (R.comp (X ^ 2)).coeff k = if 2 ∣ k then R.coeff (k / 2) else 0 := by
  rw [← expand_eq_comp_X_pow, coeff_expand two_pos]

private theorem coeff_comp_X_sq_of_odd (R : ℂ[X]) {k : ℕ} (hk : Odd k) :
    (R.comp (X ^ 2)).coeff k = 0 := by
  rw [coeff_comp_X_sq, ite_eq_right]
  exact fun h => (Nat.not_even_iff_odd.mpr hk) (even_iff_two_dvd.mpr h)

private theorem isEven_comp_X_sq (R : ℂ[X]) : IsEven (R.comp (X ^ 2)) :=
  fun _ hk => coeff_comp_X_sq_of_odd R hk

private theorem isOdd_X_mul_comp_X_sq (R : ℂ[X]) : IsOdd (X * R.comp (X ^ 2)) :=
  (isEven_comp_X_sq R).X_mul

private theorem IsEven.eq_expand_evenRoot {P : ℂ[X]} (h : IsEven P) : P = expand ℂ 2 (evenRoot P) := by
  ext k
  rw [coeff_expand two_pos, coeff_evenRoot]
  split_ifs with hk
  · rw [Nat.mul_div_cancel' hk]
  · exact h k (Nat.not_even_iff_odd.mp fun he => hk (even_iff_two_dvd.mp he))

private theorem IsEven.eq_evenRoot_comp {P : ℂ[X]} (h : IsEven P) : P = (evenRoot P).comp (X ^ 2) := by
  rw [← expand_eq_comp_X_pow]
  exact h.eq_expand_evenRoot

private theorem IsOdd.eq_X_mul_expand_oddRoot {P : ℂ[X]} (h : IsOdd P) :
    P = X * expand ℂ 2 (oddRoot P) := by
  ext k
  rcases k with _ | m
  · rw [coeff_X_mul_zero]
    exact h 0 (by decide)
  · rw [coeff_X_mul, coeff_expand two_pos, coeff_oddRoot]
    split_ifs with hm
    · rw [Nat.mul_div_cancel' hm]
    · exact h (m + 1) (Nat.even_add_one.mpr fun he => hm (even_iff_two_dvd.mp he))

private theorem IsOdd.eq_X_mul_oddRoot_comp {P : ℂ[X]} (h : IsOdd P) :
    P = X * (oddRoot P).comp (X ^ 2) := by
  rw [← expand_eq_comp_X_pow]
  exact h.eq_X_mul_expand_oddRoot

private theorem isEven_iff_exists_comp_X_sq {P : ℂ[X]} : IsEven P ↔ ∃ R : ℂ[X], P = R.comp (X ^ 2) :=
  ⟨fun h => ⟨_, h.eq_evenRoot_comp⟩, fun ⟨R, hR⟩ => hR ▸ isEven_comp_X_sq R⟩

private theorem isOdd_iff_exists_X_mul_comp_X_sq {P : ℂ[X]} :
    IsOdd P ↔ ∃ R : ℂ[X], P = X * R.comp (X ^ 2) :=
  ⟨fun h => ⟨_, h.eq_X_mul_oddRoot_comp⟩, fun ⟨R, hR⟩ => hR ▸ isOdd_X_mul_comp_X_sq R⟩

private theorem IsEven.eval_eq {P : ℂ[X]} (h : IsEven P) (x : ℂ) :
    P.eval x = (evenRoot P).eval (x ^ 2) := by
  conv_lhs => rw [h.eq_expand_evenRoot]
  rw [expand_eval]

end Poly

open D5.S3.ContinuousObservables.IntervalSOSCompletion.Poly Complex Topology Filter

private noncomputable def conjP (P : ℂ[X]) : ℂ[X] := P.map (starRingEnd ℂ)

private theorem eval_conjP (P : ℂ[X]) (z : ℂ) :
    (conjP P).eval z = (starRingEnd ℂ) (P.eval ((starRingEnd ℂ) z)) := by
  rw [conjP, Polynomial.eval_map]
  conv_lhs => rw [← Complex.conj_conj z]
  exact Polynomial.eval₂_hom _ _

namespace Poly

private theorem HasParity.one_sub_X_sq_mul {P : ℂ[X]} {n : ℕ} (hP : HasParity P n) :
    HasParity ((1 - X ^ 2) * P) n :=
  ⟨fun hn => (hP.1 hn).one_sub_X_sq_mul, fun hn => (hP.2 hn).one_sub_X_sq_mul⟩

end Poly

open D5.S3.ContinuousObservables.IntervalSOSCompletion.Poly Complex Topology Filter

@[simp]
private theorem coeff_conjP (P : ℂ[X]) (m : ℕ) : (conjP P).coeff m = (starRingEnd ℂ) (P.coeff m) :=
  Polynomial.coeff_map _ _

namespace Poly

private theorem IsEven.mul {P Q : ℂ[X]} (hP : IsEven P) (hQ : IsEven Q) : IsEven (P * Q) := by
  obtain ⟨R, rfl⟩ := isEven_iff_exists_comp_X_sq.mp hP
  obtain ⟨S, rfl⟩ := isEven_iff_exists_comp_X_sq.mp hQ
  rw [← mul_comp]
  exact isEven_comp_X_sq _

private theorem IsEven.mul_isOdd {P Q : ℂ[X]} (hP : IsEven P) (hQ : IsOdd Q) : IsOdd (P * Q) := by
  obtain ⟨R, rfl⟩ := isEven_iff_exists_comp_X_sq.mp hP
  obtain ⟨S, rfl⟩ := isOdd_iff_exists_X_mul_comp_X_sq.mp hQ
  rw [show R.comp (X ^ 2) * (X * S.comp (X ^ 2)) = X * (R * S).comp (X ^ 2) by
    rw [mul_comp]; ring]
  exact isOdd_X_mul_comp_X_sq _

private theorem IsOdd.mul_isEven {P Q : ℂ[X]} (hP : IsOdd P) (hQ : IsEven Q) : IsOdd (P * Q) := by
  rw [mul_comm]
  exact hQ.mul_isOdd hP

private theorem IsOdd.mul {P Q : ℂ[X]} (hP : IsOdd P) (hQ : IsOdd Q) : IsEven (P * Q) := by
  obtain ⟨R, rfl⟩ := isOdd_iff_exists_X_mul_comp_X_sq.mp hP
  obtain ⟨S, rfl⟩ := isOdd_iff_exists_X_mul_comp_X_sq.mp hQ
  rw [show X * R.comp (X ^ 2) * (X * S.comp (X ^ 2)) = (X * (R * S)).comp (X ^ 2) by
    rw [mul_comp, mul_comp, X_comp]; ring]
  exact isEven_comp_X_sq _

private theorem HasParity.mul {P Q : ℂ[X]} {m n : ℕ} (hP : HasParity P m) (hQ : HasParity Q n) :
    HasParity (P * Q) (m + n) := by
  rcases Nat.even_or_odd m with hm | hm <;> rcases Nat.even_or_odd n with hn | hn
  · exact ((hP.1 hm).mul (hQ.1 hn)).hasParity (hm.add hn)
  · exact ((hP.1 hm).mul_isOdd (hQ.2 hn)).hasParity (hm.add_odd hn)
  · exact ((hP.2 hm).mul_isEven (hQ.1 hn)).hasParity (hm.add_even hn)
  · exact ((hP.2 hm).mul (hQ.2 hn)).hasParity (hm.add_odd hn)

private theorem HasParity.of_X_mul_X_mul {P : ℂ[X]} {n : ℕ} (h : HasParity (X * (X * P)) n) :
    HasParity P n := by
  refine ⟨fun hn k hk => ?_, fun hn k hk => ?_⟩
  · have := h.1 hn (k + 1 + 1) (by rw [add_assoc]; exact hk.add_even even_two)
    rwa [coeff_X_mul, coeff_X_mul] at this
  · have := h.2 hn (k + 1 + 1) (by rw [add_assoc]; exact hk.add even_two)
    rwa [coeff_X_mul, coeff_X_mul] at this

private theorem HasParity.of_X_mul {P : ℂ[X]} {n : ℕ} (h : HasParity (X * P) (n + 1)) :
    HasParity P n := by
  refine ⟨fun hn k hk => ?_, fun hn k hk => ?_⟩
  · have := h.2 hn.add_one (k + 1) hk.add_one
    rwa [coeff_X_mul] at this
  · have := h.1 hn.add_one (k + 1) hk.add_one
    rwa [coeff_X_mul] at this

private theorem IsEven.of_mul_left {F G : ℂ[X]} (hF : IsEven F) (hF0 : F ≠ 0) (hFG : IsEven (F * G)) :
    IsEven G := by
  have hdecomp : F * evenPart G + F * oddPart G = F * G := by
    rw [← mul_add, evenPart_add_oddPart]
  have hodd : oddPart (F * G) = F * oddPart G :=
    oddPart_eq_of_add (hF.mul (isEven_evenPart G)) (hF.mul_isOdd (isOdd_oddPart G)) hdecomp
  have hzero : oddPart (F * G) = 0 := oddPart_eq_of_add hFG isOdd_zero (add_zero _)
  rw [hzero] at hodd
  have hG : oddPart G = 0 := (mul_eq_zero.mp hodd.symm).resolve_left hF0
  have h := evenPart_add_oddPart G
  rw [hG, add_zero] at h
  rw [← h]
  exact isEven_evenPart G

private theorem IsEven.eval_neg {P : ℂ[X]} (hP : IsEven P) (z : ℂ) : P.eval (-z) = P.eval z := by
  rw [hP.eval_eq, hP.eval_eq, neg_sq]

end Poly

open D5.S3.ContinuousObservables.IntervalSOSCompletion.Poly Complex Topology Filter

private theorem conjP_map_algebraMap (P : ℝ[X]) :
    conjP (P.map (algebraMap ℝ ℂ)) = P.map (algebraMap ℝ ℂ) := by
  ext k
  rw [coeff_conjP, coeff_map, Complex.coe_algebraMap, Complex.conj_ofReal]

private theorem eval_map_algebraMap_ofReal (P : ℝ[X]) (x : ℝ) :
    (P.map (algebraMap ℝ ℂ)).eval (x : ℂ) = ((P.eval x : ℝ) : ℂ) := by
  change (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ x) = algebraMap ℝ ℂ (P.eval x)
  rw [eval_map, eval₂_at_apply]

private theorem natDegree_le_natDegree_X_mul (P : ℝ[X]) : P.natDegree ≤ (X * P).natDegree := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  · rw [natDegree_X_mul hP]
    omega

private def SOSRep (k : ℕ) (A : ℝ[X]) : Prop :=
  ∃ B C : ℝ[X], A = B ^ 2 + (1 - X ^ 2) * C ^ 2 ∧ B.natDegree ≤ k ∧ (X * C).natDegree ≤ k ∧
    HasParity (B.map (algebraMap ℝ ℂ)) k ∧ HasParity (X * C.map (algebraMap ℝ ℂ)) k

private theorem sumsq_mul_sumsq {R : Type*} [CommRing R] (w B₁ C₁ B₂ C₂ : R) :
    (B₁ ^ 2 + w * C₁ ^ 2) * (B₂ ^ 2 + w * C₂ ^ 2) =
      (B₁ * B₂ - w * (C₁ * C₂)) ^ 2 + w * (B₁ * C₂ + B₂ * C₁) ^ 2 := by
  ring

private theorem SOSRep.mul {k₁ k₂ : ℕ} {A₁ A₂ : ℝ[X]} (h₁ : SOSRep k₁ A₁) (h₂ : SOSRep k₂ A₂) :
    SOSRep (k₁ + k₂) (A₁ * A₂) := by
  obtain ⟨B₁, C₁, rfl, hB₁, hC₁, pB₁, pC₁⟩ := h₁
  obtain ⟨B₂, C₂, rfl, hB₂, hC₂, pB₂, pC₂⟩ := h₂
  refine ⟨B₁ * B₂ - (1 - X ^ 2) * (C₁ * C₂), B₁ * C₂ + B₂ * C₁, sumsq_mul_sumsq _ _ _ _ _,
    ?_, ?_, ?_, ?_⟩
  · have h1 : ((1 - X ^ 2) * (C₁ * C₂)).natDegree ≤ k₁ + k₂ := by
      rw [show (1 - X ^ 2) * (C₁ * C₂) = C₁ * C₂ - (X * C₁) * (X * C₂) by ring]
      refine (natDegree_sub_le _ _).trans (max_le ?_ (natDegree_mul_le_of_le hC₁ hC₂))
      exact natDegree_mul_le_of_le ((natDegree_le_natDegree_X_mul C₁).trans hC₁)
        ((natDegree_le_natDegree_X_mul C₂).trans hC₂)
    exact (natDegree_sub_le _ _).trans (max_le (natDegree_mul_le_of_le hB₁ hB₂) h1)
  · rw [show X * (B₁ * C₂ + B₂ * C₁) = B₁ * (X * C₂) + B₂ * (X * C₁) by ring]
    exact natDegree_add_le_of_degree_le (natDegree_mul_le_of_le hB₁ hC₂)
      ((natDegree_mul_le_of_le hB₂ hC₁).trans (by omega))
  · simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one, Polynomial.map_pow,
      Polynomial.map_X]
    refine (pB₁.mul pB₂).sub (HasParity.one_sub_X_sq_mul (HasParity.of_X_mul_X_mul ?_))
    rw [show X * (X * (C₁.map (algebraMap ℝ ℂ) * C₂.map (algebraMap ℝ ℂ))) =
      (X * C₁.map (algebraMap ℝ ℂ)) * (X * C₂.map (algebraMap ℝ ℂ)) by ring]
    exact pC₁.mul pC₂
  · simp only [Polynomial.map_add, Polynomial.map_mul]
    rw [show X * (B₁.map (algebraMap ℝ ℂ) * C₂.map (algebraMap ℝ ℂ) +
        B₂.map (algebraMap ℝ ℂ) * C₁.map (algebraMap ℝ ℂ)) =
      B₁.map (algebraMap ℝ ℂ) * (X * C₂.map (algebraMap ℝ ℂ)) +
        B₂.map (algebraMap ℝ ℂ) * (X * C₁.map (algebraMap ℝ ℂ)) by ring]
    refine (pB₁.mul pC₂).add ?_
    rw [Nat.add_comm k₁ k₂]
    exact pB₂.mul pC₁

private theorem SOSRep.succ {k : ℕ} {A : ℝ[X]} (h : SOSRep k A) : SOSRep (k + 1) A := by
  obtain ⟨B, C, rfl, hB, hC, pB, pC⟩ := h
  refine ⟨X * B - (1 - X ^ 2) * C, B + X * C, by ring, ?_, ?_, ?_, ?_⟩
  · rw [show X * B - (1 - X ^ 2) * C = X * B - C + X * (X * C) by ring]
    refine natDegree_add_le_of_degree_le ((natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_
    · exact (natDegree_mul_le_of_le natDegree_X_le hB).trans (by omega)
    · exact ((natDegree_le_natDegree_X_mul C).trans hC).trans (by omega)
    · exact (natDegree_mul_le_of_le natDegree_X_le hC).trans (by omega)
  · rw [show X * (B + X * C) = X * B + X * (X * C) by ring]
    exact natDegree_add_le_of_degree_le ((natDegree_mul_le_of_le natDegree_X_le hB).trans
      (by omega)) ((natDegree_mul_le_of_le natDegree_X_le hC).trans (by omega))
  · simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one, Polynomial.map_pow,
      Polynomial.map_X]
    exact pB.X_mul.sub (HasParity.one_sub_X_sq_mul (HasParity.of_X_mul_X_mul pC.X_mul))
  · simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X]
    rw [mul_add]
    exact pB.X_mul.add pC.X_mul

private theorem sosRep_C_of_nonneg {a : ℝ} (ha : 0 ≤ a) : SOSRep 0 (C a) := by
  refine ⟨C (Real.sqrt a), 0, ?_, (natDegree_C _).le, by simp, ?_, ?_⟩
  · rw [← C_pow, Real.sq_sqrt ha]
    ring
  · rw [Polynomial.map_C]
    exact hasParity_C _
  · rw [Polynomial.map_zero, mul_zero]
    exact hasParity_zero _

private theorem sosRep_quad (v : ℝ) : SOSRep 1 (C |1 - v| * X ^ 2 + C |v| * (1 - X ^ 2)) := by
  refine ⟨C (Real.sqrt |1 - v|) * X, C (Real.sqrt |v|), ?_, ?_, ?_, ?_, ?_⟩
  · rw [mul_pow, ← C_pow, Real.sq_sqrt (abs_nonneg _), ← C_pow, Real.sq_sqrt (abs_nonneg _)]
    ring
  · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  · compute_degree
  · rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
    exact hasParity_X.C_mul _
  · rw [Polynomial.map_C]
    exact (hasParity_C _).X_mul

private theorem sosRep_sq (r : ℝ) : SOSRep 2 ((X ^ 2 - C r) ^ 2) := by
  refine ⟨X ^ 2 - C r, 0, by ring, by compute_degree, by simp, ?_, ?_⟩
  · rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, sq]
    exact hasParity_X.X_mul.sub (hasParity_C _).add_two
  · rw [Polynomial.map_zero, mul_zero]
    exact hasParity_zero _

private noncomputable def quartic (a : ℂ) : ℝ[X] :=
  X ^ 4 - C (2 * a.re) * X ^ 2 + C (Complex.normSq a)

private theorem quartic_map (a : ℂ) :
    (quartic a).map (algebraMap ℝ ℂ) = (X ^ 2 - C a) * (X ^ 2 - C ((starRingEnd ℂ) a)) := by
  simp only [quartic, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Complex.coe_algebraMap]
  rw [← Complex.add_conj, ← Complex.mul_conj, C_add, C_mul]
  ring

private theorem eval_quartic (a : ℂ) (x : ℝ) :
    (quartic a).eval x = (x ^ 2 - a.re) ^ 2 + a.im ^ 2 := by
  simp only [quartic, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, Complex.normSq_apply]
  ring

private theorem sosRep_quartic (a : ℂ) : SOSRep 2 (quartic a) := by
  set m := ‖a‖ with hm
  set n := ‖a - 1‖ with hn
  have hn2 : n ^ 2 = m ^ 2 + 1 - 2 * a.re := by
    rw [hn, hm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub, Complex.normSq_one, map_one,
      mul_one]
  have h1 : 1 ≤ m + n := by
    have h := abs_norm_sub_norm_le a 1
    rw [norm_one, ← hm, ← hn] at h
    linarith [neg_abs_le (m - 1)]
  have hγ : Real.sqrt ((m + n) ^ 2 - 1) ^ 2 = (m + n) ^ 2 - 1 :=
    Real.sq_sqrt (by nlinarith)
  refine ⟨C (m + n) * X ^ 2 - C m, C (Real.sqrt ((m + n) ^ 2 - 1)) * X, ?_, by compute_degree,
    by compute_degree, ?_, ?_⟩
  · have hγ' : (C (Real.sqrt ((m + n) ^ 2 - 1)) : ℝ[X]) ^ 2 = (C m + C n) ^ 2 - 1 := by
      rw [← C_pow, hγ, C_sub, C_pow, C_add, C_1]
    have hn' : (C n : ℝ[X]) ^ 2 = C m ^ 2 + 1 - C 2 * C a.re := by
      rw [← C_pow, hn2, C_sub, C_add, C_pow, C_1, C_mul]
    rw [quartic, Complex.normSq_eq_norm_sq, ← hm, C_pow, C_add, C_mul]
    linear_combination (X ^ 4 - X ^ 2) * hγ' - X ^ 2 * hn'
  · rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, sq]
    exact (hasParity_X.X_mul.C_mul _).sub (hasParity_C _).add_two
  · rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      show X * (C ((algebraMap ℝ ℂ) (Real.sqrt ((m + n) ^ 2 - 1))) * X) =
        C ((algebraMap ℝ ℂ) (Real.sqrt ((m + n) ^ 2 - 1))) * (X * X) by ring]
    exact hasParity_X.X_mul.C_mul _

private theorem eval_nonneg_of_eventually_nhdsGT (D : ℝ[X]) (s : ℝ)
    (h : ∀ᶠ x in 𝓝[>] s, 0 ≤ D.eval x) : 0 ≤ D.eval s :=
  ge_of_tendsto (tendsto_nhdsWithin_of_tendsto_nhds (D.continuous.tendsto s)) h

private theorem eval_nonneg_of_eventually_nhdsLT (D : ℝ[X]) (s : ℝ)
    (h : ∀ᶠ x in 𝓝[<] s, 0 ≤ D.eval x) : 0 ≤ D.eval s :=
  ge_of_tendsto (tendsto_nhdsWithin_of_tendsto_nhds (D.continuous.tendsto s)) h

private theorem eval_nonneg_of_nonneg_off_finite (D : ℝ[X]) {S : Set ℝ} (hS : S.Finite)
    (h : ∀ x ∈ Set.Icc (-1 : ℝ) 1, x ∉ S → 0 ≤ D.eval x) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ D.eval x := by
  intro s hs
  by_cases hsS : s ∈ S
  · have hS' : ∀ᶠ x in 𝓝[≠] s, x ∉ S := by
      have : ∀ᶠ x in 𝓝[≠] s, ∀ t ∈ S, x ≠ t := by
        rw [eventually_all_finite hS]
        intro t ht
        rcases eq_or_ne s t with rfl | hst
        · exact eventually_mem_nhdsWithin.mono fun x hx => hx
        · exact eventually_ne_nhdsWithin hst
      exact this.mono fun x hx hxS => hx x hxS rfl
    rcases lt_or_eq_of_le hs.2 with hs1 | hs1
    · apply eval_nonneg_of_eventually_nhdsGT
      have h2 : ∀ᶠ x in 𝓝[>] s, x ∉ S :=
        hS'.filter_mono (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
      filter_upwards [Ioo_mem_nhdsGT hs1, h2] with x hx1 hx2
      exact h x ⟨by linarith [hs.1, hx1.1], hx1.2.le⟩ hx2
    · apply eval_nonneg_of_eventually_nhdsLT
      have h2 : ∀ᶠ x in 𝓝[<] s, x ∉ S :=
        hS'.filter_mono (nhdsWithin_mono _ fun x hx => ne_of_lt hx)
      filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < s by linarith), h2] with x hx1 hx2
      exact h x ⟨hx1.1.le, by linarith [hx1.2]⟩ hx2
  · exact h s hs hsS

private theorem eval_nonneg_of_mul_nonneg {F G : ℝ[X]} {S : Set ℝ} (hS : S.Finite)
    (hF : ∀ x ∈ Set.Icc (-1 : ℝ) 1, x ∉ S → 0 < F.eval x)
    (hFG : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ (F * G).eval x) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ G.eval x :=
  eval_nonneg_of_nonneg_off_finite G hS fun x hx hxS => by
    have h := hFG x hx
    rw [eval_mul] at h
    exact nonneg_of_mul_nonneg_right h (hF x hx hxS)

private theorem X_sub_C_sq_dvd_of_nonneg {A : ℝ[X]} (hA : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ A.eval x)
    {r : ℝ} (hr : r ∈ Set.Ioo (-1 : ℝ) 1) (hroot : A.IsRoot r) : (X - C r) ^ 2 ∣ A := by
  rcases eq_or_ne A 0 with rfl | hA0
  · exact dvd_zero _
  obtain ⟨D, hD, hDr⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd A hA0 r
  rw [dvd_iff_isRoot] at hDr
  have hm : 0 < rootMultiplicity r A := (rootMultiplicity_pos hA0).mpr hroot
  rcases Nat.lt_or_ge (rootMultiplicity r A) 2 with h2 | h2
  · exfalso
    have hm1 : rootMultiplicity r A = 1 := by omega
    rw [hm1, pow_one] at hD
    have key : ∀ x, A.eval x = (x - r) * D.eval x := fun x => by
      rw [hD, eval_mul, eval_sub, eval_X, eval_C]
    have hpos : 0 ≤ D.eval r := by
      apply eval_nonneg_of_eventually_nhdsGT
      filter_upwards [Ioo_mem_nhdsGT hr.2] with x hx
      have h := hA x ⟨by linarith [hr.1, hx.1], hx.2.le⟩
      rw [key] at h
      exact nonneg_of_mul_nonneg_right h (by linarith [hx.1])
    have hneg : 0 ≤ (-D).eval r := by
      apply eval_nonneg_of_eventually_nhdsLT
      filter_upwards [Ioo_mem_nhdsLT hr.1] with x hx
      have h := hA x ⟨hx.1.le, by linarith [hx.2, hr.2]⟩
      rw [key, show (x - r) * D.eval x = (r - x) * (-D).eval x by rw [eval_neg]; ring] at h
      exact nonneg_of_mul_nonneg_right h (by linarith [hx.2])
    rw [eval_neg] at hneg
    exact hDr (IsRoot.def.mpr (le_antisymm (by linarith) hpos))
  · exact (pow_dvd_pow _ h2).trans (Dvd.intro D hD.symm)

private theorem X_sq_sub_C_dvd_of_isRoot {P : ℂ[X]} {s : ℂ} (hs0 : s ≠ 0) (h1 : P.IsRoot s)
    (h2 : P.IsRoot (-s)) : X ^ 2 - C (s ^ 2) ∣ P := by
  have hcop : IsCoprime (X - C s) (X - C (-s)) := by
    apply isCoprime_X_sub_C_of_isUnit_sub
    rw [sub_neg_eq_add]
    exact isUnit_iff_ne_zero.mpr fun h => hs0 (by linear_combination h / 2)
  have h := hcop.mul_dvd (dvd_iff_isRoot.mpr h1) (dvd_iff_isRoot.mpr h2)
  rwa [show (X - C s) * (X - C (-s)) = X ^ 2 - C (s ^ 2) by rw [C_neg, C_pow]; ring] at h

private theorem isRoot_neg_of_isEven {A : ℝ[X]} (hAe : IsEven (A.map (algebraMap ℝ ℂ))) {s : ℂ}
    (hs : (A.map (algebraMap ℝ ℂ)).IsRoot s) : (A.map (algebraMap ℝ ℂ)).IsRoot (-s) := by
  rw [IsRoot.def, hAe.eval_neg]
  exact hs.eq_zero

private theorem isRoot_conj_of_map {A : ℝ[X]} {s : ℂ} (hs : (A.map (algebraMap ℝ ℂ)).IsRoot s) :
    (A.map (algebraMap ℝ ℂ)).IsRoot ((starRingEnd ℂ) s) := by
  have h := eval_conjP (A.map (algebraMap ℝ ℂ)) ((starRingEnd ℂ) s)
  rw [conjP_map_algebraMap, Complex.conj_conj] at h
  rw [IsRoot.def, h, hs.eq_zero, map_zero]

private theorem cofactor_props {A F G : ℝ[X]} (hAe : IsEven (A.map (algebraMap ℝ ℂ))) (hA0 : A ≠ 0)
    (hA : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ A.eval x) (hFe : IsEven (F.map (algebraMap ℝ ℂ)))
    (hAFG : A = F * G) {S : Set ℝ} (hS : S.Finite)
    (hF : ∀ x ∈ Set.Icc (-1 : ℝ) 1, x ∉ S → 0 < F.eval x) :
    G.natDegree + F.natDegree = A.natDegree ∧ IsEven (G.map (algebraMap ℝ ℂ)) ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ G.eval x := by
  have hF0 : F ≠ 0 := fun h => hA0 (by rw [hAFG, h, zero_mul])
  have hG0 : G ≠ 0 := fun h => hA0 (by rw [hAFG, h, mul_zero])
  refine ⟨by rw [hAFG, natDegree_mul hF0 hG0, add_comm], ?_, ?_⟩
  · refine hFe.of_mul_left ((Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).mpr hF0) ?_
    rw [← Polynomial.map_mul, ← hAFG]
    exact hAe
  · exact eval_nonneg_of_mul_nonneg hS hF fun x hx => by rw [← hAFG]; exact hA x hx

private theorem exists_factor_of_isRoot {A : ℝ[X]} (hAe : IsEven (A.map (algebraMap ℝ ℂ))) (hA0 : A ≠ 0)
    (hA : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ A.eval x) {s : ℂ}
    (hs : (A.map (algebraMap ℝ ℂ)).IsRoot s) :
    ∃ j : ℕ, ∃ F G : ℝ[X], 0 < j ∧ SOSRep j F ∧ A = F * G ∧
      G.natDegree + 2 * j ≤ A.natDegree ∧ IsEven (G.map (algebraMap ℝ ℂ)) ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ G.eval x := by
  have hinj := (algebraMap ℝ ℂ).injective
  have hs' : (A.map (algebraMap ℝ ℂ)).IsRoot (-s) := isRoot_neg_of_isEven hAe hs
  by_cases him : (s ^ 2).im = 0
  · -- `s²` is real
    set v := (s ^ 2).re with hv
    have hsv : s ^ 2 = (v : ℂ) := Complex.ext (by simp [hv]) (by simp [him])
    by_cases hv01 : 0 < v ∧ v < 1
    · -- Case I: `s = ±r` real with `0 < r² < 1`: double roots `±r`, factor `(X² - r²)²`
      have hsim : s.im = 0 := by
        have h2 : s.re * s.im = 0 := by
          have h := him
          rw [sq, Complex.mul_im] at h
          linarith
        rcases mul_eq_zero.mp h2 with h | h
        · exfalso
          have hv' : v = -(s.im ^ 2) := by
            rw [hv, sq, Complex.mul_re, h]
            ring
          nlinarith [hv01.1, sq_nonneg s.im]
        · exact h
      set r := s.re with hr
      have hsr : s = (r : ℂ) := Complex.ext (by simp [hr]) (by simp [hsim])
      have hr2 : r ^ 2 = v := by
        have h := congrArg Complex.re hsv
        rw [hsr, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_re] at h
        exact h
      have hrI : r ∈ Set.Ioo (-1 : ℝ) 1 := by
        rw [Set.mem_Ioo, ← abs_lt, ← sq_lt_one_iff_abs_lt_one, hr2]
        exact hv01.2
      have hr0 : r ≠ 0 := by
        intro h
        rw [h, zero_pow two_ne_zero] at hr2
        linarith [hv01.1]
      have hrootr : A.IsRoot r := by
        have h := hs.eq_zero
        rw [hsr, eval_map_algebraMap_ofReal, Complex.ofReal_eq_zero] at h
        exact h
      have hrootr' : A.IsRoot (-r) := by
        have h := hs'.eq_zero
        rw [hsr, ← Complex.ofReal_neg, eval_map_algebraMap_ofReal, Complex.ofReal_eq_zero] at h
        exact h
      have hd1 := X_sub_C_sq_dvd_of_nonneg hA hrI hrootr
      have hd2 := X_sub_C_sq_dvd_of_nonneg hA
        (by rw [Set.mem_Ioo] at hrI ⊢; constructor <;> linarith [hrI.1, hrI.2]) hrootr'
      have hcop : IsCoprime ((X - C r) ^ 2) ((X - C (-r)) ^ 2) := by
        refine IsCoprime.pow (isCoprime_X_sub_C_of_isUnit_sub ?_)
        rw [sub_neg_eq_add]
        exact isUnit_iff_ne_zero.mpr fun h => hr0 (by linarith)
      obtain ⟨G, hG⟩ := hcop.mul_dvd hd1 hd2
      rw [show (X - C r) ^ 2 * (X - C (-r)) ^ 2 = (X ^ 2 - C (r ^ 2)) ^ 2 by
        rw [C_neg, C_pow]; ring] at hG
      have hFe : IsEven (((X ^ 2 - C (r ^ 2)) ^ 2).map (algebraMap ℝ ℂ)) := by
        rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
          Polynomial.map_C]
        exact isEven_iff_exists_comp_X_sq.mpr
          ⟨(X - C ((algebraMap ℝ ℂ) (r ^ 2))) ^ 2, by rw [pow_comp, sub_comp, X_comp, C_comp]⟩
      have hFpos : ∀ x ∈ Set.Icc (-1 : ℝ) 1, x ∉ ({r, -r} : Set ℝ) →
          0 < ((X ^ 2 - C (r ^ 2)) ^ 2).eval x := by
        intro x _ hxS
        simp only [eval_pow, eval_sub, eval_X, eval_C]
        have hne : x ^ 2 - r ^ 2 ≠ 0 := by
          intro h
          rcases eq_or_eq_neg_of_sq_eq_sq x r (by linarith) with h | h <;> simp [h] at hxS
        exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
      obtain ⟨hdeg, hGe, hGnn⟩ := cofactor_props hAe hA0 hA hFe hG (Set.toFinite _) hFpos
      refine ⟨2, _, G, two_pos, sosRep_sq _, hG, ?_, hGe, hGnn⟩
      have h4 : ((X ^ 2 - C (r ^ 2)) ^ 2 : ℝ[X]).natDegree = 4 := by compute_degree!
      omega
    · -- Case II: `v = s² ≤ 0` or `v ≥ 1`: the quadratic factor `±(X² - v)` (GSLW (10), (11))
      have hv' : v ≤ 0 ∨ 1 ≤ v := by
        rcases le_or_gt v 0 with h | h
        · exact Or.inl h
        · exact Or.inr (le_of_not_gt fun h1 => hv01 ⟨h, h1⟩)
      have hdvd : X ^ 2 - C v ∣ A := by
        rcases eq_or_ne s 0 with hs0 | hs0
        · have hv0 : v = 0 := by rw [hv, hs0, zero_pow two_ne_zero, Complex.zero_re]
          have h0 : A.IsRoot 0 := by
            have h := hs.eq_zero
            rw [hs0, ← Complex.ofReal_zero, eval_map_algebraMap_ofReal] at h
            exact IsRoot.def.mpr (by exact_mod_cast h)
          have h := X_sub_C_sq_dvd_of_nonneg hA (by norm_num) h0
          rw [C_0, sub_zero] at h
          rw [hv0, C_0, sub_zero]
          exact h
        · have h := X_sq_sub_C_dvd_of_isRoot hs0 hs hs'
          have hmap : (X ^ 2 - C v).map (algebraMap ℝ ℂ) = X ^ 2 - C (v : ℂ) := by
            rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
              Complex.coe_algebraMap]
          rw [hsv, ← hmap] at h
          exact (map_dvd_map _ hinj (monic_X_pow_sub_C v two_ne_zero)).mp h
      obtain ⟨G₀, hG₀⟩ := hdvd
      obtain ⟨ε, hε1, hFε⟩ : ∃ ε : ℝ, ε * ε = 1 ∧
          C |1 - v| * X ^ 2 + C |v| * (1 - X ^ 2) = C ε * (X ^ 2 - C v) := by
        rcases hv' with hv0 | hv1
        · refine ⟨1, one_mul 1, ?_⟩
          rw [abs_of_nonneg (by linarith), abs_of_nonpos hv0, C_sub, C_1, C_neg]
          ring
        · refine ⟨-1, by norm_num, ?_⟩
          rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
          simp only [C_neg, C_sub, C_1]
          ring
      have hAFG : A = (C |1 - v| * X ^ 2 + C |v| * (1 - X ^ 2)) * (C ε * G₀) := by
        rw [hFε, hG₀]
        have hεε : (C ε : ℝ[X]) * C ε = 1 := by rw [← C_mul, hε1, C_1]
        linear_combination (-(X ^ 2 - C v) * G₀) * hεε
      have hFe : IsEven ((C |1 - v| * X ^ 2 + C |v| * (1 - X ^ 2)).map (algebraMap ℝ ℂ)) := by
        rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
          Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sub,
          Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
        exact isEven_iff_exists_comp_X_sq.mpr
          ⟨C ((algebraMap ℝ ℂ) |1 - v|) * X + C ((algebraMap ℝ ℂ) |v|) * (1 - X), by
            simp only [add_comp, mul_comp, C_comp, X_comp, sub_comp, one_comp]⟩
      have hFpos : ∀ x ∈ Set.Icc (-1 : ℝ) 1, x ∉ ({-1, 0, 1} : Set ℝ) →
          0 < (C |1 - v| * X ^ 2 + C |v| * (1 - X ^ 2)).eval x := by
        intro x hx hxS
        simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one]
        have h1 : 0 ≤ |1 - v| * x ^ 2 := mul_nonneg (abs_nonneg _) (sq_nonneg _)
        have h2 : 0 ≤ |v| * (1 - x ^ 2) :=
          mul_nonneg (abs_nonneg _) (by nlinarith [hx.1, hx.2])
        rcases h1.lt_or_eq with h1 | h1
        · linarith
        rcases h2.lt_or_eq with h2 | h2
        · linarith
        exfalso
        rcases mul_eq_zero.mp h1.symm with ha | hx0
        · have hv1 : v = 1 := by
            have := abs_eq_zero.mp ha
            linarith
          rcases mul_eq_zero.mp h2.symm with hb | hx1
          · rw [abs_eq_zero] at hb
            linarith
          · rcases eq_or_eq_neg_of_sq_eq_sq x 1 (by linarith) with h | h <;> simp [h] at hxS
        · have hx0' : x = 0 := pow_eq_zero_iff two_ne_zero |>.mp hx0
          simp [hx0'] at hxS
      obtain ⟨-, hGe, hGnn⟩ := cofactor_props hAe hA0 hA hFe hAFG (Set.toFinite _) hFpos
      refine ⟨1, _, C ε * G₀, one_pos, sosRep_quad v, hAFG, ?_, hGe, hGnn⟩
      have hG₀0 : G₀ ≠ 0 := fun h => hA0 (by rw [hG₀, h, mul_zero])
      have h1 : A.natDegree = 2 + G₀.natDegree := by
        rw [hG₀, natDegree_mul (monic_X_pow_sub_C v two_ne_zero).ne_zero hG₀0,
          natDegree_X_pow_sub_C]
      have h2 := natDegree_C_mul_le ε G₀
      omega
  · -- Case III: `s²` is not real: the quartic factor `(X² - s²)(X² - s̄²)` (GSLW (12))
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact him (by rw [zero_pow two_ne_zero, Complex.zero_im])
    have hsc : (A.map (algebraMap ℝ ℂ)).IsRoot ((starRingEnd ℂ) s) := isRoot_conj_of_map hs
    have hsc' : (A.map (algebraMap ℝ ℂ)).IsRoot (-(starRingEnd ℂ) s) :=
      isRoot_neg_of_isEven hAe hsc
    have hd1 : X ^ 2 - C (s ^ 2) ∣ A.map (algebraMap ℝ ℂ) := X_sq_sub_C_dvd_of_isRoot hs0 hs hs'
    have hd2 : X ^ 2 - C ((starRingEnd ℂ) (s ^ 2)) ∣ A.map (algebraMap ℝ ℂ) := by
      have h := X_sq_sub_C_dvd_of_isRoot
        ((map_ne_zero_iff _ (RingHom.injective _)).mpr hs0) hsc hsc'
      rwa [← map_pow] at h
    have hne : (starRingEnd ℂ) (s ^ 2) - s ^ 2 ≠ 0 := by
      intro h
      exact him (Complex.conj_eq_iff_im.mp (sub_eq_zero.mp h))
    have hcop : IsCoprime (X ^ 2 - C (s ^ 2)) (X ^ 2 - C ((starRingEnd ℂ) (s ^ 2))) := by
      refine ⟨C ((starRingEnd ℂ) (s ^ 2) - s ^ 2)⁻¹, -C ((starRingEnd ℂ) (s ^ 2) - s ^ 2)⁻¹, ?_⟩
      rw [show C ((starRingEnd ℂ) (s ^ 2) - s ^ 2)⁻¹ * (X ^ 2 - C (s ^ 2)) +
          -C ((starRingEnd ℂ) (s ^ 2) - s ^ 2)⁻¹ * (X ^ 2 - C ((starRingEnd ℂ) (s ^ 2))) =
          C (((starRingEnd ℂ) (s ^ 2) - s ^ 2)⁻¹ * ((starRingEnd ℂ) (s ^ 2) - s ^ 2)) by
        rw [C_mul, C_sub]; ring]
      rw [inv_mul_cancel₀ hne, C_1]
    have hmonic : (quartic (s ^ 2)).Monic := by
      unfold quartic
      monicity!
    obtain ⟨G, hG⟩ : quartic (s ^ 2) ∣ A := by
      have h := hcop.mul_dvd hd1 hd2
      rw [← quartic_map] at h
      exact (map_dvd_map _ hinj hmonic).mp h
    have hFe : IsEven ((quartic (s ^ 2)).map (algebraMap ℝ ℂ)) := by
      rw [quartic_map]
      exact isEven_iff_exists_comp_X_sq.mpr
        ⟨(X - C (s ^ 2)) * (X - C ((starRingEnd ℂ) (s ^ 2))), by
          simp only [mul_comp, sub_comp, X_comp, C_comp]⟩
    have hFpos : ∀ x ∈ Set.Icc (-1 : ℝ) 1, x ∉ (∅ : Set ℝ) → 0 < (quartic (s ^ 2)).eval x := by
      intro x _ _
      rw [eval_quartic]
      have h := lt_of_le_of_ne (sq_nonneg (s ^ 2).im) (Ne.symm (pow_ne_zero 2 him))
      nlinarith [sq_nonneg (x ^ 2 - (s ^ 2).re)]
    obtain ⟨hdeg, hGe, hGnn⟩ := cofactor_props hAe hA0 hA hFe hG Set.finite_empty hFpos
    refine ⟨2, _, G, two_pos, sosRep_quartic _, hG, ?_, hGe, hGnn⟩
    have h4 : (quartic (s ^ 2)).natDegree = 4 := by
      unfold quartic
      compute_degree!
    omega

private theorem sosRep_of_nonneg (k : ℕ) :
    ∀ A : ℝ[X], IsEven (A.map (algebraMap ℝ ℂ)) → A.natDegree ≤ 2 * k →
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ A.eval x) → SOSRep k A := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro A hAe hAd hA
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hAd0 : A.natDegree ≤ 0 := by simpa using hAd
    rw [eq_C_of_natDegree_le_zero hAd0]
    apply sosRep_C_of_nonneg
    rw [coeff_zero_eq_eval_zero]
    exact hA 0 ⟨by norm_num, by norm_num⟩
  · by_cases hlow : A.natDegree ≤ 2 * (k - 1)
    · have h := (ih (k - 1) (by omega) A hAe hlow hA).succ
      rwa [Nat.sub_add_cancel hk] at h
    · have hA0 : A ≠ 0 := fun h => hlow (by rw [h, natDegree_zero]; exact Nat.zero_le _)
      have hpos : 0 < (A.map (algebraMap ℝ ℂ)).degree := by
        rw [← natDegree_pos_iff_degree_pos,
          natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]
        omega
      obtain ⟨s, hs⟩ := Complex.exists_root hpos
      obtain ⟨j, F, G, hj, hF, hAFG, hdeg, hGe, hGnn⟩ := exists_factor_of_isRoot hAe hA0 hA hs
      have hjk : j ≤ k := by omega
      have h := hF.mul (ih (k - j) (by omega) G hGe (by omega) hGnn)
      rwa [← hAFG, Nat.add_sub_cancel' hjk] at h

private theorem natDegree_le_pred_of_X_mul {C : ℝ[X]} {k : ℕ} (h : (X * C).natDegree ≤ k) :
    C.natDegree ≤ k - 1 ∧ (k = 0 → C = 0) := by
  rcases eq_or_ne C 0 with rfl | hC
  · simp
  · rw [natDegree_X_mul hC] at h
    exact ⟨by omega, fun hk => absurd h (by omega)⟩

private theorem hasParity_pred_of_X_mul {C : ℂ[X]} {k : ℕ} (h : HasParity (X * C) k) (hC : k = 0 → C = 0) :
    HasParity C (k - 1) := by
  rcases k with _ | n
  · rw [hC rfl]
    exact hasParity_zero _
  · rw [Nat.add_sub_cancel]
    exact h.of_X_mul

theorem exists_sumsq_decomposition (k : ℕ) (A : ℝ[X]) (hAe : IsEven (A.map (algebraMap ℝ ℂ)))
    (hAd : A.natDegree ≤ 2 * k) (hA : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ A.eval x) :
    ∃ B C : ℝ[X], A = B ^ 2 + (1 - X ^ 2) * C ^ 2 ∧ B.natDegree ≤ k ∧ C.natDegree ≤ k - 1 ∧
      (k = 0 → C = 0) ∧ HasParity (B.map (algebraMap ℝ ℂ)) k ∧
      HasParity (C.map (algebraMap ℝ ℂ)) (k - 1) := by
  obtain ⟨B, C, hABC, hB, hC, pB, pC⟩ := sosRep_of_nonneg k A hAe hAd hA
  obtain ⟨hC', hC0⟩ := natDegree_le_pred_of_X_mul hC
  exact ⟨B, C, hABC, hB, hC', hC0, pB,
    hasParity_pred_of_X_mul pC fun hk => by rw [hC0 hk, Polynomial.map_zero]⟩

open D5.S3.ContinuousObservables.CentralWinding

private def completionMatrix (a b c : ℝ) : Matrix (ZMod 2) (ZMod 2) ℂ :=
  fun i j => if i = 0 then
    if j = 0 then (a : ℂ) + Complex.I * (b : ℂ) else Complex.I * (c : ℂ)
  else if j = 0 then Complex.I * (c : ℂ) else (a : ℂ) - Complex.I * (b : ℂ)

/-- Signed-circle completion: the off-diagonal uses `Im z`, not its absolute value. -/
noncomputable def phaseCompletion (p B C : ℝ[X]) : CyclicObservable 2 :=
  ⟨fun t => completionMatrix (p.eval (windingPhase t).re)
      (B.eval (windingPhase t).re) ((windingPhase t).im * C.eval (windingPhase t).re), by
    have hx := Complex.continuous_re.comp windingPhase.continuous
    have hy := Complex.continuous_im.comp windingPhase.continuous
    have hp := Complex.continuous_ofReal.comp (p.continuous.comp hx)
    have hB := Complex.continuous_ofReal.comp (B.continuous.comp hx)
    have hC := Complex.continuous_ofReal.comp (hy.mul (C.continuous.comp hx))
    apply continuous_matrix
    intro i j
    simp only [completionMatrix]
    split_ifs <;> fun_prop⟩

private theorem completion_matrix_laws (a b c : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 = 1) :
    let M := completionMatrix a b c
    star M * M = 1 ∧ M * star M = 1 ∧ M.det = 1 ∧ (M 0 0).re = a := by
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  have cases2 (i : ZMod 2) : i = 0 ∨ i = 1 := by
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Matrix.ext
    intro i j
    simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply]
    rcases cases2 i with rfl | rfl <;> rcases cases2 j with rfl | rfl <;>
      simp [hu, completionMatrix] <;> apply Complex.ext <;> norm_num <;> nlinarith [h]
  · apply Matrix.ext
    intro i j
    simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply]
    rcases cases2 i with rfl | rfl <;> rcases cases2 j with rfl | rfl <;>
      simp [hu, completionMatrix] <;> apply Complex.ext <;> norm_num <;> nlinarith [h]
  · have hm : (completionMatrix a b c).submatrix
        (ZMod.finEquiv 2).toEquiv (ZMod.finEquiv 2).toEquiv =
        !![(a : ℂ) + Complex.I * (b : ℂ), Complex.I * (c : ℂ);
           Complex.I * (c : ℂ), (a : ℂ) - Complex.I * (b : ℂ)] := by
      have e0 : (ZMod.finEquiv 2).toEquiv 0 = 0 := rfl
      have e1 : (ZMod.finEquiv 2).toEquiv 1 = 1 := rfl
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.submatrix_apply, e0, e1, completionMatrix]
    rw [← Matrix.det_submatrix_equiv_self (ZMod.finEquiv 2).toEquiv, hm, Matrix.det_fin_two]
    apply Complex.ext <;> norm_num <;> nlinarith [h]
  · simp [completionMatrix]

/-- Every bounded parity polynomial admits a native continuous SU(2) completion,
with all scalar SOS degree, parity and zero-degree endpoint data retained. -/
theorem exists_phase_unitary_completion (k : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ k)
    (hpar : HasParity (p.map (algebraMap ℝ ℂ)) k)
    (hbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, p.eval x ^ 2 ≤ 1) :
    ∃ (B C : ℝ[X]) (U : CyclicObservable 2),
      1 - p ^ 2 = B ^ 2 + (1 - X ^ 2) * C ^ 2 ∧
      B.natDegree ≤ k ∧ C.natDegree ≤ k - 1 ∧ (k = 0 → C = 0) ∧
      HasParity (B.map (algebraMap ℝ ℂ)) k ∧
      HasParity (C.map (algebraMap ℝ ℂ)) (k - 1) ∧
      U = phaseCompletion p B C ∧ star U * U = 1 ∧ U * star U = 1 ∧
      (∀ t, (U t).det = 1) ∧ (∀ t, (U t 0 0).re = p.eval (windingPhase t).re) := by
  have he : IsEven ((1 - p ^ 2).map (algebraMap ℝ ℂ)) := by
    rw [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, sq]
    apply IsEven.sub
    · simpa using (isEven_C (1 : ℂ))
    · exact (hpar.mul hpar).1 ⟨k, rfl⟩
  have hd : (1 - p ^ 2).natDegree ≤ 2 * k := by
    refine (natDegree_sub_le _ _).trans (max_le (by rw [natDegree_one]; omega) ?_)
    exact natDegree_pow_le.trans (by omega)
  have hn : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ (1 - p ^ 2).eval x := by
    intro x hx
    simp only [eval_sub, eval_one, eval_pow]
    linarith [hbound x hx]
  obtain ⟨B, C, h, hB, hC, hC0, hBp, hCp⟩ :=
    exists_sumsq_decomposition k (1 - p ^ 2) he hd hn
  have laws (t : AddCircle (1 : ℝ)) := by
    have hc : (windingPhase t).re ^ 2 + (windingPhase t).im ^ 2 = 1 := by
      have hz : ‖windingPhase t‖ = 1 := by simp [windingPhase]
      rw [sq, sq, ← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz]
      norm_num
    have hx : (windingPhase t).re ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor <;> nlinarith [sq_nonneg (windingPhase t).im]
    have heval := congrArg (Polynomial.eval (windingPhase t).re) h
    simp only [eval_sub, eval_one, eval_pow, eval_add, eval_mul, eval_X] at heval
    have hs : (p.eval (windingPhase t).re) ^ 2 + (B.eval (windingPhase t).re) ^ 2 +
        ((windingPhase t).im * C.eval (windingPhase t).re) ^ 2 = 1 := by
      nlinarith [sq_nonneg (C.eval (windingPhase t).re)]
    exact completion_matrix_laws _ _ _ hs
  refine ⟨B, C, phaseCompletion p B C, h, hB, hC, hC0, hBp, hCp, rfl, ?_, ?_, ?_, ?_⟩
  · apply ContinuousMap.ext
    intro t
    simpa [phaseCompletion] using (laws t).1
  · apply ContinuousMap.ext
    intro t
    simpa [phaseCompletion] using (laws t).2.1
  · intro t
    simpa [phaseCompletion] using (laws t).2.2.1
  · intro t
    simpa [phaseCompletion] using (laws t).2.2.2

end D5.S3.ContinuousObservables.IntervalSOSCompletion
