/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeThreeDivision
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicNativeThreeDivision
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The native elliptic three-torsion quartic has an explicit cubic subfield and irreducible reduction. -/

import D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeElliptic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.SpecificDegree

set_option autoImplicit false

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeThreeDivision
open Polynomial D5.S1.Scale
open D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeCyclic
open D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeElliptic
open WeierstrassCurve WeierstrassCurve.Affine

noncomputable def quartic {R : Type*} [CommRing R] (l : R) : R[X] :=
  X^4 - C (6*(l^2+3))*X^2 + C (8*(l^2+3)*l)*X - C (3*(l^2+3)^2)

def quarticValue {R : Type*} [CommRing R] (l x : R) : R :=
  x^4-6*(l^2+3)*x^2+8*(l^2+3)*l*x-3*(l^2+3)^2

theorem eval_quartic {R : Type*} [CommRing R] (l x : R) :
    (quartic l).eval x = quarticValue l x := by
  simp [quartic, quarticValue]

/-- The normalized quartic equation is exactly the group-law condition
on an actual nonzero affine point of the native Weierstrass model. -/
theorem affine_three_torsion_iff {F : Type*} [Field F] [CharZero F] [DecidableEq F]
    (l : F) (x y : F) (h : (model l 1).Nonsingular x y) :
    let P := Point.some x y h
    (P + P + P = 0) ↔ (quartic l).IsRoot x := by
  dsimp only
  rw [Polynomial.IsRoot.def, eval_quartic]
  let W := model l 1
  let P := Point.some x y h
  change (P+P+P=0) ↔ quarticValue l x = 0
  have hP : P ≠ 0 := Point.some_ne_zero _
  have hY : y^2 = equation l x := by
    have H := (WeierstrassCurve.Affine.equation_iff ..).mp h.1
    simp [model, equation] at H ⊢
    linear_combination H
  by_cases hy : y = 0
  · have hd : P+P=0 := Point.add_self_of_Y_eq (by simp [model, negY, hy])
    rw [hd, zero_add]
    have H : 3*x^2-3*(l^2+3) ≠ 0 := by
      have hs := (WeierstrassCurve.Affine.nonsingular_iff ..).mp h
      rcases hs.2 with hs | hs
      · simp [model, hy] at hs ⊢
        exact fun H => hs (by linear_combination -H)
      · simp [model, hy] at hs
    have he : 3*quarticValue l x = -(3*x^2-3*(l^2+3))^2 := by
      rw [hy] at hY
      simp [equation] at hY
      dsimp [quarticValue]
      linear_combination -(12*x)*hY
    have hn : quarticValue l x ≠ 0 := by
      intro Hz
      rw [Hz, mul_zero] at he
      exact pow_ne_zero 2 H (by simpa using he.symm)
    exact iff_of_false hP hn
  have hYn : y ≠ W.negY x y := by
    simp [W, model, negY]
    intro H
    exact hy (by linear_combination (1/2:F)*H)
  let num := x^4 - W.b₄*x^2 - 2*W.b₆*x - W.b₈
  let den := 4*x^3 + W.b₂*x^2 + 2*W.b₄*x + W.b₆
  have hden : den ≠ 0 := by
    have H : den = (2*y)^2 := by
      dsimp [den, W, model, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
      unfold equation at hY
      linear_combination -4*hY
    rw [H]
    exact pow_ne_zero _ (mul_ne_zero (by norm_num) hy)
  have hb : num - x*den = -3*quarticValue l x := by
    simp [num, den, W, model, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, quarticValue]
    ring
  have hcoord : (P+P).xRep = P.xRep ↔ num/den = x := by
    rw [Point.xRep_add_self_of_Y_ne h hYn, Point.xRep_some]
    simp only [Matrix.vecCons_inj, and_true, num, den]
    rfl
  have hg : P+P+P=0 ↔ (P+P).xRep = P.xRep := by
    rw [Point.xRep_eq_xRep_iff]
    constructor
    · intro H
      exact Or.inr (eq_neg_of_add_eq_zero_left H)
    · rintro (H|H)
      · have hzero : P=0 := by simpa using add_left_cancel (H.trans (add_zero P).symm)
        exact False.elim (hP hzero)
      · rw [H, neg_add_cancel]
  rw [hg, hcoord, div_eq_iff hden, ← sub_eq_zero, hb, mul_eq_zero,
    or_iff_right (by norm_num : (-3:F) ≠ 0)]

noncomputable def cubicResolvent {R : Type*} [CommRing R] (l : R) : R[X] :=
  X^3 + C (6*(l^2+3))*X^2 + C (12*(l^2+3)^2)*X +
    C (72*(l^2+3)^3-64*(l^2+3)^2*l^2)

theorem resolvent_exact {R : Type*} [CommRing R] (l : R) :
    cubicResolvent l = (X+C (2*(l^2+3)))^3 + C (192*(l^2+3)^2) := by
  simp only [cubicResolvent, map_mul, map_pow, map_ofNat, map_sub, map_add]
  ring

private theorem resolvent_pair_identity {R : Type*} [CommRing R] (a b c d : R) :
    let s₁ := a+b+c+d
    let s₂ := a*b+a*c+a*d+b*c+b*d+c*d
    let s₃ := a*b*c+a*b*d+a*c*d+b*c*d
    let s₄ := a*b*c*d
    (X-C (a*b+c*d))*(X-C (a*c+b*d))*(X-C (a*d+b*c)) =
      X^3-C s₂*X^2+C (s₁*s₃-4*s₄)*X+C (4*s₂*s₄-s₃^2-s₁^2*s₄) := by
  simp only [map_mul, map_sub, map_add, map_pow, map_ofNat]
  ring

/-- In any splitting presentation the actual three pairing values are
exactly the linear factors of the resolvent. -/
theorem resolvent_split_pair_values {R : Type*} [CommRing R] (l a b c d : R)
    (h : quartic l = (X-C a)*(X-C b)*(X-C c)*(X-C d)) :
    cubicResolvent l = (X-C (a*b+c*d))*(X-C (a*c+b*d))*(X-C (a*d+b*c)) := by
  have hv : (X-C a)*(X-C b)*(X-C c)*(X-C d) =
      X^4-C (a+b+c+d)*X^3+C (a*b+a*c+a*d+b*c+b*d+c*d)*X^2 -
        C (a*b*c+a*b*d+a*c*d+b*c*d)*X+C (a*b*c*d) := by
    simp only [map_add, map_mul]
    ring
  rw [hv] at h
  have hs₁ := congrArg (fun p : R[X] => p.coeff 3) h
  have hs₂ := congrArg (fun p : R[X] => p.coeff 2) h
  have hs₃ := congrArg (fun p : R[X] => p.coeff 1) h
  have hs₄ := congrArg (fun p : R[X] => p.coeff 0) h
  simp only [quartic, coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X,
    coeff_C] at hs₁ hs₂ hs₃ hs₄
  norm_num at hs₁ hs₂ hs₃ hs₄
  rw [resolvent_pair_identity]
  have h₁ : a+b+c+d=0 := by linear_combination hs₁
  have h₂ : a*b+a*c+a*d+b*c+b*d+c*d = -6*(l^2+3) := by
    simpa using hs₂.symm
  have h₃ : a*b*c+a*b*d+a*c*d+b*c*d = -8*(l^2+3)*l := by
    linear_combination hs₃
  have h₄ : a*b*c*d = -3*(l^2+3)^2 := by simpa using hs₄.symm
  rw [h₁, h₂, h₃, h₄]
  simp only [cubicResolvent, map_mul, map_sub, map_add, map_pow, map_ofNat, map_neg, map_zero]
  ring

open D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueEisenstein

private def shiftedResolvent (l : ℤ) : Cubic ℤ := ⟨1,0,0,192*(l^2+3)^2⟩

theorem shifted_resolvent_eisenstein (l : ℤ) (hl : l%3=1) :
    ((shiftedResolvent l).toPoly).IsEisensteinAt (Ideal.span ({3}:Set ℤ)) := by
  have hn : ¬(9:ℤ) ∣ 192*(l^2+3)^2 := by
    rw [show (192:ℤ)*(l^2+3)^2 = 3*(64*(l^2+3)^2) by ring]
    intro H
    have hf : (3:ℤ) ∣ 64*(l^2+3)^2 := by
      obtain ⟨k,hk⟩ := H
      refine ⟨k, ?_⟩
      omega
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hf
    have hL : (l:ZMod 3) = 1 := by
      exact (ZMod.intCast_eq_intCast_iff' l 1 3).mpr (by simpa using hl)
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_add, Int.cast_ofNat, hL] at h
    exact (by decide : ¬ (64*(1^2+3)^2:ZMod 3)=0) h
  refine (show EisensteinCoeffs 3 (shiftedResolvent l) from ?_).isEisensteinAt
    (by rw [Int.isUnit_iff]; decide)
  refine ⟨rfl, dvd_zero _, dvd_zero _, ?_, hn⟩
  exact ⟨64*(l^2+3)^2, by change 192*(l^2+3)^2=3*(64*(l^2+3)^2); ring⟩

theorem native_shifted_resolvent_irreducible (j : ℕ) (hj : 1 ≤ j) :
    let l := goldenLucas (3^j)
    Irreducible ((X^3 + C (192*((l:ℚ)^2+3)^2)) : ℚ[X]) := by
  dsimp only
  let l := goldenLucas (3^j)
  have hm := (native_lucas_mod j hj).1
  have hs := shifted_resolvent_eisenstein l (by dsimp [l]; omega)
  have hmon : (shiftedResolvent l).toPoly.Monic := Cubic.monic_of_a_eq_one rfl
  have hprime : (Ideal.span ({(3:ℤ)}:Set ℤ)).IsPrime :=
    (Ideal.span_singleton_prime (by decide)).2 (Int.prime_iff_natAbs_prime.mpr Nat.prime_three)
  have hd : 0 < (shiftedResolvent l).toPoly.natDegree := by
    rw [Cubic.natDegree_of_a_ne_zero (show (shiftedResolvent l).a ≠ 0 by simp [shiftedResolvent])]
    decide
  have hi := (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hmon.isPrimitive).mp
    (hs.irreducible hprime hmon.isPrimitive hd)
  have he : (shiftedResolvent l).toPoly.map (Int.castRingHom ℚ) =
      X^3 + C (192*((l:ℚ)^2+3)^2) := by
    simp only [shiftedResolvent, Cubic.toPoly, Polynomial.map_add,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Int.coe_castRingHom,
      Int.cast_mul, Int.cast_pow, Int.cast_add, Int.cast_ofNat,
      map_zero, map_one, one_mul, zero_mul, add_zero]
  rw [he] at hi
  exact hi

open scoped IntermediateField

theorem quartic_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (l : R) :
    (quartic l).map f = quartic (f l) := by
  simp only [quartic, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_mul, map_mul, map_ofNat, map_add, map_pow]
  rw [show Polynomial.map f (6:R[X]) = 6 from Polynomial.map_natCast f 6,
    show Polynomial.map f (8:R[X]) = 8 from Polynomial.map_natCast f 8,
    show Polynomial.map f (3:R[X]) = 3 from Polynomial.map_natCast f 3]

theorem quartic_monic_degree {F : Type*} [CommRing F] [IsDomain F] (l : F) :
    (quartic l).Monic ∧ (quartic l).natDegree = 4 := by
  constructor <;> unfold quartic
  · monicity!
  · compute_degree <;> norm_num

/-- The marked pair-product in the actual quartic splitting field
generates a cubic subfield; dividing the shifted element by minus four
exhibits a cube root of the precise rational radicand. -/
theorem native_quartic_cubic_subfield (j : ℕ) (hj : 1 ≤ j) :
    let l := goldenLucas (3^j)
    let K := (quartic (l:ℚ)).SplittingField
    ∃ z : K, (z/(-4))^3 = 3*((l:K)^2+3)^2 ∧
      Module.finrank ℚ (ℚ⟮z⟯ : IntermediateField ℚ K) = 3 := by
  dsimp only
  let l := goldenLucas (3^j)
  let p := quartic (l:ℚ)
  let K := p.SplittingField
  change ∃ z : K, (z/(-4))^3 = 3*((l:K)^2+3)^2 ∧
    Module.finrank ℚ (ℚ⟮z⟯ : IntermediateField ℚ K) = 3
  have hcast : algebraMap ℚ K (l:ℚ) = (l:K) := map_intCast _ _
  have hp : p.map (algebraMap ℚ K) = quartic (l:K) := by
    change (quartic (l:ℚ)).map (algebraMap ℚ K) = _
    rw [quartic_map, hcast]
  have hs : (quartic (l:K)).Splits := hp ▸ SplittingField.splits p
  let rs := (quartic (l:K)).roots
  have hlen : rs.toList.length = 4 := by
    rw [Multiset.length_toList, ← hs.natDegree_eq_card_roots, (quartic_monic_degree _).2]
  obtain ⟨a,b,c,d,hd⟩ := List.length_eq_four.mp hlen
  have hr : rs = ([a,b,c,d] : Multiset K) := by
    rw [← Multiset.coe_toList rs, hd]
  have hf := hs.eq_prod_roots_of_monic (quartic_monic_degree _).1
  change quartic (l:K) = (rs.map fun x => X-C x).prod at hf
  rw [hr] at hf
  change quartic (l:K) =
    ((a ::ₘ b ::ₘ c ::ₘ d ::ₘ 0).map (fun x => X-C x)).prod at hf
  simp only [Multiset.map_cons, Multiset.map_zero, Multiset.prod_cons, Multiset.prod_zero, mul_one] at hf
  have hv := resolvent_split_pair_values (l:K) a b c d
    (by simpa only [mul_assoc] using hf)
  have he := congrArg (fun f : K[X] => f.eval (a*b+c*d)) hv
  rw [resolvent_exact] at he
  let z := a*b+c*d+2*((l:K)^2+3)
  have hz : z^3+192*((l:K)^2+3)^2=0 := by
    simpa [z] using he
  refine ⟨z, ?_, ?_⟩
  · rw [div_pow]
    apply (div_eq_iff (by norm_num)).mpr
    linear_combination hz
  · let g := (X^3+C (192*((l:ℚ)^2+3)^2) : ℚ[X])
    have hm : g.Monic := by dsimp [g]; monicity!
    have hdeg : g.natDegree = 3 := by dsimp [g]; compute_degree; norm_num
    have hroot : aeval z g = 0 := by
      simpa [g] using hz
    have hmin : minpoly ℚ z = g :=
      (minpoly.eq_of_irreducible_of_monic (native_shifted_resolvent_irreducible j hj)
        hroot hm).symm
    rw [IntermediateField.adjoin.finrank (IsIntegral.of_finite ℚ z), hmin, hdeg]


private noncomputable def plus {R : Type*} [CommRing R] : R[X] := X^4 + X^2 + 2*X + 2
private noncomputable def subs {R : Type*} [CommRing R] : R[X] := -X^3 - 2*X^2 - X

private theorem exact_remainder :
    (X: (ZMod 5)[X])^25-X = (X^21 - X^19 - 2*X^18 - X^17 - X^16 + 2*X^15 + 2*X^14 + 2*X^13 + X^12 + X^10 - X^9 + 2*X^8 - X^7 - 2*X^6 - X^5 + 2*X^3 + X^2)*plus + subs := by
  have H : (X:ℤ[X])^25-X = (X^21 - X^19 - 2*X^18 - X^17 - X^16 + 2*X^15 + 2*X^14 + 2*X^13 + X^12 + X^10 - X^9 + 2*X^8 - X^7 - 2*X^6 - X^5 + 2*X^3 + X^2)*plus + subs + 5*(X^20 + X^19 + X^18 - X^16 - 2*X^15 - 2*X^14 - X^13 - X^12 + X^7 + X^6 - X^4 - X^3) := by
    unfold plus subs
    ring
  have H' := congrArg (Polynomial.mapRingHom (Int.castRingHom (ZMod 5))) H
  have h5 : (5:(ZMod 5)[X]) = 0 := by
    rw [← Polynomial.C_ofNat]
    simpa only [map_zero] using congrArg Polynomial.C (by decide : (5:ZMod 5) = 0)
  simpa [plus, subs, h5, Polynomial.map_X] using H'

private theorem exact_bezout :
    (-X^2 - X - 2)*(plus : (ZMod 5)[X]) + (-X^3 + X^2 + X - 1)*subs = 1 := by
  have H : (-X^2 - X - 2)*(plus : ℤ[X]) + (-X^3 + X^2 + X - 1)*subs = 1+5*(-X^4 - X^3 - X^2 - X - 1) := by
    unfold plus subs
    ring
  have H' := congrArg (Polynomial.mapRingHom (Int.castRingHom (ZMod 5))) H
  have h5 : (5:(ZMod 5)[X]) = 0 := by
    rw [← Polynomial.C_ofNat]
    simpa only [map_zero] using congrArg Polynomial.C (by decide : (5:ZMod 5) = 0)
  simpa [plus, subs, h5, Polynomial.map_X] using H'

private theorem quartic_mod5_pos_irreducible : Irreducible (plus : (ZMod 5)[X]) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let f := (plus : (ZMod 5)[X])
  have hd : f.natDegree = 4 := by
    dsimp [f, plus]
    compute_degree <;> decide
  have hm : f.Monic := by
    dsimp [f, plus]
    monicity!
  have h1 : f ≠ 1 := by intro h; simp [h] at hd
  apply (hm.irreducible_iff_lt_natDegree_lt h1).mpr
  intro g hg hgd hgf
  have hg' : 0 < g.natDegree ∧ g.natDegree ≤ 2 := by simpa [hd] using hgd
  obtain ⟨r, hr, hrg⟩ := exists_irreducible_of_natDegree_pos hg'.1
  have hrf : r ∣ f := dvd_trans hrg hgf
  have hrpos := hr.natDegree_pos
  have hrle : r.natDegree ≤ g.natDegree := natDegree_le_of_dvd hrg hg.ne_zero
  have hr2 : r.natDegree ∣ 2 := by
    have he : r.natDegree=1 ∨ r.natDegree=2 := by omega
    rcases he with h|h <;> simp [h]
  have hx : r ∣ (X:(ZMod 5)[X])^25-X := by
    have H := (hr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n:=2)).mp hr2
    simpa [Nat.card_eq_fintype_card, ZMod.card] using H
  rw [exact_remainder] at hx
  have hdR : r ∣ (subs:(ZMod 5)[X]) := (dvd_add_right (dvd_mul_of_dvd_right hrf _)).mp hx
  have H :=
    dvd_add (dvd_mul_of_dvd_right hrf (-X^2 - X - 2))
      (dvd_mul_of_dvd_right hdR (-X^3 + X^2 + X - 1))
  rw [exact_bezout] at H
  exact hr.not_isUnit (isUnit_of_dvd_one H)

theorem quartic_comp_neg {R : Type*} [CommRing R] (l : R) :
    (quartic l).comp (-X) = quartic (-l) := by
  simp only [quartic, sub_comp, pow_comp, X_comp, mul_comp, C_comp, add_comp]
  simp only [map_mul, map_pow, map_neg, map_ofNat, map_add]
  ring

private theorem positive_quartic_eq :
    quartic (1:ZMod 5) = (plus:(ZMod 5)[X]) := by
  have h₂ : -(6*((1:ZMod 5)^2+3)) = 1 := by decide
  have h₁ : 8*((1:ZMod 5)^2+3)*1 = 2 := by decide
  have h₀ : -(3*((1:ZMod 5)^2+3)^2) = 2 := by decide
  simp only [quartic, sub_eq_add_neg, ← neg_mul, ← map_neg, h₂, map_one,
    one_mul, h₁, h₀, plus, Polynomial.C_ofNat]

theorem quartic_mod5_of_lucas {l : ZMod 5} (h : l^2=1) :
    Irreducible (quartic l) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hs : l=1 ∨ l = -1 := sq_eq_one_iff.mp h
  have hp : Irreducible (quartic (1:ZMod 5)) := by
    rw [positive_quartic_eq]
    exact quartic_mod5_pos_irreducible
  rcases hs with rfl|rfl
  · exact hp
  · let e : (ZMod 5)[X] ≃ₐ[ZMod 5] (ZMod 5)[X] :=
      algEquivOfCompEqX (-X) (-X) (by simp [neg_comp]) (by simp [neg_comp])
    have H := (MulEquiv.irreducible_iff (f := e.toMulEquiv)).mpr hp
    change Irreducible (aeval (-X : (ZMod 5)[X]) (quartic (1:ZMod 5))) at H
    rwa [← comp_eq_aeval, quartic_comp_neg] at H

theorem native_quartic_mod5_irreducible (j : ℕ) (hj : 1 ≤ j) :
    Irreducible ((quartic (goldenLucas (3^j))).map (Int.castRingHom (ZMod 5))) := by
  rw [quartic_map]
  apply quartic_mod5_of_lucas
  have H := (golden_cubic_lucas_block j hj).2.2.2.1
  simpa only [Int.coe_castRingHom, Int.cast_pow] using H

theorem native_quartic_rational_irreducible (j : ℕ) (hj : 1 ≤ j) :
    Irreducible (quartic (goldenLucas (3^j):ℚ)) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let f := quartic (goldenLucas (3^j))
  have hm := (quartic_monic_degree (goldenLucas (3^j))).1
  have hi := Polynomial.Monic.irreducible_of_irreducible_map
    (Int.castRingHom (ZMod 5)) f hm (native_quartic_mod5_irreducible j hj)
  have h := (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hm.isPrimitive).mp hi
  change Irreducible ((quartic (goldenLucas (3^j))).map (Int.castRingHom ℚ)) at h
  rwa [quartic_map] at h

/-- Over an algebraic closure the quartic gives every abscissa and only
abscissas of actual nonzero three-torsion points. -/
theorem three_torsion_abscissa_iff {F : Type*} [Field F] [CharZero F]
    [IsAlgClosed F] [DecidableEq F] (l : ℤ) (x : F) :
    (quartic (l:F)).IsRoot x ↔ ∃ y, ∃ h : (model (l:F) 1).Nonsingular x y,
      let P := Point.some x y h
      P+P+P=0 := by
  constructor
  · intro h
    obtain ⟨y,hy⟩ := IsAlgClosed.exists_pow_nat_eq (equation (l:F) x) (n:=2) (by decide)
    have he : (model (l:F) 1).Equation x y := by
      rw [WeierstrassCurve.Affine.equation_iff]
      simp [model, equation] at hy ⊢
      linear_combination hy
    have hs := (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
      (model_discriminant_ne l (by norm_num : (1:F) ≠ 0))).mp he
    exact ⟨y,hs,(affine_three_torsion_iff (l:F) x y hs).mpr h⟩
  · rintro ⟨y,h,H⟩
    exact (affine_three_torsion_iff (l:F) x y h).mp H

/-- The degree of the actual projective splitting field is divisible by
twelve, from the marked cubic subfield and an irreducible quartic root. -/
theorem native_projective_degree_multiple_twelve (j : ℕ) (hj : 1 ≤ j) :
    let l := goldenLucas (3^j)
    let K := (quartic (l:ℚ)).SplittingField
    12 ∣ Module.finrank ℚ K := by
  dsimp only
  let l := goldenLucas (3^j)
  let p := quartic (l:ℚ)
  let K := p.SplittingField
  change 12 ∣ Module.finrank ℚ K
  obtain ⟨z,_,h3⟩ := native_quartic_cubic_subfield j hj
  have hdvd3 : 3 ∣ Module.finrank ℚ K := by
    rw [← h3]
    exact Module.finrank_dvd_finrank_right ℚ (ℚ⟮z⟯ : IntermediateField ℚ K) K
  have hdeg : p.natDegree = 4 := (quartic_monic_degree (l:ℚ)).2
  have hmon : p.Monic := (quartic_monic_degree (l:ℚ)).1
  have hdm : (p.map (algebraMap ℚ K)).degree ≠ 0 := by
    rw [degree_map, degree_eq_natDegree hmon.ne_zero, hdeg]
    decide
  obtain ⟨x,hx⟩ := (SplittingField.splits p).exists_eval_eq_zero hdm
  have hr : aeval x p=0 := by rwa [← eval_map_algebraMap]
  have hx4 : Module.finrank ℚ (ℚ⟮x⟯ : IntermediateField ℚ K) = 4 := by
    rw [IntermediateField.adjoin.finrank (IsIntegral.of_finite ℚ x),
      (minpoly.eq_of_irreducible_of_monic (native_quartic_rational_irreducible j hj)
        hr hmon).symm, hdeg]
  have hdvd4 : 4 ∣ Module.finrank ℚ K := by
    rw [← hx4]
    exact Module.finrank_dvd_finrank_right ℚ (ℚ⟮x⟯ : IntermediateField ℚ K) K
  exact (by decide : Nat.Coprime 3 4).mul_dvd_of_dvd_of_dvd hdvd3 hdvd4

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeThreeDivision
