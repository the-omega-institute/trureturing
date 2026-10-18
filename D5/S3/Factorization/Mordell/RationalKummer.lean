/- GID: D5/S3/Factorization/Mordell/RationalKummer
   generality: G
   mirror-B: D5/B/S3/Factorization/Mordell/RationalKummer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational split-cubic descent coordinates and explicit rational halving. -/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Mordell.RationalKummer

open WeierstrassCurve WeierstrassCurve.Affine

/-- The rational twist in the ordered descent convention `(x,x+5D)`. -/
def curve (D : ℚ) : WeierstrassCurve.Affine ℚ := ⟨0, -10 * D, 0, -75 * D ^ 2, 0⟩

private theorem equation_iff (D x y : ℚ) :
    (curve D).Equation x y ↔ y ^ 2 = x * (x + 5 * D) * (x - 15 * D) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [curve]
  constructor <;> intro h <;> nlinarith [h]

/-- Nonzero twists are elliptic. -/
theorem curve_is_elliptic (D : ℚ) (hD : D ≠ 0) : (curve D).IsElliptic := by
  constructor
  apply isUnit_iff_ne_zero.mpr
  have hdisc : (curve D).Δ = 36000000 * D ^ 6 := by
    simp [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  rw [hdisc]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ hD)

/-- The three ordered rational roots. -/
def root (D : ℚ) (i : Fin 3) : ℚ := ![0, -5 * D, 15 * D] i

private def derivative (D e : ℚ) : ℚ := 3 * e ^ 2 - 20 * D * e - 75 * D ^ 2

private theorem root_equation (D : ℚ) (i : Fin 3) :
    root D i * (root D i + 5 * D) * (root D i - 15 * D) = 0 := by
  fin_cases i <;> simp [root]

private theorem derivative_ne_zero (D : ℚ) (hD : D ≠ 0) (i : Fin 3) :
    derivative D (root D i) ≠ 0 := by
  fin_cases i <;> dsimp [derivative, root] <;> ring_nf <;> simp_all

private theorem shifted_equation (D x y : ℚ) (i : Fin 3)
    (h : (curve D).Equation x y) :
    y ^ 2 = (x - root D i) ^ 3 + (3 * root D i - 10 * D) * (x - root D i) ^ 2 +
      derivative D (root D i) * (x - root D i) := by
  have he := root_equation D i
  have hy := (equation_iff D x y).mp h
  dsimp [derivative]
  linear_combination hy + he

/-- A rational half-point, constructed from square roots of the three shifted coordinates.
The sign convention on the product is `a * b * c = -y`. -/
theorem explicit_half (D x y a b c : ℚ) (hD : D ≠ 0)
    (ha : a ^ 2 = x) (hb : b ^ 2 = x + 5 * D) (hc : c ^ 2 = x - 15 * D)
    (habc : a * b * c = -y) (hP : (curve D).Nonsingular x y) :
    ∃ hQ : (curve D).Nonsingular
        (x + a * b + a * c + b * c) (-((a+b) * (a+c) * (b+c))),
      (Point.some _ _ hQ : (curve D).Point) + Point.some _ _ hQ = Point.some x y hP := by
  let u := x + a * b + a * c + b * c
  let v := -((a+b) * (a+c) * (b+c))
  have hab : a + b ≠ 0 := by
    intro h; have : a = -b := by linarith
    rw [this] at ha
    apply hD
    nlinarith [ha, hb]
  have hac : a + c ≠ 0 := by
    intro h; have : a = -c := by linarith
    rw [this] at ha
    apply hD
    nlinarith [ha, hc]
  have hbc : b + c ≠ 0 := by
    intro h; have : b = -c := by linarith
    rw [this] at hb
    apply hD
    nlinarith [hb, hc]
  have hv : v ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hab hac) hbc)
  have heq : (curve D).Equation u v := by
    rw [equation_iff]
    dsimp [u, v]
    have hu0 : x + a * b + a * c + b * c = (a+b) * (a+c) := by nlinarith [ha]
    have hu1 : x + a * b + a * c + b * c + 5 * D = (a+b) * (b+c) := by nlinarith [hb]
    have hu2 : x + a * b + a * c + b * c - 15 * D = (a+c) * (b+c) := by nlinarith [hc]
    rw [hu1, hu2, hu0]
    ring
  letI := curve_is_elliptic D hD
  have hQ : (curve D).Nonsingular u v := (equation_iff_nonsingular).mp heq
  refine ⟨hQ, ?_⟩
  have hnv : v ≠ (curve D).negY u v := by
    simp only [negY, curve, zero_mul, sub_zero]
    intro h; apply hv; linarith
  rw [Point.add_self_of_Y_ne hnv]
  apply (Point.some.injEq ..).mpr
  have hslope : (curve D).slope u u v v = -(a+b+c) := by
    rw [slope_of_Y_ne rfl hnv]
    simp only [curve, negY, zero_mul, sub_zero]
    apply (div_eq_iff (by intro h; apply hv; linarith)).mpr
    dsimp [u, v]
    clear hP hQ heq hnv hv hab hac hbc this hD habc
    grobner
  rw [hslope]
  constructor
  · dsimp [addX, curve, u]
    nlinarith [ha, hb, hc]
  · dsimp [addY, negAddY, negY, addX, curve, u, v]
    clear hP hQ heq hnv hv hab hac hbc this hD hslope
    grobner


/-- A shifted coordinate is replaced by the derivative at its zero. -/
def descentRep (D : ℚ) (i : Fin 3) : (curve D).Point → ℚ
  | .zero => 1
  | .some x _ _ => if x = root D i then derivative D (root D i) else x - root D i

private theorem descentRep_ne_zero (D : ℚ) (hD : D ≠ 0) (i : Fin 3)
    (P : (curve D).Point) : descentRep D i P ≠ 0 := by
  cases P with
  | zero => exact one_ne_zero
  | some x y h =>
    dsimp [descentRep]
    split_ifs with hx
    · exact derivative_ne_zero D hD i
    · exact sub_ne_zero.mpr hx

private def rep (B u : ℚ) : ℚ := if u = 0 then B else u

private theorem rep_triple_square (B u v w l b : ℚ) (hB : B ≠ 0)
    (hpair : u * v + u * w + v * w = B - 2 * l * b) (hprod : u * v * w = b ^ 2) :
    IsSquare (rep B u * rep B v * rep B w) := by
  by_cases hu : u = 0
  · subst u
    have hb : b = 0 := by nlinarith [sq_nonneg b]
    rw [hb] at hpair
    have hvw : v * w = B := by nlinarith [hpair]
    have hv : v ≠ 0 := by intro h; apply hB; rw [← hvw, h, zero_mul]
    have hw : w ≠ 0 := by intro h; apply hB; rw [← hvw, h, mul_zero]
    refine ⟨B, ?_⟩
    have he : B * v * w = B * B := by rw [mul_assoc, hvw]
    simpa [rep, hv, hw] using he
  by_cases hv : v = 0
  · subst v
    have hb : b = 0 := by nlinarith [sq_nonneg b]
    rw [hb] at hpair
    have huw : u * w = B := by nlinarith [hpair]
    have hw : w ≠ 0 := by intro h; apply hB; rw [← huw, h, mul_zero]
    refine ⟨B, ?_⟩
    have he : u * B * w = B * B := by calc
      u * B * w = B * (u * w) := by ring
      _ = B * B := by rw [huw]
    simpa [rep, hu, hw] using he
  by_cases hw : w = 0
  · subst w
    have hb : b = 0 := by nlinarith [sq_nonneg b]
    rw [hb] at hpair
    have huv : u * v = B := by nlinarith [hpair]
    refine ⟨B, ?_⟩
    have he : u * v * B = B * B := by rw [huv]
    simpa [rep, hu, hv] using he
  · refine ⟨b, ?_⟩
    simpa [rep, hu, hv, hw, pow_two] using hprod

private theorem secant_coefficients (A B u v y z : ℚ) (huv : u ≠ v)
    (hy : y ^ 2 = u ^ 3 + A * u ^ 2 + B * u) (hz : z ^ 2 = v ^ 3 + A * v ^ 2 + B * v) :
    let l := (y-z)/(u-v)
    let b := y-l * u
    let w := l ^ 2-A-u-v
    u * v + u * w + v * w = B-2 * l * b ∧ u * v * w = b ^ 2 := by
  dsimp
  constructor <;> field_simp [sub_ne_zero.mpr huv] <;> grobner

private theorem tangent_coefficients (A B u y : ℚ) (hy0 : y ≠ 0)
    (hy : y ^ 2 = u ^ 3 + A * u ^ 2 + B * u) :
    let l := (3 * u ^ 2+2 * A * u+B)/(2 * y)
    let b := y-l * u
    let w := l ^ 2-A-u-u
    u * u + u * w + u * w = B-2 * l * b ∧ u * u * w = b ^ 2 := by
  dsimp
  constructor <;> field_simp [hy0] <;> grobner

/-- Each total descent coordinate has square triple product on an actual sum. -/
theorem descentRep_add_square (D : ℚ) (hD : D ≠ 0) (i : Fin 3)
    (P Q : (curve D).Point) :
    IsSquare (descentRep D i P * descentRep D i Q * descentRep D i (P+Q)) := by
  cases P with
  | zero => simpa only [← Point.zero_def, zero_add, add_zero, descentRep, one_mul, mul_one] using IsSquare.mul_self (descentRep D i Q)
  | some x y hP =>
    cases Q with
    | zero => simpa only [← Point.zero_def, zero_add, add_zero, descentRep, one_mul, mul_one] using IsSquare.mul_self (descentRep D i (.some x y hP))
    | some z t hQ =>
      by_cases hv : x = z ∧ y = (curve D).negY z t
      · rw [Point.add_of_Y_eq hv.1 hv.2]
        simpa [descentRep, hv.1] using IsSquare.mul_self (descentRep D i (.some z t hQ))
      · have hsum := Point.add_some (h₁ := hP) (h₂ := hQ) hv
        rw [hsum]
        let e := root D i
        let A := 3 * e-10 * D
        let B := derivative D e
        let l := (curve D).slope x z y t
        have hxy := shifted_equation D x y i hP.1
        have hzt := shifted_equation D z t i hQ.1
        have hc : (x-e) * (z-e) + (x-e) * ((curve D).addX x z l-e) +
            (z-e) * ((curve D).addX x z l-e) = B-2 * l * (y-l * (x-e)) ∧
            (x-e) * (z-e) * ((curve D).addX x z l-e) = (y-l * (x-e)) ^ 2 := by
          by_cases hxz : x = z
          · subst z
            have hyt : y = t := by
              have := (equation_iff D x y).mp hP.1
              have := (equation_iff D x t).mp hQ.1
              have hn : y ≠ -t := by simpa [curve, negY] using hv
              have hf : (y-t) * (y+t) = 0 := by nlinarith [hxy, hzt]
              rcases mul_eq_zero.mp hf with hh | hh
              · linarith
              · exact (hn (by linarith)).elim
            subst t
            have hy0 : y ≠ 0 := by
              intro hz; apply hv; simp [hz, curve, negY]
            have H := tangent_coefficients A B (x-e) y hy0 hxy
            have hl : l = (3 * (x-e) ^ 2+2 * A * (x-e)+B)/(2 * y) := by
              dsimp [l]
              rw [slope_of_Y_ne rfl (by simp only [curve, negY, zero_mul, sub_zero]; intro hz; apply hy0; linarith)]
              dsimp [curve, negY, A, B, derivative]
              congr 1 <;> ring
            rw [hl]
            convert H using 1 <;> dsimp [A, B, addX, curve] <;> ring
          · have H := secant_coefficients A B (x-e) (z-e) y t
                (by intro h; apply hxz; linarith) hxy hzt
            have hl : l = (y-t)/((x-e)-(z-e)) := by
              dsimp [l]
              rw [slope_of_X_ne hxz]
              congr 1 <;> ring
            rw [hl]
            convert H using 1 <;> dsimp [A, B, addX, curve] <;> ring
        have H := rep_triple_square B (x-e) (z-e) ((curve D).addX x z l-e)
          l (y-l * (x-e)) (derivative_ne_zero D hD i) hc.1 hc.2
        simpa only [descentRep, rep, sub_eq_zero, e, B, l] using H


/-- Rational units modulo squares, using the standard power quotient. -/
abbrev SquareClass := ℚˣ ⧸ (powMonoidHom 2 : ℚˣ →* ℚˣ).range

private theorem squareClass_mul_self (a : SquareClass) : a * a = 1 := by
  induction a using Quotient.inductionOn with
  | h a =>
    change ((a * a : ℚˣ) : SquareClass) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨a, by simp [pow_two]⟩

private theorem unit_class_one_iff (u : ℚˣ) :
    (u : SquareClass) = 1 ↔ IsSquare (u : ℚ) := by
  rw [QuotientGroup.eq_one_iff, MonoidHom.mem_range]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨(v : ℚ), ?_⟩
    have H := congrArg (fun w : ℚˣ => (w : ℚ)) hv
    simpa [pow_two] using H.symm
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      intro hz
      have := u.ne_zero
      rw [hr, hz, zero_mul] at this
      exact this rfl
    refine ⟨Units.mk0 r hr0, ?_⟩
    ext
    simpa [pow_two] using hr.symm

private def descentUnit (D : ℚ) (hD : D ≠ 0) (i : Fin 3) (P : (curve D).Point) : ℚˣ :=
  Units.mk0 (descentRep D i P) (descentRep_ne_zero D hD i P)

/-- The total single-coordinate Kummer homomorphism. -/
def coordinate (D : ℚ) (hD : D ≠ 0) (i : Fin 3) :
    (curve D).Point →+ Additive SquareClass where
  toFun P := Additive.ofMul ((descentUnit D hD i P : ℚˣ) : SquareClass)
  map_zero' := by
    change ((descentUnit D hD i 0 : ℚˣ) : SquareClass) = 1
    have h : descentUnit D hD i 0 = 1 := by ext; rfl
    rw [h]; rfl
  map_add' P Q := by
    change ((descentUnit D hD i (P+Q) : ℚˣ) : SquareClass) =
      ((descentUnit D hD i P : ℚˣ) : SquareClass) *
      ((descentUnit D hD i Q : ℚˣ) : SquareClass)
    let a : SquareClass := (descentUnit D hD i P : ℚˣ)
    let b : SquareClass := (descentUnit D hD i Q : ℚˣ)
    let c : SquareClass := (descentUnit D hD i (P+Q) : ℚˣ)
    have H : a * b * c = 1 := by
      change (((descentUnit D hD i P * descentUnit D hD i Q *
        descentUnit D hD i (P+Q)) : ℚˣ) : SquareClass) = 1
      apply (unit_class_one_iff _).mpr
      exact descentRep_add_square D hD i P Q
    change c = a * b
    calc
      c = (a * b * c) * c := by rw [H, one_mul]
      _ = a * b := by rw [mul_assoc, squareClass_mul_self c, mul_one]

/-- The complete rational Kummer map in the ordered pair convention `(x,x+5D)`. -/
def kummer (D : ℚ) (hD : D ≠ 0) :
    (curve D).Point →+ (Additive SquareClass × Additive SquareClass) :=
  (coordinate D hD 0).prod (coordinate D hD 1)

private theorem coordinate_zero_iff (D : ℚ) (hD : D ≠ 0) (i : Fin 3)
    (P : (curve D).Point) : coordinate D hD i P = 0 ↔ IsSquare (descentRep D i P) :=
  unit_class_one_iff _

/-- Every actual rational double is in the Kummer kernel. -/
private theorem kummer_double (D : ℚ) (hD : D ≠ 0) (P : (curve D).Point) :
    kummer D hD (P+P) = 0 := by
  rw [map_add]
  apply Prod.ext
  · change ((kummer D hD P).1.toMul) * ((kummer D hD P).1.toMul) = 1
    exact squareClass_mul_self _
  · change ((kummer D hD P).2.toMul) * ((kummer D hD P).2.toMul) = 1
    exact squareClass_mul_self _


private theorem descentRep_some_values (D x y : ℚ) (hP : (curve D).Nonsingular x y) :
    descentRep D 0 (.some x y hP) = (if x = 0 then -75 * D ^ 2 else x) ∧
    descentRep D 1 (.some x y hP) = (if x = -5 * D then 100 * D ^ 2 else x+5 * D) ∧
    descentRep D 2 (.some x y hP) = (if x = 15 * D then 300 * D ^ 2 else x-15 * D) := by
  dsimp [descentRep, root, derivative]
  constructor
  · split_ifs <;> simp_all <;> ring
  constructor <;> split_ifs <;> simp_all <;> ring

/-- The three descent classes have product one, including all rational two-torsion points. -/
theorem descentRep_product_square (D : ℚ) (hD : D ≠ 0) (P : (curve D).Point) :
    IsSquare (descentRep D 0 P * descentRep D 1 P * descentRep D 2 P) := by
  cases P with
  | zero => exact ⟨1, by norm_num [descentRep]⟩
  | some x y h =>
    obtain ⟨hval0, hval1, hval2⟩ := descentRep_some_values D x y h
    rw [hval0, hval1, hval2]
    by_cases h0 : x = 0
    · subst x
      have h1 : (0:ℚ) ≠ -5 * D := by intro hz; apply hD; linarith
      have h2 : (0:ℚ) ≠ 15 * D := by intro hz; apply hD; linarith
      refine ⟨75 * D ^ 2, ?_⟩
      simp only [ite_true, if_pos rfl, if_neg h1, if_neg h2]
      ring
    by_cases h1 : x = -5 * D
    · have h2 : x ≠ 15 * D := by intro hz; apply hD; rw [h1] at hz; linarith
      refine ⟨100 * D ^ 2, ?_⟩
      simp only [if_neg h0, if_pos h1, if_neg h2]
      rw [h1]
      ring
    by_cases h2 : x = 15 * D
    · refine ⟨300 * D ^ 2, ?_⟩
      simp only [if_neg h0, if_neg h1, if_pos h2]
      rw [h2]
      ring
    · refine ⟨y, ?_⟩
      simp only [if_neg h0, if_neg h1, if_neg h2]
      exact (by simpa only [pow_two] using ((equation_iff D x y).mp h.1).symm)

private theorem all_coordinate_zero_of_pair (D : ℚ) (hD : D ≠ 0)
    (P : (curve D).Point) (h : kummer D hD P = 0) :
    ∀ i : Fin 3, coordinate D hD i P = 0 := by
  have h0 : coordinate D hD 0 P = 0 := congrArg Prod.fst h
  have h1 : coordinate D hD 1 P = 0 := congrArg Prod.snd h
  have hprod :
      (coordinate D hD 0 P).toMul * (coordinate D hD 1 P).toMul *
      (coordinate D hD 2 P).toMul = 1 := by
    change (((descentUnit D hD 0 P * descentUnit D hD 1 P * descentUnit D hD 2 P) : ℚˣ) : SquareClass) = 1
    exact (unit_class_one_iff _).mpr (descentRep_product_square D hD P)
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · change (coordinate D hD 2 P).toMul = 1
    rw [h0, h1] at hprod
    change 1 * 1 * (coordinate D hD 2 P).toMul = 1 at hprod
    simpa using hprod

private theorem shifted_square_of_coordinate_zero (D : ℚ) (hD : D ≠ 0)
    (i : Fin 3) (x y : ℚ) (hP : (curve D).Nonsingular x y)
    (h : coordinate D hD i (.some x y hP) = 0) : IsSquare (x-root D i) := by
  by_cases hx : x = root D i
  · rw [hx, sub_self]; exact ⟨0, by ring⟩
  · have H := (coordinate_zero_iff D hD i _).mp h
    simpa [descentRep, hx] using H

/-- A trivial Kummer class has an actual rational half-point. -/
private theorem half_of_squares (D x y : ℚ) (hD : D ≠ 0)
    (hP : (curve D).Nonsingular x y)
    (ha : IsSquare x) (hb : IsSquare (x+5 * D)) (hc : IsSquare (x-15 * D)) :
    ∃ Q : (curve D).Point, Q+Q = Point.some x y hP := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  obtain ⟨c, hc⟩ := hc
  have ha' : a ^ 2 = x := by nlinarith [ha]
  have hb' : b ^ 2 = x+5 * D := by nlinarith [hb]
  have hc' : c ^ 2 = x-15 * D := by nlinarith [hc]
  have hs : (a * b * c) ^ 2 = y ^ 2 := by
    rw [mul_pow, mul_pow, ha', hb', hc']
    exact ((equation_iff D x y).mp hP.1).symm
  have hm : (a * b * c-y) * (a * b * c+y) = 0 := by nlinarith [hs]
  rcases mul_eq_zero.mp hm with hp | hn
  · have hp' : (-a) * b * c = -y := by nlinarith [hp]
    obtain ⟨hQ, hQeq⟩ := explicit_half D x y (-a) b c hD (by simpa using ha') hb' hc' hp' hP
    exact ⟨.some _ _ hQ, hQeq⟩
  · have hn' : a * b * c = -y := by linarith
    obtain ⟨hQ, hQeq⟩ := explicit_half D x y a b c hD ha' hb' hc' hn' hP
    exact ⟨.some _ _ hQ, hQeq⟩

private theorem half_of_kummer_zero (D : ℚ) (hD : D ≠ 0) (P : (curve D).Point)
    (h : kummer D hD P = 0) : ∃ Q : (curve D).Point, Q+Q = P := by
  cases P with
  | zero => exact ⟨0, zero_add _⟩
  | some x y hP =>
    have H := all_coordinate_zero_of_pair D hD (.some x y hP) h
    have ha := shifted_square_of_coordinate_zero D hD 0 x y hP (H 0)
    have hb := shifted_square_of_coordinate_zero D hD 1 x y hP (H 1)
    have hc := shifted_square_of_coordinate_zero D hD 2 x y hP (H 2)
    simp [root] at ha hb hc
    exact half_of_squares D x y hD hP ha hb hc

/-- The kernel is precisely actual rational doubling, with no generic-position restriction. -/
theorem kummer_zero_iff_double (D : ℚ) (hD : D ≠ 0) (P : (curve D).Point) :
    kummer D hD P = 0 ↔ ∃ Q : (curve D).Point, Q+Q = P := by
  constructor
  · exact half_of_kummer_zero D hD P
  · rintro ⟨Q, rfl⟩
    exact kummer_double D hD Q

/-- The affine halving criterion includes vanishing shifted coordinates. -/
theorem affine_double_iff (D x y : ℚ) (hD : D ≠ 0) (hP : (curve D).Nonsingular x y) :
    (∃ Q : (curve D).Point, Q+Q = Point.some x y hP) ↔
      IsSquare x ∧ IsSquare (x+5 * D) ∧ IsSquare (x-15 * D) := by
  constructor
  · rintro ⟨Q,hQ⟩
    have hk : kummer D hD (Point.some x y hP) = 0 := by
      rw [← hQ]
      exact kummer_double D hD Q
    have H := all_coordinate_zero_of_pair D hD (Point.some x y hP) hk
    have ha := shifted_square_of_coordinate_zero D hD 0 x y hP (H 0)
    have hb := shifted_square_of_coordinate_zero D hD 1 x y hP (H 1)
    have hc := shifted_square_of_coordinate_zero D hD 2 x y hP (H 2)
    simpa [root] using And.intro ha (And.intro hb hc)
  · rintro ⟨ha,hb,hc⟩
    exact half_of_squares D x y hD hP ha hb hc

/-- The class of a nonzero rational number. -/
def classOf (a : ℚ) (ha : a ≠ 0) : Additive SquareClass :=
  Additive.ofMul ((Units.mk0 a ha : ℚˣ) : SquareClass)

/-- The original block point and its original translate have the required images,
which are preserved by all positive odd multiples of the translate. -/
theorem block_kummer_images (D C L F : ℚ) (hD : D ≠ 0) (hC : C ≠ 0)
    (hL : L ≠ 0) (hF : F ≠ 0) (hblock : L ^ 2+3 = D * C ^ 2) (hfib : L ^ 2+4 = 5 * F ^ 2)
    (hR : (curve D).Nonsingular (5 * D * (L ^ 2+3)) (25 * D ^ 2 * L * C * F))
    (hS : (curve D).Nonsingular (-15/C ^ 2) (75 * L * F/C ^ 3)) :
    kummer D hD (Point.some _ _ hR) = (classOf 5 (by norm_num), classOf D hD) ∧
    kummer D hD (Point.some _ _ hS) =
      (classOf (-15) (by norm_num), classOf 5 (by norm_num)) ∧
    ∀ n : ℤ, kummer D hD ((2 * n+1) • (Point.some _ _ hS)) =
      (classOf (-15) (by norm_num), classOf 5 (by norm_num)) := by
  have hB : L ^ 2+3 ≠ 0 := by nlinarith [sq_nonneg L]
  have hxR : 5 * D * (L ^ 2+3) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hD) hB
  have hxR5 : 5 * D * (L ^ 2+3)+5 * D = 25 * D * F ^ 2 := by linear_combination 5 * D * hfib
  have hxR1 : 5 * D * (L ^ 2+3) ≠ -5 * D := by
    intro hz
    have H := mul_ne_zero (mul_ne_zero (by norm_num : (25:ℚ) ≠ 0) hD) (pow_ne_zero 2 hF)
    apply H
    rw [← hxR5, hz]
    ring
  have hxS : -15/C ^ 2 ≠ 0 := div_ne_zero (by norm_num) (pow_ne_zero _ hC)
  have hxS5 : -15/C ^ 2+5 * D = 5 * (L/C) ^ 2 := by
    field_simp [hC]
    nlinarith [hblock]
  have hxS1 : -15/C ^ 2 ≠ -5 * D := by
    intro hz
    have H := mul_ne_zero (by norm_num : (5:ℚ) ≠ 0) (pow_ne_zero 2 (div_ne_zero hL hC))
    apply H
    rw [← hxS5, hz]
    ring
  have himageR : kummer D hD (Point.some _ _ hR) =
      (classOf 5 (by norm_num), classOf D hD) := by
    apply Prod.ext
    · change ((descentUnit D hD 0 (.some _ _ hR) : ℚˣ) : SquareClass) =
        ((Units.mk0 5 (by norm_num) : ℚˣ) : SquareClass)
      rw [QuotientGroup.eq_iff_div_mem]
      refine ⟨Units.mk0 (D * C) (mul_ne_zero hD hC), ?_⟩
      apply Units.ext
      change (D * C) ^ 2 = descentRep D 0 (.some _ _ hR)/5
      rw [(descentRep_some_values D _ _ hR).1, if_neg hxR]
      field_simp
      nlinarith [hblock]
    · change ((descentUnit D hD 1 (.some _ _ hR) : ℚˣ) : SquareClass) =
        ((Units.mk0 D hD : ℚˣ) : SquareClass)
      rw [QuotientGroup.eq_iff_div_mem]
      refine ⟨Units.mk0 (5 * F) (mul_ne_zero (by norm_num) hF), ?_⟩
      apply Units.ext
      change (5 * F) ^ 2 = descentRep D 1 (.some _ _ hR)/D
      rw [(descentRep_some_values D _ _ hR).2.1, if_neg hxR1, hxR5]
      field_simp
      ring
  have himageS : kummer D hD (Point.some _ _ hS) =
      (classOf (-15) (by norm_num), classOf 5 (by norm_num)) := by
    apply Prod.ext
    · change ((descentUnit D hD 0 (.some _ _ hS) : ℚˣ) : SquareClass) =
        ((Units.mk0 (-15) (by norm_num) : ℚˣ) : SquareClass)
      rw [QuotientGroup.eq_iff_div_mem]
      refine ⟨Units.mk0 (1/C) (div_ne_zero one_ne_zero hC), ?_⟩
      apply Units.ext
      change (1/C) ^ 2 = descentRep D 0 (.some _ _ hS)/(-15)
      rw [(descentRep_some_values D _ _ hS).1, if_neg hxS]
      field_simp
    · change ((descentUnit D hD 1 (.some _ _ hS) : ℚˣ) : SquareClass) =
        ((Units.mk0 5 (by norm_num) : ℚˣ) : SquareClass)
      rw [QuotientGroup.eq_iff_div_mem]
      refine ⟨Units.mk0 (L/C) (div_ne_zero hL hC), ?_⟩
      apply Units.ext
      change (L/C) ^ 2 = descentRep D 1 (.some _ _ hS)/5
      rw [(descentRep_some_values D _ _ hS).2.1, if_neg hxS1, hxS5]
      field_simp
  refine ⟨himageR,himageS,?_⟩
  intro n
  have hd : (2 : ℤ) • kummer D hD (Point.some _ _ hS) = 0 := by
    simpa only [two_zsmul, map_add] using kummer_double D hD (Point.some _ _ hS)
  rw [map_zsmul, add_zsmul, one_zsmul, mul_zsmul]
  rw [smul_comm (2 : ℤ) n, hd, zsmul_zero, zero_add]
  exact himageS


/-- The block equations themselves construct both original affine points and identify
translation by the actual point `(0,0)` in the rational point group. -/
theorem block_translation (D C L F : ℚ) (hC : C ≠ 0)
    (hblock : L ^ 2 + 3 = D * C ^ 2) (hfib : L ^ 2 + 4 = 5 * F ^ 2) :
    ∃ (hR : (curve D).Nonsingular (5 * D * (L ^ 2 + 3)) (25 * D ^ 2 * L * C * F))
      (hT : (curve D).Nonsingular 0 0)
      (hS : (curve D).Nonsingular (-15 / C ^ 2) (75 * L * F / C ^ 3)),
      Point.some _ _ hR + Point.some _ _ hT = Point.some _ _ hS := by
  have hD : D ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hblock
    nlinarith [sq_nonneg L]
  letI : (curve D).IsElliptic := curve_is_elliptic D hD
  have hB : L ^ 2 + 3 ≠ 0 := by nlinarith [sq_nonneg L]
  have hx : 5 * D * (L ^ 2 + 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hD) hB
  have hReq : (curve D).Equation (5 * D * (L ^ 2 + 3))
      (25 * D ^ 2 * L * C * F) := by
    rw [equation_iff]
    calc
      (25 * D ^ 2 * L * C * F) ^ 2 =
          125 * D ^ 3 * L ^ 2 * (D * C ^ 2) * (5 * F ^ 2) := by ring
      _ = 125 * D ^ 3 * L ^ 2 * (L ^ 2 + 3) * (L ^ 2 + 4) := by
        rw [← hblock, ← hfib]
      _ = _ := by ring
  have hR := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp hReq
  have hT : (curve D).Nonsingular 0 0 := by
    apply (WeierstrassCurve.Affine.equation_iff_nonsingular).mp
    rw [equation_iff]
    ring
  have hSeq : (curve D).Equation (-15 / C ^ 2) (75 * L * F / C ^ 3) := by
    rw [equation_iff]
    field_simp [hC]
    linear_combination -1125 * L ^ 2 * hfib +
      1125 * (D * C ^ 2 + L ^ 2 + 1) * hblock
  have hS := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp hSeq
  refine ⟨hR, hT, hS, ?_⟩
  rw [Point.add_of_X_ne hx]
  have hslope : (curve D).slope (5 * D * (L ^ 2 + 3)) 0
      (25 * D ^ 2 * L * C * F) 0 = 5 * L * F / C := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
    simp only [sub_zero]
    rw [hblock]
    field_simp [hD, hC]
    <;> ring
  have hxadd : (curve D).addX (5 * D * (L ^ 2 + 3)) 0 (5 * L * F / C) =
      -15 / C ^ 2 := by
    change (5 * L * F / C) ^ 2 + 0 * (5 * L * F / C) - (-10 * D) -
      (5 * D * (L ^ 2 + 3)) - 0 = -15 / C ^ 2
    field_simp [hC]
    linear_combination -5 * L ^ 2 * hfib + (5 * L ^ 2 + 5) * hblock
  have hyadd : (curve D).addY (5 * D * (L ^ 2 + 3)) 0
      (25 * D ^ 2 * L * C * F) (5 * L * F / C) = 75 * L * F / C ^ 3 := by
    unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    rw [hxadd]
    change -(5 * L * F / C * (-15 / C ^ 2 - 5 * D * (L ^ 2 + 3)) +
      25 * D ^ 2 * L * C * F) - 0 * (-15 / C ^ 2) - 0 = 75 * L * F / C ^ 3
    field_simp [hC]
    linear_combination 25 * D * L * C ^ 2 * F * hblock
  simp only [hslope]
  exact (Point.some.injEq ..).mpr ⟨hxadd, hyadd⟩

end D5.S3.Factorization.Mordell.RationalKummer
