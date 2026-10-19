/- GID: D5/S3/Factorization/Mordell/FieldKummer
   generality: G
   mirror-B: D5/B/S3/Factorization/Mordell/FieldKummer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Total split-cubic Kummer maps and common projective covering fibers. -/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-! Total split-cubic descent over characteristic-zero fields. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Mordell.FieldKummer

open WeierstrassCurve WeierstrassCurve.Affine

universe u
variable {K : Type u} [Field K] [CharZero K] [DecidableEq K]

/-- A characteristic-zero field, with its actual field operations and equality decision. -/
structure Context where
  Carrier : Type u
  field : Field Carrier
  charZero : @CharZero Carrier field.toAddMonoidWithOne
  decEq : DecidableEq Carrier

attribute [instance] Context.field Context.charZero Context.decEq

/-- A nonzero twist over a characteristic-zero field. -/
structure Twist where
  k : Context.{u}
  d : k.Carrier
  hd : d ≠ 0

/-- A change of nonzero square representatives of one twist. -/
structure RepresentativeChange where
  twist : Twist.{u}
  b₁ : twist.k.Carrierˣ
  b₂ : twist.k.Carrierˣ
  b₁' : twist.k.Carrierˣ
  b₂' : twist.k.Carrierˣ
  u : twist.k.Carrierˣ
  v : twist.k.Carrierˣ
  h₁ : (b₁' : twist.k.Carrier)*(u : twist.k.Carrier)^2 = (b₁ : twist.k.Carrier)
  h₂ : (b₂' : twist.k.Carrier)*(v : twist.k.Carrier)^2 = (b₂ : twist.k.Carrier)

/-- The field twist in the ordered descent convention `(x,x+5D)`. -/
def curve (D : K) : WeierstrassCurve.Affine K := ⟨0, -10 * D, 0, -75 * D ^ 2, 0⟩

private theorem equation_iff (D x y : K) :
    (curve D).Equation x y ↔ y ^ 2 = x * (x + 5 * D) * (x - 15 * D) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [curve]
  constructor <;> intro h <;> linear_combination h

/-- Nonzero twists are elliptic. -/
theorem curve_is_elliptic (C : Context.{u}) (D : C.Carrier) (hD : D ≠ 0) : (curve D).IsElliptic := by
  constructor
  apply isUnit_iff_ne_zero.mpr
  have hdisc : (curve D).Δ = 36000000 * D ^ 6 := by
    simp [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  rw [hdisc]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ hD)

/-- The three ordered field roots. -/
def root (D : K) (i : Fin 3) : K := ![0, -5 * D, 15 * D] i

private def derivative (D e : K) : K := 3 * e ^ 2 - 20 * D * e - 75 * D ^ 2

private theorem root_equation (D : K) (i : Fin 3) :
    root D i * (root D i + 5 * D) * (root D i - 15 * D) = 0 := by
  fin_cases i <;> simp [root]

private theorem derivative_ne_zero (D : K) (hD : D ≠ 0) (i : Fin 3) :
    derivative D (root D i) ≠ 0 := by
  fin_cases i <;> dsimp [derivative, root] <;> ring_nf <;> simp_all

private theorem shifted_equation (D x y : K) (i : Fin 3)
    (h : (curve D).Equation x y) :
    y ^ 2 = (x - root D i) ^ 3 + (3 * root D i - 10 * D) * (x - root D i) ^ 2 +
      derivative D (root D i) * (x - root D i) := by
  have he := root_equation D i
  have hy := (equation_iff D x y).mp h
  dsimp [derivative]
  linear_combination hy + he

/-- A shifted coordinate is replaced by the derivative at its zero. -/
def descentRep (D : K) (i : Fin 3) : (curve D).Point → K
  | .zero => 1
  | .some x _ _ => if x = root D i then derivative D (root D i) else x - root D i

private theorem descentRep_ne_zero (D : K) (hD : D ≠ 0) (i : Fin 3)
    (P : (curve D).Point) : descentRep D i P ≠ 0 := by
  cases P with
  | zero => exact one_ne_zero
  | some x y h =>
    dsimp [descentRep]
    split_ifs with hx
    · exact derivative_ne_zero D hD i
    · exact sub_ne_zero.mpr hx

private def rep (B u : K) : K := if u = 0 then B else u

private theorem rep_triple_square (B u v w l b : K) (hB : B ≠ 0)
    (hpair : u * v + u * w + v * w = B - 2 * l * b) (hprod : u * v * w = b ^ 2) :
    IsSquare (rep B u * rep B v * rep B w) := by
  by_cases hu : u = 0
  · subst u
    have hb : b = 0 := by
      apply (sq_eq_zero_iff).mp
      linear_combination -hprod
    rw [hb] at hpair
    have hvw : v * w = B := by linear_combination hpair
    have hv : v ≠ 0 := by intro h; apply hB; rw [← hvw, h, zero_mul]
    have hw : w ≠ 0 := by intro h; apply hB; rw [← hvw, h, mul_zero]
    refine ⟨B, ?_⟩
    have he : B * v * w = B * B := by rw [mul_assoc, hvw]
    simpa [rep, hv, hw] using he
  by_cases hv : v = 0
  · subst v
    have hb : b = 0 := by
      apply (sq_eq_zero_iff).mp
      linear_combination -hprod
    rw [hb] at hpair
    have huw : u * w = B := by linear_combination hpair
    have hw : w ≠ 0 := by intro h; apply hB; rw [← huw, h, mul_zero]
    refine ⟨B, ?_⟩
    have he : u * B * w = B * B := by calc
      u * B * w = B * (u * w) := by ring
      _ = B * B := by rw [huw]
    simpa [rep, hu, hw] using he
  by_cases hw : w = 0
  · subst w
    have hb : b = 0 := by
      apply (sq_eq_zero_iff).mp
      linear_combination -hprod
    rw [hb] at hpair
    have huv : u * v = B := by linear_combination hpair
    refine ⟨B, ?_⟩
    have he : u * v * B = B * B := by rw [huv]
    simpa [rep, hu, hv] using he
  · refine ⟨b, ?_⟩
    simpa [rep, hu, hv, hw, pow_two] using hprod

private theorem secant_coefficients (A B u v y z : K) (huv : u ≠ v)
    (hy : y ^ 2 = u ^ 3 + A * u ^ 2 + B * u) (hz : z ^ 2 = v ^ 3 + A * v ^ 2 + B * v) :
    let l := (y-z)/(u-v)
    let b := y-l * u
    let w := l ^ 2-A-u-v
    u * v + u * w + v * w = B-2 * l * b ∧ u * v * w = b ^ 2 := by
  dsimp
  constructor <;> field_simp [sub_ne_zero.mpr huv] <;> grobner

private theorem tangent_coefficients (A B u y : K) (hy0 : y ≠ 0)
    (hy : y ^ 2 = u ^ 3 + A * u ^ 2 + B * u) :
    let l := (3 * u ^ 2+2 * A * u+B)/(2 * y)
    let b := y-l * u
    let w := l ^ 2-A-u-u
    u * u + u * w + u * w = B-2 * l * b ∧ u * u * w = b ^ 2 := by
  dsimp
  constructor <;> field_simp [hy0] <;> grobner

/-- Each total descent coordinate has square triple product on an actual sum. -/
theorem descentRep_add_square (C : Context.{u}) (D : C.Carrier) (hD : D ≠ 0) (i : Fin 3)
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
              have hf : (y-t) * (y+t) = 0 := by linear_combination hxy - hzt
              rcases mul_eq_zero.mp hf with hh | hh
              · linear_combination hh
              · exact (hn (by linear_combination hh)).elim
            subst t
            have hy0 : y ≠ 0 := by
              intro hz; apply hv; simp [hz, curve, negY]
            have H := tangent_coefficients A B (x-e) y hy0 hxy
            have hl : l = (3 * (x-e) ^ 2+2 * A * (x-e)+B)/(2 * y) := by
              dsimp [l]
              rw [slope_of_Y_ne rfl (by simp only [curve, negY, zero_mul, sub_zero]; intro hz; apply hy0; linear_combination hz / 2)]
              dsimp [curve, negY, A, B, derivative]
              congr 1 <;> ring
            rw [hl]
            convert H using 1 <;> dsimp [A, B, addX, curve] <;> ring
          · have H := secant_coefficients A B (x-e) (z-e) y t
                (by intro h; apply hxz; linear_combination h) hxy hzt
            have hl : l = (y-t)/((x-e)-(z-e)) := by
              dsimp [l]
              rw [slope_of_X_ne hxz]
              congr 1 <;> ring
            rw [hl]
            convert H using 1 <;> dsimp [A, B, addX, curve] <;> ring
        have H := rep_triple_square B (x-e) (z-e) ((curve D).addX x z l-e)
          l (y-l * (x-e)) (derivative_ne_zero D hD i) hc.1 hc.2
        simpa only [descentRep, rep, sub_eq_zero, e, B, l] using H


/-- Field units modulo squares, using the standard power quotient. -/
abbrev SquareClass (K : Type u) [Field K] := Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range

private theorem squareClass_mul_self (a : SquareClass K) : a * a = 1 := by
  induction a using Quotient.inductionOn with
  | h a =>
    change ((a * a : Kˣ) : SquareClass K) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨a, by simp [pow_two]⟩

private theorem unit_class_one_iff (u : Kˣ) :
    (u : SquareClass K) = 1 ↔ IsSquare (u : K) := by
  rw [QuotientGroup.eq_one_iff, MonoidHom.mem_range]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨(v : K), ?_⟩
    have H := congrArg (fun w : Kˣ => (w : K)) hv
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

def descentUnit (D : K) (hD : D ≠ 0) (i : Fin 3) (P : (curve D).Point) : Kˣ :=
  Units.mk0 (descentRep D i P) (descentRep_ne_zero D hD i P)

/-- The total single-coordinate Kummer homomorphism. -/
def coordinate (D : K) (hD : D ≠ 0) (i : Fin 3) :
    (curve D).Point →+ Additive (SquareClass K) where
  toFun P := Additive.ofMul ((descentUnit D hD i P : Kˣ) : SquareClass K)
  map_zero' := by
    change ((descentUnit D hD i 0 : Kˣ) : SquareClass K) = 1
    have h : descentUnit D hD i 0 = 1 := by ext; rfl
    rw [h]; rfl
  map_add' P Q := by
    change ((descentUnit D hD i (P+Q) : Kˣ) : SquareClass K) =
      ((descentUnit D hD i P : Kˣ) : SquareClass K) *
      ((descentUnit D hD i Q : Kˣ) : SquareClass K)
    let a : SquareClass K := (descentUnit D hD i P : Kˣ)
    let b : SquareClass K := (descentUnit D hD i Q : Kˣ)
    let c : SquareClass K := (descentUnit D hD i (P+Q) : Kˣ)
    have H : a * b * c = 1 := by
      change (((descentUnit D hD i P * descentUnit D hD i Q *
        descentUnit D hD i (P+Q)) : Kˣ) : SquareClass K) = 1
      apply (unit_class_one_iff _).mpr
      exact descentRep_add_square ⟨K,inferInstance,inferInstance,inferInstance⟩ D hD i P Q
    change c = a * b
    calc
      c = (a * b * c) * c := by rw [H, one_mul]
      _ = a * b := by rw [mul_assoc, squareClass_mul_self c, mul_one]

/-- The complete field Kummer map in the ordered pair convention `(x,x+5D)`. -/
def kummer (D : K) (hD : D ≠ 0) :
    (curve D).Point →+ (Additive (SquareClass K) × Additive (SquareClass K)) :=
  (coordinate D hD 0).prod (coordinate D hD 1)

private theorem descentRep_some_values (D x y : K) (hP : (curve D).Nonsingular x y) :
    descentRep D 0 (.some x y hP) = (if x = 0 then -75 * D ^ 2 else x) ∧
    descentRep D 1 (.some x y hP) = (if x = -5 * D then 100 * D ^ 2 else x+5 * D) ∧
    descentRep D 2 (.some x y hP) = (if x = 15 * D then 300 * D ^ 2 else x-15 * D) := by
  dsimp [descentRep, root, derivative]
  constructor
  · split_ifs <;> simp_all <;> ring
  constructor <;> split_ifs <;> simp_all <;> ring

/-- The three descent classes have product one, including all field two-torsion points. -/
theorem descentRep_product_square (C : Context.{u}) (D : C.Carrier) (hD : D ≠ 0) (P : (curve D).Point) :
    IsSquare (descentRep D 0 P * descentRep D 1 P * descentRep D 2 P) := by
  cases P with
  | zero => exact ⟨1, by norm_num [descentRep]⟩
  | some x y h =>
    obtain ⟨hval0, hval1, hval2⟩ := descentRep_some_values D x y h
    rw [hval0, hval1, hval2]
    by_cases h0 : x = 0
    · subst x
      have h1 : (0:C.Carrier) ≠ -5 * D := by intro hz; apply hD; linear_combination hz / 5
      have h2 : (0:C.Carrier) ≠ 15 * D := by intro hz; apply hD; linear_combination -hz / 15
      refine ⟨75 * D ^ 2, ?_⟩
      simp only [ite_true, if_pos rfl, if_neg h1, if_neg h2]
      ring
    by_cases h1 : x = -5 * D
    · have h2 : x ≠ 15 * D := by intro hz; apply hD; rw [h1] at hz; linear_combination -hz / 20
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



/-- A unit represented in the additive squareclass group. -/
def unitClass (b : Kˣ) : Additive (SquareClass K) := Additive.ofMul (b : SquareClass K)

private theorem class_eq_iff (a b : Kˣ) :
    unitClass a = unitClass b ↔ ∃ z : K, (a : K) = (b : K) * z ^ 2 := by
  change (a : SquareClass K) = (b : SquareClass K) ↔ _
  rw [QuotientGroup.eq_iff_div_mem, MonoidHom.mem_range]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have h := congrArg (fun v : Kˣ => (v : K)) hz
    have h' : (z : K) ^ 2 = (a : K) / (b : K) := by simpa using h
    exact (eq_div_iff b.ne_zero).mp h' |>.symm.trans (by ring)
  · rintro ⟨z, hz⟩
    have hz0 : z ≠ 0 := by
      intro h; apply a.ne_zero; rw [hz, h]; ring
    refine ⟨Units.mk0 z hz0, ?_⟩
    apply Units.ext
    have h : z ^ 2 = (a : K) / (b : K) := by
      rw [hz]
      field_simp
    simpa using h

private theorem coordinate_eq_iff (d : K) (hd : d ≠ 0) (i : Fin 3)
    (P : (curve d).Point) (b : Kˣ) :
    coordinate d hd i P = unitClass b ↔
      ∃ z : K, descentRep d i P = (b : K) * z ^ 2 :=
  class_eq_iff (descentUnit d hd i P) b

private theorem third_coordinate (d : K) (hd : d ≠ 0) (P : (curve d).Point) :
    coordinate d hd 2 P = coordinate d hd 0 P + coordinate d hd 1 P := by
  have h : (coordinate d hd 0 P).toMul * (coordinate d hd 1 P).toMul *
      (coordinate d hd 2 P).toMul = 1 := by
    change (((descentUnit d hd 0 P * descentUnit d hd 1 P *
      descentUnit d hd 2 P) : Kˣ) : SquareClass K) = 1
    exact (unit_class_one_iff _).mpr (descentRep_product_square ⟨K,inferInstance,inferInstance,inferInstance⟩ d hd P)
  change (coordinate d hd 2 P).toMul =
    (coordinate d hd 0 P).toMul * (coordinate d hd 1 P).toMul
  calc
    _ = ((coordinate d hd 0 P).toMul * (coordinate d hd 1 P).toMul *
        (coordinate d hd 2 P).toMul) * (coordinate d hd 2 P).toMul := by rw [h, one_mul]
    _ = _ := by rw [mul_assoc, squareClass_mul_self, mul_one]

/-- One common nonzero homogeneous tuple satisfying the two covering equations.
No image or solubility condition is used in this definition. -/
structure CommonRep (d : K) (b₁ b₂ : Kˣ) (b₃ : K) where
  t : K
  z₁ : K
  z₂ : K
  z₃ : K
  nonzero : t ≠ 0 ∨ z₁ ≠ 0 ∨ z₂ ≠ 0 ∨ z₃ ≠ 0
  eq₁₂ : (b₂ : K) * z₂ ^ 2 - (b₁ : K) * z₁ ^ 2 = 5 * d * t ^ 2
  eq₁₃ : (b₁ : K) * z₁ ^ 2 - b₃ * z₃ ^ 2 = 15 * d * t ^ 2

/-- The product-normalized common tuple. -/
abbrev CoveringRep (d : K) (b₁ b₂ : Kˣ) := CommonRep d b₁ b₂ ((b₁ : K)*(b₂ : K))

private theorem third_equation (d : K) (b₁ b₂ : Kˣ) (c : CoveringRep d b₁ b₂) :
    (b₂ : K) * c.z₂ ^ 2 - (b₁ : K) * (b₂ : K) * c.z₃ ^ 2 =
      20 * d * c.t ^ 2 := by
  linear_combination c.eq₁₂ + c.eq₁₃

/-- Common nonzero scaling of the entire tuple. -/
def CommonRel (d : K) (b₁ b₂ : Kˣ) (b₃ : K) (c c' : CommonRep d b₁ b₂ b₃) : Prop :=
  ∃ a : Kˣ, c'.t = (a : K) * c.t ∧ c'.z₁ = (a : K) * c.z₁ ∧
    c'.z₂ = (a : K) * c.z₂ ∧ c'.z₃ = (a : K) * c.z₃

private def commonSetoid (d : K) (b₁ b₂ : Kˣ) (b₃ : K) : Setoid (CommonRep d b₁ b₂ b₃) where
  r := CommonRel d b₁ b₂ b₃
  iseqv := {
    refl := fun c => ⟨1, by simp⟩
    symm := by
      rintro c c' ⟨a, ht, h₁, h₂, h₃⟩
      refine ⟨a⁻¹, ?_, ?_, ?_, ?_⟩ <;>
        simp only [Units.val_inv_eq_inv_val] <;>
        first | (rw [ht]; field_simp) | (rw [h₁]; field_simp) |
          (rw [h₂]; field_simp) | (rw [h₃]; field_simp)
    trans := by
      rintro c c' c'' ⟨a, ht, h₁, h₂, h₃⟩ ⟨b, kt, k₁, k₂, k₃⟩
      exact ⟨b*a, by simpa [ht, mul_assoc] using kt,
        by simpa [h₁, mul_assoc] using k₁,
        by simpa [h₂, mul_assoc] using k₂,
        by simpa [h₃, mul_assoc] using k₃⟩ }

/-- Common projective scaling with product-normalized third coefficient. -/
abbrev ProjectiveRel (d : K) (b₁ b₂ : Kˣ) := CommonRel d b₁ b₂ ((b₁ : K)*(b₂ : K))

private abbrev coveringSetoid (d : K) (b₁ b₂ : Kˣ) := commonSetoid d b₁ b₂ ((b₁ : K)*(b₂ : K))

/-- Independently chosen third coefficient, with the same common projective scaling. -/
def CommonCovering (d : K) (b₁ b₂ : Kˣ) (b₃ : K) := Quotient (commonSetoid d b₁ b₂ b₃)

/-- The common projective two-covering, modulo common unit scaling. -/
def Covering (d : K) (b₁ b₂ : Kˣ) := Quotient (coveringSetoid d b₁ b₂)

private theorem covering_equation (d : K) (b₁ b₂ : Kˣ)
    (c : CoveringRep d b₁ b₂) (ht : c.t ≠ 0) :
    (curve d).Equation ((b₁ : K) * c.z₁ ^ 2 / c.t ^ 2)
      ((b₁ : K) * (b₂ : K) * c.z₁ * c.z₂ * c.z₃ / c.t ^ 3) := by
  rw [equation_iff]
  have h₂ : (b₁ : K) * c.z₁ ^ 2 / c.t ^ 2 + 5*d =
      (b₂ : K) * c.z₂ ^ 2 / c.t ^ 2 := by
    field_simp
    linear_combination -c.eq₁₂
  have h₃ : (b₁ : K) * c.z₁ ^ 2 / c.t ^ 2 - 15*d =
      (b₁ : K) * (b₂ : K) * c.z₃ ^ 2 / c.t ^ 2 := by
    field_simp
    linear_combination third_equation d b₁ b₂ c - c.eq₁₂
  rw [h₂, h₃]
  field_simp
  <;> ring

/-- Projection to the actual point group; its ordinate is part of the definition. -/
def projectRep (d : K) (hd : d ≠ 0) (b₁ b₂ : Kˣ)
    (c : CoveringRep d b₁ b₂) : (curve d).Point :=
  if ht : c.t = 0 then 0 else
    .some ((b₁ : K)*c.z₁^2/c.t^2) ((b₁ : K)*(b₂ : K)*c.z₁*c.z₂*c.z₃/c.t^3)
      (by
        letI := curve_is_elliptic ⟨K,inferInstance,inferInstance,inferInstance⟩ d hd
        exact equation_iff_nonsingular.mp (covering_equation d b₁ b₂ c ht))

private theorem projectRep_scaling (d : K) (hd : d ≠ 0) (b₁ b₂ : Kˣ)
    (c c' : CoveringRep d b₁ b₂) (h : ProjectiveRel d b₁ b₂ c c') :
    projectRep d hd b₁ b₂ c = projectRep d hd b₁ b₂ c' := by
  obtain ⟨a, ht, h₁, h₂, h₃⟩ := h
  by_cases h0 : c.t = 0
  · have h0' : c'.t = 0 := by rw [ht,h0,mul_zero]
    simp [projectRep,h0,h0']
  · have h0' : c'.t ≠ 0 := by rw [ht]; exact mul_ne_zero a.ne_zero h0
    simp only [projectRep, dif_neg h0, dif_neg h0']
    apply (Point.some.injEq ..).mpr
    constructor
    · rw [ht,h₁]
      field_simp [a.ne_zero,h0]
      <;> ring
    · rw [ht,h₁,h₂,h₃]
      field_simp [a.ne_zero,h0]
      <;> ring

/-- Projection is well defined on the projective quotient. -/
def project (d : K) (hd : d ≠ 0) (b₁ b₂ : Kˣ) :
    Covering d b₁ b₂ → (curve d).Point :=
  Quotient.lift (projectRep d hd b₁ b₂) (projectRep_scaling d hd b₁ b₂)


private theorem shifted_of_coordinate (d : K) (hd : d ≠ 0) (i : Fin 3)
    (x y : K) (hP : (curve d).Nonsingular x y) (b : Kˣ)
    (h : coordinate d hd i (.some x y hP) = unitClass b) :
    ∃ z : K, x-root d i = (b : K)*z^2 := by
  by_cases hx : x = root d i
  · exact ⟨0, by simp [hx]⟩
  · obtain ⟨z,hz⟩ := (coordinate_eq_iff d hd i _ b).mp h
    exact ⟨z, by simpa [descentRep,hx] using hz⟩

private theorem affine_class_iff (d : K) (hd : d ≠ 0) (b₁ b₂ : Kˣ)
    (x y : K) (hP : (curve d).Nonsingular x y) :
    kummer d hd (.some x y hP) = (unitClass b₁,unitClass b₂) ↔
      ∃ a b c : K, x = (b₁ : K)*a^2 ∧ x+5*d = (b₂ : K)*b^2 ∧
        x-15*d = (b₁ : K)*(b₂ : K)*c^2 := by
  constructor
  · intro h
    have h₀ : coordinate d hd 0 (.some x y hP) = unitClass b₁ := congrArg Prod.fst h
    have h₁ : coordinate d hd 1 (.some x y hP) = unitClass b₂ := congrArg Prod.snd h
    have h₂ : coordinate d hd 2 (.some x y hP) = unitClass (b₁*b₂) := by
      rw [third_coordinate,h₀,h₁]
      rfl
    obtain ⟨a,ha⟩ := shifted_of_coordinate d hd 0 x y hP b₁ h₀
    obtain ⟨b,hb⟩ := shifted_of_coordinate d hd 1 x y hP b₂ h₁
    obtain ⟨c,hc⟩ := shifted_of_coordinate d hd 2 x y hP (b₁*b₂) h₂
    exact ⟨a,b,c,by simpa [root] using ha,by simpa [root] using hb,
      by simpa [root] using hc⟩
  · rintro ⟨a,b,c,ha,hb,hc⟩
    obtain ⟨h₀,h₁,h₂⟩ := descentRep_some_values d x y hP
    apply Prod.ext
    · apply (coordinate_eq_iff d hd 0 _ b₁).mpr
      by_cases hx : x = 0
      · refine ⟨(b₂ : K)*b*c, ?_⟩
        rw [h₀,if_pos hx]
        have hh : (x+5*d)*(x-15*d) = -75*d^2 := by rw [hx]; ring
        rw [hb,hc] at hh
        linear_combination -hh
      · exact ⟨a, by rw [h₀,if_neg hx]; exact ha⟩
    · apply (coordinate_eq_iff d hd 1 _ b₂).mpr
      by_cases hx : x = -5*d
      · refine ⟨(b₁ : K)*a*c, ?_⟩
        rw [h₁,if_pos hx]
        have hh : x*(x-15*d) = 100*d^2 := by rw [hx]; ring
        rw [hc,ha] at hh
        linear_combination -hh
      · exact ⟨b, by rw [h₁,if_neg hx]; exact hb⟩

private theorem projectRep_image (d : K) (hd : d ≠ 0) (b₁ b₂ : Kˣ)
    (c : CoveringRep d b₁ b₂) :
    kummer d hd (projectRep d hd b₁ b₂ c) = (unitClass b₁,unitClass b₂) := by
  by_cases ht : c.t = 0
  · have h₁₂ := c.eq₁₂
    have h₁₃ := c.eq₁₃
    rw [ht] at h₁₂ h₁₃
    have hz₁ : c.z₁ ≠ 0 := by
      intro hz₁
      have hz₂ : c.z₂ = 0 := by
        have hh : c.z₂^2 = 0 := by
          apply (mul_eq_zero.mp (show (b₂ : K)*c.z₂^2 = 0 by
            simpa [hz₁] using h₁₂)).resolve_left b₂.ne_zero
        exact sq_eq_zero_iff.mp hh
      have hz₃ : c.z₃ = 0 := by
        have hh : c.z₃^2 = 0 := by
          apply (mul_eq_zero.mp (show ((b₁ : K)*(b₂ : K))*c.z₃^2 = 0 by
            simpa [hz₁] using congrArg Neg.neg h₁₃)).resolve_left (mul_ne_zero b₁.ne_zero b₂.ne_zero)
        exact sq_eq_zero_iff.mp hh
      rcases c.nonzero with hh|hh|hh|hh <;> contradiction
    have hz₂ : c.z₂ ≠ 0 := by
      intro hz₂
      apply hz₁
      apply sq_eq_zero_iff.mp
      apply (mul_eq_zero.mp (show (b₁ : K)*c.z₁^2=0 by
        simpa [hz₂] using h₁₂.symm)).resolve_left b₁.ne_zero
    have hz₃ : c.z₃ ≠ 0 := by
      intro hz₃
      apply hz₁
      apply sq_eq_zero_iff.mp
      apply (mul_eq_zero.mp (show (b₁ : K)*c.z₁^2=0 by
        simpa [hz₃] using h₁₃)).resolve_left b₁.ne_zero
    have hb₂ : (b₂ : K) = (c.z₁/c.z₃)^2 := by
      field_simp [hz₃]
      have hh : c.z₁^2 = (b₂ : K)*c.z₃^2 := by
        apply (mul_left_cancel₀ b₁.ne_zero)
        linear_combination h₁₃
      exact hh.symm
    have hb₁ : (b₁ : K) = (c.z₂/c.z₃)^2 := by
      field_simp [hz₃]
      have hh : (b₁ : K)*c.z₁^2 = (b₂ : K)*c.z₂^2 := by linear_combination -h₁₂
      have hk : c.z₁^2 = (b₂ : K)*c.z₃^2 := by
        apply (mul_left_cancel₀ b₁.ne_zero)
        linear_combination h₁₃
      rw [hk] at hh
      exact mul_left_cancel₀ b₂.ne_zero (by linear_combination hh)
    have hclass₁ : unitClass b₁ = 0 := by
      change (b₁ : SquareClass K) = 1
      exact (unit_class_one_iff _).mpr ⟨c.z₂/c.z₃,by simpa [pow_two] using hb₁⟩
    have hclass₂ : unitClass b₂ = 0 := by
      change (b₂ : SquareClass K) = 1
      exact (unit_class_one_iff _).mpr ⟨c.z₁/c.z₃,by simpa [pow_two] using hb₂⟩
    simp only [projectRep,dif_pos ht,map_zero,hclass₁,hclass₂]
    rfl
  · simp only [projectRep,dif_neg ht]
    apply (affine_class_iff d hd b₁ b₂ _ _ _).mpr
    refine ⟨c.z₁/c.t,c.z₂/c.t,c.z₃/c.t,?_,?_,?_⟩
    · field_simp
    · field_simp [ht]
      linear_combination -c.eq₁₂
    · field_simp [ht]
      linear_combination c.eq₁₃


private theorem affine_preimage (d : K) (hd : d ≠ 0) (b₁ b₂ : Kˣ)
    (x y : K) (hP : (curve d).Nonsingular x y)
    (h : kummer d hd (.some x y hP) = (unitClass b₁,unitClass b₂)) :
    ∃ c : CoveringRep d b₁ b₂, projectRep d hd b₁ b₂ c = .some x y hP := by
  obtain ⟨a,b,c,ha,hb,hc⟩ := (affine_class_iff d hd b₁ b₂ x y hP).mp h
  have hy : ((b₁ : K)*(b₂ : K)*a*b*c)^2 = y^2 := by
    rw [(equation_iff d x y).mp hP.1]
    calc
      _ = ((b₁ : K)*a^2)*((b₂ : K)*b^2)*((b₁ : K)*(b₂ : K)*c^2) := by ring
      _ = _ := by rw [←ha,←hb,←hc]
  have hsign : ((b₁ : K)*(b₂ : K)*a*b*c-y)*
      ((b₁ : K)*(b₂ : K)*a*b*c+y) = 0 := by linear_combination hy
  have construct (a' : K) (ha' : x = (b₁ : K)*a'^2)
      (hy' : (b₁ : K)*(b₂ : K)*a'*b*c = y) :
      ∃ c : CoveringRep d b₁ b₂, projectRep d hd b₁ b₂ c = .some x y hP := by
    let r : CoveringRep d b₁ b₂ := {
      t := 1, z₁ := a', z₂ := b, z₃ := c,
      nonzero := Or.inl one_ne_zero,
      eq₁₂ := by linear_combination -hb+ha',
      eq₁₃ := by linear_combination -ha'+hc }
    refine ⟨r,?_⟩
    simp only [projectRep, r, one_ne_zero, ↓reduceDIte, one_pow,div_one]
    exact (Point.some.injEq ..).mpr ⟨ha'.symm,hy'⟩
  rcases mul_eq_zero.mp hsign with hp|hn
  · exact construct a ha (by linear_combination hp)
  · exact construct (-a) (by simpa using ha) (by linear_combination -hn)

private theorem infinity_preimage (d : K) (hd : d ≠ 0) (b₁ b₂ : Kˣ)
    (h : kummer d hd 0 = (unitClass b₁,unitClass b₂)) :
    ∃ c : CoveringRep d b₁ b₂, projectRep d hd b₁ b₂ c = 0 := by
  have h₁ : unitClass b₁ = 0 := by simpa using (congrArg Prod.fst h).symm
  have h₂ : unitClass b₂ = 0 := by simpa using (congrArg Prod.snd h).symm
  obtain ⟨a,ha⟩ := (unit_class_one_iff b₁).mp h₁
  obtain ⟨b,hb⟩ := (unit_class_one_iff b₂).mp h₂
  let c : CoveringRep d b₁ b₂ := {
    t := 0,z₁ := b,z₂ := a,z₃ := 1,
    nonzero := Or.inr (Or.inr (Or.inr one_ne_zero)),
    eq₁₂ := by rw [ha,hb]; ring,
    eq₁₃ := by rw [hb]; ring }
  exact ⟨c,by simp [projectRep,c]⟩

/-- The exact fiber over every actual point is its complete Kummer class.
Infinity, all root points, and every allowed zero coordinate are included. -/
theorem covering_fiber (T : Twist.{u}) (b₁ b₂ : T.k.Carrierˣ)
    (P : (curve T.d).Point) :
    (∃ c : Covering T.d b₁ b₂, project T.d T.hd b₁ b₂ c = P) ↔
      kummer T.d T.hd P = (unitClass b₁,unitClass b₂) := by
  constructor
  · rintro ⟨c,hc⟩
    revert hc
    induction c using Quotient.inductionOn with
    | h c =>
      intro hc
      rw [←hc]
      exact projectRep_image T.d T.hd b₁ b₂ c
  · intro h
    cases P with
    | zero =>
      obtain ⟨c,hc⟩ := infinity_preimage T.d T.hd b₁ b₂ h
      exact ⟨Quotient.mk _ c,hc⟩
    | some x y hP =>
      obtain ⟨c,hc⟩ := affine_preimage T.d T.hd b₁ b₂ x y hP h
      exact ⟨Quotient.mk _ c,hc⟩

private def rebaseRep (d : K) (b₁ b₂ b₁' b₂' u v : Kˣ)
    (h₁ : (b₁' : K)*(u : K)^2 = (b₁ : K))
    (h₂ : (b₂' : K)*(v : K)^2 = (b₂ : K))
    (c : CoveringRep d b₁ b₂) : CoveringRep d b₁' b₂' where
  t := c.t
  z₁ := (u : K)*c.z₁
  z₂ := (v : K)*c.z₂
  z₃ := (u : K)*(v : K)*c.z₃
  nonzero := c.nonzero.imp_right (fun h => h.imp
    (mul_ne_zero u.ne_zero) (fun h => h.imp (mul_ne_zero v.ne_zero)
      (mul_ne_zero (mul_ne_zero u.ne_zero v.ne_zero))))
  eq₁₂ := by
    calc
      _ = ((b₂' : K)*(v : K)^2)*c.z₂^2 - ((b₁' : K)*(u : K)^2)*c.z₁^2 := by ring
      _ = _ := by rw [h₁,h₂]; exact c.eq₁₂
  eq₁₃ := by
    calc
      _ = ((b₁' : K)*(u : K)^2)*c.z₁^2 -
        ((b₁' : K)*(u : K)^2)*((b₂' : K)*(v : K)^2)*c.z₃^2 := by ring
      _ = _ := by rw [h₁,h₂]; exact c.eq₁₃

private theorem rebaseRel (d : K) (b₁ b₂ b₁' b₂' u v : Kˣ)
    (h₁ : (b₁' : K)*(u : K)^2 = (b₁ : K))
    (h₂ : (b₂' : K)*(v : K)^2 = (b₂ : K))
    (c c' : CoveringRep d b₁ b₂) (h : ProjectiveRel d b₁ b₂ c c') :
    ProjectiveRel d b₁' b₂' (rebaseRep d b₁ b₂ b₁' b₂' u v h₁ h₂ c)
      (rebaseRep d b₁ b₂ b₁' b₂' u v h₁ h₂ c') := by
  obtain ⟨a,ht,hz₁,hz₂,hz₃⟩ := h
  refine ⟨a,ht,?_,?_,?_⟩ <;> dsimp [rebaseRep]
  · rw [hz₁]; ring
  · rw [hz₂]; ring
  · rw [hz₃]; ring

private theorem inverse_coeff (b b' u : Kˣ)
    (h : (b' : K)*(u : K)^2 = (b : K)) :
    (b : K)*(u⁻¹ : Kˣ)^2 = (b' : K) := by
  simp only [Units.val_inv_eq_inv_val]
  rw [←h]
  field_simp

/-- Changing both nonzero square representatives is an equivalence of common projective loci. -/
def changeRepresentatives (d : K) (b₁ b₂ b₁' b₂' u v : Kˣ)
    (h₁ : (b₁' : K)*(u : K)^2 = (b₁ : K))
    (h₂ : (b₂' : K)*(v : K)^2 = (b₂ : K)) :
    Covering d b₁ b₂ ≃ Covering d b₁' b₂' where
  toFun := Quotient.map (rebaseRep d b₁ b₂ b₁' b₂' u v h₁ h₂)
    (rebaseRel d b₁ b₂ b₁' b₂' u v h₁ h₂)
  invFun := Quotient.map (rebaseRep d b₁' b₂' b₁ b₂ u⁻¹ v⁻¹
    (inverse_coeff b₁ b₁' u h₁) (inverse_coeff b₂ b₂' v h₂))
    (rebaseRel d b₁' b₂' b₁ b₂ u⁻¹ v⁻¹
      (inverse_coeff b₁ b₁' u h₁) (inverse_coeff b₂ b₂' v h₂))
  left_inv := by
    intro c
    induction c using Quotient.inductionOn with
    | h c =>
      apply Quotient.sound
      refine ⟨1,?_,?_,?_,?_⟩ <;> dsimp [rebaseRep] <;>
        simp only [Units.val_one,one_mul,Units.val_inv_eq_inv_val] <;>
        field_simp <;> ring
  right_inv := by
    intro c
    induction c using Quotient.inductionOn with
    | h c =>
      apply Quotient.sound
      refine ⟨1,?_,?_,?_,?_⟩ <;> dsimp [rebaseRep] <;>
        simp only [Units.val_one,one_mul,Units.val_inv_eq_inv_val] <;>
        field_simp <;> ring

/-- The equivalence preserves the actual ordinate as well as the abscissa, also at infinity. -/
theorem project_changeRepresentatives (a : RepresentativeChange.{u})
    (c : Covering a.twist.d a.b₁ a.b₂) :
    project a.twist.d a.twist.hd a.b₁' a.b₂'
        (changeRepresentatives a.twist.d a.b₁ a.b₂ a.b₁' a.b₂' a.u a.v a.h₁ a.h₂ c) =
      project a.twist.d a.twist.hd a.b₁ a.b₂ c := by
  rcases a with ⟨⟨ctx,d,hd⟩,b₁,b₂,b₁',b₂',u,v,h₁,h₂⟩
  induction c using Quotient.inductionOn with
  | h c =>
    change projectRep d hd b₁' b₂' (rebaseRep d b₁ b₂ b₁' b₂' u v h₁ h₂ c) =
      projectRep d hd b₁ b₂ c
    dsimp only [projectRep,rebaseRep]
    split_ifs with ht
    · rfl
    · apply (Point.some.injEq ..).mpr
      constructor
      · congr 1
        calc
          _ = ((b₁' : ctx.Carrier)*(u : ctx.Carrier)^2)*c.z₁^2 := by ring
          _ = _ := by rw [h₁]
      · congr 1
        calc
          _ = ((b₁' : ctx.Carrier)*(u : ctx.Carrier)^2)*((b₂' : ctx.Carrier)*(v : ctx.Carrier)^2)*c.z₁*c.z₂*c.z₃ := by ring
          _ = _ := by rw [h₁,h₂]


private def normalizeThirdRep (d : K) (b₁ b₂ b₃ w : Kˣ)
    (hw : (b₃ : K) = (b₁ : K)*(b₂ : K)*(w : K)^2)
    (c : CommonRep d b₁ b₂ b₃) : CoveringRep d b₁ b₂ where
  t := c.t
  z₁ := c.z₁
  z₂ := c.z₂
  z₃ := (w : K)*c.z₃
  nonzero := c.nonzero.imp_right (fun h => h.imp_right
    (fun h => h.imp_right (mul_ne_zero w.ne_zero)))
  eq₁₂ := c.eq₁₂
  eq₁₃ := by
    linear_combination c.eq₁₃ + hw*c.z₃^2

private def unnormalizeThirdRep (d : K) (b₁ b₂ b₃ w : Kˣ)
    (hw : (b₃ : K) = (b₁ : K)*(b₂ : K)*(w : K)^2)
    (c : CoveringRep d b₁ b₂) : CommonRep d b₁ b₂ b₃ where
  t := c.t
  z₁ := c.z₁
  z₂ := c.z₂
  z₃ := (w : K)⁻¹*c.z₃
  nonzero := c.nonzero.imp_right (fun h => h.imp_right
    (fun h => h.imp_right (mul_ne_zero (inv_ne_zero w.ne_zero))))
  eq₁₂ := c.eq₁₂
  eq₁₃ := by
    calc
      _ = (b₁ : K)*c.z₁^2 - (b₁ : K)*(b₂ : K)*c.z₃^2 := by
        rw [hw]
        field_simp
      _ = _ := c.eq₁₃

/-- Normalization of an independently chosen third representative preserves the entire
common projective locus, including every zero coordinate and the locus at infinity. -/
def normalizeThird (d : K) (b₁ b₂ b₃ w : Kˣ)
    (hw : (b₃ : K) = (b₁ : K)*(b₂ : K)*(w : K)^2) :
    CommonCovering d b₁ b₂ b₃ ≃ Covering d b₁ b₂ where
  toFun := Quotient.map (normalizeThirdRep d b₁ b₂ b₃ w hw) (by
    rintro c c' ⟨a,ht,h₁,h₂,h₃⟩
    refine ⟨a,ht,h₁,h₂,?_⟩
    dsimp [normalizeThirdRep]
    rw [h₃]; ring)
  invFun := Quotient.map (unnormalizeThirdRep d b₁ b₂ b₃ w hw) (by
    rintro c c' ⟨a,ht,h₁,h₂,h₃⟩
    refine ⟨a,ht,h₁,h₂,?_⟩
    dsimp [unnormalizeThirdRep]
    rw [h₃]; ring)
  left_inv := by
    intro c
    induction c using Quotient.inductionOn with
    | h c =>
      apply Quotient.sound
      refine ⟨1,?_,?_,?_,?_⟩ <;> simp [normalizeThirdRep,unnormalizeThirdRep,mul_assoc]
  right_inv := by
    intro c
    induction c using Quotient.inductionOn with
    | h c =>
      apply Quotient.sound
      refine ⟨1,?_,?_,?_,?_⟩ <;> simp [normalizeThirdRep,unnormalizeThirdRep,mul_assoc]

private theorem third_witness (b₁ b₂ b₃ : Kˣ)
    (h : unitClass b₃ = unitClass b₁ + unitClass b₂) :
    ∃ w : Kˣ, (b₃ : K) = (b₁ : K)*(b₂ : K)*(w : K)^2 := by
  have h' : unitClass b₃ = unitClass (b₁*b₂) := h
  obtain ⟨w,hw⟩ := (class_eq_iff b₃ (b₁*b₂)).mp h'
  have hn : w ≠ 0 := by intro hh; apply b₃.ne_zero; simpa [hh] using hw
  exact ⟨Units.mk0 w hn,hw⟩

/-- The projective normalization is available from the squareclass product-one convention;
no squareclass injectivity or square reflection is assumed. -/
noncomputable def normalizeThirdOfClass (d : K) (b₁ b₂ b₃ : Kˣ)
    (h : unitClass b₃ = unitClass b₁ + unitClass b₂) :
    CommonCovering d b₁ b₂ b₃ ≃ Covering d b₁ b₂ :=
  normalizeThird d b₁ b₂ b₃ (third_witness b₁ b₂ b₃ h).choose
    (third_witness b₁ b₂ b₃ h).choose_spec

/-- Projection with an independently chosen third coefficient. Its finite ordinate is
`b₁*b₂*w*z₁*z₂*z₃/t³`, where `b₃=b₁*b₂*w²`. -/
def projectThird (d : K) (hd : d ≠ 0) (b₁ b₂ b₃ w : Kˣ)
    (hw : (b₃ : K) = (b₁ : K)*(b₂ : K)*(w : K)^2) :
    CommonCovering d b₁ b₂ b₃ → (curve d).Point :=
  project d hd b₁ b₂ ∘ normalizeThird d b₁ b₂ b₃ w hw


end D5.S3.Factorization.Mordell.FieldKummer
