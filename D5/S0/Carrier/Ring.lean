/- GID: D5/S0/Carrier/Ring
   generality: G
   mirror-B: D5/B/S0/Carrier/Ring
   mirror-E: none(waiver:pure-definition)
   anchors: [GICT-v3.6-I.1-definition-1.2]
   digest: Integer coordinates for the golden ring with phi squared equal to phi plus one. -/

import Mathlib.NumberTheory.Zsqrtd.Basic

namespace D5.S0.Carrier

/-- The golden integer `a + b * phi`, represented in the integral basis `(1, phi)`. -/
@[ext]
structure GoldenInt where
  a : ℤ
  b : ℤ
  deriving DecidableEq

instance : Zero GoldenInt := ⟨⟨0, 0⟩⟩
instance : One GoldenInt := ⟨⟨1, 0⟩⟩
instance : Add GoldenInt := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg GoldenInt := ⟨fun x => ⟨-x.a, -x.b⟩⟩

/-- Multiplication reduced by the defining relation `phi^2 = phi + 1`. -/
instance : Mul GoldenInt :=
  ⟨fun x y => ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩⟩

@[simp] theorem a_zero : (0 : GoldenInt).a = 0 := rfl
@[simp] theorem b_zero : (0 : GoldenInt).b = 0 := rfl
@[simp] theorem a_one : (1 : GoldenInt).a = 1 := rfl
@[simp] theorem b_one : (1 : GoldenInt).b = 0 := rfl
@[simp] theorem a_add (x y : GoldenInt) : (x + y).a = x.a + y.a := rfl
@[simp] theorem b_add (x y : GoldenInt) : (x + y).b = x.b + y.b := rfl
@[simp] theorem a_neg (x : GoldenInt) : (-x).a = -x.a := rfl
@[simp] theorem b_neg (x : GoldenInt) : (-x).b = -x.b := rfl
@[simp] theorem a_mul (x y : GoldenInt) : (x * y).a = x.a * y.a + x.b * y.b := rfl
@[simp] theorem b_mul (x y : GoldenInt) :
    (x * y).b = x.a * y.b + x.b * y.a + x.b * y.b := rfl

instance addCommGroup : AddCommGroup GoldenInt := by
  refine
    { sub := fun x y => x + -y
      nsmul := @nsmulRec GoldenInt ⟨0⟩ ⟨(· + ·)⟩
      zsmul := @zsmulRec GoldenInt ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩
        (@nsmulRec GoldenInt ⟨0⟩ ⟨(· + ·)⟩)
      add_assoc := ?_
      zero_add := ?_
      add_zero := ?_
      neg_add_cancel := ?_
      add_comm := ?_ } <;>
    intros <;> ext <;> simp [add_comm, add_left_comm]

instance addGroupWithOne : AddGroupWithOne GoldenInt :=
  { addCommGroup with
    natCast := fun n => ⟨n, 0⟩
    intCast := fun z => ⟨z, 0⟩ }

@[simp] theorem a_natCast (n : ℕ) : (n : GoldenInt).a = n := rfl
@[simp] theorem b_natCast (n : ℕ) : (n : GoldenInt).b = 0 := rfl
@[simp] theorem a_intCast (z : ℤ) : (z : GoldenInt).a = z := rfl
@[simp] theorem b_intCast (z : ℤ) : (z : GoldenInt).b = 0 := rfl

instance commRing : CommRing GoldenInt := by
  refine
    { addGroupWithOne with
      npow := @npowRec GoldenInt ⟨1⟩ ⟨(· * ·)⟩
      mul_assoc := ?_
      one_mul := ?_
      mul_one := ?_
      left_distrib := ?_
      right_distrib := ?_
      zero_mul := ?_
      mul_zero := ?_
      add_comm := ?_
      mul_comm := ?_ } <;>
    intros <;> ext <;> simp <;> ring

/-- The distinguished golden generator. -/
def phi : GoldenInt := ⟨0, 1⟩

@[simp] theorem phi_a : phi.a = 0 := rfl
@[simp] theorem phi_b : phi.b = 1 := rfl

/-- The defining fixed-point equation in the golden integer ring. -/
theorem phi_sq : phi ^ 2 = phi + 1 := by
  ext <;> norm_num [phi, pow_two]

/-- Twice `a + b*phi`, written as `(2a+b) + b*sqrt(5)` in mathlib's `Zsqrtd 5`. -/
def toZsqrtd (x : GoldenInt) : ℤ√5 := ⟨2 * x.a + x.b, x.b⟩

theorem toZsqrtd_injective : Function.Injective toZsqrtd := by
  intro x y h
  have hb : x.b = y.b := congr_arg Zsqrtd.im h
  have ha2 : 2 * x.a = 2 * y.a := by
    have := congr_arg Zsqrtd.re h
    simpa [toZsqrtd, hb] using this
  ext
  · omega
  · exact hb

theorem toZsqrtd_add (x y : GoldenInt) : toZsqrtd (x + y) = toZsqrtd x + toZsqrtd y := by
  apply Zsqrtd.ext
  · simp [toZsqrtd]
    ring
  · simp [toZsqrtd]

/-- The factor `2` records that `toZsqrtd` stores twice the algebraic integer. -/
theorem toZsqrtd_mul (x y : GoldenInt) :
    toZsqrtd x * toZsqrtd y = (2 : ℤ√5) * toZsqrtd (x * y) := by
  apply Zsqrtd.ext
  · simp [toZsqrtd]
    ring
  · simp [toZsqrtd]
    ring

end D5.S0.Carrier
