module
prelude

public import OmegaMath.Algebra.QuadraticExt.Ring
public import OmegaMath.Arithmetic.WDigits

/-!
Omega original.

The first three weights of the geometric sequence with a nonzero common scale
cannot agree with the first three positive Fibonacci weights.
-/

noncomputable section
@[expose] public section

namespace Omega.Arithmetic.WDigits

/-- The geometric sequence with first coefficient `w` and quotient `ratio`. -/
def geometricWeight (w ratio : FiniteRatio) (n : Nat) : FiniteRatio :=
  Nat.rec w (fun _ prev => prev.mul ratio) n

private theorem cancel_scale (scale : FiniteRatio) (hn : Not (Eq scale.num Int.zero))
    {x y : FiniteRatio} (h : FiniteRatio.Equivalent (scale.mul x) (scale.mul y)) :
    FiniteRatio.Equivalent x y :=
  let laws := rationalRingLaws
  have cancel (z : FiniteRatio) : FiniteRatio.Equivalent (scale.inv.mul (scale.mul z)) z :=
    laws.trans (laws.symm (laws.mul_assoc scale.inv scale z))
      (laws.trans (laws.mul_congr
        (laws.trans (laws.mul_comm scale.inv scale) (scale.mul_inv_cancel hn)) (laws.refl z))
        (laws.one_mul z))
  laws.trans (laws.symm (cancel x))
    (laws.trans (laws.mul_congr (laws.refl scale.inv) h) (cancel y))

private theorem two_squared_ne_three :
    Not (FiniteRatio.Equivalent ((FiniteRatio.ofInt Int.two).mul (FiniteRatio.ofInt Int.two))
      (FiniteRatio.ofInt (Int.ofNat Nat.one.succ.succ))) :=
  fun h =>
    have e : Eq (Nat.succ .zero) Nat.zero :=
      Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (congrArg Int.natAbs h)))
    Nat.succ_ne_zero .zero e

/-- A nonzero scaling cannot make the weights `1`, `2`, and `3` geometric. -/
theorem no_geometric_first_three (w ratio scale : FiniteRatio)
    (hn : Not (Eq scale.num Int.zero))
    (h₀ : FiniteRatio.Equivalent w scale)
    (h₁ : FiniteRatio.Equivalent (w.mul ratio) (scale.mul (FiniteRatio.ofInt Int.two)))
    (h₂ : FiniteRatio.Equivalent ((w.mul ratio).mul ratio)
      (scale.mul (FiniteRatio.ofInt (Int.ofNat Nat.one.succ.succ)))) : False :=
  let laws := rationalRingLaws
  have hRatio : FiniteRatio.Equivalent ratio (FiniteRatio.ofInt Int.two) :=
    cancel_scale scale hn (laws.trans (laws.mul_congr (laws.symm h₀) (laws.refl ratio)) h₁)
  have hSquare : FiniteRatio.Equivalent (ratio.mul ratio)
      (FiniteRatio.ofInt (Int.ofNat Nat.one.succ.succ)) :=
    cancel_scale scale hn (laws.trans (laws.symm (laws.mul_assoc scale ratio ratio))
      (laws.trans (laws.mul_congr (laws.mul_congr (laws.symm h₀) (laws.refl ratio))
        (laws.refl ratio)) h₂))
  two_squared_ne_three (laws.trans (laws.symm (laws.mul_congr hRatio hRatio)) hSquare)

/-- A geometric sequence agrees with every W weight up to a common scale. -/
def MatchesScaledWeights (first ratio scale : FiniteRatio) : Prop :=
  ∀ k : Nat, FiniteRatio.Equivalent (geometricWeight first ratio k)
    (scale.mul (FiniteRatio.ofInt (Int.ofNat (wValue k))))

/-- The W weights admit no geometric sequence with a nonzero common scale. -/
theorem no_scaled_geometric_weights :
    Not (Exists fun first : FiniteRatio => Exists fun ratio : FiniteRatio =>
      Exists fun scale : FiniteRatio =>
        And (Not (Eq scale.num Int.zero)) (MatchesScaledWeights first ratio scale)) :=
  fun witnesses => witnesses.elim fun first ratios => ratios.elim fun ratio scales =>
    scales.elim fun scale h => no_geometric_first_three first ratio scale h.left
      (rationalRingLaws.trans (h.right .zero) (rationalRingLaws.mul_one scale))
      (h.right Nat.one) (h.right Nat.one.succ)

end Omega.Arithmetic.WDigits
