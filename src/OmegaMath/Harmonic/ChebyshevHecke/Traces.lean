/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Harmonic.ChebyshevHecke.Character
public import OmegaMath.Harmonic.ChebyshevHecke.SpinShells

/-!
Omega original.

The rotation character at squared scalar overlap (1/5), evaluated without
denominator growth by the recurrence for its scaled integer numerator.
-/

noncomputable section
@[expose] public section

namespace Omega.Chebyshev.S5

def traceNumerator (n : Nat) : Int :=
  let twentyFive := i5.square
  first (Nat.rec (pair Int.one Int.one.neg)
    (fun _ p => pair (second p) ((i6.neg.mul (second p)).sub (twentyFive.mul (first p)))) n)

def traceRepresentative (n : Nat) : IntRatio :=
  IntRatio.value (traceNumerator n) (powFive n)

/-- The trace of the six-generator average in the rotation-character model.
Each defining matrix has characteristic polynomial (z^2-2z+5). In the complex
eigenbasis, dividing the two roots by the positive square root of five gives
product one and sum (2c) with (c^2=1/5). The symmetric-power character is
therefore the same for each generator by the even character identity. -/
def averageCharacter (n : Nat) : FiniteRatio :=
  E rationalRing ⟨Int.one, n4⟩ n

private theorem traceStep (n : Nat) :
    IntRatio.Equivalent
      (((IntRatio.value i6.neg n5).mul (traceRepresentative n.succ)).sub (traceRepresentative n))
      (traceRepresentative n.succ.succ) :=
  let d := powFive n
  let d₂ := powFive n.succ.succ
  let a := i6.neg.mul (traceNumerator n.succ)
  let b := (traceNumerator n).mul i5.square
  have denom : Eq (n5.mul (powFive n.succ)) d₂ := Nat.mul_comm n5 (powFive n.succ)
  have scale : Eq (d.mul (n5.mul n5)) d₂ := (Nat.mul_assoc d n5 n5).symm
  have left : Eq ((IntRatio.value i6.neg n5).mul (traceRepresentative n.succ))
      (IntRatio.value a d₂) :=
    (IntRatio.value_mul i6.neg (traceNumerator n.succ) n5 (powFive n.succ)).trans
      (congrArg (IntRatio.value a) denom)
  have right : IntRatio.Equivalent (traceRepresentative n) (IntRatio.value b d₂) :=
    Eq.subst (fun v => IntRatio.Equivalent (traceRepresentative n) (IntRatio.value b v))
      scale (IntRatio.value_scale_of_ne_zero (traceNumerator n) d (n5.mul n5)
        (Nat.succ_ne_zero _)).symm
  have out : Eq (a.add b.neg) (traceNumerator n.succ.succ) :=
    congrArg (fun t => a.sub t) (Int.mul_comm (traceNumerator n) i5.square)
  (IntRatio.sub_congr (Eq.subst (fun u => IntRatio.Equivalent u (IntRatio.value a d₂))
      left.symm (IntRatio.equivalent_refl _)) right).trans
    (Eq.subst (fun u => IntRatio.Equivalent ((IntRatio.value a d₂).sub (IntRatio.value b d₂))
        (IntRatio.value u d₂)) out
      (Eq.subst (fun u => IntRatio.Equivalent ((IntRatio.value a d₂).add u)
        (IntRatio.value (a.add b.neg) d₂)) (value_neg b d₂).symm
        (IntRatio.value_add_same a b.neg d₂)))
where
  value_neg (b : Int) (d : Nat) : Eq (IntRatio.value b d).neg (IntRatio.value b.neg d) :=
    Nat.rec (motive := fun d => Eq (IntRatio.value b d).neg (IntRatio.value b.neg d))
      Eq.refl (fun _ _ => Eq.refl) d

theorem average_character_eq_trace (n : Nat) :
    IntRatio.Equivalent (averageCharacter n).toRatio (traceRepresentative n) :=
  let κ : FiniteRatio := ⟨Int.one, n4⟩
  let q := evenCoefficient rationalRing κ
  let P := fun (n : Nat) => IntRatio.Equivalent (averageCharacter n).toRatio (traceRepresentative n)
  have hq : IntRatio.Equivalent q.toRatio (IntRatio.value i6.neg n5) := Eq.refl
  (Nat.rec (motive := fun n => And (P n) (P n.succ))
    (And.intro Eq.refl Eq.refl)
    (fun k ih => And.intro ih.right
      ((IntRatio.sub_congr (IntRatio.mul_congr hq ih.right) ih.left).trans (traceStep k))) n).left

/-- Decimal construction of a large natural via one place at a time. -/
def decimalStep (acc digit : Nat) : Nat := (acc.mul (n5.add n5)).add digit

def traceTable : Prop :=
  let d0 := Nat.zero
  let d7 := n6.succ
  let d8 := d7.succ
  let d9 := d8.succ
  let d := decimalStep
  let v := fun (num : Nat) => Int.ofNat num
  And (Eq (traceRepresentative n1) (IntRatio.value Int.one.neg n5))
    (And (Eq (traceRepresentative n2) (IntRatio.value (v (d n1 d9)).neg (d n2 n5)))
      (And (Eq (traceRepresentative n3) (IntRatio.value (v (d (d n1 n3) d9))
          (d (d n1 n2) n5)))
        (And (Eq (traceRepresentative n4) (IntRatio.value (v (d (d n3 n5) d9)).neg
            (d (d n6 n2) n5)))
          (And (Eq (traceRepresentative n5) (IntRatio.value (v (d (d (d n1 n3) n2) n1)).neg
              (d (d (d n3 n1) n2) n5)))
            (Eq (traceRepresentative n6) (IntRatio.value (v (d (d (d (d n1 n6) d9) d0) n1))
              (d (d (d (d n1 n5) n6) n2) n5)))))))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 6000000 in
theorem trace_table : traceTable :=
  And.intro Eq.refl
    (And.intro Eq.refl (And.intro Eq.refl (And.intro Eq.refl (And.intro Eq.refl Eq.refl))))

/-- Exact margins in the four finite shells, ordered by increasing degree.
The final pair has multiplicities two and three, respectively. -/
def MarginTable : Prop :=
  let d := decimalStep
  let seven := n6.succ
  let eight := seven.succ
  let nine := eight.succ
  let d0 := Nat.zero
  let predicted := fun num den => IntRatio.value (Int.ofNat num) den
  And (Eq (margin .degreeOne .false) (predicted (d n6 n4) n5))
    (And (Eq (margin .degreeTwo .false) (predicted (d (d n4 nine) n6) (d n2 n5)))
      (And (Eq (margin .degreeThree .false)
          (predicted (d (d (d n2 n1) seven) n6) (d (d n1 n2) n5)))
        (And (Eq (margin .degreeFour .false)
            (predicted (d (d (d nine n5) eight) n4) (d (d n6 n2) n5)))
          (Eq (margin .degreeFour .true)
            (predicted (d (d (d seven d0) n2) n4) (d (d n6 n2) n5))))))

set_option maxRecDepth 25000 in
set_option maxHeartbeats 2000000 in
theorem margin_table : MarginTable :=
  And.intro Eq.refl (And.intro Eq.refl (And.intro Eq.refl (And.intro Eq.refl Eq.refl)))

end Omega.Chebyshev.S5
