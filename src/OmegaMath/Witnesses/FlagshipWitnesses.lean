module
prelude
public import OmegaMath.Matrix.Mat2
public import OmegaMath.Ternion.Heap
public import OmegaMath.Geometry.BargmannGram
public import OmegaMath.Computability.Fractran
public import OmegaMath.Arithmetic.Euclidean.Division

/-!
Omega original.

Concrete signed spinor and fraction-program witnesses, with the integer
determinant, ternion, and Gram identities needed alongside them.
-/

noncomputable section

@[expose] public section

namespace Omega

theorem mat2_det_mul (A B : Mat2) : Eq (A.mul B).det (A.det.mul B.det) :=
  Mat2.det_mul A B

theorem phalf_qhalf_noncommutative :
    Not (Ternion.RayEquiv (Ternion.triad Ternion.pHalf Ternion.p0 Ternion.qHalf)
      (Ternion.triad Ternion.qHalf Ternion.p0 Ternion.pHalf)) :=
  Ternion.triad_noncommutative

theorem orthogonal_triad_excess_quarter :
    IntRatio.Equivalent
      (Geometry.BargmannGram.detGram3 Geometry.BargmannGram.Quad4.one
        Geometry.BargmannGram.pHalf Geometry.BargmannGram.qHalf)
      (IntRatio.value Int.one Nat.one.succ.succ.succ) :=
  Geometry.BargmannGram.orthogonal_triad_excess

namespace PythSpinor

/-- The six homogeneous signed spinors, with the third and sixth given by the
radius-one antipode and identity. -/
def SixBeatOrbit : Prop :=
  let two := Nat.one.succ
  let three := two.succ
  let four := three.succ
  let five := four.succ
  let six := five.succ
  let pos := Int.one
  let neg := Int.one.neg
  let second := ofNumerator ⟨neg, pos, pos, pos⟩ Nat.one Eq.refl
  let fourth := ofNumerator ⟨neg, neg, neg, neg⟩ Nat.one Eq.refl
  let fifth := ofNumerator ⟨pos, neg, neg, neg⟩ Nat.one Eq.refl
  And (Equivalent (g120_spin.pow Nat.one) g120_spin)
    (And (Equivalent (g120_spin.pow two) second)
      (And (Equivalent (g120_spin.pow three) antipode)
        (And (Equivalent (g120_spin.pow four) fourth)
          (And (Equivalent (g120_spin.pow five) fifth)
            (And (Equivalent (g120_spin.pow six) one)
              (And (IntRatio.Equivalent (kappa_spin one (g120_spin.pow three)) (IntRatio.ofInt Int.zero))
                   (IntRatio.Equivalent (kappa_spin one (g120_spin.pow six)) (IntRatio.ofInt Int.one))))))))

theorem g120_spin_six_beat_orbit : SixBeatOrbit :=
  And.intro Eq.refl
    (And.intro Eq.refl
      (And.intro g120_third_beat.left
        (And.intro Eq.refl
          (And.intro Eq.refl
            (And.intro g120_sixth_beat.left
              (And.intro g120_third_beat.right g120_sixth_beat.right))))))

end PythSpinor

namespace Fractran


open Arithmetic (NatList)

abbrev two : Nat := Nat.one.succ
abbrev three : Nat := Nat.one.succ.succ
abbrev four : Nat := Nat.one.succ.succ.succ
abbrev five : Nat := Nat.one.succ.succ.succ.succ
abbrev six : Nat := Nat.one.succ.succ.succ.succ.succ
abbrev seven : Nat := Nat.one.succ.succ.succ.succ.succ.succ
abbrev eight : Nat := Nat.one.succ.succ.succ.succ.succ.succ.succ
abbrev nine : Nat := Nat.one.succ.succ.succ.succ.succ.succ.succ.succ
abbrev ten : Nat := Nat.one.succ.succ.succ.succ.succ.succ.succ.succ.succ

def appendDigit (previous digit : Nat) : Nat := (previous.mul ten).add digit

/-- Evaluate decimal digits stored with the least significant digit first. -/
def decimalValue (digits : NatList) : Nat :=
  NatList.rec Nat.zero (fun digit _ previous => appendDigit previous digit) digits

private def divideDigits (d : Nat) (digits : NatList) : Arithmetic.DivMod :=
  NatList.rec ⟨Nat.zero, Nat.zero⟩ (fun digit _ previous =>
    let next := Arithmetic.divMod (appendDigit previous.remainder digit) d
    ⟨appendDigit previous.quotient next.quotient, next.remainder⟩) digits

private theorem reassemble_digit (d q r u v digit : Nat)
    (last : Eq ((d.mul u).add v) (appendDigit r digit)) :
    Eq ((d.mul (appendDigit q u)).add v) (appendDigit ((d.mul q).add r) digit) :=
  ((congrArg (fun n : Nat => n.add v) (Nat.mul_add d (q.mul ten) u)).trans
    (Nat.add_assoc (d.mul (q.mul ten)) (d.mul u) v)).trans
    ((Eq.map₂ Nat.add (Nat.mul_assoc d q ten).symm last).trans
      ((Nat.add_assoc ((d.mul q).mul ten) (r.mul ten) digit).symm.trans
        (congrArg (fun n : Nat => n.add digit) (Nat.add_mul (d.mul q) r ten).symm)))

private theorem divideDigits_sound (d : Nat) (hd : Nat.lt Nat.zero d) (digits : NatList) :
    Eq ((d.mul (divideDigits d digits).quotient).add (divideDigits d digits).remainder)
      (decimalValue digits) :=
  NatList.rec (motive := fun ds =>
    Eq ((d.mul (divideDigits d ds).quotient).add (divideDigits d ds).remainder) (decimalValue ds))
    Eq.refl
    (fun digit ds ih =>
      let old := divideDigits d ds
      let next := Arithmetic.divMod (appendDigit old.remainder digit) d
      (reassemble_digit d old.quotient old.remainder next.quotient next.remainder digit
        (Arithmetic.divMod_spec (appendDigit old.remainder digit) d hd).left.symm).trans
        (congrArg (fun n => appendDigit n digit) ih)) digits

private theorem exact_decimalQuotient (d : Nat) (hd : Nat.lt Nat.zero d) (digits : NatList)
    (exact : Eq (divideDigits d digits).remainder Nat.zero) :
    Eq (d.mul (divideDigits d digits).quotient) (decimalValue digits) :=
  (congrArg (Nat.add (d.mul (divideDigits d digits).quotient)) exact.symm).trans
    (divideDigits_sound d hd digits)

private theorem skip_decimal (rule : Rule) (digits : NatList)
    (nonzero : Not (Eq (divideDigits rule.denominator digits).remainder Nat.zero))
    (bound : Nat.lt (divideDigits rule.denominator digits).remainder rule.denominator) :
    Not (Divides rule (decimalValue digits)) :=
  fun h => h.elim (fun _ eq =>
    nonzero (Arithmetic.divMod_remainder_unique
      ((divideDigits_sound rule.denominator (Nat.zero_le rule.denominatorPred) digits).trans eq.symm)
      bound (Nat.zero_le rule.denominatorPred)))

private theorem fire_decimal (rule : Rule) (rest : Program) (input output : NatList)
    (inputExact : Eq (divideDigits rule.denominator input).remainder Nat.zero)
    (outputExact : Eq (divideDigits rule.numerator output).remainder Nat.zero)
    (sameQuotient : Eq (divideDigits rule.denominator input).quotient
      (divideDigits rule.numerator output).quotient) :
    Step (.cons rule rest) (decimalValue input) (decimalValue output) :=
  Or.inl (Exists.intro (divideDigits rule.denominator input).quotient
    (And.intro (exact_decimalQuotient rule.denominator (Nat.zero_le rule.denominatorPred) input inputExact)
      ((Nat.mul_comm rule.numerator _).symm.trans
        ((congrArg rule.numerator.mul sameQuotient).trans
          (exact_decimalQuotient rule.numerator (Nat.zero_le rule.numeratorPred) output outputExact)))))

def rule11Over49 : Rule := ⟨appendDigit Nat.one Nat.zero, appendDigit four eight⟩
def rule7Over25 : Rule := ⟨six, appendDigit two four⟩
def rule5Over9 : Rule := ⟨four, eight⟩
def rule3Over4 : Rule := ⟨two, three⟩

/-- The four reduced FRACTRAN rules, in priority order. -/
def pOmega : Program :=
  .cons rule11Over49 (.cons rule7Over25 (.cons rule5Over9 (.cons rule3Over4 .nil)))

/-- Every entry in the trace is reached by an actual transition. -/
def Follows (prog : Program) : NatList → Nat → Prop :=
  NatList.rec (fun _ => True)
    (fun next _ remaining current => And (Step prog current next) (remaining next))

abbrev d131072 : NatList := (.cons two (.cons seven (.cons Nat.zero (.cons Nat.one (.cons three (.cons Nat.one (.nil)))))))
abbrev d98304 : NatList := (.cons four (.cons Nat.zero (.cons three (.cons eight (.cons nine (.nil))))))
abbrev d73728 : NatList := (.cons eight (.cons two (.cons seven (.cons three (.cons seven (.nil))))))
abbrev d40960 : NatList := (.cons Nat.zero (.cons six (.cons nine (.cons Nat.zero (.cons four (.nil))))))
abbrev d30720 : NatList := (.cons Nat.zero (.cons two (.cons seven (.cons Nat.zero (.cons three (.nil))))))
abbrev d23040 : NatList := (.cons Nat.zero (.cons four (.cons Nat.zero (.cons three (.cons two (.nil))))))
abbrev d12800 : NatList := (.cons Nat.zero (.cons Nat.zero (.cons eight (.cons two (.cons Nat.one (.nil))))))
abbrev d3584 : NatList := (.cons four (.cons eight (.cons five (.cons three (.nil)))))
abbrev d2688 : NatList := (.cons eight (.cons eight (.cons six (.cons two (.nil)))))
abbrev d2016 : NatList := (.cons six (.cons Nat.one (.cons Nat.zero (.cons two (.nil)))))
abbrev d1120 : NatList := (.cons Nat.zero (.cons two (.cons Nat.one (.cons Nat.one (.nil)))))
abbrev d840 : NatList := (.cons Nat.zero (.cons four (.cons eight (.nil))))
abbrev d630 : NatList := (.cons Nat.zero (.cons three (.cons six (.nil))))
abbrev d350 : NatList := (.cons Nat.zero (.cons five (.cons three (.nil))))
abbrev d98 : NatList := (.cons eight (.cons nine (.nil)))
abbrev d22 : NatList := (.cons two (.cons two (.nil)))

/-- The initial state, two to the seventeenth power. -/
def pOmegaStart : Nat := decimalValue d131072

def pOmegaFinal : Nat := decimalValue d22

/-- The fifteen states after the initial state, in execution order. -/
def pOmegaTrace : NatList :=
  .cons (decimalValue d98304) (.cons (decimalValue d73728) (.cons (decimalValue d40960) (
  .cons (decimalValue d30720) (.cons (decimalValue d23040) (.cons (decimalValue d12800) (
  .cons (decimalValue d3584) (.cons (decimalValue d2688) (.cons (decimalValue d2016) (
  .cons (decimalValue d1120) (.cons (decimalValue d840) (.cons (decimalValue d630) (
  .cons (decimalValue d350) (.cons (decimalValue d98) (.cons (decimalValue d22) (
  .nil)))))))))))))))

set_option maxRecDepth 4096 in
private theorem transition_1 : Step pOmega (decimalValue d131072) (decimalValue d98304) :=
  Step.skip (skip_decimal rule11Over49 d131072 (Nat.succ_ne_zero _) True.intro)
    (Step.skip (skip_decimal rule7Over25 d131072 (Nat.succ_ne_zero _) True.intro)
      (Step.skip (skip_decimal rule5Over9 d131072 (Nat.succ_ne_zero _) True.intro)
        (fire_decimal rule3Over4 .nil d131072 d98304 Eq.refl Eq.refl Eq.refl)))

set_option maxRecDepth 4096 in
private theorem transition_2 : Step pOmega (decimalValue d98304) (decimalValue d73728) :=
  Step.skip (skip_decimal rule11Over49 d98304 (Nat.succ_ne_zero _) True.intro)
    (Step.skip (skip_decimal rule7Over25 d98304 (Nat.succ_ne_zero _) True.intro)
      (Step.skip (skip_decimal rule5Over9 d98304 (Nat.succ_ne_zero _) True.intro)
        (fire_decimal rule3Over4 .nil d98304 d73728 Eq.refl Eq.refl Eq.refl)))

set_option maxRecDepth 4096 in
private theorem transition_3 : Step pOmega (decimalValue d73728) (decimalValue d40960) :=
  Step.skip (skip_decimal rule11Over49 d73728 (Nat.succ_ne_zero _) True.intro)
    (Step.skip (skip_decimal rule7Over25 d73728 (Nat.succ_ne_zero _) True.intro)
      (fire_decimal rule5Over9 (.cons rule3Over4 .nil) d73728 d40960 Eq.refl Eq.refl Eq.refl))

set_option maxRecDepth 4096 in
private theorem transition_4 : Step pOmega (decimalValue d40960) (decimalValue d30720) :=
  Step.skip (skip_decimal rule11Over49 d40960 (Nat.succ_ne_zero _) True.intro)
    (Step.skip (skip_decimal rule7Over25 d40960 (Nat.succ_ne_zero _) True.intro)
      (Step.skip (skip_decimal rule5Over9 d40960 (Nat.succ_ne_zero _) True.intro)
        (fire_decimal rule3Over4 .nil d40960 d30720 Eq.refl Eq.refl Eq.refl)))

set_option maxRecDepth 4096 in
private theorem transition_5 : Step pOmega (decimalValue d30720) (decimalValue d23040) :=
  Step.skip (skip_decimal rule11Over49 d30720 (Nat.succ_ne_zero _) True.intro)
    (Step.skip (skip_decimal rule7Over25 d30720 (Nat.succ_ne_zero _) True.intro)
      (Step.skip (skip_decimal rule5Over9 d30720 (Nat.succ_ne_zero _) True.intro)
        (fire_decimal rule3Over4 .nil d30720 d23040 Eq.refl Eq.refl Eq.refl)))

set_option maxRecDepth 4096 in
private theorem transition_6 : Step pOmega (decimalValue d23040) (decimalValue d12800) :=
  Step.skip (skip_decimal rule11Over49 d23040 (Nat.succ_ne_zero _) True.intro)
    (Step.skip (skip_decimal rule7Over25 d23040 (Nat.succ_ne_zero _) True.intro)
      (fire_decimal rule5Over9 (.cons rule3Over4 .nil) d23040 d12800 Eq.refl Eq.refl Eq.refl))

set_option maxRecDepth 4096 in
private theorem transition_7 : Step pOmega (decimalValue d12800) (decimalValue d3584) :=
  Step.skip (skip_decimal rule11Over49 d12800 (Nat.succ_ne_zero _) True.intro)
    (fire_decimal rule7Over25 (.cons rule5Over9 (.cons rule3Over4 .nil)) d12800 d3584 Eq.refl Eq.refl Eq.refl)

set_option maxRecDepth 4096 in
private theorem transition_8 : Step pOmega (decimalValue d3584) (decimalValue d2688) :=
  Step.skip (skip_decimal rule11Over49 d3584 (Nat.succ_ne_zero _) True.intro)
    (Step.skip (skip_decimal rule7Over25 d3584 (Nat.succ_ne_zero _) True.intro)
      (Step.skip (skip_decimal rule5Over9 d3584 (Nat.succ_ne_zero _) True.intro)
        (fire_decimal rule3Over4 .nil d3584 d2688 Eq.refl Eq.refl Eq.refl)))

set_option maxRecDepth 4096 in
private theorem transition_9 : Step pOmega (decimalValue d2688) (decimalValue d2016) :=
  Step.skip (skip_decimal rule11Over49 d2688 (Nat.succ_ne_zero _) True.intro)
    (Step.skip (skip_decimal rule7Over25 d2688 (Nat.succ_ne_zero _) True.intro)
      (Step.skip (skip_decimal rule5Over9 d2688 (Nat.succ_ne_zero _) True.intro)
        (fire_decimal rule3Over4 .nil d2688 d2016 Eq.refl Eq.refl Eq.refl)))

set_option maxRecDepth 4096 in
private theorem transition_10 : Step pOmega (decimalValue d2016) (decimalValue d1120) :=
  Step.skip (skip_decimal rule11Over49 d2016 (Nat.succ_ne_zero _) True.intro)
    (Step.skip (skip_decimal rule7Over25 d2016 (Nat.succ_ne_zero _) True.intro)
      (fire_decimal rule5Over9 (.cons rule3Over4 .nil) d2016 d1120 Eq.refl Eq.refl Eq.refl))

set_option maxRecDepth 4096 in
private theorem transition_11 : Step pOmega (decimalValue d1120) (decimalValue d840) :=
  Step.skip (skip_decimal rule11Over49 d1120 (Nat.succ_ne_zero _) True.intro)
    (Step.skip (skip_decimal rule7Over25 d1120 (Nat.succ_ne_zero _) True.intro)
      (Step.skip (skip_decimal rule5Over9 d1120 (Nat.succ_ne_zero _) True.intro)
        (fire_decimal rule3Over4 .nil d1120 d840 Eq.refl Eq.refl Eq.refl)))

set_option maxRecDepth 4096 in
private theorem transition_12 : Step pOmega (decimalValue d840) (decimalValue d630) :=
  Step.skip (skip_decimal rule11Over49 d840 (Nat.succ_ne_zero _) True.intro)
    (Step.skip (skip_decimal rule7Over25 d840 (Nat.succ_ne_zero _) True.intro)
      (Step.skip (skip_decimal rule5Over9 d840 (Nat.succ_ne_zero _) True.intro)
        (fire_decimal rule3Over4 .nil d840 d630 Eq.refl Eq.refl Eq.refl)))

set_option maxRecDepth 4096 in
private theorem transition_13 : Step pOmega (decimalValue d630) (decimalValue d350) :=
  Step.skip (skip_decimal rule11Over49 d630 (Nat.succ_ne_zero _) True.intro)
    (Step.skip (skip_decimal rule7Over25 d630 (Nat.succ_ne_zero _) True.intro)
      (fire_decimal rule5Over9 (.cons rule3Over4 .nil) d630 d350 Eq.refl Eq.refl Eq.refl))

set_option maxRecDepth 4096 in
private theorem transition_14 : Step pOmega (decimalValue d350) (decimalValue d98) :=
  Step.skip (skip_decimal rule11Over49 d350 (Nat.succ_ne_zero _) True.intro)
    (fire_decimal rule7Over25 (.cons rule5Over9 (.cons rule3Over4 .nil)) d350 d98 Eq.refl Eq.refl Eq.refl)

set_option maxRecDepth 4096 in
private theorem transition_15 : Step pOmega (decimalValue d98) (decimalValue d22) :=
  fire_decimal rule11Over49 (.cons rule7Over25 (.cons rule5Over9 (.cons rule3Over4 .nil))) d98 d22 Eq.refl Eq.refl Eq.refl


def traceLength (states : NatList) : Nat :=
  NatList.rec Nat.zero (fun _ _ length => length.succ) states

def traceFinal (states : NatList) : Nat → Nat :=
  NatList.rec (fun start => start) (fun next _ final _ => final next) states

theorem run_succ_first (prog : Program) (k n : Nat) :
    Eq (run prog k.succ n) (run prog k (advance prog n)) :=
  Nat.rec (motive := fun i => Eq (run prog i.succ n) (run prog i (advance prog n))) Eq.refl
    (fun _ ih => congrArg (advance prog) ih) k

theorem advance_of_step {prog : Program} {n m : Nat} (h : Step prog n m) :
    Eq (advance prog n) m :=
  congrArg (Result.rec (motive := fun _ => Nat) n (fun next => next)) (Step.sound h)

theorem run_follows (prog : Program) (states : NatList) (n : Nat) (h : Follows prog states n) :
    Eq (run prog (traceLength states) n) (traceFinal states n) :=
  (NatList.rec (motive := fun states => ∀ current, Follows prog states current →
    Eq (run prog (traceLength states) current) (traceFinal states current))
    (fun _ _ => Eq.refl)
    (fun next rest ih current h =>
      (run_succ_first prog (traceLength rest) current).trans
        ((congrArg (run prog (traceLength rest)) (advance_of_step h.left)).trans
          (ih next h.right))) states) n h

theorem p_omega_halts_at_22 :
    And (Follows pOmega pOmegaTrace pOmegaStart)
      (And (Eq (run pOmega (appendDigit Nat.one five) pOmegaStart) pOmegaFinal)
        (Halts pOmega pOmegaFinal)) :=
  have trace : Follows pOmega pOmegaTrace pOmegaStart :=
    And.intro transition_1 (And.intro transition_2 (And.intro transition_3 (
    And.intro transition_4 (And.intro transition_5 (And.intro transition_6 (
    And.intro transition_7 (And.intro transition_8 (And.intro transition_9 (
    And.intro transition_10 (And.intro transition_11 (And.intro transition_12 (
    And.intro transition_13 (And.intro transition_14 (And.intro transition_15 (True.intro)))))))))))))))

  have halted : Halts pOmega pOmegaFinal :=
    And.intro (skip_decimal rule11Over49 d22 (Nat.succ_ne_zero _) True.intro)
      (And.intro (skip_decimal rule7Over25 d22 (Nat.succ_ne_zero _) True.intro)
        (And.intro (skip_decimal rule5Over9 d22 (Nat.succ_ne_zero _) True.intro)
          (And.intro (skip_decimal rule3Over4 d22 (Nat.succ_ne_zero _) True.intro) True.intro)))
  And.intro trace (And.intro (run_follows pOmega pOmegaTrace pOmegaStart trace) halted)

end Fractran
end Omega
