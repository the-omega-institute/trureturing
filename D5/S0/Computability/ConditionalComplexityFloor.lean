/- GID: D5/S0/Computability/ConditionalComplexityFloor
   generality: G
   mirror-B: D5/B/S0/Computability/ConditionalComplexityFloor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonempty class with bounded realizing programs gives a conditional complexity floor. -/

module
prelude
import all OmegaInit.Prelude
public import D5.S0.Arithmetic.Euclidean.Division

namespace D5.S0.Computability.ConditionalComplexityFloor

open Omega

/-- Class members that have a realizing program within the supplied length budget. -/
@[expose] public def BudgetedRealizers {ClassMember : Type u} {Program : Type v}
    (realizes : ClassMember → Program → Prop)
    (length : Program → Nat) (budget : Nat) : ClassMember → Prop :=
  fun member => Exists (fun program => And (realizes member program) (Nat.le (length program) budget))

/-- A compiler with bounded overhead puts conditional complexity minus that overhead
below the length budget of a nonempty class of realizers. -/
public theorem conditional_complexity_floor {ClassMember : Type u} {Program : Type v}
    (realizes : ClassMember → Program → Prop)
    (length : Program → Nat)
    (budget conditionalComplexity overhead : Nat)
    (nonempty : Exists (BudgetedRealizers realizes length budget))
    (compile : ∀ member program, realizes member program →
      Nat.le conditionalComplexity (Nat.add (length program) overhead)) :
    Nat.le (Nat.sub conditionalComplexity overhead) budget :=
  nonempty.elim (fun member realizer =>
    realizer.elim (fun program witness =>
      Nat.sub_le_of_le_add (Nat.le_trans (compile member program witness.left)
        (Arithmetic.add_le_add_right witness.right overhead))))

private inductive One where
  | only

example : Exists (fun _ : One => Exists (fun _ : One => True)) :=
  Exists.intro .only (Exists.intro .only True.intro)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Nat.add Nat.sub Nat.pred in
/-- A program of length three with overhead two attains complexity five. -/
example :
    let two := Nat.zero.succ.succ
    let three := two.succ
    let five := three.succ.succ
    let realizes : One → One → Prop := fun _ _ => True
    let length : One → Nat := fun _ => three
    And (Exists (BudgetedRealizers realizes length three))
      (And (∀ member program, realizes member program → Nat.le five (Nat.add (length program) two))
        (Nat.le (Nat.sub five two) three)) :=
  let two := Nat.zero.succ.succ
  let three := two.succ
  let five := three.succ.succ
  And.intro (Exists.intro .only (Exists.intro .only (And.intro True.intro (Nat.le_refl three))))
    (And.intro (fun _ _ _ => Nat.le_refl five) (Nat.le_refl three))

end D5.S0.Computability.ConditionalComplexityFloor
