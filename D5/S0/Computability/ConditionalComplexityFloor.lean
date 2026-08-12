/- GID: D5/S0/Computability/ConditionalComplexityFloor
   generality: G
   mirror-B: D5/B/S0/Computability/ConditionalComplexityFloor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonempty class with bounded realizing programs gives a conditional complexity floor. -/

import Mathlib.Data.Nat.Basic

namespace D5.S0.Computability.ConditionalComplexityFloor

/-- Class members that have a realizing program within the supplied length budget. -/
def BudgetedRealizers {ClassMember Program : Type*}
    (realizes : ClassMember -> Program -> Prop)
    (length : Program -> Nat) (budget : Nat) : Set ClassMember :=
  {f | exists p, realizes f p /\ length p <= budget}

/-- If every realizing program compiles to a conditional description with fixed overhead,
nonemptiness of the budgeted class forces conditional complexity minus that overhead below the
budget. -/
theorem conditional_complexity_floor {ClassMember Program : Type*}
    (realizes : ClassMember -> Program -> Prop)
    (length : Program -> Nat)
    (budget conditionalComplexity overhead : Nat)
    (hnonempty : (BudgetedRealizers realizes length budget).Nonempty)
    (hcompile : forall f p, realizes f p -> conditionalComplexity <= length p + overhead) :
    conditionalComplexity - overhead <= budget := by
  rcases hnonempty with ⟨f, p, hrealizes, hlength⟩
  rw [Nat.sub_le_iff_le_add]
  exact le_trans (hcompile f p hrealizes) (Nat.add_le_add_right hlength overhead)

/-- The member and program domains can both be inhabited. -/
example : Nonempty (Unit × Unit) := inferInstance

/-- A one-member class with a length-three program, complexity five, and overhead two satisfies
the hypotheses and attains the floor bound. -/
example :
    let realizes : Unit -> Unit -> Prop := fun _ _ => True
    let length : Unit -> Nat := fun _ => 3
    let budget := 3
    let conditionalComplexity := 5
    let overhead := 2
    (BudgetedRealizers realizes length budget).Nonempty /\
      (forall f p, realizes f p -> conditionalComplexity <= length p + overhead) /\
      conditionalComplexity - overhead <= budget := by
  dsimp
  exact ⟨⟨(), (), trivial, by decide⟩, fun _ _ _ => by decide, by decide⟩

end D5.S0.Computability.ConditionalComplexityFloor
