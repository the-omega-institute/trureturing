/- GID: D5/S0/History/Accounting/CumulativeTax
   generality: G
   mirror-B: D5/B/S0/History/Accounting/CumulativeTax
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Stepwise additive taxes accumulate to the terminal balance. -/

module
prelude
public import OmegaMath.Algebra.BigOperators.Range
public import OmegaMath.Topology.SimplicialCoboundary

namespace D5.S0.History.Accounting.CumulativeTax

open Omega

/-- If each transition adds its tax to the balance, the balance at any stage
is the initial balance plus the sum of the preceding taxes. -/
public theorem terminal_balance_eq_initial_add_tax
    {A : Type u} (group : AddCommGroup A) (laws : group.Laws) (balance tax : Nat → A)
    (step : ∀ index, Eq (balance index.succ) (group.add (balance index) (tax index)))
    (bound : Nat) :
    Eq (balance bound) (group.add (balance .zero) (sumRange group.zero group.add tax bound)) :=
  Nat.rec
    (motive := fun index =>
      Eq (balance index) (group.add (balance .zero) (sumRange group.zero group.add tax index)))
    (group.add_zero laws (balance .zero)).symm
    (fun index previous =>
      (step index).trans
        ((congrArg (fun total => group.add total (tax index)) previous).trans
          (laws.add_assoc (balance .zero) (sumRange group.zero group.add tax index) (tax index))))
    bound

end D5.S0.History.Accounting.CumulativeTax
