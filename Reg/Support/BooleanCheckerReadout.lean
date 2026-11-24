import Reg.Support.SingleDependentReadout

/-! Generic proof terms keep literal certificate evaluation out of audit elaboration. -/
namespace Reg.Support.BooleanCheckerReadout
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature (X : Type) :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => X) (fun _ => Bool)

/-- Reading a Boolean checker at an input preserves the complete success proposition. -/
theorem bridge {X : Type} (f : X → Bool) (x : X) :
    (f x = true) ↔
      (realize (signature X) (fun _ _ s => f s) (fun e => nomatch e)).readout
        () () x = true := Iff.rfl

/-- One successful input and one rejected input prove actual observational dependence. -/
theorem dependence {X : Type} (f : X → Bool) (x y : X)
    (hx : f x = true) (hy : f y = false) :
    ObservationalDependence (signature X)
      (realize (signature X) (fun _ _ s => f s) (fun e => nomatch e)) := by
  intro i
  refine ⟨(), x, y, ?_⟩
  change f x ≠ f y
  rw [hx, hy]
  decide

end Reg.Support.BooleanCheckerReadout
