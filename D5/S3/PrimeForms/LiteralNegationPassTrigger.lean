/- GID: D5/S3/PrimeForms/LiteralNegationPassTrigger
   generality: I
   mirror-B: D5/B/S3/PrimeForms/LiteralNegationPassTrigger
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/PrimeForms/LiteralNegationPassTrigger.claim; result=D5/S3/PrimeForms/LiteralNegationPassTrigger.result; claim=D5/S3/PrimeForms/LiteralNegationPassTrigger.claim
   digest: Two is not below two. -/

namespace TriggerFixtures.LiteralNegation

/-- Every natural number is below two. -/
def claim : Prop := ∀ n : Nat, n < 2

/-- Two is a counterexample. -/
theorem result : ¬ claim := fun h => absurd (h 2) (by decide)

end TriggerFixtures.LiteralNegation
