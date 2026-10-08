/- GID: D5/S3/PrimeForms/LiteralNegationTrigger
   generality: I
   mirror-B: D5/B/S3/PrimeForms/LiteralNegationTrigger
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/PrimeForms/LiteralNegationTrigger.claim; result=D5/S3/PrimeForms/LiteralNegationTrigger.result; claim=D5/S3/PrimeForms/LiteralNegationTrigger.claim
   digest: Two is not below two. -/

namespace D5.S3.PrimeForms.LiteralNegationTrigger

/-- Every natural number is below two. -/
def claim : Prop := ∀ n : Nat, n < 2

/-- Two is a counterexample. -/
theorem result : claim → False := fun h => absurd (h 2) (by decide)

end D5.S3.PrimeForms.LiteralNegationTrigger
