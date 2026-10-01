import LeanInformationAuditInterface.Contract.Core
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord
import D5.S3.ConceptDynamics.InformationEscape.EscapeRecord
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/- L0 原型 -/
namespace LeanInformationAudit.Contract
open D5.S3.ConceptDynamics.InformationEscape
universe u v w t s r o a k

/-- Each original bridge is checked at the exact target proposition. The report
checks its constant identity and provenance, without supplying a missing proof. -/
inductive Implementation (P : Prop) :
    Type (max (u+1) (v+1) (w+1) (t+1) (s+1) (r+1) (o+1) (a+1) (k+1)) where
  | legacy (arena : PrimitiveLawArena.{u,v,w})
      (actual : PrimitiveRealization arena.signature)
      (bridge : Ref (LegacyPrimitiveRealization arena P actual))
  | forward (arena : PrimitiveLawArena.{u,v,w})
      (actual : PrimitiveRealization arena.signature)
      (bridge : Ref (EscapeRecord.EscapePrimitiveRealization arena P actual))
  | witness (arena : CounterexampleRecord.WitnessArena.{k})
      (actual : PrimitiveRealization arena.signature)
      (bridge : Ref (CounterexampleRecord.WitnessPrimitiveRealization arena P actual))
      (positive : arena.Law actual)
  | source (arena : DependentFamily.Arena.{t,s,r,o,a})
      (bridge : Ref (DependentFamily.Registration arena P))

end LeanInformationAudit.Contract
