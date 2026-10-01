import LeanInformationAuditInterface.Contract.Core

/- L0 原型 -/
namespace LeanInformationAudit.Contract
open Lean
universe a b c d e f g h i j

/-- A complete four-slot input. Bridge is instantiated with the target theorem
statement, including its original telescope. The report checks the bridge family,
constant identities, source ownership and all semantic policies. -/
structure Registration {P : Prop} (target : P)
    (A : Sort a) (O : Sort b) (Bridge : Prop → Sort c)
    (Readout : Type d) (Bundle : Type e) (Variation : Sort f)
    (Sensitivity : Sort g) (From : Type h) (Residual : Sort i)
    (FamilyRecord : Sort j) where
  targetName : Name
  arena : Ref A
  objectArena : Ref O
  catalog : Name
  localNames : Bool
  realization : Ref (Bridge P)
  readout : Option Readout
  primitives : Option Bundle
  variation : Option (Ref Variation)
  sensitivity : Option (Ref Sensitivity)
  escapeFrom : Option From
  sourceSelection : Option SourceSelection
  continuation : Continuation Residual
  familyRecord : Option (Ref FamilyRecord)
  options : Options

end LeanInformationAudit.Contract
