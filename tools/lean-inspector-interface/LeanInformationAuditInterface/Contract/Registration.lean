import LeanInformationAuditInterface.Contract.Implementation

namespace LeanInformationAudit.Contract
open Lean
universe aa bb d e f g h i j u v w t s r o a k

/-- A complete four-slot input. The implementation is indexed by the
target statement, including its original telescope. The report checks the bridge family,
constant identities, source ownership and all semantic policies. -/
structure Registration {P : Prop} (target : P)
    (A : Sort aa) (O : Sort bb)
    (Readout : Type d) (Variation : Sort f)
    (Sensitivity : Sort g) (From : Type h) (Residual : Sort i)
    (FamilyRecord : Sort j) where
  unitName : Name
  realizationName : Name
  realizationSource : Option Name
  generated : Bool
  arena : Ref A
  objectArena : Ref O
  catalog : Name
  localNames : Bool
  realization : Implementation.{u,v,w,t,s,r,o,a,k} P
  readout : Option Readout
  variation : Option (Ref Variation)
  sensitivity : Option (Ref Sensitivity)
  escapeFrom : Option From
  sourceSelection : Option SourceSelection
  continuation : Continuation Residual
  familyRecord : Option (Ref FamilyRecord)
  options : Array OptionSetting

end LeanInformationAudit.Contract
